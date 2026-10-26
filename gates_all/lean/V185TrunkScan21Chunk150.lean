import V185TrunkScan21Chunk149

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1829709 : List Nat := [1, 6, 1, 2, 2, 2, 1, 1, 5]
def baseStart_1829709 : Nat := 118140960795 + 1829709 * 2 ^ 59
def prefixEnd_1829709 : Nat := 4983230072969 + 3 ^ 40 * 1829709 * 2
def baseEnd_1829709 : Nat := 417564522158883106143479

theorem tailTrace_1829709 : CollatzResearch.WordTrace tailWord_1829709 prefixEnd_1829709 417564522158883106143479 := by
  unfold tailWord_1829709
  simp only [CollatzResearch.WordTrace]
  refine ⟨66734969728284257263756181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44489979818856171509170787 66734969728284257263756181)
  ·
    refine ⟨3128201706013324559238571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 66734969728284257263756181 3128201706013324559238571)
    ·
      refine ⟨4692302559019986838857857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3128201706013324559238571 4692302559019986838857857)
      ·
        refine ⟨3519226919264990129143393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4692302559019986838857857 3519226919264990129143393)
        ·
          refine ⟨2639420189448742596857545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3519226919264990129143393 2639420189448742596857545)
          ·
            refine ⟨1979565142086556947643159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2639420189448742596857545 1979565142086556947643159)
            ·
              refine ⟨2969347713129835421464739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1979565142086556947643159 2969347713129835421464739)
              ·
                refine ⟨4454021569694753132197109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2969347713129835421464739 4454021569694753132197109)
                ·
                  refine ⟨417564522158883106143479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4454021569694753132197109 417564522158883106143479)
                  ·
                    rfl

theorem cell21_1829709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_1829709 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1829709 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1829709 prefixEnd_1829709 := by exact prefixLift 1829709
  have htrace : WordTrace (prefixWord ++ tailWord_1829709) baseStart_1829709 baseEnd_1829709 := by
    simpa [prefixWord, tailWord_1829709, baseEnd_1829709] using wordTrace_append hprefix tailTrace_1829709
  have hstable : (prefixWord ++ tailWord_1829709).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829709).length < 2 ^ (prefixWord ++ tailWord_1829709).sum := by decide
  have hdescent : baseEnd_1829709 < baseStart_1829709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829765 : List Nat := [1, 3, 1, 1, 3, 3, 1, 4, 4]
def baseStart_1829765 : Nat := 118140960795 + 1829765 * 2 ^ 59
def prefixEnd_1829765 : Nat := 4983230072969 + 3 ^ 40 * 1829765 * 2
def baseEnd_1829765 : Nat := 417577302121839453210031

theorem tailTrace_1829765 : CollatzResearch.WordTrace tailWord_1829765 prefixEnd_1829765 417577302121839453210031 := by
  unfold tailWord_1829765
  simp only [CollatzResearch.WordTrace]
  refine ⟨66737012216081378827794749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44491341477387585885196499 66737012216081378827794749)
  ·
    refine ⟨25026379581030517060423031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66737012216081378827794749 25026379581030517060423031)
    ·
      refine ⟨37539569371545775590634547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25026379581030517060423031 37539569371545775590634547)
      ·
        refine ⟨56309354057318663385951821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37539569371545775590634547 56309354057318663385951821)
        ·
          refine ⟨21116007771494498769731933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56309354057318663385951821 21116007771494498769731933)
          ·
            refine ⟨7918502914310437038649475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21116007771494498769731933 7918502914310437038649475)
            ·
              refine ⟨11877754371465655557974213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7918502914310437038649475 11877754371465655557974213)
              ·
                refine ⟨2227078944649810417120165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11877754371465655557974213 2227078944649810417120165)
                ·
                  refine ⟨417577302121839453210031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2227078944649810417120165 417577302121839453210031)
                  ·
                    rfl

theorem cell21_1829765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 4, 4].length) (baseStart_1829765 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1829765 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1829765 prefixEnd_1829765 := by exact prefixLift 1829765
  have htrace : WordTrace (prefixWord ++ tailWord_1829765) baseStart_1829765 baseEnd_1829765 := by
    simpa [prefixWord, tailWord_1829765, baseEnd_1829765] using wordTrace_append hprefix tailTrace_1829765
  have hstable : (prefixWord ++ tailWord_1829765).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829765).length < 2 ^ (prefixWord ++ tailWord_1829765).sum := by decide
  have hdescent : baseEnd_1829765 < baseStart_1829765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829768 : List Nat := [2, 1, 3, 3, 2, 2, 1, 4, 3]
def baseStart_1829768 : Nat := 118140960795 + 1829768 * 2 ^ 59
def prefixEnd_1829768 : Nat := 4983230072969 + 3 ^ 40 * 1829768 * 2
def baseEnd_1829768 : Nat := 417577986762712114660025

theorem tailTrace_1829768 : CollatzResearch.WordTrace tailWord_1829768 prefixEnd_1829768 417577986762712114660025 := by
  unfold tailWord_1829768
  simp only [CollatzResearch.WordTrace]
  refine ⟨33368560817535255170076979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44491414423380340226769305 33368560817535255170076979)
  ·
    refine ⟨50052841226302882755115469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33368560817535255170076979 50052841226302882755115469)
    ·
      refine ⟨18769815459863581033168301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50052841226302882755115469 18769815459863581033168301)
      ·
        refine ⟨7038680797448842887438113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18769815459863581033168301 7038680797448842887438113)
        ·
          refine ⟨5279010598086632165578585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7038680797448842887438113 5279010598086632165578585)
          ·
            refine ⟨3959257948564974124183939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5279010598086632165578585 3959257948564974124183939)
            ·
              refine ⟨5938886922847461186275909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3959257948564974124183939 5938886922847461186275909)
              ·
                refine ⟨1113541298033898972426733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5938886922847461186275909 1113541298033898972426733)
                ·
                  refine ⟨417577986762712114660025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1113541298033898972426733 417577986762712114660025)
                  ·
                    rfl

theorem cell21_1829768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 4, 3].length) (baseStart_1829768 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1829768 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1829768 prefixEnd_1829768 := by exact prefixLift 1829768
  have htrace : WordTrace (prefixWord ++ tailWord_1829768) baseStart_1829768 baseEnd_1829768 := by
    simpa [prefixWord, tailWord_1829768, baseEnd_1829768] using wordTrace_append hprefix tailTrace_1829768
  have hstable : (prefixWord ++ tailWord_1829768).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829768).length < 2 ^ (prefixWord ++ tailWord_1829768).sum := by decide
  have hdescent : baseEnd_1829768 < baseStart_1829768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829796 : List Nat := [2, 3, 1, 2, 1, 2, 5, 5]
def baseStart_1829796 : Nat := 118140960795 + 1829796 * 2 ^ 59
def prefixEnd_1829796 : Nat := 4983230072969 + 3 ^ 40 * 1829796 * 2
def baseEnd_1829796 : Nat := 139194792248063429397767

theorem tailTrace_1829796 : CollatzResearch.WordTrace tailWord_1829796 prefixEnd_1829796 139194792248063429397767 := by
  unfold tailWord_1829796
  simp only [CollatzResearch.WordTrace]
  refine ⟨33369071439484535561086621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44492095252646047414782161 33369071439484535561086621)
  ·
    refine ⟨12513401789806700835407483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33369071439484535561086621 12513401789806700835407483)
    ·
      refine ⟨18770102684710051253111225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12513401789806700835407483 18770102684710051253111225)
      ·
        refine ⟨14077577013532538439833419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18770102684710051253111225 14077577013532538439833419)
        ·
          refine ⟨21116365520298807659750129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14077577013532538439833419 21116365520298807659750129)
          ·
            refine ⟨15837274140224105744812597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21116365520298807659750129 15837274140224105744812597)
            ·
              refine ⟨1484744450646009913576181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15837274140224105744812597 1484744450646009913576181)
              ·
                refine ⟨139194792248063429397767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1484744450646009913576181 139194792248063429397767)
                ·
                  rfl

theorem cell21_1829796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 5, 5].length) (baseStart_1829796 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1829796 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1829796 prefixEnd_1829796 := by exact prefixLift 1829796
  have htrace : WordTrace (prefixWord ++ tailWord_1829796) baseStart_1829796 baseEnd_1829796 := by
    simpa [prefixWord, tailWord_1829796, baseEnd_1829796] using wordTrace_append hprefix tailTrace_1829796
  have hstable : (prefixWord ++ tailWord_1829796).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829796).length < 2 ^ (prefixWord ++ tailWord_1829796).sum := by decide
  have hdescent : baseEnd_1829796 < baseStart_1829796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829858 : List Nat := [3, 3, 3, 1, 1, 1, 1, 2, 6]
def baseStart_1829858 : Nat := 118140960795 + 1829858 * 2 ^ 59
def prefixEnd_1829858 : Nat := 4983230072969 + 3 ^ 40 * 1829858 * 2
def baseEnd_1829858 : Nat := 417598525988891958159841

theorem tailTrace_1829858 : CollatzResearch.WordTrace tailWord_1829858 prefixEnd_1829858 417598525988891958159841 := by
  unfold tailWord_1829858
  simp only [CollatzResearch.WordTrace]
  refine ⟨16685101051186113927732557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44493602803162970473953485 16685101051186113927732557)
  ·
    refine ⟨6256912894194792722899709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16685101051186113927732557 6256912894194792722899709)
    ·
      refine ⟨2346342335323047271087391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6256912894194792722899709 2346342335323047271087391)
      ·
        refine ⟨3519513502984570906631087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2346342335323047271087391 3519513502984570906631087)
        ·
          refine ⟨5279270254476856359946631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3519513502984570906631087 5279270254476856359946631)
          ·
            refine ⟨7918905381715284539919947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5279270254476856359946631 7918905381715284539919947)
            ·
              refine ⟨11878358072572926809879921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7918905381715284539919947 11878358072572926809879921)
              ·
                refine ⟨8908768554429695107409941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11878358072572926809879921 8908768554429695107409941)
                ·
                  refine ⟨417598525988891958159841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8908768554429695107409941 417598525988891958159841)
                  ·
                    rfl

theorem cell21_1829858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_1829858 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1829858 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1829858 prefixEnd_1829858 := by exact prefixLift 1829858
  have htrace : WordTrace (prefixWord ++ tailWord_1829858) baseStart_1829858 baseEnd_1829858 := by
    simpa [prefixWord, tailWord_1829858, baseEnd_1829858] using wordTrace_append hprefix tailTrace_1829858
  have hstable : (prefixWord ++ tailWord_1829858).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829858).length < 2 ^ (prefixWord ++ tailWord_1829858).sum := by decide
  have hdescent : baseEnd_1829858 < baseStart_1829858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829934 : List Nat := [4, 1, 3, 1, 1, 1, 4, 2, 4]
def baseStart_1829934 : Nat := 118140960795 + 1829934 * 2 ^ 59
def prefixEnd_1829934 : Nat := 4983230072969 + 3 ^ 40 * 1829934 * 2
def baseEnd_1829934 : Nat := 417615870224332714893019

theorem tailTrace_1829934 : CollatzResearch.WordTrace tailWord_1829934 prefixEnd_1829934 417615870224332714893019 := by
  unfold tailWord_1829934
  simp only [CollatzResearch.WordTrace]
  refine ⟨8342897019058640086337107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44495450768312747127131237 8342897019058640086337107)
  ·
    refine ⟨12514345528587960129505661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8342897019058640086337107 12514345528587960129505661)
    ·
      refine ⟨4692879573220485048564623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12514345528587960129505661 4692879573220485048564623)
      ·
        refine ⟨7039319359830727572846935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4692879573220485048564623 7039319359830727572846935)
        ·
          refine ⟨10558979039746091359270403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7039319359830727572846935 10558979039746091359270403)
          ·
            refine ⟨15838468559619137038905605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10558979039746091359270403 15838468559619137038905605)
            ·
              refine ⟨2969712854928588194794801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15838468559619137038905605 2969712854928588194794801)
              ·
                refine ⟨2227284641196441146096101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2969712854928588194794801 2227284641196441146096101)
                ·
                  refine ⟨417615870224332714893019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2227284641196441146096101 417615870224332714893019)
                  ·
                    rfl

theorem cell21_1829934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 2, 4].length) (baseStart_1829934 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1829934 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1829934 prefixEnd_1829934 := by exact prefixLift 1829934
  have htrace : WordTrace (prefixWord ++ tailWord_1829934) baseStart_1829934 baseEnd_1829934 := by
    simpa [prefixWord, tailWord_1829934, baseEnd_1829934] using wordTrace_append hprefix tailTrace_1829934
  have hstable : (prefixWord ++ tailWord_1829934).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829934).length < 2 ^ (prefixWord ++ tailWord_1829934).sum := by decide
  have hdescent : baseEnd_1829934 < baseStart_1829934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829948 : List Nat := [2, 2, 2, 2, 2, 4, 1, 6]
def baseStart_1829948 : Nat := 118140960795 + 1829948 * 2 ^ 59
def prefixEnd_1829948 : Nat := 4983230072969 + 3 ^ 40 * 1829948 * 2
def baseEnd_1829948 : Nat := 139206355071690600553219

theorem tailTrace_1829948 : CollatzResearch.WordTrace tailWord_1829948 prefixEnd_1829948 139206355071690600553219 := by
  unfold tailWord_1829948
  simp only [CollatzResearch.WordTrace]
  refine ⟨33371843387209200540853249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44495791182945600721137665 33371843387209200540853249)
  ·
    refine ⟨25028882540406900405639937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33371843387209200540853249 25028882540406900405639937)
    ·
      refine ⟨18771661905305175304229953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25028882540406900405639937 18771661905305175304229953)
      ·
        refine ⟨14078746428978881478172465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18771661905305175304229953 14078746428978881478172465)
        ·
          refine ⟨10559059821734161108629349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14078746428978881478172465 10559059821734161108629349)
          ·
            refine ⟨1979823716575155207868003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10559059821734161108629349 1979823716575155207868003)
            ·
              refine ⟨2969735574862732811802005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1979823716575155207868003 2969735574862732811802005)
              ·
                refine ⟨139206355071690600553219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2969735574862732811802005 139206355071690600553219)
                ·
                  rfl

theorem cell21_1829948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 6].length) (baseStart_1829948 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1829948 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1829948 prefixEnd_1829948 := by exact prefixLift 1829948
  have htrace : WordTrace (prefixWord ++ tailWord_1829948) baseStart_1829948 baseEnd_1829948 := by
    simpa [prefixWord, tailWord_1829948, baseEnd_1829948] using wordTrace_append hprefix tailTrace_1829948
  have hstable : (prefixWord ++ tailWord_1829948).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829948).length < 2 ^ (prefixWord ++ tailWord_1829948).sum := by decide
  have hdescent : baseEnd_1829948 < baseStart_1829948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829965 : List Nat := [1, 6, 1, 1, 1, 3, 3, 5]
def baseStart_1829965 : Nat := 118140960795 + 1829965 * 2 ^ 59
def prefixEnd_1829965 : Nat := 4983230072969 + 3 ^ 40 * 1829965 * 2
def baseEnd_1829965 : Nat := 139207648282227849958763

theorem tailTrace_1829965 : CollatzResearch.WordTrace tailWord_1829965 prefixEnd_1829965 139207648282227849958763 := by
  unfold tailWord_1829965
  simp only [CollatzResearch.WordTrace]
  refine ⟨66744306815356812985075349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44496204543571208656716899 66744306815356812985075349)
  ·
    refine ⟨3128639381969850608675407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 66744306815356812985075349 3128639381969850608675407)
    ·
      refine ⟨4692959072954775913013111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3128639381969850608675407 4692959072954775913013111)
      ·
        refine ⟨7039438609432163869519667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4692959072954775913013111 7039438609432163869519667)
        ·
          refine ⟨10559157914148245804279501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7039438609432163869519667 10559157914148245804279501)
          ·
            refine ⟨3959684217805592176604813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10559157914148245804279501 3959684217805592176604813)
            ·
              refine ⟨1484881581677097066226805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3959684217805592176604813 1484881581677097066226805)
              ·
                refine ⟨139207648282227849958763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1484881581677097066226805 139207648282227849958763)
                ·
                  rfl

theorem cell21_1829965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 3, 5].length) (baseStart_1829965 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1829965 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1829965 prefixEnd_1829965 := by exact prefixLift 1829965
  have htrace : WordTrace (prefixWord ++ tailWord_1829965) baseStart_1829965 baseEnd_1829965 := by
    simpa [prefixWord, tailWord_1829965, baseEnd_1829965] using wordTrace_append hprefix tailTrace_1829965
  have hstable : (prefixWord ++ tailWord_1829965).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829965).length < 2 ^ (prefixWord ++ tailWord_1829965).sum := by decide
  have hdescent : baseEnd_1829965 < baseStart_1829965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829976 : List Nat := [2, 1, 2, 2, 1, 3, 2, 2, 6]
def baseStart_1829976 : Nat := 118140960795 + 1829976 * 2 ^ 59
def prefixEnd_1829976 : Nat := 4983230072969 + 3 ^ 40 * 1829976 * 2
def baseEnd_1829976 : Nat := 417625455196549975192933

theorem tailTrace_1829976 : CollatzResearch.WordTrace tailWord_1829976 prefixEnd_1829976 417625455196549975192933 := by
  unfold tailWord_1829976
  simp only [CollatzResearch.WordTrace]
  refine ⟨33372354009158480931862891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44496472012211307909150521 33372354009158480931862891)
  ·
    refine ⟨50058531013737721397794337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33372354009158480931862891 50058531013737721397794337)
    ·
      refine ⟨37543898260303291048345753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50058531013737721397794337 37543898260303291048345753)
      ·
        refine ⟨28157923695227468286259315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37543898260303291048345753 28157923695227468286259315)
        ·
          refine ⟨42236885542841202429388973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28157923695227468286259315 42236885542841202429388973)
          ·
            refine ⟨15838832078565450911020865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42236885542841202429388973 15838832078565450911020865)
            ·
              refine ⟨11879124058924088183265649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15838832078565450911020865 11879124058924088183265649)
              ·
                refine ⟨8909343044193066137449237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11879124058924088183265649 8909343044193066137449237)
                ·
                  refine ⟨417625455196549975192933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8909343044193066137449237 417625455196549975192933)
                  ·
                    rfl

theorem cell21_1829976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 6].length) (baseStart_1829976 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1829976 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1829976 prefixEnd_1829976 := by exact prefixLift 1829976
  have htrace : WordTrace (prefixWord ++ tailWord_1829976) baseStart_1829976 baseEnd_1829976 := by
    simpa [prefixWord, tailWord_1829976, baseEnd_1829976] using wordTrace_append hprefix tailTrace_1829976
  have hstable : (prefixWord ++ tailWord_1829976).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829976).length < 2 ^ (prefixWord ++ tailWord_1829976).sum := by decide
  have hdescent : baseEnd_1829976 < baseStart_1829976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829993 : List Nat := [1, 2, 1, 1, 1, 6, 3, 2, 4]
def baseStart_1829993 : Nat := 118140960795 + 1829993 * 2 ^ 59
def prefixEnd_1829993 : Nat := 4983230072969 + 3 ^ 40 * 1829993 * 2
def baseEnd_1829993 : Nat := 417629334828161723409565

theorem tailTrace_1829993 : CollatzResearch.WordTrace tailWord_1829993 prefixEnd_1829993 417629334828161723409565 := by
  unfold tailWord_1829993
  simp only [CollatzResearch.WordTrace]
  refine ⟨66745328059255373767094633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44496885372836915844729755 66745328059255373767094633)
  ·
    refine ⟨50058996044441530325320975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66745328059255373767094633 50058996044441530325320975)
    ·
      refine ⟨75088494066662295487981463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50058996044441530325320975 75088494066662295487981463)
      ·
        refine ⟨112632741099993443231972195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75088494066662295487981463 112632741099993443231972195)
        ·
          refine ⟨168949111649990164847958293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112632741099993443231972195 168949111649990164847958293)
          ·
            refine ⟨7919489608593288977248045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 168949111649990164847958293 7919489608593288977248045)
            ·
              refine ⟨2969808603222483366468017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7919489608593288977248045 2969808603222483366468017)
              ·
                refine ⟨2227356452416862524851013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2969808603222483366468017 2227356452416862524851013)
                ·
                  refine ⟨417629334828161723409565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2227356452416862524851013 417629334828161723409565)
                  ·
                    rfl

theorem cell21_1829993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 2, 4].length) (baseStart_1829993 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1829993 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1829993 prefixEnd_1829993 := by exact prefixLift 1829993
  have htrace : WordTrace (prefixWord ++ tailWord_1829993) baseStart_1829993 baseEnd_1829993 := by
    simpa [prefixWord, tailWord_1829993, baseEnd_1829993] using wordTrace_append hprefix tailTrace_1829993
  have hstable : (prefixWord ++ tailWord_1829993).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829993).length < 2 ^ (prefixWord ++ tailWord_1829993).sum := by decide
  have hdescent : baseEnd_1829993 < baseStart_1829993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830024 : List Nat := [2, 1, 3, 4, 2, 1, 1, 7]
def baseStart_1830024 : Nat := 118140960795 + 1830024 * 2 ^ 59
def prefixEnd_1830024 : Nat := 4983230072969 + 3 ^ 40 * 1830024 * 2
def baseEnd_1830024 : Nat := 139212136483504186130945

theorem tailTrace_1830024 : CollatzResearch.WordTrace tailWord_1830024 prefixEnd_1830024 139212136483504186130945 := by
  unfold tailWord_1830024
  simp only [CollatzResearch.WordTrace]
  refine ⟨33373229361071533030736563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44497639148095377374315417 33373229361071533030736563)
  ·
    refine ⟨50059844041607299546104845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33373229361071533030736563 50059844041607299546104845)
    ·
      refine ⟨18772441515602737329789317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50059844041607299546104845 18772441515602737329789317)
      ·
        refine ⟨3519832784175513249335497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18772441515602737329789317 3519832784175513249335497)
        ·
          refine ⟨2639874588131634937001623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3519832784175513249335497 2639874588131634937001623)
          ·
            refine ⟨3959811882197452405502435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2639874588131634937001623 3959811882197452405502435)
            ·
              refine ⟨5939717823296178608253653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3959811882197452405502435 5939717823296178608253653)
              ·
                refine ⟨139212136483504186130945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5939717823296178608253653 139212136483504186130945)
                ·
                  rfl

theorem cell21_1830024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 7].length) (baseStart_1830024 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1830024 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1830024 prefixEnd_1830024 := by exact prefixLift 1830024
  have htrace : WordTrace (prefixWord ++ tailWord_1830024) baseStart_1830024 baseEnd_1830024 := by
    simpa [prefixWord, tailWord_1830024, baseEnd_1830024] using wordTrace_append hprefix tailTrace_1830024
  have hstable : (prefixWord ++ tailWord_1830024).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830024).length < 2 ^ (prefixWord ++ tailWord_1830024).sum := by decide
  have hdescent : baseEnd_1830024 < baseStart_1830024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830055 : List Nat := [1, 1, 6, 2, 1, 1, 3, 1, 5]
def baseStart_1830055 : Nat := 118140960795 + 1830055 * 2 ^ 59
def prefixEnd_1830055 : Nat := 4983230072969 + 3 ^ 40 * 1830055 * 2
def baseEnd_1830055 : Nat := 417643484072863393376105

theorem tailTrace_1830055 : CollatzResearch.WordTrace tailWord_1830055 prefixEnd_1830055 417643484072863393376105 := by
  unfold tailWord_1830055
  simp only [CollatzResearch.WordTrace]
  refine ⟨66747589385030758355851619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44498392923353838903901079 66747589385030758355851619)
  ·
    refine ⟨100121384077546137533777429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66747589385030758355851619 100121384077546137533777429)
    ·
      refine ⟨4693189878634975196895817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 100121384077546137533777429 4693189878634975196895817)
      ·
        refine ⟨3519892408976231397671863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4693189878634975196895817 3519892408976231397671863)
        ·
          refine ⟨5279838613464347096507795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3519892408976231397671863 5279838613464347096507795)
          ·
            refine ⟨7919757920196520644761693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5279838613464347096507795 7919757920196520644761693)
            ·
              refine ⟨2969909220073695241785635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7919757920196520644761693 2969909220073695241785635)
              ·
                refine ⟨4454863830110542862678453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2969909220073695241785635 4454863830110542862678453)
                ·
                  refine ⟨417643484072863393376105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4454863830110542862678453 417643484072863393376105)
                  ·
                    rfl

theorem cell21_1830055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 1, 5].length) (baseStart_1830055 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1830055 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1830055 prefixEnd_1830055 := by exact prefixLift 1830055
  have htrace : WordTrace (prefixWord ++ tailWord_1830055) baseStart_1830055 baseEnd_1830055 := by
    simpa [prefixWord, tailWord_1830055, baseEnd_1830055] using wordTrace_append hprefix tailTrace_1830055
  have hstable : (prefixWord ++ tailWord_1830055).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830055).length < 2 ^ (prefixWord ++ tailWord_1830055).sum := by decide
  have hdescent : baseEnd_1830055 < baseStart_1830055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830100 : List Nat := [2, 4, 1, 4, 1, 9]
def baseStart_1830100 : Nat := 118140960795 + 1830100 * 2 ^ 59
def prefixEnd_1830100 : Nat := 4983230072969 + 3 ^ 40 * 1830100 * 2
def baseEnd_1830100 : Nat := 15468657543924196856519

theorem tailTrace_1830100 : CollatzResearch.WordTrace tailWord_1830100 prefixEnd_1830100 15468657543924196856519 := by
  unfold tailWord_1830100
  simp only [CollatzResearch.WordTrace]
  refine ⟨33374615334933865520619877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44499487113245154027493169 33374615334933865520619877)
  ·
    refine ⟨6257740375300099785116227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33374615334933865520619877 6257740375300099785116227)
    ·
      refine ⟨9386610562950149677674341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6257740375300099785116227 9386610562950149677674341)
      ·
        refine ⟨1759989480553153064563939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9386610562950149677674341 1759989480553153064563939)
        ·
          refine ⟨2639984220829729596845909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1759989480553153064563939 2639984220829729596845909)
          ·
            refine ⟨15468657543924196856519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2639984220829729596845909 15468657543924196856519)
            ·
              rfl

theorem cell21_1830100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 9].length) (baseStart_1830100 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1830100 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1830100 prefixEnd_1830100 := by exact prefixLift 1830100
  have htrace : WordTrace (prefixWord ++ tailWord_1830100) baseStart_1830100 baseEnd_1830100 := by
    simpa [prefixWord, tailWord_1830100, baseEnd_1830100] using wordTrace_append hprefix tailTrace_1830100
  have hstable : (prefixWord ++ tailWord_1830100).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830100).length < 2 ^ (prefixWord ++ tailWord_1830100).sum := by decide
  have hdescent : baseEnd_1830100 < baseStart_1830100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830117 : List Nat := [1, 3, 1, 4, 4, 1, 1, 6]
def baseStart_1830117 : Nat := 118140960795 + 1830117 * 2 ^ 59
def prefixEnd_1830117 : Nat := 4983230072969 + 3 ^ 40 * 1830117 * 2
def baseEnd_1830117 : Nat := 139219211105855021114215

theorem tailTrace_1830117 : CollatzResearch.WordTrace tailWord_1830117 prefixEnd_1830117 139219211105855021114215 := by
  unfold tailWord_1830117
  simp only [CollatzResearch.WordTrace]
  refine ⟨66749850710806142944608605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44499900473870761963072403 66749850710806142944608605)
  ·
    refine ⟨25031194016552303604228227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66749850710806142944608605 25031194016552303604228227)
    ·
      refine ⟨37546791024828455406342341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25031194016552303604228227 37546791024828455406342341)
      ·
        refine ⟨7040023317155335388689189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37546791024828455406342341 7040023317155335388689189)
        ·
          refine ⟨1320004371966625385379223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7040023317155335388689189 1320004371966625385379223)
          ·
            refine ⟨1980006557949938078068835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1320004371966625385379223 1980006557949938078068835)
            ·
              refine ⟨2970009836924907117103253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1980006557949938078068835 2970009836924907117103253)
              ·
                refine ⟨139219211105855021114215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2970009836924907117103253 139219211105855021114215)
                ·
                  rfl

theorem cell21_1830117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 6].length) (baseStart_1830117 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1830117 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1830117 prefixEnd_1830117 := by exact prefixLift 1830117
  have htrace : WordTrace (prefixWord ++ tailWord_1830117) baseStart_1830117 baseEnd_1830117 := by
    simpa [prefixWord, tailWord_1830117, baseEnd_1830117] using wordTrace_append hprefix tailTrace_1830117
  have hstable : (prefixWord ++ tailWord_1830117).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830117).length < 2 ^ (prefixWord ++ tailWord_1830117).sum := by decide
  have hdescent : baseEnd_1830117 < baseStart_1830117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830148 : List Nat := [2, 3, 2, 2, 2, 2, 2, 3, 3]
def baseStart_1830148 : Nat := 118140960795 + 1830148 * 2 ^ 59
def prefixEnd_1830148 : Nat := 4983230072969 + 3 ^ 40 * 1830148 * 2
def baseEnd_1830148 : Nat := 417664707939915898325915

theorem tailTrace_1830148 : CollatzResearch.WordTrace tailWord_1830148 prefixEnd_1830148 417664707939915898325915 := by
  unfold tailWord_1830148
  simp only [CollatzResearch.WordTrace]
  refine ⟨33375490686846917619493549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44500654249129223492658065 33375490686846917619493549)
  ·
    refine ⟨12515809007567594107310081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33375490686846917619493549 12515809007567594107310081)
    ·
      refine ⟨9386856755675695580482561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12515809007567594107310081 9386856755675695580482561)
      ·
        refine ⟨7040142566756771685361921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9386856755675695580482561 7040142566756771685361921)
        ·
          refine ⟨5280106925067578764021441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7040142566756771685361921 5280106925067578764021441)
          ·
            refine ⟨3960080193800684073016081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5280106925067578764021441 3960080193800684073016081)
            ·
              refine ⟨2970060145350513054762061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3960080193800684073016081 2970060145350513054762061)
              ·
                refine ⟨1113772554506442395535773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2970060145350513054762061 1113772554506442395535773)
                ·
                  refine ⟨417664707939915898325915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1113772554506442395535773 417664707939915898325915)
                  ·
                    rfl

theorem cell21_1830148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 3, 3].length) (baseStart_1830148 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1830148 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1830148 prefixEnd_1830148 := by exact prefixLift 1830148
  have htrace : WordTrace (prefixWord ++ tailWord_1830148) baseStart_1830148 baseEnd_1830148 := by
    simpa [prefixWord, tailWord_1830148, baseEnd_1830148] using wordTrace_append hprefix tailTrace_1830148
  have hstable : (prefixWord ++ tailWord_1830148).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830148).length < 2 ^ (prefixWord ++ tailWord_1830148).sum := by decide
  have hdescent : baseEnd_1830148 < baseStart_1830148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830204 : List Nat := [2, 2, 2, 2, 1, 3, 1, 2, 6]
def baseStart_1830204 : Nat := 118140960795 + 1830204 * 2 ^ 59
def prefixEnd_1830204 : Nat := 4983230072969 + 3 ^ 40 * 1830204 * 2
def baseEnd_1830204 : Nat := 417677487902872245392467

theorem tailTrace_1830204 : CollatzResearch.WordTrace tailWord_1830204 prefixEnd_1830204 417677487902872245392467 := by
  unfold tailWord_1830204
  simp only [CollatzResearch.WordTrace]
  refine ⟨33376511930745478401512833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44502015907660637868683777 33376511930745478401512833)
  ·
    refine ⟨25032383948059108801134625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33376511930745478401512833 25032383948059108801134625)
    ·
      refine ⟨18774287961044331600850969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25032383948059108801134625 18774287961044331600850969)
      ·
        refine ⟨14080715970783248700638227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18774287961044331600850969 14080715970783248700638227)
        ·
          refine ⟨21121073956174873050957341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14080715970783248700638227 21121073956174873050957341)
          ·
            refine ⟨7920402733565577394109003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21121073956174873050957341 7920402733565577394109003)
            ·
              refine ⟨11880604100348366091163505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7920402733565577394109003 11880604100348366091163505)
              ·
                refine ⟨8910453075261274568372629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11880604100348366091163505 8910453075261274568372629)
                ·
                  refine ⟨417677487902872245392467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8910453075261274568372629 417677487902872245392467)
                  ·
                    rfl

theorem cell21_1830204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 6].length) (baseStart_1830204 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1830204 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1830204 prefixEnd_1830204 := by exact prefixLift 1830204
  have htrace : WordTrace (prefixWord ++ tailWord_1830204) baseStart_1830204 baseEnd_1830204 := by
    simpa [prefixWord, tailWord_1830204, baseEnd_1830204] using wordTrace_append hprefix tailTrace_1830204
  have hstable : (prefixWord ++ tailWord_1830204).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830204).length < 2 ^ (prefixWord ++ tailWord_1830204).sum := by decide
  have hdescent : baseEnd_1830204 < baseStart_1830204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830207 : List Nat := [1, 1, 2, 2, 4, 2, 3, 3, 3]
def baseStart_1830207 : Nat := 118140960795 + 1830207 * 2 ^ 59
def prefixEnd_1830207 : Nat := 4983230072969 + 3 ^ 40 * 1830207 * 2
def baseEnd_1830207 : Nat := 417678172543744906842461

theorem tailTrace_1830207 : CollatzResearch.WordTrace tailWord_1830207 prefixEnd_1830207 417678172543744906842461 := by
  unfold tailWord_1830207
  simp only [CollatzResearch.WordTrace]
  refine ⟨66753133280480088315384875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44502088853653392210256583 66753133280480088315384875)
  ·
    refine ⟨100129699920720132473077313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66753133280480088315384875 100129699920720132473077313)
    ·
      refine ⟨75097274940540099354807985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100129699920720132473077313 75097274940540099354807985)
      ·
        refine ⟨56322956205405074516105989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75097274940540099354807985 56322956205405074516105989)
        ·
          refine ⟨10560554288513451471769873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56322956205405074516105989 10560554288513451471769873)
          ·
            refine ⟨7920415716385088603827405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10560554288513451471769873 7920415716385088603827405)
            ·
              refine ⟨2970155893644408226435277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7920415716385088603827405 2970155893644408226435277)
              ·
                refine ⟨1113808460116653084913229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2970155893644408226435277 1113808460116653084913229)
                ·
                  refine ⟨417678172543744906842461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1113808460116653084913229 417678172543744906842461)
                  ·
                    rfl

theorem cell21_1830207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 3, 3].length) (baseStart_1830207 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1830207 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1830207 prefixEnd_1830207 := by exact prefixLift 1830207
  have htrace : WordTrace (prefixWord ++ tailWord_1830207) baseStart_1830207 baseEnd_1830207 := by
    simpa [prefixWord, tailWord_1830207, baseEnd_1830207] using wordTrace_append hprefix tailTrace_1830207
  have hstable : (prefixWord ++ tailWord_1830207).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830207).length < 2 ^ (prefixWord ++ tailWord_1830207).sum := by decide
  have hdescent : baseEnd_1830207 < baseStart_1830207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830230 : List Nat := [5, 2, 3, 1, 1, 2, 2, 1, 4]
def baseStart_1830230 : Nat := 118140960795 + 1830230 * 2 ^ 59
def prefixEnd_1830230 : Nat := 4983230072969 + 3 ^ 40 * 1830230 * 2
def baseEnd_1830230 : Nat := 417683421457101977959081

theorem tailTrace_1830230 : CollatzResearch.WordTrace tailWord_1830230 prefixEnd_1830230 417683421457101977959081 := by
  unfold tailWord_1830230
  simp only [CollatzResearch.WordTrace]
  refine ⟨4172123259962297702717009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44502648106264508828981429 4172123259962297702717009)
  ·
    refine ⟨3129092444971723277037757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4172123259962297702717009 3129092444971723277037757)
    ·
      refine ⟨1173409666864396228889159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3129092444971723277037757 1173409666864396228889159)
      ·
        refine ⟨1760114500296594343333739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1173409666864396228889159 1760114500296594343333739)
        ·
          refine ⟨2640171750444891515000609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1760114500296594343333739 2640171750444891515000609)
          ·
            refine ⟨1980128812833668636250457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2640171750444891515000609 1980128812833668636250457)
            ·
              refine ⟨1485096609625251477187843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1980128812833668636250457 1485096609625251477187843)
              ·
                refine ⟨2227644914437877215781765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1485096609625251477187843 2227644914437877215781765)
                ·
                  refine ⟨417683421457101977959081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2227644914437877215781765 417683421457101977959081)
                  ·
                    rfl

theorem cell21_1830230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_1830230 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1830230 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1830230 prefixEnd_1830230 := by exact prefixLift 1830230
  have htrace : WordTrace (prefixWord ++ tailWord_1830230) baseStart_1830230 baseEnd_1830230 := by
    simpa [prefixWord, tailWord_1830230, baseEnd_1830230] using wordTrace_append hprefix tailTrace_1830230
  have hstable : (prefixWord ++ tailWord_1830230).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830230).length < 2 ^ (prefixWord ++ tailWord_1830230).sum := by decide
  have hdescent : baseEnd_1830230 < baseStart_1830230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830404 : List Nat := [2, 3, 2, 3, 2, 1, 2, 6]
def baseStart_1830404 : Nat := 118140960795 + 1830404 * 2 ^ 59
def prefixEnd_1830404 : Nat := 4983230072969 + 3 ^ 40 * 1830404 * 2
def baseEnd_1830404 : Nat := 139241043542572114019575

theorem tailTrace_1830404 : CollatzResearch.WordTrace tailWord_1830404 prefixEnd_1830404 139241043542572114019575 := by
  unfold tailWord_1830404
  simp only [CollatzResearch.WordTrace]
  refine ⟨33380159230383195480153133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44506878973844260640204177 33380159230383195480153133)
  ·
    refine ⟨12517559711393698305057425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33380159230383195480153133 12517559711393698305057425)
    ·
      refine ⟨9388169783545273728793069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12517559711393698305057425 9388169783545273728793069)
      ·
        refine ⟨3520563668829477648297401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9388169783545273728793069 3520563668829477648297401)
        ·
          refine ⟨2640422751622108236223051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3520563668829477648297401 2640422751622108236223051)
          ·
            refine ⟨3960634127433162354334577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2640422751622108236223051 3960634127433162354334577)
            ·
              refine ⟨2970475595574871765750933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3960634127433162354334577 2970475595574871765750933)
              ·
                refine ⟨139241043542572114019575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2970475595574871765750933 139241043542572114019575)
                ·
                  rfl

theorem cell21_1830404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 6].length) (baseStart_1830404 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1830404 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1830404 prefixEnd_1830404 := by exact prefixLift 1830404
  have htrace : WordTrace (prefixWord ++ tailWord_1830404) baseStart_1830404 baseEnd_1830404 := by
    simpa [prefixWord, tailWord_1830404, baseEnd_1830404] using wordTrace_append hprefix tailTrace_1830404
  have hstable : (prefixWord ++ tailWord_1830404).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830404).length < 2 ^ (prefixWord ++ tailWord_1830404).sum := by decide
  have hdescent : baseEnd_1830404 < baseStart_1830404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830463 : List Nat := [1, 1, 2, 2, 3, 5, 1, 6]
def baseStart_1830463 : Nat := 118140960795 + 1830463 * 2 ^ 59
def prefixEnd_1830463 : Nat := 4983230072969 + 3 ^ 40 * 1830463 * 2
def baseEnd_1830463 : Nat := 139245531743848450191757

theorem tailTrace_1830463 : CollatzResearch.WordTrace tailWord_1830463 prefixEnd_1830463 139245531743848450191757 := by
  unfold tailWord_1830463
  simp only [CollatzResearch.WordTrace]
  refine ⟨66762470367552644036704043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44508313578368429357802695 66762470367552644036704043)
  ·
    refine ⟨100143705551328966055056065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66762470367552644036704043 100143705551328966055056065)
    ·
      refine ⟨75107779163496724541292049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100143705551328966055056065 75107779163496724541292049)
      ·
        refine ⟨56330834372622543405969037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75107779163496724541292049 56330834372622543405969037)
        ·
          refine ⟨21124062889733453777238389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56330834372622543405969037 21124062889733453777238389)
          ·
            refine ⟨1980380895912511291616099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21124062889733453777238389 1980380895912511291616099)
            ·
              refine ⟨2970571343868766937424149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1980380895912511291616099 2970571343868766937424149)
              ·
                refine ⟨139245531743848450191757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2970571343868766937424149 139245531743848450191757)
                ·
                  rfl

theorem cell21_1830463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 6].length) (baseStart_1830463 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1830463 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1830463 prefixEnd_1830463 := by exact prefixLift 1830463
  have htrace : WordTrace (prefixWord ++ tailWord_1830463) baseStart_1830463 baseEnd_1830463 := by
    simpa [prefixWord, tailWord_1830463, baseEnd_1830463] using wordTrace_append hprefix tailTrace_1830463
  have hstable : (prefixWord ++ tailWord_1830463).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830463).length < 2 ^ (prefixWord ++ tailWord_1830463).sum := by decide
  have hdescent : baseEnd_1830463 < baseStart_1830463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830486 : List Nat := [5, 2, 2, 2, 1, 1, 2, 3, 3]
def baseStart_1830486 : Nat := 118140960795 + 1830486 * 2 ^ 59
def prefixEnd_1830486 : Nat := 4983230072969 + 3 ^ 40 * 1830486 * 2
def baseEnd_1830486 : Nat := 417741844144902421691891

theorem tailTrace_1830486 : CollatzResearch.WordTrace tailWord_1830486 prefixEnd_1830486 417741844144902421691891 := by
  unfold tailWord_1830486
  simp only [CollatzResearch.WordTrace]
  refine ⟨4172706827904332435299457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44508872830979545976527541 4172706827904332435299457)
  ·
    refine ⟨3129530120928249326474593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4172706827904332435299457 3129530120928249326474593)
    ·
      refine ⟨2347147590696186994855945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3129530120928249326474593 2347147590696186994855945)
      ·
        refine ⟨1760360693022140246141959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2347147590696186994855945 1760360693022140246141959)
        ·
          refine ⟨2640541039533210369212939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1760360693022140246141959 2640541039533210369212939)
          ·
            refine ⟨3960811559299815553819409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2640541039533210369212939 3960811559299815553819409)
            ·
              refine ⟨2970608669474861665364557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3960811559299815553819409 2970608669474861665364557)
              ·
                refine ⟨1113978251053073124511709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2970608669474861665364557 1113978251053073124511709)
                ·
                  refine ⟨417741844144902421691891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1113978251053073124511709 417741844144902421691891)
                  ·
                    rfl

theorem cell21_1830486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_1830486 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1830486 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1830486 prefixEnd_1830486 := by exact prefixLift 1830486
  have htrace : WordTrace (prefixWord ++ tailWord_1830486) baseStart_1830486 baseEnd_1830486 := by
    simpa [prefixWord, tailWord_1830486, baseEnd_1830486] using wordTrace_append hprefix tailTrace_1830486
  have hstable : (prefixWord ++ tailWord_1830486).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830486).length < 2 ^ (prefixWord ++ tailWord_1830486).sum := by decide
  have hdescent : baseEnd_1830486 < baseStart_1830486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830556 : List Nat := [2, 2, 3, 2, 4, 1, 7]
def baseStart_1830556 : Nat := 118140960795 + 1830556 * 2 ^ 59
def prefixEnd_1830556 : Nat := 4983230072969 + 3 ^ 40 * 1830556 * 2
def baseEnd_1830556 : Nat := 46417535455399761725009

theorem tailTrace_1830556 : CollatzResearch.WordTrace tailWord_1830556 prefixEnd_1830556 46417535455399761725009 := by
  unfold tailWord_1830556
  simp only [CollatzResearch.WordTrace]
  refine ⟨33382931178107860459919761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44510574904143813946559681 33382931178107860459919761)
  ·
    refine ⟨25037198383580895344939821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33382931178107860459919761 25037198383580895344939821)
    ·
      refine ⟨9388949393842835754352433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25037198383580895344939821 9388949393842835754352433)
      ·
        refine ⟨7041712045382126815764325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9388949393842835754352433 7041712045382126815764325)
        ·
          refine ⟨1320321008509148777955811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7041712045382126815764325 1320321008509148777955811)
          ·
            refine ⟨1980481512763723166933717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1320321008509148777955811 1980481512763723166933717)
            ·
              refine ⟨46417535455399761725009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1980481512763723166933717 46417535455399761725009)
              ·
                rfl

theorem cell21_1830556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 7].length) (baseStart_1830556 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1830556 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1830556 prefixEnd_1830556 := by exact prefixLift 1830556
  have htrace : WordTrace (prefixWord ++ tailWord_1830556) baseStart_1830556 baseEnd_1830556 := by
    simpa [prefixWord, tailWord_1830556, baseEnd_1830556] using wordTrace_append hprefix tailTrace_1830556
  have hstable : (prefixWord ++ tailWord_1830556).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830556).length < 2 ^ (prefixWord ++ tailWord_1830556).sum := by decide
  have hdescent : baseEnd_1830556 < baseStart_1830556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830629 : List Nat := [1, 3, 1, 4, 1, 1, 2, 3, 5]
def baseStart_1830629 : Nat := 118140960795 + 1830629 * 2 ^ 59
def prefixEnd_1830629 : Nat := 4983230072969 + 3 ^ 40 * 1830629 * 2
def baseEnd_1830629 : Nat := 417774478693165950808265

theorem tailTrace_1830629 : CollatzResearch.WordTrace tailWord_1830629 prefixEnd_1830629 417774478693165950808265 := by
  unfold tailWord_1830629
  simp only [CollatzResearch.WordTrace]
  refine ⟨66768524884951254387246941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44512349923300836258164627 66768524884951254387246941)
  ·
    refine ⟨25038196831856720395217603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66768524884951254387246941 25038196831856720395217603)
    ·
      refine ⟨37557295247785080592826405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25038196831856720395217603 37557295247785080592826405)
      ·
        refine ⟨7041992858959702611154951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37557295247785080592826405 7041992858959702611154951)
        ·
          refine ⟨10562989288439553916732427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7041992858959702611154951 10562989288439553916732427)
          ·
            refine ⟨15844483932659330875098641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10562989288439553916732427 15844483932659330875098641)
            ·
              refine ⟨11883362949494498156323981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15844483932659330875098641 11883362949494498156323981)
              ·
                refine ⟨4456261106060436808621493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11883362949494498156323981 4456261106060436808621493)
                ·
                  refine ⟨417774478693165950808265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4456261106060436808621493 417774478693165950808265)
                  ·
                    rfl

theorem cell21_1830629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 3, 5].length) (baseStart_1830629 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1830629 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1830629 prefixEnd_1830629 := by exact prefixLift 1830629
  have htrace : WordTrace (prefixWord ++ tailWord_1830629) baseStart_1830629 baseEnd_1830629 := by
    simpa [prefixWord, tailWord_1830629, baseEnd_1830629] using wordTrace_append hprefix tailTrace_1830629
  have hstable : (prefixWord ++ tailWord_1830629).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830629).length < 2 ^ (prefixWord ++ tailWord_1830629).sum := by decide
  have hdescent : baseEnd_1830629 < baseStart_1830629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830646 : List Nat := [5, 1, 1, 1, 1, 4, 1, 2, 5]
def baseStart_1830646 : Nat := 118140960795 + 1830646 * 2 ^ 59
def prefixEnd_1830646 : Nat := 4983230072969 + 3 ^ 40 * 1830646 * 2
def baseEnd_1830646 : Nat := 417778358324777699024897

theorem tailTrace_1830646 : CollatzResearch.WordTrace tailWord_1830646 prefixEnd_1830646 417778358324777699024897 := by
  unfold tailWord_1830646
  simp only [CollatzResearch.WordTrace]
  refine ⟨4173071557868104143163487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44512763283926444193743861 4173071557868104143163487)
  ·
    refine ⟨6259607336802156214745231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4173071557868104143163487 6259607336802156214745231)
    ·
      refine ⟨9389411005203234322117847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6259607336802156214745231 9389411005203234322117847)
      ·
        refine ⟨14084116507804851483176771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9389411005203234322117847 14084116507804851483176771)
        ·
          refine ⟨21126174761707277224765157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14084116507804851483176771 21126174761707277224765157)
          ·
            refine ⟨3961157767820114479643467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21126174761707277224765157 3961157767820114479643467)
            ·
              refine ⟨5941736651730171719465201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3961157767820114479643467 5941736651730171719465201)
              ·
                refine ⟨4456302488797628789598901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5941736651730171719465201 4456302488797628789598901)
                ·
                  refine ⟨417778358324777699024897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4456302488797628789598901 417778358324777699024897)
                  ·
                    rfl

theorem cell21_1830646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_1830646 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1830646 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1830646 prefixEnd_1830646 := by exact prefixLift 1830646
  have htrace : WordTrace (prefixWord ++ tailWord_1830646) baseStart_1830646 baseEnd_1830646 := by
    simpa [prefixWord, tailWord_1830646, baseEnd_1830646] using wordTrace_append hprefix tailTrace_1830646
  have hstable : (prefixWord ++ tailWord_1830646).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830646).length < 2 ^ (prefixWord ++ tailWord_1830646).sum := by decide
  have hdescent : baseEnd_1830646 < baseStart_1830646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830669 : List Nat := [1, 7, 2, 1, 1, 2, 1, 2, 4]
def baseStart_1830669 : Nat := 118140960795 + 1830669 * 2 ^ 59
def prefixEnd_1830669 : Nat := 4983230072969 + 3 ^ 40 * 1830669 * 2
def baseEnd_1830669 : Nat := 417783607238134770141517

theorem tailTrace_1830669 : CollatzResearch.WordTrace tailWord_1830669 prefixEnd_1830669 417783607238134770141517 := by
  unfold tailWord_1830669
  simp only [CollatzResearch.WordTrace]
  refine ⟨66769983804806341218703061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44513322536537560812468707 66769983804806341218703061)
  ·
    refine ⟨1564921495425148622313353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 66769983804806341218703061 1564921495425148622313353)
    ·
      refine ⟨1173691121568861466735015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1564921495425148622313353 1173691121568861466735015)
      ·
        refine ⟨1760536682353292200102523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1173691121568861466735015 1760536682353292200102523)
        ·
          refine ⟨2640805023529938300153785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1760536682353292200102523 2640805023529938300153785)
          ·
            refine ⟨1980603767647453725115339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2640805023529938300153785 1980603767647453725115339)
            ·
              refine ⟨2970905651471180587673009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1980603767647453725115339 2970905651471180587673009)
              ·
                refine ⟨2228179238603385440754757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2970905651471180587673009 2228179238603385440754757)
                ·
                  refine ⟨417783607238134770141517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2228179238603385440754757 417783607238134770141517)
                  ·
                    rfl

theorem cell21_1830669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_1830669 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1830669 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1830669 prefixEnd_1830669 := by exact prefixLift 1830669
  have htrace : WordTrace (prefixWord ++ tailWord_1830669) baseStart_1830669 baseEnd_1830669 := by
    simpa [prefixWord, tailWord_1830669, baseEnd_1830669] using wordTrace_append hprefix tailTrace_1830669
  have hstable : (prefixWord ++ tailWord_1830669).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830669).length < 2 ^ (prefixWord ++ tailWord_1830669).sum := by decide
  have hdescent : baseEnd_1830669 < baseStart_1830669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830677 : List Nat := [1, 3, 2, 1, 2, 5, 1, 2, 4]
def baseStart_1830677 : Nat := 118140960795 + 1830677 * 2 ^ 59
def prefixEnd_1830677 : Nat := 4983230072969 + 3 ^ 40 * 1830677 * 2
def baseEnd_1830677 : Nat := 417785432947128534008167

theorem tailTrace_1830677 : CollatzResearch.WordTrace tailWord_1830677 prefixEnd_1830677 417785432947128534008167 := by
  unfold tailWord_1830677
  simp only [CollatzResearch.WordTrace]
  refine ⟨66770275588777358584994285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44513517059184905723329523 66770275588777358584994285)
  ·
    refine ⟨25038853345791509469372857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66770275588777358584994285 25038853345791509469372857)
    ·
      refine ⟨18779140009343632102029643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25038853345791509469372857 18779140009343632102029643)
      ·
        refine ⟨28168710014015448153044465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18779140009343632102029643 28168710014015448153044465)
        ·
          refine ⟨21126532510511586114783349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28168710014015448153044465 21126532510511586114783349)
          ·
            refine ⟨1980612422860461198260939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21126532510511586114783349 1980612422860461198260939)
            ·
              refine ⟨2970918634290691797391409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1980612422860461198260939 2970918634290691797391409)
              ·
                refine ⟨2228188975718018848043557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2970918634290691797391409 2228188975718018848043557)
                ·
                  refine ⟨417785432947128534008167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2228188975718018848043557 417785432947128534008167)
                  ·
                    rfl

theorem cell21_1830677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 2, 4].length) (baseStart_1830677 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1830677 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1830677 prefixEnd_1830677 := by exact prefixLift 1830677
  have htrace : WordTrace (prefixWord ++ tailWord_1830677) baseStart_1830677 baseEnd_1830677 := by
    simpa [prefixWord, tailWord_1830677, baseEnd_1830677] using wordTrace_append hprefix tailTrace_1830677
  have hstable : (prefixWord ++ tailWord_1830677).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830677).length < 2 ^ (prefixWord ++ tailWord_1830677).sum := by decide
  have hdescent : baseEnd_1830677 < baseStart_1830677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830705 : List Nat := [1, 2, 2, 3, 2, 2, 2, 2, 5]
def baseStart_1830705 : Nat := 118140960795 + 1830705 * 2 ^ 59
def prefixEnd_1830705 : Nat := 4983230072969 + 3 ^ 40 * 1830705 * 2
def baseEnd_1830705 : Nat := 417791822928606707541443

theorem tailTrace_1830705 : CollatzResearch.WordTrace tailWord_1830705 prefixEnd_1830705 417791822928606707541443 := by
  unfold tailWord_1830705
  simp only [CollatzResearch.WordTrace]
  refine ⟨66771296832675919367013569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44514197888450612911342379 66771296832675919367013569)
  ·
    refine ⟨50078472624506939525260177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66771296832675919367013569 50078472624506939525260177)
    ·
      refine ⟨37558854468380204643945133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50078472624506939525260177 37558854468380204643945133)
      ·
        refine ⟨14084570425642576741479425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37558854468380204643945133 14084570425642576741479425)
        ·
          refine ⟨10563427819231932556109569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14084570425642576741479425 10563427819231932556109569)
          ·
            refine ⟨7922570864423949417082177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10563427819231932556109569 7922570864423949417082177)
            ·
              refine ⟨5941928148317962062811633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7922570864423949417082177 5941928148317962062811633)
              ·
                refine ⟨4456446111238471547108725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5941928148317962062811633 4456446111238471547108725)
                ·
                  refine ⟨417791822928606707541443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4456446111238471547108725 417791822928606707541443)
                  ·
                    rfl

theorem cell21_1830705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 2, 5].length) (baseStart_1830705 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1830705 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1830705 prefixEnd_1830705 := by exact prefixLift 1830705
  have htrace : WordTrace (prefixWord ++ tailWord_1830705) baseStart_1830705 baseEnd_1830705 := by
    simpa [prefixWord, tailWord_1830705, baseEnd_1830705] using wordTrace_append hprefix tailTrace_1830705
  have hstable : (prefixWord ++ tailWord_1830705).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830705).length < 2 ^ (prefixWord ++ tailWord_1830705).sum := by decide
  have hdescent : baseEnd_1830705 < baseStart_1830705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830708 : List Nat := [2, 5, 1, 1, 2, 1, 4, 5]
def baseStart_1830708 : Nat := 118140960795 + 1830708 * 2 ^ 59
def prefixEnd_1830708 : Nat := 4983230072969 + 3 ^ 40 * 1830708 * 2
def baseEnd_1830708 : Nat := 139264169189826456330479

theorem tailTrace_1830708 : CollatzResearch.WordTrace tailWord_1830708 prefixEnd_1830708 139264169189826456330479 := by
  unfold tailWord_1830708
  simp only [CollatzResearch.WordTrace]
  refine ⟨33385703125832525439686389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44514270834443367252915185 33385703125832525439686389)
  ·
    refine ⟨3129909668046799259970599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33385703125832525439686389 3129909668046799259970599)
    ·
      refine ⟨4694864502070198889955899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3129909668046799259970599 4694864502070198889955899)
      ·
        refine ⟨7042296753105298334933849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4694864502070198889955899 7042296753105298334933849)
        ·
          refine ⟨5281722564828973751200387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7042296753105298334933849 5281722564828973751200387)
          ·
            refine ⟨7922583847243460626800581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5281722564828973751200387 7922583847243460626800581)
            ·
              refine ⟨1485484471358148867525109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7922583847243460626800581 1485484471358148867525109)
              ·
                refine ⟨139264169189826456330479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1485484471358148867525109 139264169189826456330479)
                ·
                  rfl

theorem cell21_1830708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 4, 5].length) (baseStart_1830708 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1830708 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1830708 prefixEnd_1830708 := by exact prefixLift 1830708
  have htrace : WordTrace (prefixWord ++ tailWord_1830708) baseStart_1830708 baseEnd_1830708 := by
    simpa [prefixWord, tailWord_1830708, baseEnd_1830708] using wordTrace_append hprefix tailTrace_1830708
  have hstable : (prefixWord ++ tailWord_1830708).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830708).length < 2 ^ (prefixWord ++ tailWord_1830708).sum := by decide
  have hdescent : baseEnd_1830708 < baseStart_1830708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830840 : List Nat := [2, 1, 2, 1, 2, 3, 1, 2, 7]
def baseStart_1830840 : Nat := 118140960795 + 1830840 * 2 ^ 59
def prefixEnd_1830840 : Nat := 4983230072969 + 3 ^ 40 * 1830840 * 2
def baseEnd_1830840 : Nat := 417822631767876472791167

theorem tailTrace_1830840 : CollatzResearch.WordTrace tailWord_1830840 prefixEnd_1830840 417822631767876472791167 := by
  unfold tailWord_1830840
  simp only [CollatzResearch.WordTrace]
  refine ⟨33388110343593418711588987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44517480458124558282118649 33388110343593418711588987)
  ·
    refine ⟨50082165515390128067383481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33388110343593418711588987 50082165515390128067383481)
    ·
      refine ⟨37561624136542596050537611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50082165515390128067383481 37561624136542596050537611)
      ·
        refine ⟨56342436204813894075806417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37561624136542596050537611 56342436204813894075806417)
        ·
          refine ⟨42256827153610420556854813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56342436204813894075806417 42256827153610420556854813)
          ·
            refine ⟨15846310182603907708820555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42256827153610420556854813 15846310182603907708820555)
            ·
              refine ⟨23769465273905861563230833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15846310182603907708820555 23769465273905861563230833)
              ·
                refine ⟨17827098955429396172423125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23769465273905861563230833 17827098955429396172423125)
                ·
                  refine ⟨417822631767876472791167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17827098955429396172423125 417822631767876472791167)
                  ·
                    rfl

theorem cell21_1830840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 7].length) (baseStart_1830840 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1830840 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1830840 prefixEnd_1830840 := by exact prefixLift 1830840
  have htrace : WordTrace (prefixWord ++ tailWord_1830840) baseStart_1830840 baseEnd_1830840 := by
    simpa [prefixWord, tailWord_1830840, baseEnd_1830840] using wordTrace_append hprefix tailTrace_1830840
  have hstable : (prefixWord ++ tailWord_1830840).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830840).length < 2 ^ (prefixWord ++ tailWord_1830840).sum := by decide
  have hdescent : baseEnd_1830840 < baseStart_1830840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830877 : List Nat := [1, 4, 3, 1, 4, 1, 2, 5]
def baseStart_1830877 : Nat := 118140960795 + 1830877 * 2 ^ 59
def prefixEnd_1830877 : Nat := 4983230072969 + 3 ^ 40 * 1830877 * 2
def baseEnd_1830877 : Nat := 139277025223990876891475

theorem tailTrace_1830877 : CollatzResearch.WordTrace tailWord_1830877 prefixEnd_1830877 139277025223990876891475 := by
  unfold tailWord_1830877
  simp only [CollatzResearch.WordTrace]
  refine ⟨66777570188052792742274885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44518380125368528494849923 66777570188052792742274885)
  ·
    refine ⟨12520794410259898639176541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66777570188052792742274885 12520794410259898639176541)
    ·
      refine ⟨4695297903847461989691203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12520794410259898639176541 4695297903847461989691203)
      ·
        refine ⟨7042946855771192984536805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4695297903847461989691203 7042946855771192984536805)
        ·
          refine ⟨1320552535457098684600651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7042946855771192984536805 1320552535457098684600651)
          ·
            refine ⟨1980828803185648026900977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1320552535457098684600651 1980828803185648026900977)
            ·
              refine ⟨1485621602389236020175733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1980828803185648026900977 1485621602389236020175733)
              ·
                refine ⟨139277025223990876891475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1485621602389236020175733 139277025223990876891475)
                ·
                  rfl

theorem cell21_1830877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 2, 5].length) (baseStart_1830877 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1830877 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1830877 prefixEnd_1830877 := by exact prefixLift 1830877
  have htrace : WordTrace (prefixWord ++ tailWord_1830877) baseStart_1830877 baseEnd_1830877 := by
    simpa [prefixWord, tailWord_1830877, baseEnd_1830877] using wordTrace_append hprefix tailTrace_1830877
  have hstable : (prefixWord ++ tailWord_1830877).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830877).length < 2 ^ (prefixWord ++ tailWord_1830877).sum := by decide
  have hdescent : baseEnd_1830877 < baseStart_1830877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830922 : List Nat := [3, 1, 2, 2, 4, 2, 2, 1, 4]
def baseStart_1830922 : Nat := 118140960795 + 1830922 * 2 ^ 59
def prefixEnd_1830922 : Nat := 4983230072969 + 3 ^ 40 * 1830922 * 2
def baseEnd_1830922 : Nat := 417841345285062552424333

theorem tailTrace_1830922 : CollatzResearch.WordTrace tailWord_1830922 prefixEnd_1830922 417841345285062552424333 := by
  unfold tailWord_1830922
  simp only [CollatzResearch.WordTrace]
  refine ⟨16694802868222441356915755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44519474315259843618442013 16694802868222441356915755)
  ·
    refine ⟨25042204302333662035373633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16694802868222441356915755 25042204302333662035373633)
    ·
      refine ⟨18781653226750246526530225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25042204302333662035373633 18781653226750246526530225)
      ·
        refine ⟨14086239920062684894897669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18781653226750246526530225 14086239920062684894897669)
        ·
          refine ⟨2641169985011753417793313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14086239920062684894897669 2641169985011753417793313)
          ·
            refine ⟨1980877488758815063344985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2641169985011753417793313 1980877488758815063344985)
            ·
              refine ⟨1485658116569111297508739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1980877488758815063344985 1485658116569111297508739)
              ·
                refine ⟨2228487174853666946263109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1485658116569111297508739 2228487174853666946263109)
                ·
                  refine ⟨417841345285062552424333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2228487174853666946263109 417841345285062552424333)
                  ·
                    rfl

theorem cell21_1830922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 2, 1, 4].length) (baseStart_1830922 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1830922 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1830922 prefixEnd_1830922 := by exact prefixLift 1830922
  have htrace : WordTrace (prefixWord ++ tailWord_1830922) baseStart_1830922 baseEnd_1830922 := by
    simpa [prefixWord, tailWord_1830922, baseEnd_1830922] using wordTrace_append hprefix tailTrace_1830922
  have hstable : (prefixWord ++ tailWord_1830922).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830922).length < 2 ^ (prefixWord ++ tailWord_1830922).sum := by decide
  have hdescent : baseEnd_1830922 < baseStart_1830922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1830961 : List Nat := [1, 2, 2, 3, 1, 12]
def baseStart_1830961 : Nat := 118140960795 + 1830961 * 2 ^ 59
def prefixEnd_1830961 : Nat := 4983230072969 + 3 ^ 40 * 1830961 * 2
def baseEnd_1830961 : Nat := 15475935022829894491639

theorem tailTrace_1830961 : CollatzResearch.WordTrace tailWord_1830961 prefixEnd_1830961 15475935022829894491639 := by
  unfold tailWord_1830961
  simp only [CollatzResearch.WordTrace]
  refine ⟨66780633919748475088332737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44520422613165650058888491 66780633919748475088332737)
  ·
    refine ⟨50085475439811356316249553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66780633919748475088332737 50085475439811356316249553)
    ·
      refine ⟨37564106579858517237187165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50085475439811356316249553 37564106579858517237187165)
      ·
        refine ⟨14086539967446943963945187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37564106579858517237187165 14086539967446943963945187)
        ·
          refine ⟨21129809951170415945917781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14086539967446943963945187 21129809951170415945917781)
          ·
            refine ⟨15475935022829894491639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 21129809951170415945917781 15475935022829894491639)
            ·
              rfl

theorem cell21_1830961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 12].length) (baseStart_1830961 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1830961 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1830961 prefixEnd_1830961 := by exact prefixLift 1830961
  have htrace : WordTrace (prefixWord ++ tailWord_1830961) baseStart_1830961 baseEnd_1830961 := by
    simpa [prefixWord, tailWord_1830961, baseEnd_1830961] using wordTrace_append hprefix tailTrace_1830961
  have hstable : (prefixWord ++ tailWord_1830961).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1830961).length < 2 ^ (prefixWord ++ tailWord_1830961).sum := by decide
  have hdescent : baseEnd_1830961 < baseStart_1830961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1830961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831023 : List Nat := [1, 1, 2, 1, 3, 5, 1, 1, 6]
def baseStart_1831023 : Nat := 118140960795 + 1831023 * 2 ^ 59
def prefixEnd_1831023 : Nat := 4983230072969 + 3 ^ 40 * 1831023 * 2
def baseEnd_1831023 : Nat := 417864394861108821240793

theorem tailTrace_1831023 : CollatzResearch.WordTrace tailWord_1831023 prefixEnd_1831023 417864394861108821240793 := by
  unfold tailWord_1831023
  simp only [CollatzResearch.WordTrace]
  refine ⟨66782895245523859677089723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44521930163682573118059815 66782895245523859677089723)
  ·
    refine ⟨100174342868285789515634585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66782895245523859677089723 100174342868285789515634585)
    ·
      refine ⟨75130757151214342136725939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100174342868285789515634585 75130757151214342136725939)
      ·
        refine ⟨112696135726821513205088909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75130757151214342136725939 112696135726821513205088909)
        ·
          refine ⟨42261050897558067451908341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112696135726821513205088909 42261050897558067451908341)
          ·
            refine ⟨3961973521646068823616407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42261050897558067451908341 3961973521646068823616407)
            ·
              refine ⟨5942960282469103235424611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3961973521646068823616407 5942960282469103235424611)
              ·
                refine ⟨8914440423703654853136917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5942960282469103235424611 8914440423703654853136917)
                ·
                  refine ⟨417864394861108821240793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8914440423703654853136917 417864394861108821240793)
                  ·
                    rfl

theorem cell21_1831023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 6].length) (baseStart_1831023 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1831023 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1831023 prefixEnd_1831023 := by exact prefixLift 1831023
  have htrace : WordTrace (prefixWord ++ tailWord_1831023) baseStart_1831023 baseEnd_1831023 := by
    simpa [prefixWord, tailWord_1831023, baseEnd_1831023] using wordTrace_append hprefix tailTrace_1831023
  have hstable : (prefixWord ++ tailWord_1831023).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831023).length < 2 ^ (prefixWord ++ tailWord_1831023).sum := by decide
  have hdescent : baseEnd_1831023 < baseStart_1831023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831026 : List Nat := [3, 2, 1, 2, 2, 2, 2, 4, 3]
def baseStart_1831026 : Nat := 118140960795 + 1831026 * 2 ^ 59
def prefixEnd_1831026 : Nat := 4983230072969 + 3 ^ 40 * 1831026 * 2
def baseEnd_1831026 : Nat := 417865079501981482690787

theorem tailTrace_1831026 : CollatzResearch.WordTrace tailWord_1831026 prefixEnd_1831026 417865079501981482690787 := by
  unfold tailWord_1831026
  simp only [CollatzResearch.WordTrace]
  refine ⟨16695751166128247797362233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44522003109675327459632621 16695751166128247797362233)
  ·
    refine ⟨12521813374596185848021675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16695751166128247797362233 12521813374596185848021675)
    ·
      refine ⟨18782720061894278772032513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12521813374596185848021675 18782720061894278772032513)
      ·
        refine ⟨14087040046420709079024385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18782720061894278772032513 14087040046420709079024385)
        ·
          refine ⟨10565280034815531809268289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14087040046420709079024385 10565280034815531809268289)
          ·
            refine ⟨7923960026111648856951217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10565280034815531809268289 7923960026111648856951217)
            ·
              refine ⟨5942970019583736642713413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7923960026111648856951217 5942970019583736642713413)
              ·
                refine ⟨1114306878671950620508765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5942970019583736642713413 1114306878671950620508765)
                ·
                  refine ⟨417865079501981482690787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1114306878671950620508765 417865079501981482690787)
                  ·
                    rfl

theorem cell21_1831026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 4, 3].length) (baseStart_1831026 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1831026 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1831026 prefixEnd_1831026 := by exact prefixLift 1831026
  have htrace : WordTrace (prefixWord ++ tailWord_1831026) baseStart_1831026 baseEnd_1831026 := by
    simpa [prefixWord, tailWord_1831026, baseEnd_1831026] using wordTrace_append hprefix tailTrace_1831026
  have hstable : (prefixWord ++ tailWord_1831026).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831026).length < 2 ^ (prefixWord ++ tailWord_1831026).sum := by decide
  have hdescent : baseEnd_1831026 < baseStart_1831026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831099 : List Nat := [1, 1, 1, 1, 1, 2, 7, 3, 4]
def baseStart_1831099 : Nat := 118140960795 + 1831099 * 2 ^ 59
def prefixEnd_1831099 : Nat := 4983230072969 + 3 ^ 40 * 1831099 * 2
def baseEnd_1831099 : Nat := 417881739096549577973971

theorem tailTrace_1831099 : CollatzResearch.WordTrace tailWord_1831099 prefixEnd_1831099 417881739096549577973971 := by
  unfold tailWord_1831099
  simp only [CollatzResearch.WordTrace]
  refine ⟨66785667193248524656856351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44523778128832349771237567 66785667193248524656856351)
  ·
    refine ⟨100178500789872786985284527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66785667193248524656856351 100178500789872786985284527)
    ·
      refine ⟨150267751184809180477926791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100178500789872786985284527 150267751184809180477926791)
      ·
        refine ⟨225401626777213770716890187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150267751184809180477926791 225401626777213770716890187)
        ·
          refine ⟨338102440165820656075335281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225401626777213770716890187 338102440165820656075335281)
          ·
            refine ⟨253576830124365492056501461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 338102440165820656075335281 253576830124365492056501461)
            ·
              refine ⟨5943206956039816220074253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 253576830124365492056501461 5943206956039816220074253)
              ·
                refine ⟨2228702608514931082527845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5943206956039816220074253 2228702608514931082527845)
                ·
                  refine ⟨417881739096549577973971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2228702608514931082527845 417881739096549577973971)
                  ·
                    rfl

theorem cell21_1831099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 3, 4].length) (baseStart_1831099 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1831099 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1831099 prefixEnd_1831099 := by exact prefixLift 1831099
  have htrace : WordTrace (prefixWord ++ tailWord_1831099) baseStart_1831099 baseEnd_1831099 := by
    simpa [prefixWord, tailWord_1831099, baseEnd_1831099] using wordTrace_append hprefix tailTrace_1831099
  have hstable : (prefixWord ++ tailWord_1831099).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831099).length < 2 ^ (prefixWord ++ tailWord_1831099).sum := by decide
  have hdescent : baseEnd_1831099 < baseStart_1831099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831133 : List Nat := [1, 4, 3, 2, 1, 2, 2, 2, 4]
def baseStart_1831133 : Nat := 118140960795 + 1831133 * 2 ^ 59
def prefixEnd_1831133 : Nat := 4983230072969 + 3 ^ 40 * 1831133 * 2
def baseEnd_1831133 : Nat := 417889498359773074407235

theorem tailTrace_1831133 : CollatzResearch.WordTrace tailWord_1831133 prefixEnd_1831133 417889498359773074407235 := by
  unfold tailWord_1831133
  simp only [CollatzResearch.WordTrace]
  refine ⟨66786907275125348463594053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44524604850083565642396035 66786907275125348463594053)
  ·
    refine ⟨12522545114086002836923885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66786907275125348463594053 12522545114086002836923885)
    ·
      refine ⟨4695954417782251063846457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12522545114086002836923885 4695954417782251063846457)
      ·
        refine ⟨3521965813336688297884843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4695954417782251063846457 3521965813336688297884843)
        ·
          refine ⟨5282948720005032446827265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3521965813336688297884843 5282948720005032446827265)
          ·
            refine ⟨3962211540003774335120449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5282948720005032446827265 3962211540003774335120449)
            ·
              refine ⟨2971658655002830751340337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3962211540003774335120449 2971658655002830751340337)
              ·
                refine ⟨2228743991252123063505253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2971658655002830751340337 2228743991252123063505253)
                ·
                  refine ⟨417889498359773074407235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2228743991252123063505253 417889498359773074407235)
                  ·
                    rfl

theorem cell21_1831133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 2, 4].length) (baseStart_1831133 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1831133 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1831133 prefixEnd_1831133 := by exact prefixLift 1831133
  have htrace : WordTrace (prefixWord ++ tailWord_1831133) baseStart_1831133 baseEnd_1831133 := by
    simpa [prefixWord, tailWord_1831133, baseEnd_1831133] using wordTrace_append hprefix tailTrace_1831133
  have hstable : (prefixWord ++ tailWord_1831133).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831133).length < 2 ^ (prefixWord ++ tailWord_1831133).sum := by decide
  have hdescent : baseEnd_1831133 < baseStart_1831133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831316 : List Nat := [2, 4, 2, 1, 4, 1, 1, 6]
def baseStart_1831316 : Nat := 118140960795 + 1831316 * 2 ^ 59
def prefixEnd_1831316 : Nat := 4983230072969 + 3 ^ 40 * 1831316 * 2
def baseEnd_1831316 : Nat := 139310420484335140952287

theorem tailTrace_1831316 : CollatzResearch.WordTrace tailWord_1831316 prefixEnd_1831316 139310420484335140952287 := by
  unfold tailWord_1831316
  simp only [CollatzResearch.WordTrace]
  refine ⟨33396790916731185358752901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44529054555641580478337201 33396790916731185358752901)
  ·
    refine ⟨6261898296887097254766169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33396790916731185358752901 6261898296887097254766169)
    ·
      refine ⟨4696423722665322941074627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6261898296887097254766169 4696423722665322941074627)
      ·
        refine ⟨7044635583997984411611941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4696423722665322941074627 7044635583997984411611941)
        ·
          refine ⟨1320869171999622077177239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7044635583997984411611941 1320869171999622077177239)
          ·
            refine ⟨1981303757999433115765859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1320869171999622077177239 1981303757999433115765859)
            ·
              refine ⟨2971955636999149673648789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1981303757999433115765859 2971955636999149673648789)
              ·
                refine ⟨139310420484335140952287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2971955636999149673648789 139310420484335140952287)
                ·
                  rfl

theorem cell21_1831316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 6].length) (baseStart_1831316 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1831316 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1831316 prefixEnd_1831316 := by exact prefixLift 1831316
  have htrace : WordTrace (prefixWord ++ tailWord_1831316) baseStart_1831316 baseEnd_1831316 := by
    simpa [prefixWord, tailWord_1831316, baseEnd_1831316] using wordTrace_append hprefix tailTrace_1831316
  have hstable : (prefixWord ++ tailWord_1831316).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831316).length < 2 ^ (prefixWord ++ tailWord_1831316).sum := by decide
  have hdescent : baseEnd_1831316 < baseStart_1831316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831327 : List Nat := [1, 1, 2, 5, 1, 1, 1, 5, 4]
def baseStart_1831327 : Nat := 118140960795 + 1831327 * 2 ^ 59
def prefixEnd_1831327 : Nat := 4983230072969 + 3 ^ 40 * 1831327 * 2
def baseEnd_1831327 : Nat := 417933771802871848173505

theorem tailTrace_1831327 : CollatzResearch.WordTrace tailWord_1831327 prefixEnd_1831327 417933771802871848173505 := by
  unfold tailWord_1831327
  simp only [CollatzResearch.WordTrace]
  refine ⟨66793983036422519596156235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44529322024281679730770823 66793983036422519596156235)
  ·
    refine ⟨100190974554633779394234353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66793983036422519596156235 100190974554633779394234353)
    ·
      refine ⟨75143230915975334545675765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100190974554633779394234353 75143230915975334545675765)
      ·
        refine ⟨7044677898372687613657103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75143230915975334545675765 7044677898372687613657103)
        ·
          refine ⟨10567016847559031420485655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7044677898372687613657103 10567016847559031420485655)
          ·
            refine ⟨15850525271338547130728483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10567016847559031420485655 15850525271338547130728483)
            ·
              refine ⟨23775787907007820696092725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15850525271338547130728483 23775787907007820696092725)
              ·
                refine ⟨2228980116281983190258693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23775787907007820696092725 2228980116281983190258693)
                ·
                  refine ⟨417933771802871848173505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2228980116281983190258693 417933771802871848173505)
                  ·
                    rfl

theorem cell21_1831327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 5, 4].length) (baseStart_1831327 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1831327 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1831327 prefixEnd_1831327 := by exact prefixLift 1831327
  have htrace : WordTrace (prefixWord ++ tailWord_1831327) baseStart_1831327 baseEnd_1831327 := by
    simpa [prefixWord, tailWord_1831327, baseEnd_1831327] using wordTrace_append hprefix tailTrace_1831327
  have hstable : (prefixWord ++ tailWord_1831327).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831327).length < 2 ^ (prefixWord ++ tailWord_1831327).sum := by decide
  have hdescent : baseEnd_1831327 < baseStart_1831327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831378 : List Nat := [3, 2, 2, 4, 1, 1, 3, 1, 4]
def baseStart_1831378 : Nat := 118140960795 + 1831378 * 2 ^ 59
def prefixEnd_1831378 : Nat := 4983230072969 + 3 ^ 40 * 1831378 * 2
def baseEnd_1831378 : Nat := 417945410697707092823401

theorem tailTrace_1831378 : CollatzResearch.WordTrace tailWord_1831378 prefixEnd_1831378 417945410697707092823401 := by
  unfold tailWord_1831378
  simp only [CollatzResearch.WordTrace]
  refine ⟨16698960789809438826565697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44530562106158503537508525 16698960789809438826565697)
  ·
    refine ⟨12524220592357079119924273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16698960789809438826565697 12524220592357079119924273)
    ·
      refine ⟨9393165444267809339943205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12524220592357079119924273 9393165444267809339943205)
      ·
        refine ⟨1761218520800214251239351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9393165444267809339943205 1761218520800214251239351)
        ·
          refine ⟨2641827781200321376859027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1761218520800214251239351 2641827781200321376859027)
          ·
            refine ⟨3962741671800482065288541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2641827781200321376859027 3962741671800482065288541)
            ·
              refine ⟨1486028126925180774483203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3962741671800482065288541 1486028126925180774483203)
              ·
                refine ⟨2229042190387771161724805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1486028126925180774483203 2229042190387771161724805)
                ·
                  refine ⟨417945410697707092823401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2229042190387771161724805 417945410697707092823401)
                  ·
                    rfl

theorem cell21_1831378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 3, 1, 4].length) (baseStart_1831378 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1831378 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1831378 prefixEnd_1831378 := by exact prefixLift 1831378
  have htrace : WordTrace (prefixWord ++ tailWord_1831378) baseStart_1831378 baseEnd_1831378 := by
    simpa [prefixWord, tailWord_1831378, baseEnd_1831378] using wordTrace_append hprefix tailTrace_1831378
  have hstable : (prefixWord ++ tailWord_1831378).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831378).length < 2 ^ (prefixWord ++ tailWord_1831378).sum := by decide
  have hdescent : baseEnd_1831378 < baseStart_1831378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831406 : List Nat := [4, 1, 2, 1, 2, 2, 3, 3, 3]
def baseStart_1831406 : Nat := 118140960795 + 1831406 * 2 ^ 59
def prefixEnd_1831406 : Nat := 4983230072969 + 3 ^ 40 * 1831406 * 2
def baseEnd_1831406 : Nat := 417951800679185266356677

theorem tailTrace_1831406 : CollatzResearch.WordTrace tailWord_1831406 prefixEnd_1831406 417951800679185266356677 := by
  unfold tailWord_1831406
  simp only [CollatzResearch.WordTrace]
  refine ⟨8349608050392039511035259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44531242935424210725521381 8349608050392039511035259)
  ·
    refine ⟨12524412075588059266552889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8349608050392039511035259 12524412075588059266552889)
    ·
      refine ⟨9393309056691044449914667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12524412075588059266552889 9393309056691044449914667)
      ·
        refine ⟨14089963585036566674872001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9393309056691044449914667 14089963585036566674872001)
        ·
          refine ⟨10567472688777425006154001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14089963585036566674872001 10567472688777425006154001)
          ·
            refine ⟨7925604516583068754615501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10567472688777425006154001 7925604516583068754615501)
            ·
              refine ⟨2972101693718650782980813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7925604516583068754615501 2972101693718650782980813)
              ·
                refine ⟨1114538135144494043617805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2972101693718650782980813 1114538135144494043617805)
                ·
                  refine ⟨417951800679185266356677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1114538135144494043617805 417951800679185266356677)
                  ·
                    rfl

theorem cell21_1831406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 3, 3].length) (baseStart_1831406 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1831406 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1831406 prefixEnd_1831406 := by exact prefixLift 1831406
  have htrace : WordTrace (prefixWord ++ tailWord_1831406) baseStart_1831406 baseEnd_1831406 := by
    simpa [prefixWord, tailWord_1831406, baseEnd_1831406] using wordTrace_append hprefix tailTrace_1831406
  have hstable : (prefixWord ++ tailWord_1831406).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831406).length < 2 ^ (prefixWord ++ tailWord_1831406).sum := by decide
  have hdescent : baseEnd_1831406 < baseStart_1831406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831479 : List Nat := [1, 1, 3, 1, 2, 3, 4, 2, 4]
def baseStart_1831479 : Nat := 118140960795 + 1831479 * 2 ^ 59
def prefixEnd_1831479 : Nat := 4983230072969 + 3 ^ 40 * 1831479 * 2
def baseEnd_1831479 : Nat := 417968460273753361639861

theorem tailTrace_1831479 : CollatzResearch.WordTrace tailWord_1831479 prefixEnd_1831479 417968460273753361639861 := by
  unfold tailWord_1831479
  simp only [CollatzResearch.WordTrace]
  refine ⟨66799526931871849555689491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44533017954581233037126327 66799526931871849555689491)
  ·
    refine ⟨100199290397807774333534237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66799526931871849555689491 100199290397807774333534237)
    ·
      refine ⟨37574733899177915375075339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100199290397807774333534237 37574733899177915375075339)
      ·
        refine ⟨56362100848766873062613009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37574733899177915375075339 56362100848766873062613009)
        ·
          refine ⟨42271575636575154796959757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56362100848766873062613009 42271575636575154796959757)
          ·
            refine ⟨15851840863715683048859909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42271575636575154796959757 15851840863715683048859909)
            ·
              refine ⟨2972220161946690571661233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15851840863715683048859909 2972220161946690571661233)
              ·
                refine ⟨2229165121460017928745925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2972220161946690571661233 2229165121460017928745925)
                ·
                  refine ⟨417968460273753361639861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2229165121460017928745925 417968460273753361639861)
                  ·
                    rfl

theorem cell21_1831479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 2, 4].length) (baseStart_1831479 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1831479 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1831479 prefixEnd_1831479 := by exact prefixLift 1831479
  have htrace : WordTrace (prefixWord ++ tailWord_1831479) baseStart_1831479 baseEnd_1831479 := by
    simpa [prefixWord, tailWord_1831479, baseEnd_1831479] using wordTrace_append hprefix tailTrace_1831479
  have hstable : (prefixWord ++ tailWord_1831479).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831479).length < 2 ^ (prefixWord ++ tailWord_1831479).sum := by decide
  have hdescent : baseEnd_1831479 < baseStart_1831479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831482 : List Nat := [3, 1, 1, 1, 3, 3, 4, 2, 3]
def baseStart_1831482 : Nat := 118140960795 + 1831482 * 2 ^ 59
def prefixEnd_1831482 : Nat := 4983230072969 + 3 ^ 40 * 1831482 * 2
def baseEnd_1831482 : Nat := 417969144914626023089855

theorem tailTrace_1831482 : CollatzResearch.WordTrace tailWord_1831482 prefixEnd_1831482 417969144914626023089855 := by
  unfold tailWord_1831482
  simp only [CollatzResearch.WordTrace]
  refine ⟨16699909087715245267012175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44533090900573987378699133 16699909087715245267012175)
  ·
    refine ⟨25049863631572867900518263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16699909087715245267012175 25049863631572867900518263)
    ·
      refine ⟨37574795447359301850777395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25049863631572867900518263 37574795447359301850777395)
      ·
        refine ⟨56362193171038952776166093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37574795447359301850777395 56362193171038952776166093)
        ·
          refine ⟨21135822439139607291062285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56362193171038952776166093 21135822439139607291062285)
          ·
            refine ⟨7925933414677352734148357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21135822439139607291062285 7925933414677352734148357)
            ·
              refine ⟨1486112515252003637652817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7925933414677352734148357 1486112515252003637652817)
              ·
                refine ⟨1114584386439002728239613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1486112515252003637652817 1114584386439002728239613)
                ·
                  refine ⟨417969144914626023089855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1114584386439002728239613 417969144914626023089855)
                  ·
                    rfl

theorem cell21_1831482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 4, 2, 3].length) (baseStart_1831482 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1831482 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1831482 prefixEnd_1831482 := by exact prefixLift 1831482
  have htrace : WordTrace (prefixWord ++ tailWord_1831482) baseStart_1831482 baseEnd_1831482 := by
    simpa [prefixWord, tailWord_1831482, baseEnd_1831482] using wordTrace_append hprefix tailTrace_1831482
  have hstable : (prefixWord ++ tailWord_1831482).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831482).length < 2 ^ (prefixWord ++ tailWord_1831482).sum := by decide
  have hdescent : baseEnd_1831482 < baseStart_1831482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831493 : List Nat := [1, 3, 1, 1, 1, 5, 3, 6]
def baseStart_1831493 : Nat := 118140960795 + 1831493 * 2 ^ 59
def prefixEnd_1831493 : Nat := 4983230072969 + 3 ^ 40 * 1831493 * 2
def baseEnd_1831493 : Nat := 139323885088164149468833

theorem tailTrace_1831493 : CollatzResearch.WordTrace tailWord_1831493 prefixEnd_1831493 139323885088164149468833 := by
  unfold tailWord_1831493
  simp only [CollatzResearch.WordTrace]
  refine ⟨66800037553821129946699133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44533358369214086631132755 66800037553821129946699133)
  ·
    refine ⟨25050014082682923730012175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66800037553821129946699133 25050014082682923730012175)
    ·
      refine ⟨37575021124024385595018263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25050014082682923730012175 37575021124024385595018263)
      ·
        refine ⟨56362531686036578392527395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37575021124024385595018263 56362531686036578392527395)
        ·
          refine ⟨84543797529054867588791093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56362531686036578392527395 84543797529054867588791093)
          ·
            refine ⟨7925981018348893836449165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84543797529054867588791093 7925981018348893836449165)
            ·
              refine ⟨2972242881880835188668437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7925981018348893836449165 2972242881880835188668437)
              ·
                refine ⟨139323885088164149468833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2972242881880835188668437 139323885088164149468833)
                ·
                  rfl

theorem cell21_1831493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 6].length) (baseStart_1831493 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1831493 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1831493 prefixEnd_1831493 := by exact prefixLift 1831493
  have htrace : WordTrace (prefixWord ++ tailWord_1831493) baseStart_1831493 baseEnd_1831493 := by
    simpa [prefixWord, tailWord_1831493, baseEnd_1831493] using wordTrace_append hprefix tailTrace_1831493
  have hstable : (prefixWord ++ tailWord_1831493).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831493).length < 2 ^ (prefixWord ++ tailWord_1831493).sum := by decide
  have hdescent : baseEnd_1831493 < baseStart_1831493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831651 : List Nat := [1, 1, 1, 7, 1, 3, 2, 2, 3]
def baseStart_1831651 : Nat := 118140960795 + 1831651 * 2 ^ 59
def prefixEnd_1831651 : Nat := 4983230072969 + 3 ^ 40 * 1831651 * 2
def baseEnd_1831651 : Nat := 418007713017119284772843

theorem tailTrace_1831651 : CollatzResearch.WordTrace tailWord_1831651 prefixEnd_1831651 418007713017119284772843 := by
  unfold tailWord_1831651
  simp only [CollatzResearch.WordTrace]
  refine ⟨66805800287248722930950807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44537200191499148620633871 66805800287248722930950807)
  ·
    refine ⟨100208700430873084396426211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66805800287248722930950807 100208700430873084396426211)
    ·
      refine ⟨150313050646309626594639317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100208700430873084396426211 150313050646309626594639317)
      ·
        refine ⟨3522962124522881873311859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 150313050646309626594639317 3522962124522881873311859)
        ·
          refine ⟨5284443186784322809967789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3522962124522881873311859 5284443186784322809967789)
          ·
            refine ⟨1981666195044121053737921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5284443186784322809967789 1981666195044121053737921)
            ·
              refine ⟨1486249646283090790303441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1981666195044121053737921 1486249646283090790303441)
              ·
                refine ⟨1114687234712318092727581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1486249646283090790303441 1114687234712318092727581)
                ·
                  refine ⟨418007713017119284772843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1114687234712318092727581 418007713017119284772843)
                  ·
                    rfl

theorem cell21_1831651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 2, 2, 3].length) (baseStart_1831651 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1831651 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1831651 prefixEnd_1831651 := by exact prefixLift 1831651
  have htrace : WordTrace (prefixWord ++ tailWord_1831651) baseStart_1831651 baseEnd_1831651 := by
    simpa [prefixWord, tailWord_1831651, baseEnd_1831651] using wordTrace_append hprefix tailTrace_1831651
  have hstable : (prefixWord ++ tailWord_1831651).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831651).length < 2 ^ (prefixWord ++ tailWord_1831651).sum := by decide
  have hdescent : baseEnd_1831651 < baseStart_1831651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831659 : List Nat := [1, 1, 1, 1, 2, 4, 1, 5, 5]
def baseStart_1831659 : Nat := 118140960795 + 1831659 * 2 ^ 59
def prefixEnd_1831659 : Nat := 4983230072969 + 3 ^ 40 * 1831659 * 2
def baseEnd_1831659 : Nat := 418009538726113048639493

theorem tailTrace_1831659 : CollatzResearch.WordTrace tailWord_1831659 prefixEnd_1831659 418009538726113048639493 := by
  unfold tailWord_1831659
  simp only [CollatzResearch.WordTrace]
  refine ⟨66806092071219740297242031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44537394714146493531494687 66806092071219740297242031)
  ·
    refine ⟨100209138106829610445863047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66806092071219740297242031 100209138106829610445863047)
    ·
      refine ⟨150313707160244415668794571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100209138106829610445863047 150313707160244415668794571)
      ·
        refine ⟨225470560740366623503191857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150313707160244415668794571 225470560740366623503191857)
        ·
          refine ⟨169102920555274967627393893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225470560740366623503191857 169102920555274967627393893)
          ·
            refine ⟨31706797604114056430136355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 169102920555274967627393893 31706797604114056430136355)
            ·
              refine ⟨47560196406171084645204533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31706797604114056430136355 47560196406171084645204533)
              ·
                refine ⟨4458768413078539185487925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47560196406171084645204533 4458768413078539185487925)
                ·
                  refine ⟨418009538726113048639493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4458768413078539185487925 418009538726113048639493)
                  ·
                    rfl

theorem cell21_1831659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 5, 5].length) (baseStart_1831659 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1831659 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1831659 prefixEnd_1831659 := by exact prefixLift 1831659
  have htrace : WordTrace (prefixWord ++ tailWord_1831659) baseStart_1831659 baseEnd_1831659 := by
    simpa [prefixWord, tailWord_1831659, baseEnd_1831659] using wordTrace_append hprefix tailTrace_1831659
  have hstable : (prefixWord ++ tailWord_1831659).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831659).length < 2 ^ (prefixWord ++ tailWord_1831659).sum := by decide
  have hdescent : baseEnd_1831659 < baseStart_1831659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831662 : List Nat := [4, 1, 2, 1, 1, 5, 1, 6]
def baseStart_1831662 : Nat := 118140960795 + 1831662 * 2 ^ 59
def prefixEnd_1831662 : Nat := 4983230072969 + 3 ^ 40 * 1831662 * 2
def baseEnd_1831662 : Nat := 139336741122328570029829

theorem tailTrace_1831662 : CollatzResearch.WordTrace tailWord_1831662 prefixEnd_1831662 139336741122328570029829 := by
  unfold tailWord_1831662
  simp only [CollatzResearch.WordTrace]
  refine ⟨8350775186276108976200155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44537467660139247873067493 8350775186276108976200155)
  ·
    refine ⟨12526162779414163464300233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8350775186276108976200155 12526162779414163464300233)
    ·
      refine ⟨9394622084560622598225175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12526162779414163464300233 9394622084560622598225175)
      ·
        refine ⟨14091933126840933897337763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9394622084560622598225175 14091933126840933897337763)
        ·
          refine ⟨21137899690261400846006645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14091933126840933897337763 21137899690261400846006645)
          ·
            refine ⟨1981678095962006329313123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21137899690261400846006645 1981678095962006329313123)
            ·
              refine ⟨2972517143943009493969685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1981678095962006329313123 2972517143943009493969685)
              ·
                refine ⟨139336741122328570029829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2972517143943009493969685 139336741122328570029829)
                ·
                  rfl

theorem cell21_1831662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 6].length) (baseStart_1831662 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1831662 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1831662 prefixEnd_1831662 := by exact prefixLift 1831662
  have htrace : WordTrace (prefixWord ++ tailWord_1831662) baseStart_1831662 baseEnd_1831662 := by
    simpa [prefixWord, tailWord_1831662, baseEnd_1831662] using wordTrace_append hprefix tailTrace_1831662
  have hstable : (prefixWord ++ tailWord_1831662).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831662).length < 2 ^ (prefixWord ++ tailWord_1831662).sum := by decide
  have hdescent : baseEnd_1831662 < baseStart_1831662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831676 : List Nat := [2, 2, 2, 1, 3, 3, 1, 2, 5]
def baseStart_1831676 : Nat := 118140960795 + 1831676 * 2 ^ 59
def prefixEnd_1831676 : Nat := 4983230072969 + 3 ^ 40 * 1831676 * 2
def baseEnd_1831676 : Nat := 418013418357724796856125

theorem tailTrace_1831676 : CollatzResearch.WordTrace tailWord_1831676 prefixEnd_1831676 418013418357724796856125 := by
  unfold tailWord_1831676
  simp only [CollatzResearch.WordTrace]
  refine ⟨33403356056079076100305441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44537808074772101467073921 33403356056079076100305441)
  ·
    refine ⟨25052517042059307075229081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33403356056079076100305441 25052517042059307075229081)
    ·
      refine ⟨18789387781544480306421811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25052517042059307075229081 18789387781544480306421811)
      ·
        refine ⟨28184081672316720459632717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18789387781544480306421811 28184081672316720459632717)
        ·
          refine ⟨10569030627118770172362269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28184081672316720459632717 10569030627118770172362269)
          ·
            refine ⟨3963386485169538814635851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10569030627118770172362269 3963386485169538814635851)
            ·
              refine ⟨5945079727754308221953777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3963386485169538814635851 5945079727754308221953777)
              ·
                refine ⟨4458809795815731166465333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5945079727754308221953777 4458809795815731166465333)
                ·
                  refine ⟨418013418357724796856125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4458809795815731166465333 418013418357724796856125)
                  ·
                    rfl

theorem cell21_1831676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 2, 5].length) (baseStart_1831676 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1831676 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1831676 prefixEnd_1831676 := by exact prefixLift 1831676
  have htrace : WordTrace (prefixWord ++ tailWord_1831676) baseStart_1831676 baseEnd_1831676 := by
    simpa [prefixWord, tailWord_1831676, baseEnd_1831676] using wordTrace_append hprefix tailTrace_1831676
  have hstable : (prefixWord ++ tailWord_1831676).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831676).length < 2 ^ (prefixWord ++ tailWord_1831676).sum := by decide
  have hdescent : baseEnd_1831676 < baseStart_1831676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831690 : List Nat := [3, 1, 2, 2, 1, 2, 2, 2, 6]
def baseStart_1831690 : Nat := 118140960795 + 1831690 * 2 ^ 59
def prefixEnd_1831690 : Nat := 4983230072969 + 3 ^ 40 * 1831690 * 2
def baseEnd_1831690 : Nat := 418016613348463883622763

theorem tailTrace_1831690 : CollatzResearch.WordTrace tailWord_1831690 prefixEnd_1831690 418016613348463883622763 := by
  unfold tailWord_1831690
  simp only [CollatzResearch.WordTrace]
  refine ⟨16701805683526858147905131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44538148489404955061080349 16701805683526858147905131)
  ·
    refine ⟨25052708525290287221857697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16701805683526858147905131 25052708525290287221857697)
    ·
      refine ⟨18789531393967715416393273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25052708525290287221857697 18789531393967715416393273)
      ·
        refine ⟨14092148545475786562294955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18789531393967715416393273 14092148545475786562294955)
        ·
          refine ⟨21138222818213679843442433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14092148545475786562294955 21138222818213679843442433)
          ·
            refine ⟨15853667113660259882581825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21138222818213679843442433 15853667113660259882581825)
            ·
              refine ⟨11890250335245194911936369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15853667113660259882581825 11890250335245194911936369)
              ·
                refine ⟨8917687751433896183952277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11890250335245194911936369 8917687751433896183952277)
                ·
                  refine ⟨418016613348463883622763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8917687751433896183952277 418016613348463883622763)
                  ·
                    rfl

theorem cell21_1831690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 6].length) (baseStart_1831690 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1831690 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1831690 prefixEnd_1831690 := by exact prefixLift 1831690
  have htrace : WordTrace (prefixWord ++ tailWord_1831690) baseStart_1831690 baseEnd_1831690 := by
    simpa [prefixWord, tailWord_1831690, baseEnd_1831690] using wordTrace_append hprefix tailTrace_1831690
  have hstable : (prefixWord ++ tailWord_1831690).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831690).length < 2 ^ (prefixWord ++ tailWord_1831690).sum := by decide
  have hdescent : baseEnd_1831690 < baseStart_1831690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831735 : List Nat := [1, 1, 3, 1, 2, 1, 3, 4, 5]
def baseStart_1831735 : Nat := 118140960795 + 1831735 * 2 ^ 59
def prefixEnd_1831735 : Nat := 4983230072969 + 3 ^ 40 * 1831735 * 2
def baseEnd_1831735 : Nat := 418026882961553805372671

theorem tailTrace_1831735 : CollatzResearch.WordTrace tailWord_1831735 prefixEnd_1831735 418026882961553805372671 := by
  unfold tailWord_1831735
  simp only [CollatzResearch.WordTrace]
  refine ⟨66808864018944405277008659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44539242679296270184672439 66808864018944405277008659)
  ·
    refine ⟨100213296028416607915512989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66808864018944405277008659 100213296028416607915512989)
    ·
      refine ⟨37579986010656227968317371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100213296028416607915512989 37579986010656227968317371)
      ·
        refine ⟨56369979015984341952476057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37579986010656227968317371 56369979015984341952476057)
        ·
          refine ⟨42277484261988256464357043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56369979015984341952476057 42277484261988256464357043)
          ·
            refine ⟨63416226392982384696535565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42277484261988256464357043 63416226392982384696535565)
            ·
              refine ⟨23781084897368394261200837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63416226392982384696535565 23781084897368394261200837)
              ·
                refine ⟨4458953418256573923975157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23781084897368394261200837 4458953418256573923975157)
                ·
                  refine ⟨418026882961553805372671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4458953418256573923975157 418026882961553805372671)
                  ·
                    rfl

theorem cell21_1831735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 4, 5].length) (baseStart_1831735 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1831735 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1831735 prefixEnd_1831735 := by exact prefixLift 1831735
  have htrace : WordTrace (prefixWord ++ tailWord_1831735) baseStart_1831735 baseEnd_1831735 := by
    simpa [prefixWord, tailWord_1831735, baseEnd_1831735] using wordTrace_append hprefix tailTrace_1831735
  have hstable : (prefixWord ++ tailWord_1831735).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831735).length < 2 ^ (prefixWord ++ tailWord_1831735).sum := by decide
  have hdescent : baseEnd_1831735 < baseStart_1831735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831783 : List Nat := [1, 1, 5, 1, 2, 3, 1, 3, 4]
def baseStart_1831783 : Nat := 118140960795 + 1831783 * 2 ^ 59
def prefixEnd_1831783 : Nat := 4983230072969 + 3 ^ 40 * 1831783 * 2
def baseEnd_1831783 : Nat := 418037837215516388572573

theorem tailTrace_1831783 : CollatzResearch.WordTrace tailWord_1831783 prefixEnd_1831783 418037837215516388572573 := by
  unfold tailWord_1831783
  simp only [CollatzResearch.WordTrace]
  refine ⟨66810614722770509474756003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44540409815180339649837335 66810614722770509474756003)
  ·
    refine ⟨100215922084155764212134005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66810614722770509474756003 100215922084155764212134005)
    ·
      refine ⟨9395242695389602894887563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 100215922084155764212134005 9395242695389602894887563)
      ·
        refine ⟨14092864043084404342331345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9395242695389602894887563 14092864043084404342331345)
        ·
          refine ⟨10569648032313303256748509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14092864043084404342331345 10569648032313303256748509)
          ·
            refine ⟨3963618012117488721280691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10569648032313303256748509 3963618012117488721280691)
            ·
              refine ⟨5945427018176233081921037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3963618012117488721280691 5945427018176233081921037)
              ·
                refine ⟨2229535131816087405720389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5945427018176233081921037 2229535131816087405720389)
                ·
                  refine ⟨418037837215516388572573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2229535131816087405720389 418037837215516388572573)
                  ·
                    rfl

theorem cell21_1831783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 3, 4].length) (baseStart_1831783 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1831783 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1831783 prefixEnd_1831783 := by exact prefixLift 1831783
  have htrace : WordTrace (prefixWord ++ tailWord_1831783) baseStart_1831783 baseEnd_1831783 := by
    simpa [prefixWord, tailWord_1831783, baseEnd_1831783] using wordTrace_append hprefix tailTrace_1831783
  have hstable : (prefixWord ++ tailWord_1831783).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831783).length < 2 ^ (prefixWord ++ tailWord_1831783).sum := by decide
  have hdescent : baseEnd_1831783 < baseStart_1831783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831797 : List Nat := [1, 3, 4, 1, 1, 2, 2, 7]
def baseStart_1831797 : Nat := 118140960795 + 1831797 * 2 ^ 59
def prefixEnd_1831797 : Nat := 4983230072969 + 3 ^ 40 * 1831797 * 2
def baseEnd_1831797 : Nat := 139347010735418491779737

theorem tailTrace_1831797 : CollatzResearch.WordTrace tailWord_1831797 prefixEnd_1831797 139347010735418491779737 := by
  unfold tailWord_1831797
  simp only [CollatzResearch.WordTrace]
  refine ⟨66811125344719789865765645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44540750229813193243843763 66811125344719789865765645)
  ·
    refine ⟨25054172004269921199662117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66811125344719789865765645 25054172004269921199662117)
    ·
      refine ⟨4697657250800610224936647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25054172004269921199662117 4697657250800610224936647)
      ·
        refine ⟨7046485876200915337404971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4697657250800610224936647 7046485876200915337404971)
        ·
          refine ⟨10569728814301373006107457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7046485876200915337404971 10569728814301373006107457)
          ·
            refine ⟨7927296610726029754580593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10569728814301373006107457 7927296610726029754580593)
            ·
              refine ⟨5945472458044522315935445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7927296610726029754580593 5945472458044522315935445)
              ·
                refine ⟨139347010735418491779737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5945472458044522315935445 139347010735418491779737)
                ·
                  rfl

theorem cell21_1831797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 7].length) (baseStart_1831797 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1831797 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1831797 prefixEnd_1831797 := by exact prefixLift 1831797
  have htrace : WordTrace (prefixWord ++ tailWord_1831797) baseStart_1831797 baseEnd_1831797 := by
    simpa [prefixWord, tailWord_1831797, baseEnd_1831797] using wordTrace_append hprefix tailTrace_1831797
  have hstable : (prefixWord ++ tailWord_1831797).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831797).length < 2 ^ (prefixWord ++ tailWord_1831797).sum := by decide
  have hdescent : baseEnd_1831797 < baseStart_1831797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831828 : List Nat := [2, 4, 2, 1, 1, 1, 2, 3, 5]
def baseStart_1831828 : Nat := 118140960795 + 1831828 * 2 ^ 59
def prefixEnd_1831828 : Nat := 4983230072969 + 3 ^ 40 * 1831828 * 2
def baseEnd_1831828 : Nat := 418048106828606310322481

theorem tailTrace_1831828 : CollatzResearch.WordTrace tailWord_1831828 prefixEnd_1831828 418048106828606310322481 := by
  unfold tailWord_1831828
  simp only [CollatzResearch.WordTrace]
  refine ⟨33406128003803741080072069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44541504005071654773429425 33406128003803741080072069)
  ·
    refine ⟨6263649000713201452513513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33406128003803741080072069 6263649000713201452513513)
    ·
      refine ⟨4697736750534901089385135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6263649000713201452513513 4697736750534901089385135)
      ·
        refine ⟨7046605125802351634077703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4697736750534901089385135 7046605125802351634077703)
        ·
          refine ⟨10569907688703527451116555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7046605125802351634077703 10569907688703527451116555)
          ·
            refine ⟨15854861533055291176674833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10569907688703527451116555 15854861533055291176674833)
            ·
              refine ⟨11891146149791468382506125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15854861533055291176674833 11891146149791468382506125)
              ·
                refine ⟨4459179806171800643439797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11891146149791468382506125 4459179806171800643439797)
                ·
                  refine ⟨418048106828606310322481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4459179806171800643439797 418048106828606310322481)
                  ·
                    rfl

theorem cell21_1831828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_1831828 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1831828 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1831828 prefixEnd_1831828 := by exact prefixLift 1831828
  have htrace : WordTrace (prefixWord ++ tailWord_1831828) baseStart_1831828 baseEnd_1831828 := by
    simpa [prefixWord, tailWord_1831828, baseEnd_1831828] using wordTrace_append hprefix tailTrace_1831828
  have hstable : (prefixWord ++ tailWord_1831828).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831828).length < 2 ^ (prefixWord ++ tailWord_1831828).sum := by decide
  have hdescent : baseEnd_1831828 < baseStart_1831828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831876 : List Nat := [2, 3, 3, 3, 1, 1, 1, 1, 6]
def baseStart_1831876 : Nat := 118140960795 + 1831876 * 2 ^ 59
def prefixEnd_1831876 : Nat := 4983230072969 + 3 ^ 40 * 1831876 * 2
def baseEnd_1831876 : Nat := 418059061082568893522383

theorem tailTrace_1831876 : CollatzResearch.WordTrace tailWord_1831876 prefixEnd_1831876 418059061082568893522383 := by
  unfold tailWord_1831876
  simp only [CollatzResearch.WordTrace]
  refine ⟨33407003355716793178945741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44542671140955724238594321 33407003355716793178945741)
  ·
    refine ⟨12527626258393797442104653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33407003355716793178945741 12527626258393797442104653)
    ·
      refine ⟨4697859846897674040789245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12527626258393797442104653 4697859846897674040789245)
      ·
        refine ⟨1761697442586627765295967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4697859846897674040789245 1761697442586627765295967)
        ·
          refine ⟨2642546163879941647943951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1761697442586627765295967 2642546163879941647943951)
          ·
            refine ⟨3963819245819912471915927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2642546163879941647943951 3963819245819912471915927)
            ·
              refine ⟨5945728868729868707873891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3963819245819912471915927 5945728868729868707873891)
              ·
                refine ⟨8918593303094803061810837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5945728868729868707873891 8918593303094803061810837)
                ·
                  refine ⟨418059061082568893522383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8918593303094803061810837 418059061082568893522383)
                  ·
                    rfl

theorem cell21_1831876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 6].length) (baseStart_1831876 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1831876 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1831876 prefixEnd_1831876 := by exact prefixLift 1831876
  have htrace : WordTrace (prefixWord ++ tailWord_1831876) baseStart_1831876 baseEnd_1831876 := by
    simpa [prefixWord, tailWord_1831876, baseEnd_1831876] using wordTrace_append hprefix tailTrace_1831876
  have hstable : (prefixWord ++ tailWord_1831876).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831876).length < 2 ^ (prefixWord ++ tailWord_1831876).sum := by decide
  have hdescent : baseEnd_1831876 < baseStart_1831876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831887 : List Nat := [1, 1, 2, 1, 1, 6, 1, 3, 5]
def baseStart_1831887 : Nat := 118140960795 + 1831887 * 2 ^ 59
def prefixEnd_1831887 : Nat := 4983230072969 + 3 ^ 40 * 1831887 * 2
def baseEnd_1831887 : Nat := 418061571432435318839027

theorem tailTrace_1831887 : CollatzResearch.WordTrace tailWord_1831887 prefixEnd_1831887 418061571432435318839027 := by
  unfold tailWord_1831887
  simp only [CollatzResearch.WordTrace]
  refine ⟨66814407914393735236541915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44542938609595823491027943 66814407914393735236541915)
  ·
    refine ⟨100221611871590602854812873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66814407914393735236541915 100221611871590602854812873)
    ·
      refine ⟨75166208903692952141109655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100221611871590602854812873 75166208903692952141109655)
      ·
        refine ⟨112749313355539428211664483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75166208903692952141109655 112749313355539428211664483)
        ·
          refine ⟨169123970033309142317496725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112749313355539428211664483 169123970033309142317496725)
          ·
            refine ⟨7927686095311366046132659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 169123970033309142317496725 7927686095311366046132659)
            ·
              refine ⟨11891529142967049069198989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7927686095311366046132659 11891529142967049069198989)
              ·
                refine ⟨4459323428612643400949621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11891529142967049069198989 4459323428612643400949621)
                ·
                  refine ⟨418061571432435318839027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4459323428612643400949621 418061571432435318839027)
                  ·
                    rfl

theorem cell21_1831887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 3, 5].length) (baseStart_1831887 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1831887 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1831887 prefixEnd_1831887 := by exact prefixLift 1831887
  have htrace : WordTrace (prefixWord ++ tailWord_1831887) baseStart_1831887 baseEnd_1831887 := by
    simpa [prefixWord, tailWord_1831887, baseEnd_1831887] using wordTrace_append hprefix tailTrace_1831887
  have hstable : (prefixWord ++ tailWord_1831887).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831887).length < 2 ^ (prefixWord ++ tailWord_1831887).sum := by decide
  have hdescent : baseEnd_1831887 < baseStart_1831887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831921 : List Nat := [1, 2, 2, 2, 4, 1, 3, 3, 3]
def baseStart_1831921 : Nat := 118140960795 + 1831921 * 2 ^ 59
def prefixEnd_1831921 : Nat := 4983230072969 + 3 ^ 40 * 1831921 * 2
def baseEnd_1831921 : Nat := 418069330695658815272291

theorem tailTrace_1831921 : CollatzResearch.WordTrace tailWord_1831921 prefixEnd_1831921 418069330695658815272291 := by
  unfold tailWord_1831921
  simp only [CollatzResearch.WordTrace]
  refine ⟨66815647996270559043279617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44543765330847039362186411 66815647996270559043279617)
  ·
    refine ⟨50111735997202919282459713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66815647996270559043279617 50111735997202919282459713)
    ·
      refine ⟨37583801997902189461844785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50111735997202919282459713 37583801997902189461844785)
      ·
        refine ⟨28187851498426642096383589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37583801997902189461844785 28187851498426642096383589)
        ·
          refine ⟨5285222155954995393071923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28187851498426642096383589 5285222155954995393071923)
          ·
            refine ⟨7927833233932493089607885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5285222155954995393071923 7927833233932493089607885)
            ·
              refine ⟨2972937462724684908602957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7927833233932493089607885 2972937462724684908602957)
              ·
                refine ⟨1114851548521756840726109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2972937462724684908602957 1114851548521756840726109)
                ·
                  refine ⟨418069330695658815272291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1114851548521756840726109 418069330695658815272291)
                  ·
                    rfl

theorem cell21_1831921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 3, 3].length) (baseStart_1831921 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1831921 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1831921 prefixEnd_1831921 := by exact prefixLift 1831921
  have htrace : WordTrace (prefixWord ++ tailWord_1831921) baseStart_1831921 baseEnd_1831921 := by
    simpa [prefixWord, tailWord_1831921, baseEnd_1831921] using wordTrace_append hprefix tailTrace_1831921
  have hstable : (prefixWord ++ tailWord_1831921).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831921).length < 2 ^ (prefixWord ++ tailWord_1831921).sum := by decide
  have hdescent : baseEnd_1831921 < baseStart_1831921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831932 : List Nat := [2, 2, 2, 1, 2, 3, 9]
def baseStart_1831932 : Nat := 118140960795 + 1831932 * 2 ^ 59
def prefixEnd_1831932 : Nat := 4983230072969 + 3 ^ 40 * 1831932 * 2
def baseEnd_1831932 : Nat := 46452426782836137843215

theorem tailTrace_1831932 : CollatzResearch.WordTrace tailWord_1831932 prefixEnd_1831932 46452426782836137843215 := by
  unfold tailWord_1831932
  simp only [CollatzResearch.WordTrace]
  refine ⟨33408024599615353960965025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44544032799487138614620033 33408024599615353960965025)
  ·
    refine ⟨25056018449711515470723769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33408024599615353960965025 25056018449711515470723769)
    ·
      refine ⟨18792013837283636603042827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25056018449711515470723769 18792013837283636603042827)
      ·
        refine ⟨28188020755925454904564241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18792013837283636603042827 28188020755925454904564241)
        ·
          refine ⟨21141015566944091178423181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28188020755925454904564241 21141015566944091178423181)
          ·
            refine ⟨7927880837604034191908693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21141015566944091178423181 7927880837604034191908693)
            ·
              refine ⟨46452426782836137843215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7927880837604034191908693 46452426782836137843215)
              ·
                rfl

theorem cell21_1831932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 9].length) (baseStart_1831932 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1831932 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1831932 prefixEnd_1831932 := by exact prefixLift 1831932
  have htrace : WordTrace (prefixWord ++ tailWord_1831932) baseStart_1831932 baseEnd_1831932 := by
    simpa [prefixWord, tailWord_1831932, baseEnd_1831932] using wordTrace_append hprefix tailTrace_1831932
  have hstable : (prefixWord ++ tailWord_1831932).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831932).length < 2 ^ (prefixWord ++ tailWord_1831932).sum := by decide
  have hdescent : baseEnd_1831932 < baseStart_1831932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831980 : List Nat := [2, 2, 1, 1, 1, 2, 4, 5, 3]
def baseStart_1831980 : Nat := 118140960795 + 1831980 * 2 ^ 59
def prefixEnd_1831980 : Nat := 4983230072969 + 3 ^ 40 * 1831980 * 2
def baseEnd_1831980 : Nat := 418082795299487823788837

theorem tailTrace_1831980 : CollatzResearch.WordTrace tailWord_1831980 prefixEnd_1831980 418082795299487823788837 := by
  unfold tailWord_1831980
  simp only [CollatzResearch.WordTrace]
  refine ⟨33408899951528406059838697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44545199935371208079784929 33408899951528406059838697)
  ·
    refine ⟨25056674963646304544879023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33408899951528406059838697 25056674963646304544879023)
    ·
      refine ⟨37585012445469456817318535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25056674963646304544879023 37585012445469456817318535)
      ·
        refine ⟨56377518668204185225977803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37585012445469456817318535 56377518668204185225977803)
        ·
          refine ⟨84566278002306277838966705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56377518668204185225977803 84566278002306277838966705)
          ·
            refine ⟨63424708501729708379225029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84566278002306277838966705 63424708501729708379225029)
            ·
              refine ⟨11892132844074320321104693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63424708501729708379225029 11892132844074320321104693)
              ·
                refine ⟨1114887454131967530103565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11892132844074320321104693 1114887454131967530103565)
                ·
                  refine ⟨418082795299487823788837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1114887454131967530103565 418082795299487823788837)
                  ·
                    rfl

theorem cell21_1831980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 5, 3].length) (baseStart_1831980 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1831980 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1831980 prefixEnd_1831980 := by exact prefixLift 1831980
  have htrace : WordTrace (prefixWord ++ tailWord_1831980) baseStart_1831980 baseEnd_1831980 := by
    simpa [prefixWord, tailWord_1831980, baseEnd_1831980] using wordTrace_append hprefix tailTrace_1831980
  have hstable : (prefixWord ++ tailWord_1831980).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831980).length < 2 ^ (prefixWord ++ tailWord_1831980).sum := by decide
  have hdescent : baseEnd_1831980 < baseStart_1831980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831994 : List Nat := [3, 1, 1, 1, 3, 1, 3, 4, 4]
def baseStart_1831994 : Nat := 118140960795 + 1831994 * 2 ^ 59
def prefixEnd_1831994 : Nat := 4983230072969 + 3 ^ 40 * 1831994 * 2
def baseEnd_1831994 : Nat := 418085990290226910555475

theorem tailTrace_1831994 : CollatzResearch.WordTrace tailWord_1831994 prefixEnd_1831994 418085990290226910555475 := by
  unfold tailWord_1831994
  simp only [CollatzResearch.WordTrace]
  refine ⟨16704577631251523127671759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44545540350004061673791357 16704577631251523127671759)
  ·
    refine ⟨25056866446877284691507639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16704577631251523127671759 25056866446877284691507639)
    ·
      refine ⟨37585299670315927037261459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25056866446877284691507639 37585299670315927037261459)
      ·
        refine ⟨56377949505473890555892189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37585299670315927037261459 56377949505473890555892189)
        ·
          refine ⟨21141731064552708958459571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56377949505473890555892189 21141731064552708958459571)
          ·
            refine ⟨31712596596829063437689357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21141731064552708958459571 31712596596829063437689357)
            ·
              refine ⟨11892223723810898789133509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31712596596829063437689357 11892223723810898789133509)
              ·
                refine ⟨2229791948214543522962533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11892223723810898789133509 2229791948214543522962533)
                ·
                  refine ⟨418085990290226910555475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2229791948214543522962533 418085990290226910555475)
                  ·
                    rfl

theorem cell21_1831994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 4, 4].length) (baseStart_1831994 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1831994 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1831994 prefixEnd_1831994 := by exact prefixLift 1831994
  have htrace : WordTrace (prefixWord ++ tailWord_1831994) baseStart_1831994 baseEnd_1831994 := by
    simpa [prefixWord, tailWord_1831994, baseEnd_1831994] using wordTrace_append hprefix tailTrace_1831994
  have hstable : (prefixWord ++ tailWord_1831994).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831994).length < 2 ^ (prefixWord ++ tailWord_1831994).sum := by decide
  have hdescent : baseEnd_1831994 < baseStart_1831994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1831997 : List Nat := [1, 4, 1, 3, 1, 3, 1, 4, 3]
def baseStart_1831997 : Nat := 118140960795 + 1831997 * 2 ^ 59
def prefixEnd_1831997 : Nat := 4983230072969 + 3 ^ 40 * 1831997 * 2
def baseEnd_1831997 : Nat := 418086674931099572005469

theorem tailTrace_1831997 : CollatzResearch.WordTrace tailWord_1831997 prefixEnd_1831997 418086674931099572005469 := by
  unfold tailWord_1831997
  simp only [CollatzResearch.WordTrace]
  refine ⟨66818419943995224023046245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44545613295996816015364163 66818419943995224023046245)
  ·
    refine ⟨12528453739499104504321171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66818419943995224023046245 12528453739499104504321171)
    ·
      refine ⟨18792680609248656756481757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12528453739499104504321171 18792680609248656756481757)
      ·
        refine ⟨7047255228468246283680659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18792680609248656756481757 7047255228468246283680659)
        ·
          refine ⟨10570882842702369425520989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7047255228468246283680659 10570882842702369425520989)
          ·
            refine ⟨3964081066013388534570371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10570882842702369425520989 3964081066013388534570371)
            ·
              refine ⟨5946121599020082801855557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3964081066013388534570371 5946121599020082801855557)
              ·
                refine ⟨1114897799816265525347917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5946121599020082801855557 1114897799816265525347917)
                ·
                  refine ⟨418086674931099572005469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1114897799816265525347917 418086674931099572005469)
                  ·
                    rfl

theorem cell21_1831997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 4, 3].length) (baseStart_1831997 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1831997 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1831997 prefixEnd_1831997 := by exact prefixLift 1831997
  have htrace : WordTrace (prefixWord ++ tailWord_1831997) baseStart_1831997 baseEnd_1831997 := by
    simpa [prefixWord, tailWord_1831997, baseEnd_1831997] using wordTrace_append hprefix tailTrace_1831997
  have hstable : (prefixWord ++ tailWord_1831997).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1831997).length < 2 ^ (prefixWord ++ tailWord_1831997).sum := by decide
  have hdescent : baseEnd_1831997 < baseStart_1831997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1831997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832056 : List Nat := [2, 1, 2, 1, 1, 1, 6, 4, 3]
def baseStart_1832056 : Nat := 118140960795 + 1832056 * 2 ^ 59
def prefixEnd_1832056 : Nat := 4983230072969 + 3 ^ 40 * 1832056 * 2
def baseEnd_1832056 : Nat := 418100139534928580522015

theorem tailTrace_1832056 : CollatzResearch.WordTrace tailWord_1832056 prefixEnd_1832056 418100139534928580522015 := by
  unfold tailWord_1832056
  simp only [CollatzResearch.WordTrace]
  refine ⟨33410285925390738549722011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44547047900520984732962681 33410285925390738549722011)
  ·
    refine ⟨50115428888086107824583017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33410285925390738549722011 50115428888086107824583017)
    ·
      refine ⟨37586571666064580868437263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50115428888086107824583017 37586571666064580868437263)
      ·
        refine ⟨56379857499096871302655895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37586571666064580868437263 56379857499096871302655895)
        ·
          refine ⟨84569786248645306953983843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56379857499096871302655895 84569786248645306953983843)
          ·
            refine ⟨126854679372967960430975765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84569786248645306953983843 126854679372967960430975765)
            ·
              refine ⟨5946313095607873145201989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 126854679372967960430975765 5946313095607873145201989)
              ·
                refine ⟨1114933705426476214725373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5946313095607873145201989 1114933705426476214725373)
                ·
                  refine ⟨418100139534928580522015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1114933705426476214725373 418100139534928580522015)
                  ·
                    rfl

theorem cell21_1832056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 4, 3].length) (baseStart_1832056 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1832056 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1832056 prefixEnd_1832056 := by exact prefixLift 1832056
  have htrace : WordTrace (prefixWord ++ tailWord_1832056) baseStart_1832056 baseEnd_1832056 := by
    simpa [prefixWord, tailWord_1832056, baseEnd_1832056] using wordTrace_append hprefix tailTrace_1832056
  have hstable : (prefixWord ++ tailWord_1832056).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832056).length < 2 ^ (prefixWord ++ tailWord_1832056).sum := by decide
  have hdescent : baseEnd_1832056 < baseStart_1832056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832090 : List Nat := [3, 1, 1, 5, 1, 3, 1, 3, 3]
def baseStart_1832090 : Nat := 118140960795 + 1832090 * 2 ^ 59
def prefixEnd_1832090 : Nat := 4983230072969 + 3 ^ 40 * 1832090 * 2
def baseEnd_1832090 : Nat := 418107898798152076955279

theorem tailTrace_1832090 : CollatzResearch.WordTrace tailWord_1832090 prefixEnd_1832090 418107898798152076955279 := by
  unfold tailWord_1832090
  simp only [CollatzResearch.WordTrace]
  refine ⟨16705452983164575226545431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44547874621772200604121149 16705452983164575226545431)
  ·
    refine ⟨25058179474746862839818147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16705452983164575226545431 25058179474746862839818147)
    ·
      refine ⟨37587269212120294259727221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25058179474746862839818147 37587269212120294259727221)
      ·
        refine ⟨3523806488636277586849427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37587269212120294259727221 3523806488636277586849427)
        ·
          refine ⟨5285709732954416380274141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3523806488636277586849427 5285709732954416380274141)
          ·
            refine ⟨1982141149857906142602803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5285709732954416380274141 1982141149857906142602803)
            ·
              refine ⟨2973211724786859213904205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1982141149857906142602803 2973211724786859213904205)
              ·
                refine ⟨1114954396795072205214077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2973211724786859213904205 1114954396795072205214077)
                ·
                  refine ⟨418107898798152076955279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1114954396795072205214077 418107898798152076955279)
                  ·
                    rfl

theorem cell21_1832090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 3, 3].length) (baseStart_1832090 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1832090 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1832090 prefixEnd_1832090 := by exact prefixLift 1832090
  have htrace : WordTrace (prefixWord ++ tailWord_1832090) baseStart_1832090 baseEnd_1832090 := by
    simpa [prefixWord, tailWord_1832090, baseEnd_1832090] using wordTrace_append hprefix tailTrace_1832090
  have hstable : (prefixWord ++ tailWord_1832090).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832090).length < 2 ^ (prefixWord ++ tailWord_1832090).sum := by decide
  have hdescent : baseEnd_1832090 < baseStart_1832090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832115 : List Nat := [1, 1, 1, 2, 3, 2, 5, 1, 5]
def baseStart_1832115 : Nat := 118140960795 + 1832115 * 2 ^ 59
def prefixEnd_1832115 : Nat := 4983230072969 + 3 ^ 40 * 1832115 * 2
def baseEnd_1832115 : Nat := 418113604138757589038561

theorem tailTrace_1832115 : CollatzResearch.WordTrace tailWord_1832115 prefixEnd_1832115 418113604138757589038561 := by
  unfold tailWord_1832115
  simp only [CollatzResearch.WordTrace]
  refine ⟨66822723757567730175841799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44548482505045153450561199 66822723757567730175841799)
  ·
    refine ⟨100234085636351595263762699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66822723757567730175841799 100234085636351595263762699)
    ·
      refine ⟨150351128454527392895644049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100234085636351595263762699 150351128454527392895644049)
      ·
        refine ⟨112763346340895544671733037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150351128454527392895644049 112763346340895544671733037)
        ·
          refine ⟨42286254877835829251899889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112763346340895544671733037 42286254877835829251899889)
          ·
            refine ⟨31714691158376871938924917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42286254877835829251899889 31714691158376871938924917)
            ·
              refine ⟨2973252296097831744274211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31714691158376871938924917 2973252296097831744274211)
              ·
                refine ⟨4459878444146747616411317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2973252296097831744274211 4459878444146747616411317)
                ·
                  refine ⟨418113604138757589038561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4459878444146747616411317 418113604138757589038561)
                  ·
                    rfl

theorem cell21_1832115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 1, 5].length) (baseStart_1832115 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1832115 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1832115 prefixEnd_1832115 := by exact prefixLift 1832115
  have htrace : WordTrace (prefixWord ++ tailWord_1832115) baseStart_1832115 baseEnd_1832115 := by
    simpa [prefixWord, tailWord_1832115, baseEnd_1832115] using wordTrace_append hprefix tailTrace_1832115
  have hstable : (prefixWord ++ tailWord_1832115).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832115).length < 2 ^ (prefixWord ++ tailWord_1832115).sum := by decide
  have hdescent : baseEnd_1832115 < baseStart_1832115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832191 : List Nat := [1, 1, 2, 2, 1, 6, 1, 2, 5]
def baseStart_1832191 : Nat := 118140960795 + 1832191 * 2 ^ 59
def prefixEnd_1832191 : Nat := 4983230072969 + 3 ^ 40 * 1832191 * 2
def baseEnd_1832191 : Nat := 418130948374198345771739

theorem tailTrace_1832191 : CollatzResearch.WordTrace tailWord_1832191 prefixEnd_1832191 418130948374198345771739 := by
  unfold tailWord_1832191
  simp only [CollatzResearch.WordTrace]
  refine ⟨66825495705292395155608427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44550330470194930103738951 66825495705292395155608427)
  ·
    refine ⟨100238243557938592733412641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66825495705292395155608427 100238243557938592733412641)
    ·
      refine ⟨75178682668453944550059481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100238243557938592733412641 75178682668453944550059481)
      ·
        refine ⟨56384012001340458412544611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75178682668453944550059481 56384012001340458412544611)
        ·
          refine ⟨84576018002010687618816917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56384012001340458412544611 84576018002010687618816917)
          ·
            refine ⟨3964500843844250982132043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 84576018002010687618816917 3964500843844250982132043)
            ·
              refine ⟨5946751265766376473198065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3964500843844250982132043 5946751265766376473198065)
              ·
                refine ⟨4460063449324782354898549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5946751265766376473198065 4460063449324782354898549)
                ·
                  refine ⟨418130948374198345771739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4460063449324782354898549 418130948374198345771739)
                  ·
                    rfl

theorem cell21_1832191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 2, 5].length) (baseStart_1832191 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1832191 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1832191 prefixEnd_1832191 := by exact prefixLift 1832191
  have htrace : WordTrace (prefixWord ++ tailWord_1832191) baseStart_1832191 baseEnd_1832191 := by
    simpa [prefixWord, tailWord_1832191, baseEnd_1832191] using wordTrace_append hprefix tailTrace_1832191
  have hstable : (prefixWord ++ tailWord_1832191).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832191).length < 2 ^ (prefixWord ++ tailWord_1832191).sum := by decide
  have hdescent : baseEnd_1832191 < baseStart_1832191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832281 : List Nat := [1, 2, 1, 2, 2, 2, 4, 1, 6]
def baseStart_1832281 : Nat := 118140960795 + 1832281 * 2 ^ 59
def prefixEnd_1832281 : Nat := 4983230072969 + 3 ^ 40 * 1832281 * 2
def baseEnd_1832281 : Nat := 418151487600378189271555

theorem tailTrace_1832281 : CollatzResearch.WordTrace tailWord_1832281 prefixEnd_1832281 418151487600378189271555 := by
  unfold tailWord_1832281
  simp only [CollatzResearch.WordTrace]
  refine ⟨66828778274966340526384697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44552518849977560350923131 66828778274966340526384697)
  ·
    refine ⟨50121583706224755394788523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66828778274966340526384697 50121583706224755394788523)
    ·
      refine ⟨75182375559337133092182785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50121583706224755394788523 75182375559337133092182785)
      ·
        refine ⟨56386781669502849819137089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75182375559337133092182785 56386781669502849819137089)
        ·
          refine ⟨42290086252127137364352817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56386781669502849819137089 42290086252127137364352817)
          ·
            refine ⟨31717564689095353023264613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42290086252127137364352817 31717564689095353023264613)
            ·
              refine ⟨5947043379205378691862115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31717564689095353023264613 5947043379205378691862115)
              ·
                refine ⟨8920565068808068037793173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5947043379205378691862115 8920565068808068037793173)
                ·
                  refine ⟨418151487600378189271555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8920565068808068037793173 418151487600378189271555)
                  ·
                    rfl

theorem cell21_1832281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 6].length) (baseStart_1832281 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1832281 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1832281 prefixEnd_1832281 := by exact prefixLift 1832281
  have htrace : WordTrace (prefixWord ++ tailWord_1832281) baseStart_1832281 baseEnd_1832281 := by
    simpa [prefixWord, tailWord_1832281, baseEnd_1832281] using wordTrace_append hprefix tailTrace_1832281
  have hstable : (prefixWord ++ tailWord_1832281).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832281).length < 2 ^ (prefixWord ++ tailWord_1832281).sum := by decide
  have hdescent : baseEnd_1832281 < baseStart_1832281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832371 : List Nat := [1, 1, 1, 2, 3, 1, 1, 11]
def baseStart_1832371 : Nat := 118140960795 + 1832371 * 2 ^ 59
def prefixEnd_1832371 : Nat := 4983230072969 + 3 ^ 40 * 1832371 * 2
def baseEnd_1832371 : Nat := 139390675608852677590457

theorem tailTrace_1832371 : CollatzResearch.WordTrace tailWord_1832371 prefixEnd_1832371 139390675608852677590457 := by
  unfold tailWord_1832371
  simp only [CollatzResearch.WordTrace]
  refine ⟨66832060844640285897160967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44554707229760190598107311 66832060844640285897160967)
  ·
    refine ⟨100248091266960428845741451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66832060844640285897160967 100248091266960428845741451)
    ·
      refine ⟨150372136900440643268612177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100248091266960428845741451 150372136900440643268612177)
      ·
        refine ⟨112779102675330482451459133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150372136900440643268612177 112779102675330482451459133)
        ·
          refine ⟨42292163503248930919297175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112779102675330482451459133 42292163503248930919297175)
          ·
            refine ⟨63438245254873396378945763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42292163503248930919297175 63438245254873396378945763)
            ·
              refine ⟨95157367882310094568418645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63438245254873396378945763 95157367882310094568418645)
              ·
                refine ⟨139390675608852677590457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 95157367882310094568418645 139390675608852677590457)
                ·
                  rfl

theorem cell21_1832371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 11].length) (baseStart_1832371 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1832371 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1832371 prefixEnd_1832371 := by exact prefixLift 1832371
  have htrace : WordTrace (prefixWord ++ tailWord_1832371) baseStart_1832371 baseEnd_1832371 := by
    simpa [prefixWord, tailWord_1832371, baseEnd_1832371] using wordTrace_append hprefix tailTrace_1832371
  have hstable : (prefixWord ++ tailWord_1832371).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832371).length < 2 ^ (prefixWord ++ tailWord_1832371).sum := by decide
  have hdescent : baseEnd_1832371 < baseStart_1832371 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832377 : List Nat := [1, 2, 1, 4, 4, 1, 2, 3, 3]
def baseStart_1832377 : Nat := 118140960795 + 1832377 * 2 ^ 59
def prefixEnd_1832377 : Nat := 4983230072969 + 3 ^ 40 * 1832377 * 2
def baseEnd_1832377 : Nat := 418173396108303355671359

theorem tailTrace_1832377 : CollatzResearch.WordTrace tailWord_1832377 prefixEnd_1832377 418173396108303355671359 := by
  unfold tailWord_1832377
  simp only [CollatzResearch.WordTrace]
  refine ⟨66832279682618548921879385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44554853121745699281252923 66832279682618548921879385)
  ·
    refine ⟨50124209761963911691409539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66832279682618548921879385 50124209761963911691409539)
    ·
      refine ⟨75186314642945867537114309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50124209761963911691409539 75186314642945867537114309)
      ·
        refine ⟨14097433995552350163208933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75186314642945867537114309 14097433995552350163208933)
        ·
          refine ⟨2643268874166065655601675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14097433995552350163208933 2643268874166065655601675)
          ·
            refine ⟨3964903311249098483402513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2643268874166065655601675 3964903311249098483402513)
            ·
              refine ⟨2973677483436823862551885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3964903311249098483402513 2973677483436823862551885)
              ·
                refine ⟨1115129056288808948456957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2973677483436823862551885 1115129056288808948456957)
                ·
                  refine ⟨418173396108303355671359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1115129056288808948456957 418173396108303355671359)
                  ·
                    rfl

theorem cell21_1832377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 3, 3].length) (baseStart_1832377 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1832377 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1832377 prefixEnd_1832377 := by exact prefixLift 1832377
  have htrace : WordTrace (prefixWord ++ tailWord_1832377) baseStart_1832377 baseEnd_1832377 := by
    simpa [prefixWord, tailWord_1832377, baseEnd_1832377] using wordTrace_append hprefix tailTrace_1832377
  have hstable : (prefixWord ++ tailWord_1832377).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832377).length < 2 ^ (prefixWord ++ tailWord_1832377).sum := by decide
  have hdescent : baseEnd_1832377 < baseStart_1832377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832419 : List Nat := [1, 1, 1, 6, 2, 1, 2, 2, 5]
def baseStart_1832419 : Nat := 118140960795 + 1832419 * 2 ^ 59
def prefixEnd_1832419 : Nat := 4983230072969 + 3 ^ 40 * 1832419 * 2
def baseEnd_1832419 : Nat := 418182981080520615971273

theorem tailTrace_1832419 : CollatzResearch.WordTrace tailWord_1832419 prefixEnd_1832419 418182981080520615971273 := by
  unfold tailWord_1832419
  simp only [CollatzResearch.WordTrace]
  refine ⟨66833811548466390094908311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44555874365644260063272207 66833811548466390094908311)
  ·
    refine ⟨100250717322699585142362467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66833811548466390094908311 100250717322699585142362467)
    ·
      refine ⟨150376075984049377713543701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100250717322699585142362467 150376075984049377713543701)
      ·
        refine ⟨7048878561752314580322361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 150376075984049377713543701 7048878561752314580322361)
        ·
          refine ⟨5286658921314235935241771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7048878561752314580322361 5286658921314235935241771)
          ·
            refine ⟨7929988381971353902862657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5286658921314235935241771 7929988381971353902862657)
            ·
              refine ⟨5947491286478515427146993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7929988381971353902862657 5947491286478515427146993)
              ·
                refine ⟨4460618464858886570360245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5947491286478515427146993 4460618464858886570360245)
                ·
                  refine ⟨418182981080520615971273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4460618464858886570360245 418182981080520615971273)
                  ·
                    rfl

theorem cell21_1832419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 2, 5].length) (baseStart_1832419 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1832419 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1832419 prefixEnd_1832419 := by exact prefixLift 1832419
  have htrace : WordTrace (prefixWord ++ tailWord_1832419) baseStart_1832419 baseEnd_1832419 := by
    simpa [prefixWord, tailWord_1832419, baseEnd_1832419] using wordTrace_append hprefix tailTrace_1832419
  have hstable : (prefixWord ++ tailWord_1832419).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832419).length < 2 ^ (prefixWord ++ tailWord_1832419).sum := by decide
  have hdescent : baseEnd_1832419 < baseStart_1832419 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832433 : List Nat := [1, 2, 2, 2, 3, 2, 1, 2, 6]
def baseStart_1832433 : Nat := 118140960795 + 1832433 * 2 ^ 59
def prefixEnd_1832433 : Nat := 4983230072969 + 3 ^ 40 * 1832433 * 2
def baseEnd_1832433 : Nat := 418186176071259702737911

theorem tailTrace_1832433 : CollatzResearch.WordTrace tailWord_1832433 prefixEnd_1832433 418186176071259702737911 := by
  unfold tailWord_1832433
  simp only [CollatzResearch.WordTrace]
  refine ⟨66834322170415670485917953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44556214780277113657278635 66834322170415670485917953)
  ·
    refine ⟨50125741627811752864438465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66834322170415670485917953 50125741627811752864438465)
    ·
      refine ⟨37594306220858814648328849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50125741627811752864438465 37594306220858814648328849)
      ·
        refine ⟨28195729665644110986246637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37594306220858814648328849 28195729665644110986246637)
        ·
          refine ⟨10573398624616541619842489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28195729665644110986246637 10573398624616541619842489)
          ·
            refine ⟨7930048968462406214881867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10573398624616541619842489 7930048968462406214881867)
            ·
              refine ⟨11895073452693609322322801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7930048968462406214881867 11895073452693609322322801)
              ·
                refine ⟨8921305089520206991742101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11895073452693609322322801 8921305089520206991742101)
                ·
                  refine ⟨418186176071259702737911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8921305089520206991742101 418186176071259702737911)
                  ·
                    rfl

theorem cell21_1832433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 6].length) (baseStart_1832433 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1832433 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1832433 prefixEnd_1832433 := by exact prefixLift 1832433
  have htrace : WordTrace (prefixWord ++ tailWord_1832433) baseStart_1832433 baseEnd_1832433 := by
    simpa [prefixWord, tailWord_1832433, baseEnd_1832433] using wordTrace_append hprefix tailTrace_1832433
  have hstable : (prefixWord ++ tailWord_1832433).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832433).length < 2 ^ (prefixWord ++ tailWord_1832433).sum := by decide
  have hdescent : baseEnd_1832433 < baseStart_1832433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832467 : List Nat := [1, 1, 1, 2, 1, 8, 2, 1, 4]
def baseStart_1832467 : Nat := 118140960795 + 1832467 * 2 ^ 59
def prefixEnd_1832467 : Nat := 4983230072969 + 3 ^ 40 * 1832467 * 2
def baseEnd_1832467 : Nat := 418193935334483199171175

theorem tailTrace_1832467 : CollatzResearch.WordTrace tailWord_1832467 prefixEnd_1832467 418193935334483199171175 := by
  unfold tailWord_1832467
  simp only [CollatzResearch.WordTrace]
  refine ⟨66835562252292494292655655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44557041501528329528437103 66835562252292494292655655)
  ·
    refine ⟨100253343378438741438983483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66835562252292494292655655 100253343378438741438983483)
    ·
      refine ⟨150380015067658112158475225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100253343378438741438983483 150380015067658112158475225)
      ·
        refine ⟨112785011300743584118856419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150380015067658112158475225 112785011300743584118856419)
        ·
          refine ⟨169177516951115376178284629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112785011300743584118856419 169177516951115376178284629)
          ·
            refine ⟨1982549026770883314589273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 169177516951115376178284629 1982549026770883314589273)
            ·
              refine ⟨1486911770078162485941955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1982549026770883314589273 1486911770078162485941955)
              ·
                refine ⟨2230367655117243728912933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1486911770078162485941955 2230367655117243728912933)
                ·
                  refine ⟨418193935334483199171175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2230367655117243728912933 418193935334483199171175)
                  ·
                    rfl

theorem cell21_1832467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 2, 1, 4].length) (baseStart_1832467 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1832467 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1832467 prefixEnd_1832467 := by exact prefixLift 1832467
  have htrace : WordTrace (prefixWord ++ tailWord_1832467) baseStart_1832467 baseEnd_1832467 := by
    simpa [prefixWord, tailWord_1832467, baseEnd_1832467] using wordTrace_append hprefix tailTrace_1832467
  have hstable : (prefixWord ++ tailWord_1832467).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832467).length < 2 ^ (prefixWord ++ tailWord_1832467).sum := by decide
  have hdescent : baseEnd_1832467 < baseStart_1832467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832571 : List Nat := [1, 1, 1, 1, 1, 4, 3, 6, 3]
def baseStart_1832571 : Nat := 118140960795 + 1832571 * 2 ^ 59
def prefixEnd_1832571 : Nat := 4983230072969 + 3 ^ 40 * 1832571 * 2
def baseEnd_1832571 : Nat := 418217669551402129437629

theorem tailTrace_1832571 : CollatzResearch.WordTrace tailWord_1832571 prefixEnd_1832571 418217669551402129437629 := by
  unfold tailWord_1832571
  simp only [CollatzResearch.WordTrace]
  refine ⟨66839355443915720054441567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44559570295943813369627711 66839355443915720054441567)
  ·
    refine ⟨100259033165873580081662351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66839355443915720054441567 100259033165873580081662351)
    ·
      refine ⟨150388549748810370122493527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100259033165873580081662351 150388549748810370122493527)
      ·
        refine ⟨225582824623215555183740291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150388549748810370122493527 225582824623215555183740291)
        ·
          refine ⟨338374236934823332775610437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225582824623215555183740291 338374236934823332775610437)
          ·
            refine ⟨63445169425279374895426957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 338374236934823332775610437 63445169425279374895426957)
            ·
              refine ⟨23791938534479765585785109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63445169425279374895426957 23791938534479765585785109)
              ·
                refine ⟨1115247118803739011833677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23791938534479765585785109 1115247118803739011833677)
                ·
                  refine ⟨418217669551402129437629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1115247118803739011833677 418217669551402129437629)
                  ·
                    rfl

theorem cell21_1832571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 6, 3].length) (baseStart_1832571 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1832571 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1832571 prefixEnd_1832571 := by exact prefixLift 1832571
  have htrace : WordTrace (prefixWord ++ tailWord_1832571) baseStart_1832571 baseEnd_1832571 := by
    simpa [prefixWord, tailWord_1832571, baseEnd_1832571] using wordTrace_append hprefix tailTrace_1832571
  have hstable : (prefixWord ++ tailWord_1832571).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832571).length < 2 ^ (prefixWord ++ tailWord_1832571).sum := by decide
  have hdescent : baseEnd_1832571 < baseStart_1832571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832585 : List Nat := [1, 2, 1, 1, 4, 1, 2, 5, 4]
def baseStart_1832585 : Nat := 118140960795 + 1832585 * 2 ^ 59
def prefixEnd_1832585 : Nat := 4983230072969 + 3 ^ 40 * 1832585 * 2
def baseEnd_1832585 : Nat := 418220864542141216204267

theorem tailTrace_1832585 : CollatzResearch.WordTrace tailWord_1832585 prefixEnd_1832585 418220864542141216204267 := by
  unfold tailWord_1832585
  simp only [CollatzResearch.WordTrace]
  refine ⟨66839866065865000445451209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44559910710576666963634139 66839866065865000445451209)
  ·
    refine ⟨50129899549398750334088407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66839866065865000445451209 50129899549398750334088407)
    ·
      refine ⟨75194849324098125501132611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50129899549398750334088407 75194849324098125501132611)
      ·
        refine ⟨112792273986147188251698917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75194849324098125501132611 112792273986147188251698917)
        ·
          refine ⟨21148551372402597797193547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112792273986147188251698917 21148551372402597797193547)
          ·
            refine ⟨31722827058603896695790321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21148551372402597797193547 31722827058603896695790321)
            ·
              refine ⟨23792120293952922521842741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31722827058603896695790321 23792120293952922521842741)
              ·
                refine ⟨2230511277558086486422757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23792120293952922521842741 2230511277558086486422757)
                ·
                  refine ⟨418220864542141216204267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2230511277558086486422757 418220864542141216204267)
                  ·
                    rfl

theorem cell21_1832585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 5, 4].length) (baseStart_1832585 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1832585 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1832585 prefixEnd_1832585 := by exact prefixLift 1832585
  have htrace : WordTrace (prefixWord ++ tailWord_1832585) baseStart_1832585 baseEnd_1832585 := by
    simpa [prefixWord, tailWord_1832585, baseEnd_1832585] using wordTrace_append hprefix tailTrace_1832585
  have hstable : (prefixWord ++ tailWord_1832585).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832585).length < 2 ^ (prefixWord ++ tailWord_1832585).sum := by decide
  have hdescent : baseEnd_1832585 < baseStart_1832585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832622 : List Nat := [4, 1, 4, 1, 3, 1, 1, 1, 5]
def baseStart_1832622 : Nat := 118140960795 + 1832622 * 2 ^ 59
def prefixEnd_1832622 : Nat := 4983230072969 + 3 ^ 40 * 1832622 * 2
def baseEnd_1832622 : Nat := 418229308446237374087525

theorem tailTrace_1832622 : CollatzResearch.WordTrace tailWord_1832622 prefixEnd_1832622 418229308446237374087525 := by
  unfold tailWord_1832622
  simp only [CollatzResearch.WordTrace]
  refine ⟨8355151945841369470568515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44560810377820637176365413 8355151945841369470568515)
  ·
    refine ⟨12532727918762054205852773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8355151945841369470568515 12532727918762054205852773)
    ·
      refine ⟨2349886484767885163597395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12532727918762054205852773 2349886484767885163597395)
      ·
        refine ⟨3524829727151827745396093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2349886484767885163597395 3524829727151827745396093)
        ·
          refine ⟨1321811147681935404523535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3524829727151827745396093 1321811147681935404523535)
          ·
            refine ⟨1982716721522903106785303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1321811147681935404523535 1982716721522903106785303)
            ·
              refine ⟨2974075082284354660177955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1982716721522903106785303 2974075082284354660177955)
              ·
                refine ⟨4461112623426531990266933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2974075082284354660177955 4461112623426531990266933)
                ·
                  refine ⟨418229308446237374087525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4461112623426531990266933 418229308446237374087525)
                  ·
                    rfl

theorem cell21_1832622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 1, 5].length) (baseStart_1832622 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1832622 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1832622 prefixEnd_1832622 := by exact prefixLift 1832622
  have htrace : WordTrace (prefixWord ++ tailWord_1832622) baseStart_1832622 baseEnd_1832622 := by
    simpa [prefixWord, tailWord_1832622, baseEnd_1832622] using wordTrace_append hprefix tailTrace_1832622
  have hstable : (prefixWord ++ tailWord_1832622).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832622).length < 2 ^ (prefixWord ++ tailWord_1832622).sum := by decide
  have hdescent : baseEnd_1832622 < baseStart_1832622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832675 : List Nat := [1, 1, 1, 7, 11]
def baseStart_1832675 : Nat := 118140960795 + 1832675 * 2 ^ 59
def prefixEnd_1832675 : Nat := 4983230072969 + 3 ^ 40 * 1832675 * 2
def baseEnd_1832675 : Nat := 5163474120596556292643

theorem tailTrace_1832675 : CollatzResearch.WordTrace tailWord_1832675 prefixEnd_1832675 5163474120596556292643 := by
  unfold tailWord_1832675
  simp only [CollatzResearch.WordTrace]
  refine ⟨66843148635538945816227479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44562099090359297210818319 66843148635538945816227479)
  ·
    refine ⟨100264722953308418724341219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66843148635538945816227479 100264722953308418724341219)
    ·
      refine ⟨150397084429962628086511829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100264722953308418724341219 150397084429962628086511829)
      ·
        refine ⟨3524931666327249095777621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 150397084429962628086511829 3524931666327249095777621)
        ·
          refine ⟨5163474120596556292643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3524931666327249095777621 5163474120596556292643)
          ·
            rfl

theorem cell21_1832675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 11].length) (baseStart_1832675 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1832675 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1832675 prefixEnd_1832675 := by exact prefixLift 1832675
  have htrace : WordTrace (prefixWord ++ tailWord_1832675) baseStart_1832675 baseEnd_1832675 := by
    simpa [prefixWord, tailWord_1832675, baseEnd_1832675] using wordTrace_append hprefix tailTrace_1832675
  have hstable : (prefixWord ++ tailWord_1832675).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832675).length < 2 ^ (prefixWord ++ tailWord_1832675).sum := by decide
  have hdescent : baseEnd_1832675 < baseStart_1832675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832737 : List Nat := [1, 2, 3, 2, 1, 4, 1, 1, 6]
def baseStart_1832737 : Nat := 118140960795 + 1832737 * 2 ^ 59
def prefixEnd_1832737 : Nat := 4983230072969 + 3 ^ 40 * 1832737 * 2
def baseEnd_1832737 : Nat := 418255553013022729670623

theorem tailTrace_1832737 : CollatzResearch.WordTrace tailWord_1832737 prefixEnd_1832737 418255553013022729670623 := by
  unfold tailWord_1832737
  simp only [CollatzResearch.WordTrace]
  refine ⟨66845409961314330404984465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44563606640876220269989643 66845409961314330404984465)
  ·
    refine ⟨50134057470985747803738349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66845409961314330404984465 50134057470985747803738349)
    ·
      refine ⟨18800271551619655426401881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50134057470985747803738349 18800271551619655426401881)
      ·
        refine ⟨14100203663714741569801411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18800271551619655426401881 14100203663714741569801411)
        ·
          refine ⟨21150305495572112354702117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14100203663714741569801411 21150305495572112354702117)
          ·
            refine ⟨3965682280419771066506647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21150305495572112354702117 3965682280419771066506647)
            ·
              refine ⟨5948523420629656599759971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3965682280419771066506647 5948523420629656599759971)
              ·
                refine ⟨8922785130944484899639957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5948523420629656599759971 8922785130944484899639957)
                ·
                  refine ⟨418255553013022729670623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8922785130944484899639957 418255553013022729670623)
                  ·
                    rfl

theorem cell21_1832737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 6].length) (baseStart_1832737 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1832737 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1832737 prefixEnd_1832737 := by exact prefixLift 1832737
  have htrace : WordTrace (prefixWord ++ tailWord_1832737) baseStart_1832737 baseEnd_1832737 := by
    simpa [prefixWord, tailWord_1832737, baseEnd_1832737] using wordTrace_append hprefix tailTrace_1832737
  have hstable : (prefixWord ++ tailWord_1832737).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832737).length < 2 ^ (prefixWord ++ tailWord_1832737).sum := by decide
  have hdescent : baseEnd_1832737 < baseStart_1832737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832740 : List Nat := [2, 3, 1, 3, 2, 1, 2, 4, 3]
def baseStart_1832740 : Nat := 118140960795 + 1832740 * 2 ^ 59
def prefixEnd_1832740 : Nat := 4983230072969 + 3 ^ 40 * 1832740 * 2
def baseEnd_1832740 : Nat := 418256237653895391120617

theorem tailTrace_1832740 : CollatzResearch.WordTrace tailWord_1832740 prefixEnd_1832740 418256237653895391120617 := by
  unfold tailWord_1832740
  simp only [CollatzResearch.WordTrace]
  refine ⟨33422759690151730958671837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44563679586868974611562449 33422759690151730958671837)
  ·
    refine ⟨12533534883806899109501939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33422759690151730958671837 12533534883806899109501939)
    ·
      refine ⟨18800302325710348664252909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12533534883806899109501939 18800302325710348664252909)
      ·
        refine ⟨7050113372141380749094841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18800302325710348664252909 7050113372141380749094841)
        ·
          refine ⟨5287585029106035561821131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7050113372141380749094841 5287585029106035561821131)
          ·
            refine ⟨7931377543659053342731697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5287585029106035561821131 7931377543659053342731697)
            ·
              refine ⟨5948533157744290007048773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7931377543659053342731697 5948533157744290007048773)
              ·
                refine ⟨1115349967077054376321645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5948533157744290007048773 1115349967077054376321645)
                ·
                  refine ⟨418256237653895391120617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1115349967077054376321645 418256237653895391120617)
                  ·
                    rfl

theorem cell21_1832740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 4, 3].length) (baseStart_1832740 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1832740 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1832740 prefixEnd_1832740 := by exact prefixLift 1832740
  have htrace : WordTrace (prefixWord ++ tailWord_1832740) baseStart_1832740 baseEnd_1832740 := by
    simpa [prefixWord, tailWord_1832740, baseEnd_1832740] using wordTrace_append hprefix tailTrace_1832740
  have hstable : (prefixWord ++ tailWord_1832740).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832740).length < 2 ^ (prefixWord ++ tailWord_1832740).sum := by decide
  have hdescent : baseEnd_1832740 < baseStart_1832740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832774 : List Nat := [6, 1, 1, 2, 1, 1, 3, 3, 3]
def baseStart_1832774 : Nat := 118140960795 + 1832774 * 2 ^ 59
def prefixEnd_1832774 : Nat := 4983230072969 + 3 ^ 40 * 1832774 * 2
def baseEnd_1832774 : Nat := 418263996917118887553881

theorem tailTrace_1832774 : CollatzResearch.WordTrace tailWord_1832774 prefixEnd_1832774 418263996917118887553881 := by
  unfold tailWord_1832774
  simp only [CollatzResearch.WordTrace]
  refine ⟨2088961233193133928877543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 44564506308120190482720917 2088961233193133928877543)
  ·
    refine ⟨3133441849789700893316315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2088961233193133928877543 3133441849789700893316315)
    ·
      refine ⟨4700162774684551339974473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3133441849789700893316315 4700162774684551339974473)
      ·
        refine ⟨3525122081013413504980855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4700162774684551339974473 3525122081013413504980855)
        ·
          refine ⟨5287683121520120257471283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3525122081013413504980855 5287683121520120257471283)
          ·
            refine ⟨7931524682280180386206925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5287683121520120257471283 7931524682280180386206925)
            ·
              refine ⟨2974321755855067644827597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7931524682280180386206925 2974321755855067644827597)
              ·
                refine ⟨1115370658445650366810349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2974321755855067644827597 1115370658445650366810349)
                ·
                  refine ⟨418263996917118887553881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1115370658445650366810349 418263996917118887553881)
                  ·
                    rfl

theorem cell21_1832774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_1832774 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1832774 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1832774 prefixEnd_1832774 := by exact prefixLift 1832774
  have htrace : WordTrace (prefixWord ++ tailWord_1832774) baseStart_1832774 baseEnd_1832774 := by
    simpa [prefixWord, tailWord_1832774, baseEnd_1832774] using wordTrace_append hprefix tailTrace_1832774
  have hstable : (prefixWord ++ tailWord_1832774).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832774).length < 2 ^ (prefixWord ++ tailWord_1832774).sum := by decide
  have hdescent : baseEnd_1832774 < baseStart_1832774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832799 : List Nat := [1, 1, 2, 3, 1, 6, 1, 1, 5]
def baseStart_1832799 : Nat := 118140960795 + 1832799 * 2 ^ 59
def prefixEnd_1832799 : Nat := 4983230072969 + 3 ^ 40 * 1832799 * 2
def baseEnd_1832799 : Nat := 418269702257724399637163

theorem tailTrace_1832799 : CollatzResearch.WordTrace tailWord_1832799 prefixEnd_1832799 418269702257724399637163 := by
  unfold tailWord_1832799
  simp only [CollatzResearch.WordTrace]
  refine ⟨66847671287089714993741451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44565114191393143329160967 66847671287089714993741451)
  ·
    refine ⟨100271506930634572490612177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66847671287089714993741451 100271506930634572490612177)
    ·
      refine ⟨75203630197975929367959133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100271506930634572490612177 75203630197975929367959133)
      ·
        refine ⟨28201361324240973512984675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75203630197975929367959133 28201361324240973512984675)
        ·
          refine ⟨42302041986361460269477013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28201361324240973512984675 42302041986361460269477013)
          ·
            refine ⟨1982908218110693450131735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 42302041986361460269477013 1982908218110693450131735)
            ·
              refine ⟨2974362327166040175197603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1982908218110693450131735 2974362327166040175197603)
              ·
                refine ⟨4461543490749060262796405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2974362327166040175197603 4461543490749060262796405)
                ·
                  refine ⟨418269702257724399637163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4461543490749060262796405 418269702257724399637163)
                  ·
                    rfl

theorem cell21_1832799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 1, 5].length) (baseStart_1832799 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1832799 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1832799 prefixEnd_1832799 := by exact prefixLift 1832799
  have htrace : WordTrace (prefixWord ++ tailWord_1832799) baseStart_1832799 baseEnd_1832799 := by
    simpa [prefixWord, tailWord_1832799, baseEnd_1832799] using wordTrace_append hprefix tailTrace_1832799
  have hstable : (prefixWord ++ tailWord_1832799).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832799).length < 2 ^ (prefixWord ++ tailWord_1832799).sum := by decide
  have hdescent : baseEnd_1832799 < baseStart_1832799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832850 : List Nat := [3, 2, 3, 2, 1, 3, 2, 2, 3]
def baseStart_1832850 : Nat := 118140960795 + 1832850 * 2 ^ 59
def prefixEnd_1832850 : Nat := 4983230072969 + 3 ^ 40 * 1832850 * 2
def baseEnd_1832850 : Nat := 418281341152559644287059

theorem tailTrace_1832850 : CollatzResearch.WordTrace tailWord_1832850 prefixEnd_1832850 418281341152559644287059 := by
  unfold tailWord_1832850
  simp only [CollatzResearch.WordTrace]
  refine ⟨16712382852476237675962001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44566354273269967135898669 16712382852476237675962001)
  ·
    refine ⟨12534287139357178256971501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16712382852476237675962001 12534287139357178256971501)
    ·
      refine ⟨4700357677258941846364313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12534287139357178256971501 4700357677258941846364313)
      ·
        refine ⟨3525268257944206384773235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4700357677258941846364313 3525268257944206384773235)
        ·
          refine ⟨5287902386916309577159853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3525268257944206384773235 5287902386916309577159853)
          ·
            refine ⟨1982963395093616091434945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5287902386916309577159853 1982963395093616091434945)
            ·
              refine ⟨1487222546320212068576209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1982963395093616091434945 1487222546320212068576209)
              ·
                refine ⟨1115416909740159051432157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1487222546320212068576209 1115416909740159051432157)
                ·
                  refine ⟨418281341152559644287059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1115416909740159051432157 418281341152559644287059)
                  ·
                    rfl

theorem cell21_1832850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 2, 2, 3].length) (baseStart_1832850 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1832850 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1832850 prefixEnd_1832850 := by exact prefixLift 1832850
  have htrace : WordTrace (prefixWord ++ tailWord_1832850) baseStart_1832850 baseEnd_1832850 := by
    simpa [prefixWord, tailWord_1832850, baseEnd_1832850] using wordTrace_append hprefix tailTrace_1832850
  have hstable : (prefixWord ++ tailWord_1832850).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832850).length < 2 ^ (prefixWord ++ tailWord_1832850).sum := by decide
  have hdescent : baseEnd_1832850 < baseStart_1832850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1832968 : List Nat := [2, 1, 3, 2, 1, 2, 5, 2, 3]
def baseStart_1832968 : Nat := 118140960795 + 1832968 * 2 ^ 59
def prefixEnd_1832968 : Nat := 4983230072969 + 3 ^ 40 * 1832968 * 2
def baseEnd_1832968 : Nat := 418308270360217661320151

theorem tailTrace_1832968 : CollatzResearch.WordTrace tailWord_1832968 prefixEnd_1832968 418308270360217661320151 := by
  unfold tailWord_1832968
  simp only [CollatzResearch.WordTrace]
  refine ⟨33426917611738728428321779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44569223482318304571095705 33426917611738728428321779)
  ·
    refine ⟨50140376417608092642482669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33426917611738728428321779 50140376417608092642482669)
    ·
      refine ⟨18802641156603034740931001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50140376417608092642482669 18802641156603034740931001)
      ·
        refine ⟨14101980867452276055698251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18802641156603034740931001 14101980867452276055698251)
        ·
          refine ⟨21152971301178414083547377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14101980867452276055698251 21152971301178414083547377)
          ·
            refine ⟨15864728475883810562660533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21152971301178414083547377 15864728475883810562660533)
            ·
              refine ⟨1487318294614107240249425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15864728475883810562660533 1487318294614107240249425)
              ·
                refine ⟨1115488720960580430187069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1487318294614107240249425 1115488720960580430187069)
                ·
                  refine ⟨418308270360217661320151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1115488720960580430187069 418308270360217661320151)
                  ·
                    rfl

theorem cell21_1832968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 5, 2, 3].length) (baseStart_1832968 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1832968 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1832968 prefixEnd_1832968 := by exact prefixLift 1832968
  have htrace : WordTrace (prefixWord ++ tailWord_1832968) baseStart_1832968 baseEnd_1832968 := by
    simpa [prefixWord, tailWord_1832968, baseEnd_1832968] using wordTrace_append hprefix tailTrace_1832968
  have hstable : (prefixWord ++ tailWord_1832968).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1832968).length < 2 ^ (prefixWord ++ tailWord_1832968).sum := by decide
  have hdescent : baseEnd_1832968 < baseStart_1832968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1832968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833120 : List Nat := [2, 1, 1, 4, 2, 4, 1, 3, 3]
def baseStart_1833120 : Nat := 118140960795 + 1833120 * 2 ^ 59
def prefixEnd_1833120 : Nat := 4983230072969 + 3 ^ 40 * 1833120 * 2
def baseEnd_1833120 : Nat := 418342958831099174786507

theorem tailTrace_1833120 : CollatzResearch.WordTrace tailWord_1833120 prefixEnd_1833120 418342958831099174786507 := by
  unfold tailWord_1833120
  simp only [CollatzResearch.WordTrace]
  refine ⟨33429689559463393408088407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44572919412617857877451209 33429689559463393408088407)
  ·
    refine ⟨50144534339195090112132611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33429689559463393408088407 50144534339195090112132611)
    ·
      refine ⟨75216801508792635168198917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50144534339195090112132611 75216801508792635168198917)
      ·
        refine ⟨14103150282898619094037297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75216801508792635168198917 14103150282898619094037297)
        ·
          refine ⟨10577362712173964320527973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14103150282898619094037297 10577362712173964320527973)
          ·
            refine ⟨1983255508532618310098995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10577362712173964320527973 1983255508532618310098995)
            ·
              refine ⟨2974883262798927465148493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1983255508532618310098995 2974883262798927465148493)
              ·
                refine ⟨1115581223549597799430685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2974883262798927465148493 1115581223549597799430685)
                ·
                  refine ⟨418342958831099174786507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1115581223549597799430685 418342958831099174786507)
                  ·
                    rfl

theorem cell21_1833120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 3, 3].length) (baseStart_1833120 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1833120 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1833120 prefixEnd_1833120 := by exact prefixLift 1833120
  have htrace : WordTrace (prefixWord ++ tailWord_1833120) baseStart_1833120 baseEnd_1833120 := by
    simpa [prefixWord, tailWord_1833120, baseEnd_1833120] using wordTrace_append hprefix tailTrace_1833120
  have hstable : (prefixWord ++ tailWord_1833120).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833120).length < 2 ^ (prefixWord ++ tailWord_1833120).sum := by decide
  have hdescent : baseEnd_1833120 < baseStart_1833120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833137 : List Nat := [1, 2, 2, 5, 2, 1, 3, 2, 3]
def baseStart_1833137 : Nat := 118140960795 + 1833137 * 2 ^ 59
def prefixEnd_1833137 : Nat := 4983230072969 + 3 ^ 40 * 1833137 * 2
def baseEnd_1833137 : Nat := 418346838462710923003139

theorem tailTrace_1833137 : CollatzResearch.WordTrace tailWord_1833137 prefixEnd_1833137 418346838462710923003139 := by
  unfold tailWord_1833137
  simp only [CollatzResearch.WordTrace]
  refine ⟨66859999159865198719545665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44573332773243465813030443 66859999159865198719545665)
  ·
    refine ⟨50144999369898899039659249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66859999159865198719545665 50144999369898899039659249)
    ·
      refine ⟨37608749527424174279744437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50144999369898899039659249 37608749527424174279744437)
      ·
        refine ⟨3525820268196016338726041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37608749527424174279744437 3525820268196016338726041)
        ·
          refine ⟨2644365201147012254044531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3525820268196016338726041 2644365201147012254044531)
          ·
            refine ⟨3966547801720518381066797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2644365201147012254044531 3966547801720518381066797)
            ·
              refine ⟨1487455425645194392900049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3966547801720518381066797 1487455425645194392900049)
              ·
                refine ⟨1115591569233895794675037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1487455425645194392900049 1115591569233895794675037)
                ·
                  refine ⟨418346838462710923003139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1115591569233895794675037 418346838462710923003139)
                  ·
                    rfl

theorem cell21_1833137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 3, 2, 3].length) (baseStart_1833137 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1833137 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1833137 prefixEnd_1833137 := by exact prefixLift 1833137
  have htrace : WordTrace (prefixWord ++ tailWord_1833137) baseStart_1833137 baseEnd_1833137 := by
    simpa [prefixWord, tailWord_1833137, baseEnd_1833137] using wordTrace_append hprefix tailTrace_1833137
  have hstable : (prefixWord ++ tailWord_1833137).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833137).length < 2 ^ (prefixWord ++ tailWord_1833137).sum := by decide
  have hdescent : baseEnd_1833137 < baseStart_1833137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833148 : List Nat := [2, 2, 2, 3, 3, 1, 2, 6]
def baseStart_1833148 : Nat := 118140960795 + 1833148 * 2 ^ 59
def prefixEnd_1833148 : Nat := 4983230072969 + 3 ^ 40 * 1833148 * 2
def baseEnd_1833148 : Nat := 139449782937525782773261

theorem tailTrace_1833148 : CollatzResearch.WordTrace tailWord_1833148 prefixEnd_1833148 139449782937525782773261 := by
  unfold tailWord_1833148
  simp only [CollatzResearch.WordTrace]
  refine ⟨33430200181412673799098049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44573600241883565065464065 33430200181412673799098049)
  ·
    refine ⟨25072650136059505349323537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33430200181412673799098049 25072650136059505349323537)
    ·
      refine ⟨18804487602044629011992653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25072650136059505349323537 18804487602044629011992653)
      ·
        refine ⟨7051682850766735879497245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18804487602044629011992653 7051682850766735879497245)
        ·
          refine ⟨2644381069037525954811467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7051682850766735879497245 2644381069037525954811467)
          ·
            refine ⟨3966571603556288932217201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2644381069037525954811467 3966571603556288932217201)
            ·
              refine ⟨2974928702667216699162901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3966571603556288932217201 2974928702667216699162901)
              ·
                refine ⟨139449782937525782773261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2974928702667216699162901 139449782937525782773261)
                ·
                  rfl

theorem cell21_1833148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 6].length) (baseStart_1833148 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1833148 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1833148 prefixEnd_1833148 := by exact prefixLift 1833148
  have htrace : WordTrace (prefixWord ++ tailWord_1833148) baseStart_1833148 baseEnd_1833148 := by
    simpa [prefixWord, tailWord_1833148, baseEnd_1833148] using wordTrace_append hprefix tailTrace_1833148
  have hstable : (prefixWord ++ tailWord_1833148).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833148).length < 2 ^ (prefixWord ++ tailWord_1833148).sum := by decide
  have hdescent : baseEnd_1833148 < baseStart_1833148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833224 : List Nat := [2, 1, 3, 2, 3, 2, 3, 5]
def baseStart_1833224 : Nat := 118140960795 + 1833224 * 2 ^ 59
def prefixEnd_1833224 : Nat := 4983230072969 + 3 ^ 40 * 1833224 * 2
def baseEnd_1833224 : Nat := 139455564349339368350987

theorem tailTrace_1833224 : CollatzResearch.WordTrace tailWord_1833224 prefixEnd_1833224 139455564349339368350987 := by
  unfold tailWord_1833224
  simp only [CollatzResearch.WordTrace]
  refine ⟨33431586155275006288981363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44575448207033341718641817 33431586155275006288981363)
  ·
    refine ⟨50147379232912509433472045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33431586155275006288981363 50147379232912509433472045)
    ·
      refine ⟨18805267212342191037552017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50147379232912509433472045 18805267212342191037552017)
      ·
        refine ⟨14103950409256643278164013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18805267212342191037552017 14103950409256643278164013)
        ·
          refine ⟨5288981403471241229311505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14103950409256643278164013 5288981403471241229311505)
          ·
            refine ⟨3966736052603430921983629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5288981403471241229311505 3966736052603430921983629)
            ·
              refine ⟨1487526019726286595743861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3966736052603430921983629 1487526019726286595743861)
              ·
                refine ⟨139455564349339368350987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1487526019726286595743861 139455564349339368350987)
                ·
                  rfl

theorem cell21_1833224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 3, 5].length) (baseStart_1833224 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1833224 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1833224 prefixEnd_1833224 := by exact prefixLift 1833224
  have htrace : WordTrace (prefixWord ++ tailWord_1833224) baseStart_1833224 baseEnd_1833224 := by
    simpa [prefixWord, tailWord_1833224, baseEnd_1833224] using wordTrace_append hprefix tailTrace_1833224
  have hstable : (prefixWord ++ tailWord_1833224).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833224).length < 2 ^ (prefixWord ++ tailWord_1833224).sum := by decide
  have hdescent : baseEnd_1833224 < baseStart_1833224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833283 : List Nat := [1, 1, 1, 3, 1, 3, 6, 5]
def baseStart_1833283 : Nat := 118140960795 + 1833283 * 2 ^ 59
def prefixEnd_1833283 : Nat := 4983230072969 + 3 ^ 40 * 1833283 * 2
def baseEnd_1833283 : Nat := 139460052550615704523169

theorem tailTrace_1833283 : CollatzResearch.WordTrace tailWord_1833283 prefixEnd_1833283 139460052550615704523169 := by
  unfold tailWord_1833283
  simp only [CollatzResearch.WordTrace]
  refine ⟨66865324217336265654360503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44576882811557510436240335 66865324217336265654360503)
  ·
    refine ⟨100297986326004398481540755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66865324217336265654360503 100297986326004398481540755)
    ·
      refine ⟨150446979489006597722311133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100297986326004398481540755 150446979489006597722311133)
      ·
        refine ⟨56417617308377474145866675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150446979489006597722311133 56417617308377474145866675)
        ·
          refine ⟨84626425962566211218800013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56417617308377474145866675 84626425962566211218800013)
          ·
            refine ⟨31734909735962329207050005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84626425962566211218800013 31734909735962329207050005)
            ·
              refine ⟨1487573893873234181580469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 31734909735962329207050005 1487573893873234181580469)
              ·
                refine ⟨139460052550615704523169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1487573893873234181580469 139460052550615704523169)
                ·
                  rfl

theorem cell21_1833283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 6, 5].length) (baseStart_1833283 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1833283 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1833283 prefixEnd_1833283 := by exact prefixLift 1833283
  have htrace : WordTrace (prefixWord ++ tailWord_1833283) baseStart_1833283 baseEnd_1833283 := by
    simpa [prefixWord, tailWord_1833283, baseEnd_1833283] using wordTrace_append hprefix tailTrace_1833283
  have hstable : (prefixWord ++ tailWord_1833283).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833283).length < 2 ^ (prefixWord ++ tailWord_1833283).sum := by decide
  have hdescent : baseEnd_1833283 < baseStart_1833283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833418 : List Nat := [3, 1, 2, 1, 2, 2, 10]
def baseStart_1833418 : Nat := 118140960795 + 1833418 * 2 ^ 59
def prefixEnd_1833418 : Nat := 4983230072969 + 3 ^ 40 * 1833418 * 2
def baseEnd_1833418 : Nat := 46490107387901875424359

theorem tailTrace_1833418 : CollatzResearch.WordTrace tailWord_1833418 prefixEnd_1833418 46490107387901875424359 := by
  unfold tailWord_1833418
  simp only [CollatzResearch.WordTrace]
  refine ⟨16717562017961795927631227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44580165381231455807016605 16717562017961795927631227)
  ·
    refine ⟨25076343026942693891446841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16717562017961795927631227 25076343026942693891446841)
    ·
      refine ⟨18807257270207020418585131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25076343026942693891446841 18807257270207020418585131)
      ·
        refine ⟨28210885905310530627877697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18807257270207020418585131 28210885905310530627877697)
        ·
          refine ⟨21158164428982897970908273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28210885905310530627877697 21158164428982897970908273)
          ·
            refine ⟨15868623321737173478181205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21158164428982897970908273 15868623321737173478181205)
            ·
              refine ⟨46490107387901875424359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15868623321737173478181205 46490107387901875424359)
              ·
                rfl

theorem cell21_1833418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 10].length) (baseStart_1833418 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1833418 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1833418 prefixEnd_1833418 := by exact prefixLift 1833418
  have htrace : WordTrace (prefixWord ++ tailWord_1833418) baseStart_1833418 baseEnd_1833418 := by
    simpa [prefixWord, tailWord_1833418, baseEnd_1833418] using wordTrace_append hprefix tailTrace_1833418
  have hstable : (prefixWord ++ tailWord_1833418).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833418).length < 2 ^ (prefixWord ++ tailWord_1833418).sum := by decide
  have hdescent : baseEnd_1833418 < baseStart_1833418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833466 : List Nat := [3, 1, 1, 1, 1, 2, 2, 7, 3]
def baseStart_1833466 : Nat := 118140960795 + 1833466 * 2 ^ 59
def prefixEnd_1833466 : Nat := 4983230072969 + 3 ^ 40 * 1833466 * 2
def baseEnd_1833466 : Nat := 418421920745079462019133

theorem tailTrace_1833466 : CollatzResearch.WordTrace tailWord_1833466 prefixEnd_1833466 418421920745079462019133 := by
  unfold tailWord_1833466
  simp only [CollatzResearch.WordTrace]
  refine ⟨16717999693918321977068063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44581332517115525272181501 16717999693918321977068063)
  ·
    refine ⟨25076999540877482965602095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16717999693918321977068063 25076999540877482965602095)
    ·
      refine ⟨37615499311316224448403143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25076999540877482965602095 37615499311316224448403143)
      ·
        refine ⟨56423248966974336672604715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37615499311316224448403143 56423248966974336672604715)
        ·
          refine ⟨84634873450461505008907073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56423248966974336672604715 84634873450461505008907073)
          ·
            refine ⟨63476155087846128756680305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84634873450461505008907073 63476155087846128756680305)
            ·
              refine ⟨47607116315884596567510229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63476155087846128756680305 47607116315884596567510229)
              ·
                refine ⟨1115791788653545232051021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 47607116315884596567510229 1115791788653545232051021)
                ·
                  refine ⟨418421920745079462019133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1115791788653545232051021 418421920745079462019133)
                  ·
                    rfl

theorem cell21_1833466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 7, 3].length) (baseStart_1833466 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1833466 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1833466 prefixEnd_1833466 := by exact prefixLift 1833466
  have htrace : WordTrace (prefixWord ++ tailWord_1833466) baseStart_1833466 baseEnd_1833466 := by
    simpa [prefixWord, tailWord_1833466, baseEnd_1833466] using wordTrace_append hprefix tailTrace_1833466
  have hstable : (prefixWord ++ tailWord_1833466).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833466).length < 2 ^ (prefixWord ++ tailWord_1833466).sum := by decide
  have hdescent : baseEnd_1833466 < baseStart_1833466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833480 : List Nat := [2, 1, 3, 2, 1, 1, 1, 6, 4]
def baseStart_1833480 : Nat := 118140960795 + 1833480 * 2 ^ 59
def prefixEnd_1833480 : Nat := 4983230072969 + 3 ^ 40 * 1833480 * 2
def baseEnd_1833480 : Nat := 418425115735818548785771

theorem tailTrace_1833480 : CollatzResearch.WordTrace tailWord_1833480 prefixEnd_1833480 418425115735818548785771 := by
  unfold tailWord_1833480
  simp only [CollatzResearch.WordTrace]
  refine ⟨33436254698811284149640947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44581672931748378866187929 33436254698811284149640947)
  ·
    refine ⟨50154382048216926224461421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33436254698811284149640947 50154382048216926224461421)
    ·
      refine ⟨18807893268081347334173033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50154382048216926224461421 18807893268081347334173033)
      ·
        refine ⟨14105919951061010500629775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18807893268081347334173033 14105919951061010500629775)
        ·
          refine ⟨21158879926591515750944663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14105919951061010500629775 21158879926591515750944663)
          ·
            refine ⟨31738319889887273626416995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21158879926591515750944663 31738319889887273626416995)
            ·
              refine ⟨47607479834830910439625493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31738319889887273626416995 47607479834830910439625493)
              ·
                refine ⟨2231600617257698926857445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 47607479834830910439625493 2231600617257698926857445)
                ·
                  refine ⟨418425115735818548785771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2231600617257698926857445 418425115735818548785771)
                  ·
                    rfl

theorem cell21_1833480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 6, 4].length) (baseStart_1833480 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1833480 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1833480 prefixEnd_1833480 := by exact prefixLift 1833480
  have htrace : WordTrace (prefixWord ++ tailWord_1833480) baseStart_1833480 baseEnd_1833480 := by
    simpa [prefixWord, tailWord_1833480, baseEnd_1833480] using wordTrace_append hprefix tailTrace_1833480
  have hstable : (prefixWord ++ tailWord_1833480).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833480).length < 2 ^ (prefixWord ++ tailWord_1833480).sum := by decide
  have hdescent : baseEnd_1833480 < baseStart_1833480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833534 : List Nat := [4, 2, 1, 4, 1, 2, 2, 2, 3]
def baseStart_1833534 : Nat := 118140960795 + 1833534 * 2 ^ 59
def prefixEnd_1833534 : Nat := 4983230072969 + 3 ^ 40 * 1833534 * 2
def baseEnd_1833534 : Nat := 418437439271526454885661

theorem tailTrace_1833534 : CollatzResearch.WordTrace tailWord_1833534 prefixEnd_1833534 418437439271526454885661 := by
  unfold tailWord_1833534
  simp only [CollatzResearch.WordTrace]
  refine ⟨8359309867428366940218457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44582985959617957014498437 8359309867428366940218457)
  ·
    refine ⟨6269482400571275205163843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8359309867428366940218457 6269482400571275205163843)
    ·
      refine ⟨9404223600856912807745765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6269482400571275205163843 9404223600856912807745765)
      ·
        refine ⟨1763291925160671151452331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9404223600856912807745765 1763291925160671151452331)
        ·
          refine ⟨2644937887741006727178497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1763291925160671151452331 2644937887741006727178497)
          ·
            refine ⟨1983703415805755045383873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2644937887741006727178497 1983703415805755045383873)
            ·
              refine ⟨1487777561854316284037905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1983703415805755045383873 1487777561854316284037905)
              ·
                refine ⟨1115833171390737213028429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1487777561854316284037905 1115833171390737213028429)
                ·
                  refine ⟨418437439271526454885661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1115833171390737213028429 418437439271526454885661)
                  ·
                    rfl

theorem cell21_1833534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 2, 2, 3].length) (baseStart_1833534 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1833534 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1833534 prefixEnd_1833534 := by exact prefixLift 1833534
  have htrace : WordTrace (prefixWord ++ tailWord_1833534) baseStart_1833534 baseEnd_1833534 := by
    simpa [prefixWord, tailWord_1833534, baseEnd_1833534] using wordTrace_append hprefix tailTrace_1833534
  have hstable : (prefixWord ++ tailWord_1833534).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833534).length < 2 ^ (prefixWord ++ tailWord_1833534).sum := by decide
  have hdescent : baseEnd_1833534 < baseStart_1833534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833539 : List Nat := [1, 1, 1, 3, 1, 2, 1, 5, 6]
def baseStart_1833539 : Nat := 118140960795 + 1833539 * 2 ^ 59
def prefixEnd_1833539 : Nat := 4983230072969 + 3 ^ 40 * 1833539 * 2
def baseEnd_1833539 : Nat := 418438580339647557302317

theorem tailTrace_1833539 : CollatzResearch.WordTrace tailWord_1833539 prefixEnd_1833539 418438580339647557302317 := by
  unfold tailWord_1833539
  simp only [CollatzResearch.WordTrace]
  refine ⟨66874661304408821375679671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44583107536272547583786447 66874661304408821375679671)
  ·
    refine ⟨100311991956613232063519507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66874661304408821375679671 100311991956613232063519507)
    ·
      refine ⟨150467987934919848095279261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100311991956613232063519507 150467987934919848095279261)
      ·
        refine ⟨56425495475594943035729723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150467987934919848095279261 56425495475594943035729723)
        ·
          refine ⟨84638243213392414553594585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56425495475594943035729723 84638243213392414553594585)
          ·
            refine ⟨63478682410044310915195939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84638243213392414553594585 63478682410044310915195939)
            ·
              refine ⟨95218023615066466372793909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63478682410044310915195939 95218023615066466372793909)
              ·
                refine ⟨8926689713912481222449429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 95218023615066466372793909 8926689713912481222449429)
                ·
                  refine ⟨418438580339647557302317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8926689713912481222449429 418438580339647557302317)
                  ·
                    rfl

theorem cell21_1833539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 6].length) (baseStart_1833539 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1833539 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1833539 prefixEnd_1833539 := by exact prefixLift 1833539
  have htrace : WordTrace (prefixWord ++ tailWord_1833539) baseStart_1833539 baseEnd_1833539 := by
    simpa [prefixWord, tailWord_1833539, baseEnd_1833539] using wordTrace_append hprefix tailTrace_1833539
  have hstable : (prefixWord ++ tailWord_1833539).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833539).length < 2 ^ (prefixWord ++ tailWord_1833539).sum := by decide
  have hdescent : baseEnd_1833539 < baseStart_1833539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833576 : List Nat := [2, 1, 4, 3, 2, 1, 2, 3, 3]
def baseStart_1833576 : Nat := 118140960795 + 1833576 * 2 ^ 59
def prefixEnd_1833576 : Nat := 4983230072969 + 3 ^ 40 * 1833576 * 2
def baseEnd_1833576 : Nat := 418447024243743715185575

theorem tailTrace_1833576 : CollatzResearch.WordTrace tailWord_1833576 prefixEnd_1833576 418447024243743715185575 := by
  unfold tailWord_1833576
  simp only [CollatzResearch.WordTrace]
  refine ⟨33438005402637388347388291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44584007203516517796517721 33438005402637388347388291)
  ·
    refine ⟨50157008103956082521082437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33438005402637388347388291 50157008103956082521082437)
    ·
      refine ⟨9404439019491765472702957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50157008103956082521082437 9404439019491765472702957)
      ·
        refine ⟨3526664632309412052263609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9404439019491765472702957 3526664632309412052263609)
        ·
          refine ⟨2644998474232059039197707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3526664632309412052263609 2644998474232059039197707)
          ·
            refine ⟨3967497711348088558796561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2644998474232059039197707 3967497711348088558796561)
            ·
              refine ⟨2975623283511066419097421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3967497711348088558796561 2975623283511066419097421)
              ·
                refine ⟨1115858731316649907161533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2975623283511066419097421 1115858731316649907161533)
                ·
                  refine ⟨418447024243743715185575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1115858731316649907161533 418447024243743715185575)
                  ·
                    rfl

theorem cell21_1833576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 3, 3].length) (baseStart_1833576 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1833576 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1833576 prefixEnd_1833576 := by exact prefixLift 1833576
  have htrace : WordTrace (prefixWord ++ tailWord_1833576) baseStart_1833576 baseEnd_1833576 := by
    simpa [prefixWord, tailWord_1833576, baseEnd_1833576] using wordTrace_append hprefix tailTrace_1833576
  have hstable : (prefixWord ++ tailWord_1833576).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833576).length < 2 ^ (prefixWord ++ tailWord_1833576).sum := by decide
  have hdescent : baseEnd_1833576 < baseStart_1833576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833618 : List Nat := [3, 2, 3, 1, 2, 1, 2, 2, 5]
def baseStart_1833618 : Nat := 118140960795 + 1833618 * 2 ^ 59
def prefixEnd_1833618 : Nat := 4983230072969 + 3 ^ 40 * 1833618 * 2
def baseEnd_1833618 : Nat := 418456609215960975485489

theorem tailTrace_1833618 : CollatzResearch.WordTrace tailWord_1833618 prefixEnd_1833618 418456609215960975485489 := by
  unfold tailWord_1833618
  simp only [CollatzResearch.WordTrace]
  refine ⟨16719385667780654466951377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44585028447415078578537005 16719385667780654466951377)
  ·
    refine ⟨12539539250835490850213533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16719385667780654466951377 12539539250835490850213533)
    ·
      refine ⟨4702327219063309068830075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12539539250835490850213533 4702327219063309068830075)
      ·
        refine ⟨7053490828594963603245113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4702327219063309068830075 7053490828594963603245113)
        ·
          refine ⟨5290118121446222702433835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7053490828594963603245113 5290118121446222702433835)
          ·
            refine ⟨7935177182169334053650753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5290118121446222702433835 7935177182169334053650753)
            ·
              refine ⟨5951382886627000540238065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7935177182169334053650753 5951382886627000540238065)
              ·
                refine ⟨4463537164970250405178549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5951382886627000540238065 4463537164970250405178549)
                ·
                  refine ⟨418456609215960975485489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4463537164970250405178549 418456609215960975485489)
                  ·
                    rfl

theorem cell21_1833618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 2, 5].length) (baseStart_1833618 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1833618 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1833618 prefixEnd_1833618 := by exact prefixLift 1833618
  have htrace : WordTrace (prefixWord ++ tailWord_1833618) baseStart_1833618 baseEnd_1833618 := by
    simpa [prefixWord, tailWord_1833618, baseEnd_1833618] using wordTrace_append hprefix tailTrace_1833618
  have hstable : (prefixWord ++ tailWord_1833618).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833618).length < 2 ^ (prefixWord ++ tailWord_1833618).sum := by decide
  have hdescent : baseEnd_1833618 < baseStart_1833618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833711 : List Nat := [1, 1, 2, 1, 5, 2, 4, 2, 3]
def baseStart_1833711 : Nat := 118140960795 + 1833711 * 2 ^ 59
def prefixEnd_1833711 : Nat := 4983230072969 + 3 ^ 40 * 1833711 * 2
def baseEnd_1833711 : Nat := 418477833083013480435299

theorem tailTrace_1833711 : CollatzResearch.WordTrace tailWord_1833711 prefixEnd_1833711 418477833083013480435299 := by
  unfold tailWord_1833711
  simp only [CollatzResearch.WordTrace]
  refine ⟨66880934659785694750940987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44587289773190463167293991 66880934659785694750940987)
  ·
    refine ⟨100321401989678542126411481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66880934659785694750940987 100321401989678542126411481)
    ·
      refine ⟨75241051492258906594808611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100321401989678542126411481 75241051492258906594808611)
      ·
        refine ⟨112861577238388359892212917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75241051492258906594808611 112861577238388359892212917)
        ·
          refine ⟨10580772866098908739894961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 112861577238388359892212917 10580772866098908739894961)
          ·
            refine ⟨7935579649574181554921221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10580772866098908739894961 7935579649574181554921221)
            ·
              refine ⟨1487921184295159041547729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7935579649574181554921221 1487921184295159041547729)
              ·
                refine ⟨1115940888221369281160797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1487921184295159041547729 1115940888221369281160797)
                ·
                  refine ⟨418477833083013480435299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1115940888221369281160797 418477833083013480435299)
                  ·
                    rfl

theorem cell21_1833711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 4, 2, 3].length) (baseStart_1833711 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1833711 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1833711 prefixEnd_1833711 := by exact prefixLift 1833711
  have htrace : WordTrace (prefixWord ++ tailWord_1833711) baseStart_1833711 baseEnd_1833711 := by
    simpa [prefixWord, tailWord_1833711, baseEnd_1833711] using wordTrace_append hprefix tailTrace_1833711
  have hstable : (prefixWord ++ tailWord_1833711).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833711).length < 2 ^ (prefixWord ++ tailWord_1833711).sum := by decide
  have hdescent : baseEnd_1833711 < baseStart_1833711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833722 : List Nat := [3, 1, 1, 1, 1, 3, 5, 6]
def baseStart_1833722 : Nat := 118140960795 + 1833722 * 2 ^ 59
def prefixEnd_1833722 : Nat := 4983230072969 + 3 ^ 40 * 1833722 * 2
def baseEnd_1833722 : Nat := 139493447810959968583981

theorem tailTrace_1833722 : CollatzResearch.WordTrace tailWord_1833722 prefixEnd_1833722 139493447810959968583981 := by
  unfold tailWord_1833722
  simp only [CollatzResearch.WordTrace]
  refine ⟨16720333965686460907397855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44587557241830562419727613 16720333965686460907397855)
  ·
    refine ⟨25080500948529691361096783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16720333965686460907397855 25080500948529691361096783)
    ·
      refine ⟨37620751422794537041645175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25080500948529691361096783 37620751422794537041645175)
      ·
        refine ⟨56431127134191805562467763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37620751422794537041645175 56431127134191805562467763)
        ·
          refine ⟨84646690701287708343701645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56431127134191805562467763 84646690701287708343701645)
          ·
            refine ⟨31742509012982890628888117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84646690701287708343701645 31742509012982890628888117)
            ·
              refine ⟨2975860219967145996458261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31742509012982890628888117 2975860219967145996458261)
              ·
                refine ⟨139493447810959968583981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2975860219967145996458261 139493447810959968583981)
                ·
                  rfl

theorem cell21_1833722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 6].length) (baseStart_1833722 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1833722 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1833722 prefixEnd_1833722 := by exact prefixLift 1833722
  have htrace : WordTrace (prefixWord ++ tailWord_1833722) baseStart_1833722 baseEnd_1833722 := by
    simpa [prefixWord, tailWord_1833722, baseEnd_1833722] using wordTrace_append hprefix tailTrace_1833722
  have hstable : (prefixWord ++ tailWord_1833722).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833722).length < 2 ^ (prefixWord ++ tailWord_1833722).sum := by decide
  have hdescent : baseEnd_1833722 < baseStart_1833722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833829 : List Nat := [1, 3, 1, 3, 1, 1, 5, 1, 5]
def baseStart_1833829 : Nat := 118140960795 + 1833829 * 2 ^ 59
def prefixEnd_1833829 : Nat := 4983230072969 + 3 ^ 40 * 1833829 * 2
def baseEnd_1833829 : Nat := 418504762290671497468391

theorem tailTrace_1833829 : CollatzResearch.WordTrace tailWord_1833829 prefixEnd_1833829 418504762290671497468391 := by
  unfold tailWord_1833829
  simp only [CollatzResearch.WordTrace]
  refine ⟨66885238473358200903736541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44590158982238800602491027 66885238473358200903736541)
  ·
    refine ⟨25081964427509325338901203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66885238473358200903736541 25081964427509325338901203)
    ·
      refine ⟨37622946641263988008351805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25081964427509325338901203 37622946641263988008351805)
      ·
        refine ⟨14108604990473995503131927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37622946641263988008351805 14108604990473995503131927)
        ·
          refine ⟨21162907485710993254697891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14108604990473995503131927 21162907485710993254697891)
          ·
            refine ⟨31744361228566489882046837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21162907485710993254697891 31744361228566489882046837)
            ·
              refine ⟨2976033865178108426441891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31744361228566489882046837 2976033865178108426441891)
              ·
                refine ⟨4464050797767162639662837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2976033865178108426441891 4464050797767162639662837)
                ·
                  refine ⟨418504762290671497468391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4464050797767162639662837 418504762290671497468391)
                  ·
                    rfl

theorem cell21_1833829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 1, 5].length) (baseStart_1833829 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1833829 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1833829 prefixEnd_1833829 := by exact prefixLift 1833829
  have htrace : WordTrace (prefixWord ++ tailWord_1833829) baseStart_1833829 baseEnd_1833829 := by
    simpa [prefixWord, tailWord_1833829, baseEnd_1833829] using wordTrace_append hprefix tailTrace_1833829
  have hstable : (prefixWord ++ tailWord_1833829).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833829).length < 2 ^ (prefixWord ++ tailWord_1833829).sum := by decide
  have hdescent : baseEnd_1833829 < baseStart_1833829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833874 : List Nat := [3, 2, 3, 2, 11]
def baseStart_1833874 : Nat := 118140960795 + 1833874 * 2 ^ 59
def prefixEnd_1833874 : Nat := 4983230072969 + 3 ^ 40 * 1833874 * 2
def baseEnd_1833874 : Nat := 5166852245725449619979

theorem tailTrace_1833874 : CollatzResearch.WordTrace tailWord_1833874 prefixEnd_1833874 5166852245725449619979 := by
  unfold tailWord_1833874
  simp only [CollatzResearch.WordTrace]
  refine ⟨16721719939548793397281169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44591253172130115726083117 16721719939548793397281169)
  ·
    refine ⟨12541289954661595047960877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16721719939548793397281169 12541289954661595047960877)
    ·
      refine ⟨4702983732998098142985329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12541289954661595047960877 4702983732998098142985329)
      ·
        refine ⟨3527237799748573607238997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4702983732998098142985329 3527237799748573607238997)
        ·
          refine ⟨5166852245725449619979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3527237799748573607238997 5166852245725449619979)
          ·
            rfl

theorem cell21_1833874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 11].length) (baseStart_1833874 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1833874 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1833874 prefixEnd_1833874 := by exact prefixLift 1833874
  have htrace : WordTrace (prefixWord ++ tailWord_1833874) baseStart_1833874 baseEnd_1833874 := by
    simpa [prefixWord, tailWord_1833874, baseEnd_1833874] using wordTrace_append hprefix tailTrace_1833874
  have hstable : (prefixWord ++ tailWord_1833874).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833874).length < 2 ^ (prefixWord ++ tailWord_1833874).sum := by decide
  have hdescent : baseEnd_1833874 < baseStart_1833874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833967 : List Nat := [1, 1, 2, 1, 4, 5, 2, 5]
def baseStart_1833967 : Nat := 118140960795 + 1833967 * 2 ^ 59
def prefixEnd_1833967 : Nat := 4983230072969 + 3 ^ 40 * 1833967 * 2
def baseEnd_1833967 : Nat := 139512085256937974722703

theorem tailTrace_1833967 : CollatzResearch.WordTrace tailWord_1833967 prefixEnd_1833967 139512085256937974722703 := by
  unfold tailWord_1833967
  simp only [CollatzResearch.WordTrace]
  refine ⟨66890271746858250472260155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44593514497905500314840103 66890271746858250472260155)
  ·
    refine ⟨100335407620287375708390233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66890271746858250472260155 100335407620287375708390233)
    ·
      refine ⟨75251555715215531781292675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100335407620287375708390233 75251555715215531781292675)
      ·
        refine ⟨112877333572823297671939013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75251555715215531781292675 112877333572823297671939013)
        ·
          refine ⟨21164500044904368313488565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112877333572823297671939013 21164500044904368313488565)
          ·
            refine ⟨1984171879209784529389553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21164500044904368313488565 1984171879209784529389553)
            ·
              refine ⟨1488128909407338397042165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1984171879209784529389553 1488128909407338397042165)
              ·
                refine ⟨139512085256937974722703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1488128909407338397042165 139512085256937974722703)
                ·
                  rfl

theorem cell21_1833967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 2, 5].length) (baseStart_1833967 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1833967 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1833967 prefixEnd_1833967 := by exact prefixLift 1833967
  have htrace : WordTrace (prefixWord ++ tailWord_1833967) baseStart_1833967 baseEnd_1833967 := by
    simpa [prefixWord, tailWord_1833967, baseEnd_1833967] using wordTrace_append hprefix tailTrace_1833967
  have hstable : (prefixWord ++ tailWord_1833967).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833967).length < 2 ^ (prefixWord ++ tailWord_1833967).sum := by decide
  have hdescent : baseEnd_1833967 < baseStart_1833967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833973 : List Nat := [1, 3, 5, 2, 1, 2, 1, 3, 3]
def baseStart_1833973 : Nat := 118140960795 + 1833973 * 2 ^ 59
def prefixEnd_1833973 : Nat := 4983230072969 + 3 ^ 40 * 1833973 * 2
def baseEnd_1833973 : Nat := 418537625052559247068097

theorem tailTrace_1833973 : CollatzResearch.WordTrace tailWord_1833973 prefixEnd_1833973 418537625052559247068097 := by
  unfold tailWord_1833973
  simp only [CollatzResearch.WordTrace]
  refine ⟨66890490584836513496978573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44593660389891008997985715 66890490584836513496978573)
  ·
    refine ⟨25083933969313692561366965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66890490584836513496978573 25083933969313692561366965)
    ·
      refine ⟨2351618809623158677628153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25083933969313692561366965 2351618809623158677628153)
      ·
        refine ⟨1763714107217369008221115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2351618809623158677628153 1763714107217369008221115)
        ·
          refine ⟨2645571160826053512331673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1763714107217369008221115 2645571160826053512331673)
          ·
            refine ⟨1984178370619540134248755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2645571160826053512331673 1984178370619540134248755)
            ·
              refine ⟨2976267555929310201373133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1984178370619540134248755 2976267555929310201373133)
              ·
                refine ⟨1116100333473491325514925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2976267555929310201373133 1116100333473491325514925)
                ·
                  refine ⟨418537625052559247068097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1116100333473491325514925 418537625052559247068097)
                  ·
                    rfl

theorem cell21_1833973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 3, 3].length) (baseStart_1833973 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1833973 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1833973 prefixEnd_1833973 := by exact prefixLift 1833973
  have htrace : WordTrace (prefixWord ++ tailWord_1833973) baseStart_1833973 baseEnd_1833973 := by
    simpa [prefixWord, tailWord_1833973, baseEnd_1833973] using wordTrace_append hprefix tailTrace_1833973
  have hstable : (prefixWord ++ tailWord_1833973).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833973).length < 2 ^ (prefixWord ++ tailWord_1833973).sum := by decide
  have hdescent : baseEnd_1833973 < baseStart_1833973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833995 : List Nat := [1, 1, 1, 1, 6, 2, 2, 1, 6]
def baseStart_1833995 : Nat := 118140960795 + 1833995 * 2 ^ 59
def prefixEnd_1833995 : Nat := 4983230072969 + 3 ^ 40 * 1833995 * 2
def baseEnd_1833995 : Nat := 418542645752292097701385

theorem tailTrace_1833995 : CollatzResearch.WordTrace tailWord_1833995 prefixEnd_1833995 418542645752292097701385 := by
  unfold tailWord_1833995
  simp only [CollatzResearch.WordTrace]
  refine ⟨66891292990756811254279439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44594195327171207502852959 66891292990756811254279439)
  ·
    refine ⟨100336939486135216881419159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66891292990756811254279439 100336939486135216881419159)
    ·
      refine ⟨150505409229202825322128739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100336939486135216881419159 150505409229202825322128739)
      ·
        refine ⟨225758113843804237983193109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150505409229202825322128739 225758113843804237983193109)
        ·
          refine ⟨10582411586428323655462177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 225758113843804237983193109 10582411586428323655462177)
          ·
            refine ⟨7936808689821242741596633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10582411586428323655462177 7936808689821242741596633)
            ·
              refine ⟨5952606517365932056197475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7936808689821242741596633 5952606517365932056197475)
              ·
                refine ⟨8928909776048898084296213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5952606517365932056197475 8928909776048898084296213)
                ·
                  refine ⟨418542645752292097701385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8928909776048898084296213 418542645752292097701385)
                  ·
                    rfl

theorem cell21_1833995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 6].length) (baseStart_1833995 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1833995 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1833995 prefixEnd_1833995 := by exact prefixLift 1833995
  have htrace : WordTrace (prefixWord ++ tailWord_1833995) baseStart_1833995 baseEnd_1833995 := by
    simpa [prefixWord, tailWord_1833995, baseEnd_1833995] using wordTrace_append hprefix tailTrace_1833995
  have hstable : (prefixWord ++ tailWord_1833995).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833995).length < 2 ^ (prefixWord ++ tailWord_1833995).sum := by decide
  have hdescent : baseEnd_1833995 < baseStart_1833995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833998 : List Nat := [4, 1, 1, 2, 2, 4, 1, 1, 5]
def baseStart_1833998 : Nat := 118140960795 + 1833998 * 2 ^ 59
def prefixEnd_1833998 : Nat := 4983230072969 + 3 ^ 40 * 1833998 * 2
def baseEnd_1833998 : Nat := 418543330393164759151379

theorem tailTrace_1833998 : CollatzResearch.WordTrace tailWord_1833998 prefixEnd_1833998 418543330393164759151379 := by
  unfold tailWord_1833998
  simp only [CollatzResearch.WordTrace]
  refine ⟨8361425301218242845829831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44594268273163961844425765 8361425301218242845829831)
  ·
    refine ⟨12542137951827364268744747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8361425301218242845829831 12542137951827364268744747)
    ·
      refine ⟨18813206927741046403117121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12542137951827364268744747 18813206927741046403117121)
      ·
        refine ⟨14109905195805784802337841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18813206927741046403117121 14109905195805784802337841)
        ·
          refine ⟨10582428896854338601753381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14109905195805784802337841 10582428896854338601753381)
          ·
            refine ⟨1984205418160188487828759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10582428896854338601753381 1984205418160188487828759)
            ·
              refine ⟨2976308127240282731743139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1984205418160188487828759 2976308127240282731743139)
              ·
                refine ⟨4464462190860424097614709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2976308127240282731743139 4464462190860424097614709)
                ·
                  refine ⟨418543330393164759151379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4464462190860424097614709 418543330393164759151379)
                  ·
                    rfl

theorem cell21_1833998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 1, 5].length) (baseStart_1833998 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1833998 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1833998 prefixEnd_1833998 := by exact prefixLift 1833998
  have htrace : WordTrace (prefixWord ++ tailWord_1833998) baseStart_1833998 baseEnd_1833998 := by
    simpa [prefixWord, tailWord_1833998, baseEnd_1833998] using wordTrace_append hprefix tailTrace_1833998
  have hstable : (prefixWord ++ tailWord_1833998).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833998).length < 2 ^ (prefixWord ++ tailWord_1833998).sum := by decide
  have hdescent : baseEnd_1833998 < baseStart_1833998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834009 : List Nat := [1, 2, 1, 2, 1, 1, 5, 8]
def baseStart_1834009 : Nat := 118140960795 + 1834009 * 2 ^ 59
def prefixEnd_1834009 : Nat := 4983230072969 + 3 ^ 40 * 1834009 * 2
def baseEnd_1834009 : Nat := 139515280247677061489341

theorem tailTrace_1834009 : CollatzResearch.WordTrace tailWord_1834009 prefixEnd_1834009 139515280247677061489341 := by
  unfold tailWord_1834009
  simp only [CollatzResearch.WordTrace]
  refine ⟨66891803612706091645289081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44594535741804061096859387 66891803612706091645289081)
  ·
    refine ⟨50168852709529568733966811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66891803612706091645289081 50168852709529568733966811)
    ·
      refine ⟨75253279064294353100950217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50168852709529568733966811 75253279064294353100950217)
      ·
        refine ⟨56439959298220764825712663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75253279064294353100950217 56439959298220764825712663)
        ·
          refine ⟨84659938947331147238568995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56439959298220764825712663 84659938947331147238568995)
          ·
            refine ⟨126989908420996720857853493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84659938947331147238568995 126989908420996720857853493)
            ·
              refine ⟨11905303914468442580423765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 126989908420996720857853493 11905303914468442580423765)
              ·
                refine ⟨139515280247677061489341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11905303914468442580423765 139515280247677061489341)
                ·
                  rfl

theorem cell21_1834009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 8].length) (baseStart_1834009 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1834009 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1834009 prefixEnd_1834009 := by exact prefixLift 1834009
  have htrace : WordTrace (prefixWord ++ tailWord_1834009) baseStart_1834009 baseEnd_1834009 := by
    simpa [prefixWord, tailWord_1834009, baseEnd_1834009] using wordTrace_append hprefix tailTrace_1834009
  have hstable : (prefixWord ++ tailWord_1834009).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834009).length < 2 ^ (prefixWord ++ tailWord_1834009).sum := by decide
  have hdescent : baseEnd_1834009 < baseStart_1834009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834049 : List Nat := [1, 2, 5, 1, 4, 1, 2, 2, 3]
def baseStart_1834049 : Nat := 118140960795 + 1834049 * 2 ^ 59
def prefixEnd_1834049 : Nat := 4983230072969 + 3 ^ 40 * 1834049 * 2
def baseEnd_1834049 : Nat := 418554969288000003801275

theorem tailTrace_1834049 : CollatzResearch.WordTrace tailWord_1834049 prefixEnd_1834049 418554969288000003801275 := by
  unfold tailWord_1834049
  simp only [CollatzResearch.WordTrace]
  refine ⟨66893262532561178476745201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44595508355040785651163467 66893262532561178476745201)
  ·
    refine ⟨50169946899420883857558901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66893262532561178476745201 50169946899420883857558901)
    ·
      refine ⟨4703432521820707861646147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50169946899420883857558901 4703432521820707861646147)
      ·
        refine ⟨7055148782731061792469221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4703432521820707861646147 7055148782731061792469221)
        ·
          refine ⟨1322840396762074086087979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7055148782731061792469221 1322840396762074086087979)
          ·
            refine ⟨1984260595143111129131969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1322840396762074086087979 1984260595143111129131969)
            ·
              refine ⟨1488195446357333346848977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1984260595143111129131969 1488195446357333346848977)
              ·
                refine ⟨1116146584768000010136733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1488195446357333346848977 1116146584768000010136733)
                ·
                  refine ⟨418554969288000003801275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1116146584768000010136733 418554969288000003801275)
                  ·
                    rfl

theorem cell21_1834049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 2, 2, 3].length) (baseStart_1834049 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1834049 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1834049 prefixEnd_1834049 := by exact prefixLift 1834049
  have htrace : WordTrace (prefixWord ++ tailWord_1834049) baseStart_1834049 baseEnd_1834049 := by
    simpa [prefixWord, tailWord_1834049, baseEnd_1834049] using wordTrace_append hprefix tailTrace_1834049
  have hstable : (prefixWord ++ tailWord_1834049).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834049).length < 2 ^ (prefixWord ++ tailWord_1834049).sum := by decide
  have hdescent : baseEnd_1834049 < baseStart_1834049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834102 : List Nat := [5, 1, 1, 2, 1, 1, 10]
def baseStart_1834102 : Nat := 118140960795 + 1834102 * 2 ^ 59
def prefixEnd_1834102 : Nat := 4983230072969 + 3 ^ 40 * 1834102 * 2
def baseEnd_1834102 : Nat := 46507451623342632157537

theorem tailTrace_1834102 : CollatzResearch.WordTrace tailWord_1834102 prefixEnd_1834102 46507451623342632157537 := by
  unfold tailWord_1834102
  simp only [CollatzResearch.WordTrace]
  refine ⟨4180949725085573033026535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44596797067579445685616373 4180949725085573033026535)
  ·
    refine ⟨6271424587628359549539803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4180949725085573033026535 6271424587628359549539803)
    ·
      refine ⟨9407136881442539324309705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6271424587628359549539803 9407136881442539324309705)
      ·
        refine ⟨7055352661081904493232279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9407136881442539324309705 7055352661081904493232279)
        ·
          refine ⟨10583028991622856739848419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7055352661081904493232279 10583028991622856739848419)
          ·
            refine ⟨15874543487434285109772629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10583028991622856739848419 15874543487434285109772629)
            ·
              refine ⟨46507451623342632157537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15874543487434285109772629 46507451623342632157537)
              ·
                rfl

theorem cell21_1834102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 10].length) (baseStart_1834102 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1834102 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1834102 prefixEnd_1834102 := by exact prefixLift 1834102
  have htrace : WordTrace (prefixWord ++ tailWord_1834102) baseStart_1834102 baseEnd_1834102 := by
    simpa [prefixWord, tailWord_1834102, baseEnd_1834102] using wordTrace_append hprefix tailTrace_1834102
  have hstable : (prefixWord ++ tailWord_1834102).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834102).length < 2 ^ (prefixWord ++ tailWord_1834102).sum := by decide
  have hdescent : baseEnd_1834102 < baseStart_1834102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834105 : List Nat := [1, 2, 1, 3, 5, 2, 1, 2, 4]
def baseStart_1834105 : Nat := 118140960795 + 1834105 * 2 ^ 59
def prefixEnd_1834105 : Nat := 4983230072969 + 3 ^ 40 * 1834105 * 2
def baseEnd_1834105 : Nat := 418567749250956350867827

theorem tailTrace_1834105 : CollatzResearch.WordTrace tailWord_1834105 prefixEnd_1834105 418567749250956350867827 := by
  unfold tailWord_1834105
  simp only [CollatzResearch.WordTrace]
  refine ⟨66895305020358300040783769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44596870013572200027189179 66895305020358300040783769)
  ·
    refine ⟨50171478765268725030587827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66895305020358300040783769 50171478765268725030587827)
    ·
      refine ⟨75257218147903087545881741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50171478765268725030587827 75257218147903087545881741)
      ·
        refine ⟨28221456805463657829705653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75257218147903087545881741 28221456805463657829705653)
        ·
          refine ⟨2645761575512217921534905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28221456805463657829705653 2645761575512217921534905)
          ·
            refine ⟨1984321181634163441151179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2645761575512217921534905 1984321181634163441151179)
            ·
              refine ⟨2976481772451245161726769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1984321181634163441151179 2976481772451245161726769)
              ·
                refine ⟨2232361329338433871295077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2976481772451245161726769 2232361329338433871295077)
                ·
                  refine ⟨418567749250956350867827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2232361329338433871295077 418567749250956350867827)
                  ·
                    rfl

theorem cell21_1834105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 2, 4].length) (baseStart_1834105 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1834105 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1834105 prefixEnd_1834105 := by exact prefixLift 1834105
  have htrace : WordTrace (prefixWord ++ tailWord_1834105) baseStart_1834105 baseEnd_1834105 := by
    simpa [prefixWord, tailWord_1834105, baseEnd_1834105] using wordTrace_append hprefix tailTrace_1834105
  have hstable : (prefixWord ++ tailWord_1834105).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834105).length < 2 ^ (prefixWord ++ tailWord_1834105).sum := by decide
  have hdescent : baseEnd_1834105 < baseStart_1834105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834274 : List Nat := [3, 3, 1, 1, 5, 1, 1, 2, 4]
def baseStart_1834274 : Nat := 118140960795 + 1834274 * 2 ^ 59
def prefixEnd_1834274 : Nat := 4983230072969 + 3 ^ 40 * 1834274 * 2
def baseEnd_1834274 : Nat := 418606317353449612550815

theorem tailTrace_1834274 : CollatzResearch.WordTrace tailWord_1834274 prefixEnd_1834274 418606317353449612550815 := by
  unfold tailWord_1834274
  simp only [CollatzResearch.WordTrace]
  refine ⟨16725367239186510475921469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44600979304497361269123917 16725367239186510475921469)
  ·
    refine ⟨6272012714694941428470551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16725367239186510475921469 6272012714694941428470551)
    ·
      refine ⟨9408019072042412142705827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6272012714694941428470551 9408019072042412142705827)
      ·
        refine ⟨14112028608063618214058741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9408019072042412142705827 14112028608063618214058741)
        ·
          refine ⟨1323002682005964207568007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14112028608063618214058741 1323002682005964207568007)
          ·
            refine ⟨1984504023008946311352011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1323002682005964207568007 1984504023008946311352011)
            ·
              refine ⟨2976756034513419467028017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1984504023008946311352011 2976756034513419467028017)
              ·
                refine ⟨2232567025885064600271013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2976756034513419467028017 2232567025885064600271013)
                ·
                  refine ⟨418606317353449612550815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2232567025885064600271013 418606317353449612550815)
                  ·
                    rfl

theorem cell21_1834274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 2, 4].length) (baseStart_1834274 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1834274 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1834274 prefixEnd_1834274 := by exact prefixLift 1834274
  have htrace : WordTrace (prefixWord ++ tailWord_1834274) baseStart_1834274 baseEnd_1834274 := by
    simpa [prefixWord, tailWord_1834274, baseEnd_1834274] using wordTrace_append hprefix tailTrace_1834274
  have hstable : (prefixWord ++ tailWord_1834274).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834274).length < 2 ^ (prefixWord ++ tailWord_1834274).sum := by decide
  have hdescent : baseEnd_1834274 < baseStart_1834274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834454 : List Nat := [5, 2, 1, 1, 1, 3, 2, 1, 5]
def baseStart_1834454 : Nat := 118140960795 + 1834454 * 2 ^ 59
def prefixEnd_1834454 : Nat := 4983230072969 + 3 ^ 40 * 1834454 * 2
def baseEnd_1834454 : Nat := 418647395805809299550447

theorem tailTrace_1834454 : CollatzResearch.WordTrace tailWord_1834454 prefixEnd_1834454 418647395805809299550447 := by
  unfold tailWord_1834454
  simp only [CollatzResearch.WordTrace]
  refine ⟨4181752131005870790327401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44605356064062621763492277 4181752131005870790327401)
  ·
    refine ⟨3136314098254403092745551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4181752131005870790327401 3136314098254403092745551)
    ·
      refine ⟨4704471147381604639118327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3136314098254403092745551 4704471147381604639118327)
      ·
        refine ⟨7056706721072406958677491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4704471147381604639118327 7056706721072406958677491)
        ·
          refine ⟨10585060081608610438016237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7056706721072406958677491 10585060081608610438016237)
          ·
            refine ⟨3969397530603228914256089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10585060081608610438016237 3969397530603228914256089)
            ·
              refine ⟨2977048147952421685692067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3969397530603228914256089 2977048147952421685692067)
              ·
                refine ⟨4465572221928632528538101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2977048147952421685692067 4465572221928632528538101)
                ·
                  refine ⟨418647395805809299550447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4465572221928632528538101 418647395805809299550447)
                  ·
                    rfl

theorem cell21_1834454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_1834454 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1834454 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1834454 prefixEnd_1834454 := by exact prefixLift 1834454
  have htrace : WordTrace (prefixWord ++ tailWord_1834454) baseStart_1834454 baseEnd_1834454 := by
    simpa [prefixWord, tailWord_1834454, baseEnd_1834454] using wordTrace_append hprefix tailTrace_1834454
  have hstable : (prefixWord ++ tailWord_1834454).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834454).length < 2 ^ (prefixWord ++ tailWord_1834454).sum := by decide
  have hdescent : baseEnd_1834454 < baseStart_1834454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834482 : List Nat := [3, 2, 1, 4, 1, 2, 1, 7]
def baseStart_1834482 : Nat := 118140960795 + 1834482 * 2 ^ 59
def prefixEnd_1834482 : Nat := 4983230072969 + 3 ^ 40 * 1834482 * 2
def baseEnd_1834482 : Nat := 139551261929095824361241

theorem tailTrace_1834482 : CollatzResearch.WordTrace tailWord_1834482 prefixEnd_1834482 139551261929095824361241 := by
  unfold tailWord_1834482
  simp only [CollatzResearch.WordTrace]
  refine ⟨16727263834998123356814425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44606036893328328951505133 16727263834998123356814425)
  ·
    refine ⟨12545447876248592517610819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16727263834998123356814425 12545447876248592517610819)
    ·
      refine ⟨18818171814372888776416229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12545447876248592517610819 18818171814372888776416229)
      ·
        refine ⟨3528407215194916645578043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18818171814372888776416229 3528407215194916645578043)
        ·
          refine ⟨5292610822792374968367065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3528407215194916645578043 5292610822792374968367065)
          ·
            refine ⟨3969458117094281226275299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5292610822792374968367065 3969458117094281226275299)
            ·
              refine ⟨5954187175641421839412949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3969458117094281226275299 5954187175641421839412949)
              ·
                refine ⟨139551261929095824361241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5954187175641421839412949 139551261929095824361241)
                ·
                  rfl

theorem cell21_1834482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 7].length) (baseStart_1834482 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1834482 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1834482 prefixEnd_1834482 := by exact prefixLift 1834482
  have htrace : WordTrace (prefixWord ++ tailWord_1834482) baseStart_1834482 baseEnd_1834482 := by
    simpa [prefixWord, tailWord_1834482, baseEnd_1834482] using wordTrace_append hprefix tailTrace_1834482
  have hstable : (prefixWord ++ tailWord_1834482).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834482).length < 2 ^ (prefixWord ++ tailWord_1834482).sum := by decide
  have hdescent : baseEnd_1834482 < baseStart_1834482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834648 : List Nat := [2, 1, 2, 4, 1, 2, 2, 2, 5]
def baseStart_1834648 : Nat := 118140960795 + 1834648 * 2 ^ 59
def prefixEnd_1834648 : Nat := 4983230072969 + 3 ^ 40 * 1834648 * 2
def baseEnd_1834648 : Nat := 418691669248908073316717

theorem tailTrace_1834648 : CollatzResearch.WordTrace tailWord_1834648 prefixEnd_1834648 418691669248908073316717 := by
  unfold tailWord_1834648
  simp only [CollatzResearch.WordTrace]
  refine ⟨33457554928695551888900299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44610073238260735851867065 33457554928695551888900299)
  ·
    refine ⟨50186332393043327833350449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33457554928695551888900299 50186332393043327833350449)
    ·
      refine ⟨37639749294782495875012837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50186332393043327833350449 37639749294782495875012837)
      ·
        refine ⟨7057452992771717976564907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37639749294782495875012837 7057452992771717976564907)
        ·
          refine ⟨10586179489157576964847361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7057452992771717976564907 10586179489157576964847361)
          ·
            refine ⟨7939634616868182723635521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10586179489157576964847361 7939634616868182723635521)
            ·
              refine ⟨5954725962651137042726641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7939634616868182723635521 5954725962651137042726641)
              ·
                refine ⟨4466044471988352782044981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5954725962651137042726641 4466044471988352782044981)
                ·
                  refine ⟨418691669248908073316717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4466044471988352782044981 418691669248908073316717)
                  ·
                    rfl

theorem cell21_1834648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 2, 5].length) (baseStart_1834648 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1834648 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1834648 prefixEnd_1834648 := by exact prefixLift 1834648
  have htrace : WordTrace (prefixWord ++ tailWord_1834648) baseStart_1834648 baseEnd_1834648 := by
    simpa [prefixWord, tailWord_1834648, baseEnd_1834648] using wordTrace_append hprefix tailTrace_1834648
  have hstable : (prefixWord ++ tailWord_1834648).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834648).length < 2 ^ (prefixWord ++ tailWord_1834648).sum := by decide
  have hdescent : baseEnd_1834648 < baseStart_1834648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834682 : List Nat := [3, 1, 1, 1, 2, 5, 3, 2, 3]
def baseStart_1834682 : Nat := 118140960795 + 1834682 * 2 ^ 59
def prefixEnd_1834682 : Nat := 4983230072969 + 3 ^ 40 * 1834682 * 2
def baseEnd_1834682 : Nat := 418699428512131569749981

theorem tailTrace_1834682 : CollatzResearch.WordTrace tailWord_1834682 prefixEnd_1834682 418699428512131569749981 := by
  unfold tailWord_1834682
  simp only [CollatzResearch.WordTrace]
  refine ⟨16729087484816981896134575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44610899959511951723025533 16729087484816981896134575)
  ·
    refine ⟨25093631227225472844201863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16729087484816981896134575 25093631227225472844201863)
    ·
      refine ⟨37640446840838209266302795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25093631227225472844201863 37640446840838209266302795)
      ·
        refine ⟨56460670261257313899454193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37640446840838209266302795 56460670261257313899454193)
        ·
          refine ⟨42345502695942985424590645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56460670261257313899454193 42345502695942985424590645)
          ·
            refine ⟨3969890877744654883555373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42345502695942985424590645 3969890877744654883555373)
            ·
              refine ⟨1488709079154245581333265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3969890877744654883555373 1488709079154245581333265)
              ·
                refine ⟨1116531809365684185999949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1488709079154245581333265 1116531809365684185999949)
                ·
                  refine ⟨418699428512131569749981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1116531809365684185999949 418699428512131569749981)
                  ·
                    rfl

theorem cell21_1834682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 3, 2, 3].length) (baseStart_1834682 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1834682 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1834682 prefixEnd_1834682 := by exact prefixLift 1834682
  have htrace : WordTrace (prefixWord ++ tailWord_1834682) baseStart_1834682 baseEnd_1834682 := by
    simpa [prefixWord, tailWord_1834682, baseEnd_1834682] using wordTrace_append hprefix tailTrace_1834682
  have hstable : (prefixWord ++ tailWord_1834682).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834682).length < 2 ^ (prefixWord ++ tailWord_1834682).sum := by decide
  have hdescent : baseEnd_1834682 < baseStart_1834682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834783 : List Nat := [1, 1, 2, 4, 2, 1, 1, 2, 7]
def baseStart_1834783 : Nat := 118140960795 + 1834783 * 2 ^ 59
def prefixEnd_1834783 : Nat := 4983230072969 + 3 ^ 40 * 1834783 * 2
def baseEnd_1834783 : Nat := 418722478088177838566441

theorem tailTrace_1834783 : CollatzResearch.WordTrace tailWord_1834783 prefixEnd_1834783 418722478088177838566441 := by
  unfold tailWord_1834783
  simp only [CollatzResearch.WordTrace]
  refine ⟨66920033711902021833965003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44613355807934681222643335 66920033711902021833965003)
  ·
    refine ⟨100380050567853032750947505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66920033711902021833965003 100380050567853032750947505)
    ·
      refine ⟨75285037925889774563210629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100380050567853032750947505 75285037925889774563210629)
      ·
        refine ⟨14115944611104332730601993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75285037925889774563210629 14115944611104332730601993)
        ·
          refine ⟨10586958458328249547951495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14115944611104332730601993 10586958458328249547951495)
          ·
            refine ⟨15880437687492374321927243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10586958458328249547951495 15880437687492374321927243)
            ·
              refine ⟨23820656531238561482890865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15880437687492374321927243 23820656531238561482890865)
              ·
                refine ⟨17865492398428921112168149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23820656531238561482890865 17865492398428921112168149)
                ·
                  refine ⟨418722478088177838566441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17865492398428921112168149 418722478088177838566441)
                  ·
                    rfl

theorem cell21_1834783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 7].length) (baseStart_1834783 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1834783 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1834783 prefixEnd_1834783 := by exact prefixLift 1834783
  have htrace : WordTrace (prefixWord ++ tailWord_1834783) baseStart_1834783 baseEnd_1834783 := by
    simpa [prefixWord, tailWord_1834783, baseEnd_1834783] using wordTrace_append hprefix tailTrace_1834783
  have hstable : (prefixWord ++ tailWord_1834783).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834783).length < 2 ^ (prefixWord ++ tailWord_1834783).sum := by decide
  have hdescent : baseEnd_1834783 < baseStart_1834783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834834 : List Nat := [3, 2, 2, 1, 1, 5, 1, 3, 3]
def baseStart_1834834 : Nat := 118140960795 + 1834834 * 2 ^ 59
def prefixEnd_1834834 : Nat := 4983230072969 + 3 ^ 40 * 1834834 * 2
def baseEnd_1834834 : Nat := 418734116983013083216337

theorem tailTrace_1834834 : CollatzResearch.WordTrace tailWord_1834834 prefixEnd_1834834 418734116983013083216337 := by
  unfold tailWord_1834834
  simp only [CollatzResearch.WordTrace]
  refine ⟨16730473458679314386017889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44614595889811505029381037 16730473458679314386017889)
  ·
    refine ⟨12547855094009485789513417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16730473458679314386017889 12547855094009485789513417)
    ·
      refine ⟨9410891320507114342135063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12547855094009485789513417 9410891320507114342135063)
      ·
        refine ⟨14116336980760671513202595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9410891320507114342135063 14116336980760671513202595)
        ·
          refine ⟨21174505471141007269803893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14116336980760671513202595 21174505471141007269803893)
          ·
            refine ⟨1985109887919469431544115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21174505471141007269803893 1985109887919469431544115)
            ·
              refine ⟨2977664831879204147316173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1985109887919469431544115 2977664831879204147316173)
              ·
                refine ⟨1116624311954701555243565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2977664831879204147316173 1116624311954701555243565)
                ·
                  refine ⟨418734116983013083216337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1116624311954701555243565 418734116983013083216337)
                  ·
                    rfl

theorem cell21_1834834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 3, 3].length) (baseStart_1834834 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1834834 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1834834 prefixEnd_1834834 := by exact prefixLift 1834834
  have htrace : WordTrace (prefixWord ++ tailWord_1834834) baseStart_1834834 baseEnd_1834834 := by
    simpa [prefixWord, tailWord_1834834, baseEnd_1834834] using wordTrace_append hprefix tailTrace_1834834
  have hstable : (prefixWord ++ tailWord_1834834).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834834).length < 2 ^ (prefixWord ++ tailWord_1834834).sum := by decide
  have hdescent : baseEnd_1834834 < baseStart_1834834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834862 : List Nat := [4, 1, 2, 3, 1, 2, 2, 6]
def baseStart_1834862 : Nat := 118140960795 + 1834862 * 2 ^ 59
def prefixEnd_1834862 : Nat := 4983230072969 + 3 ^ 40 * 1834862 * 2
def baseEnd_1834862 : Nat := 139580168988163752249871

theorem tailTrace_1834862 : CollatzResearch.WordTrace tailWord_1834862 prefixEnd_1834862 139580168988163752249871 := by
  unfold tailWord_1834862
  simp only [CollatzResearch.WordTrace]
  refine ⟨8365364384826977290761355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44615276719077212217393893 8365364384826977290761355)
  ·
    refine ⟨12548046577240465936142033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8365364384826977290761355 12548046577240465936142033)
    ·
      refine ⟨9411034932930349452106525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12548046577240465936142033 9411034932930349452106525)
      ·
        refine ⟨3529138099848881044539947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9411034932930349452106525 3529138099848881044539947)
        ·
          refine ⟨5293707149773321566809921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3529138099848881044539947 5293707149773321566809921)
          ·
            refine ⟨3970280362329991175107441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5293707149773321566809921 3970280362329991175107441)
            ·
              refine ⟨2977710271747493381330581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3970280362329991175107441 2977710271747493381330581)
              ·
                refine ⟨139580168988163752249871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2977710271747493381330581 139580168988163752249871)
                ·
                  rfl

theorem cell21_1834862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 6].length) (baseStart_1834862 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1834862 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1834862 prefixEnd_1834862 := by exact prefixLift 1834862
  have htrace : WordTrace (prefixWord ++ tailWord_1834862) baseStart_1834862 baseEnd_1834862 := by
    simpa [prefixWord, tailWord_1834862, baseEnd_1834862] using wordTrace_append hprefix tailTrace_1834862
  have hstable : (prefixWord ++ tailWord_1834862).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834862).length < 2 ^ (prefixWord ++ tailWord_1834862).sum := by decide
  have hdescent : baseEnd_1834862 < baseStart_1834862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834902 : List Nat := [5, 3, 1, 1, 3, 1, 2, 2, 3]
def baseStart_1834902 : Nat := 118140960795 + 1834902 * 2 ^ 59
def prefixEnd_1834902 : Nat := 4983230072969 + 3 ^ 40 * 1834902 * 2
def baseEnd_1834902 : Nat := 418749635509460076082865

theorem tailTrace_1834902 : CollatzResearch.WordTrace tailWord_1834902 prefixEnd_1834902 418749635509460076082865 := by
  unfold tailWord_1834902
  simp only [CollatzResearch.WordTrace]
  refine ⟨4182773374904431572346685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44616249332313936771697973 4182773374904431572346685)
  ·
    refine ⟨1568540015589161839630007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4182773374904431572346685 1568540015589161839630007)
    ·
      refine ⟨2352810023383742759445011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1568540015589161839630007 2352810023383742759445011)
      ·
        refine ⟨3529215035075614139167517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2352810023383742759445011 3529215035075614139167517)
        ·
          refine ⟨1323455638153355302187819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3529215035075614139167517 1323455638153355302187819)
          ·
            refine ⟨1985183457230032953281729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1323455638153355302187819 1985183457230032953281729)
            ·
              refine ⟨1488887592922524714961297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1985183457230032953281729 1488887592922524714961297)
              ·
                refine ⟨1116665694691893536220973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1488887592922524714961297 1116665694691893536220973)
                ·
                  refine ⟨418749635509460076082865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1116665694691893536220973 418749635509460076082865)
                  ·
                    rfl

theorem cell21_1834902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_1834902 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1834902 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1834902 prefixEnd_1834902 := by exact prefixLift 1834902
  have htrace : WordTrace (prefixWord ++ tailWord_1834902) baseStart_1834902 baseEnd_1834902 := by
    simpa [prefixWord, tailWord_1834902, baseEnd_1834902] using wordTrace_append hprefix tailTrace_1834902
  have hstable : (prefixWord ++ tailWord_1834902).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834902).length < 2 ^ (prefixWord ++ tailWord_1834902).sum := by decide
  have hdescent : baseEnd_1834902 < baseStart_1834902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834980 : List Nat := [2, 3, 1, 1, 1, 1, 4, 8]
def baseStart_1834980 : Nat := 118140960795 + 1834980 * 2 ^ 59
def prefixEnd_1834980 : Nat := 4983230072969 + 3 ^ 40 * 1834980 * 2
def baseEnd_1834980 : Nat := 139589145390716424594235

theorem tailTrace_1834980 : CollatzResearch.WordTrace tailWord_1834980 prefixEnd_1834980 139589145390716424594235 := by
  unfold tailWord_1834980
  simp only [CollatzResearch.WordTrace]
  refine ⟨33463609446094162239443197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44618145928125549652590929 33463609446094162239443197)
  ·
    refine ⟨12548853542285310839791199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33463609446094162239443197 12548853542285310839791199)
    ·
      refine ⟨18823280313427966259686799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12548853542285310839791199 18823280313427966259686799)
      ·
        refine ⟨28234920470141949389530199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18823280313427966259686799 28234920470141949389530199)
        ·
          refine ⟨42352380705212924084295299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28234920470141949389530199 42352380705212924084295299)
          ·
            refine ⟨63528571057819386126442949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42352380705212924084295299 63528571057819386126442949)
            ·
              refine ⟨11911607073341134898708053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63528571057819386126442949 11911607073341134898708053)
              ·
                refine ⟨139589145390716424594235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11911607073341134898708053 139589145390716424594235)
                ·
                  rfl

theorem cell21_1834980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 8].length) (baseStart_1834980 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1834980 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1834980 prefixEnd_1834980 := by exact prefixLift 1834980
  have htrace : WordTrace (prefixWord ++ tailWord_1834980) baseStart_1834980 baseEnd_1834980 := by
    simpa [prefixWord, tailWord_1834980, baseEnd_1834980] using wordTrace_append hprefix tailTrace_1834980
  have hstable : (prefixWord ++ tailWord_1834980).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834980).length < 2 ^ (prefixWord ++ tailWord_1834980).sum := by decide
  have hdescent : baseEnd_1834980 < baseStart_1834980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835056 : List Nat := [2, 1, 1, 1, 2, 5, 2, 7]
def baseStart_1835056 : Nat := 118140960795 + 1835056 * 2 ^ 59
def prefixEnd_1835056 : Nat := 4983230072969 + 3 ^ 40 * 1835056 * 2
def baseEnd_1835056 : Nat := 139594926802530010171961

theorem tailTrace_1835056 : CollatzResearch.WordTrace tailWord_1835056 prefixEnd_1835056 139594926802530010171961 := by
  unfold tailWord_1835056
  simp only [CollatzResearch.WordTrace]
  refine ⟨33464995419956494729326511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44619993893275326305768681 33464995419956494729326511)
  ·
    refine ⟨50197493129934742093989767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33464995419956494729326511 50197493129934742093989767)
    ·
      refine ⟨75296239694902113140984651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50197493129934742093989767 75296239694902113140984651)
      ·
        refine ⟨112944359542353169711476977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75296239694902113140984651 112944359542353169711476977)
        ·
          refine ⟨84708269656764877283607733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112944359542353169711476977 84708269656764877283607733)
          ·
            refine ⟨7941400280321707245338225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84708269656764877283607733 7941400280321707245338225)
            ·
              refine ⟨5956050210241280434003669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7941400280321707245338225 5956050210241280434003669)
              ·
                refine ⟨139594926802530010171961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5956050210241280434003669 139594926802530010171961)
                ·
                  rfl

theorem cell21_1835056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 7].length) (baseStart_1835056 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1835056 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1835056 prefixEnd_1835056 := by exact prefixLift 1835056
  have htrace : WordTrace (prefixWord ++ tailWord_1835056) baseStart_1835056 baseEnd_1835056 := by
    simpa [prefixWord, tailWord_1835056, baseEnd_1835056] using wordTrace_append hprefix tailTrace_1835056
  have hstable : (prefixWord ++ tailWord_1835056).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835056).length < 2 ^ (prefixWord ++ tailWord_1835056).sum := by decide
  have hdescent : baseEnd_1835056 < baseStart_1835056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835090 : List Nat := [3, 2, 2, 1, 4, 2, 1, 6]
def baseStart_1835090 : Nat := 118140960795 + 1835090 * 2 ^ 59
def prefixEnd_1835090 : Nat := 4983230072969 + 3 ^ 40 * 1835090 * 2
def baseEnd_1835090 : Nat := 139597513223604508983049

theorem tailTrace_1835090 : CollatzResearch.WordTrace tailWord_1835090 prefixEnd_1835090 139597513223604508983049 := by
  unfold tailWord_1835090
  simp only [CollatzResearch.WordTrace]
  refine ⟨16732807730447453316347681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44620820614526542176927149 16732807730447453316347681)
  ·
    refine ⟨12549605797835589987260761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16732807730447453316347681 12549605797835589987260761)
    ·
      refine ⟨9412204348376692490445571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12549605797835589987260761 9412204348376692490445571)
      ·
        refine ⟨14118306522565038735668357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9412204348376692490445571 14118306522565038735668357)
        ·
          refine ⟨2647182472980944762937817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14118306522565038735668357 2647182472980944762937817)
          ·
            refine ⟨1985386854735708572203363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2647182472980944762937817 1985386854735708572203363)
            ·
              refine ⟨2978080282103562858305045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1985386854735708572203363 2978080282103562858305045)
              ·
                refine ⟨139597513223604508983049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2978080282103562858305045 139597513223604508983049)
                ·
                  rfl

theorem cell21_1835090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 6].length) (baseStart_1835090 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1835090 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1835090 prefixEnd_1835090 := by exact prefixLift 1835090
  have htrace : WordTrace (prefixWord ++ tailWord_1835090) baseStart_1835090 baseEnd_1835090 := by
    simpa [prefixWord, tailWord_1835090, baseEnd_1835090] using wordTrace_append hprefix tailTrace_1835090
  have hstable : (prefixWord ++ tailWord_1835090).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835090).length < 2 ^ (prefixWord ++ tailWord_1835090).sum := by decide
  have hdescent : baseEnd_1835090 < baseStart_1835090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835118 : List Nat := [4, 1, 2, 2, 1, 1, 2, 2, 6]
def baseStart_1835118 : Nat := 118140960795 + 1835118 * 2 ^ 59
def prefixEnd_1835118 : Nat := 4983230072969 + 3 ^ 40 * 1835118 * 2
def baseEnd_1835118 : Nat := 418798929652291700482423

theorem tailTrace_1835118 : CollatzResearch.WordTrace tailWord_1835118 prefixEnd_1835118 418798929652291700482423 := by
  unfold tailWord_1835118
  simp only [CollatzResearch.WordTrace]
  refine ⟨8366531520711046755926251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44621501443792249364940005 8366531520711046755926251)
  ·
    refine ⟨12549797281066570133889377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8366531520711046755926251 12549797281066570133889377)
    ·
      refine ⟨9412347960799927600417033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12549797281066570133889377 9412347960799927600417033)
      ·
        refine ⟨7059260970599945700312775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9412347960799927600417033 7059260970599945700312775)
        ·
          refine ⟨10588891455899918550469163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7059260970599945700312775 10588891455899918550469163)
          ·
            refine ⟨15883337183849877825703745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10588891455899918550469163 15883337183849877825703745)
            ·
              refine ⟨11912502887887408369277809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15883337183849877825703745 11912502887887408369277809)
              ·
                refine ⟨8934377165915556276958357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11912502887887408369277809 8934377165915556276958357)
                ·
                  refine ⟨418798929652291700482423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8934377165915556276958357 418798929652291700482423)
                  ·
                    rfl

theorem cell21_1835118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_1835118 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1835118 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1835118 prefixEnd_1835118 := by exact prefixLift 1835118
  have htrace : WordTrace (prefixWord ++ tailWord_1835118) baseStart_1835118 baseEnd_1835118 := by
    simpa [prefixWord, tailWord_1835118, baseEnd_1835118] using wordTrace_append hprefix tailTrace_1835118
  have hstable : (prefixWord ++ tailWord_1835118).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835118).length < 2 ^ (prefixWord ++ tailWord_1835118).sum := by decide
  have hdescent : baseEnd_1835118 < baseStart_1835118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835132 : List Nat := [2, 2, 2, 1, 1, 5, 8]
def baseStart_1835132 : Nat := 118140960795 + 1835132 * 2 ^ 59
def prefixEnd_1835132 : Nat := 4983230072969 + 3 ^ 40 * 1835132 * 2
def baseEnd_1835132 : Nat := 46533569404781198583229

theorem tailTrace_1835132 : CollatzResearch.WordTrace tailWord_1835132 prefixEnd_1835132 46533569404781198583229 := by
  unfold tailWord_1835132
  simp only [CollatzResearch.WordTrace]
  refine ⟨33466381393818827219209825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44621841858425102958946433 33466381393818827219209825)
  ·
    refine ⟨25099786045364120414407369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33466381393818827219209825 25099786045364120414407369)
    ·
      refine ⟨18824839534023090310805527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25099786045364120414407369 18824839534023090310805527)
      ·
        refine ⟨28237259301034635466208291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18824839534023090310805527 28237259301034635466208291)
        ·
          refine ⟨42355888951551953199312437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28237259301034635466208291 42355888951551953199312437)
          ·
            refine ⟨3970864589207995612435541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42355888951551953199312437 3970864589207995612435541)
            ·
              refine ⟨46533569404781198583229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3970864589207995612435541 46533569404781198583229)
              ·
                rfl

theorem cell21_1835132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 8].length) (baseStart_1835132 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1835132 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1835132 prefixEnd_1835132 := by exact prefixLift 1835132
  have htrace : WordTrace (prefixWord ++ tailWord_1835132) baseStart_1835132 baseEnd_1835132 := by
    simpa [prefixWord, tailWord_1835132, baseEnd_1835132] using wordTrace_append hprefix tailTrace_1835132
  have hstable : (prefixWord ++ tailWord_1835132).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835132).length < 2 ^ (prefixWord ++ tailWord_1835132).sum := by decide
  have hdescent : baseEnd_1835132 < baseStart_1835132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835158 : List Nat := [5, 3, 2, 1, 1, 2, 2, 5]
def baseStart_1835158 : Nat := 118140960795 + 1835158 * 2 ^ 59
def prefixEnd_1835158 : Nat := 4983230072969 + 3 ^ 40 * 1835158 * 2
def baseEnd_1835158 : Nat := 139602686065753506605225

theorem tailTrace_1835158 : CollatzResearch.WordTrace tailWord_1835158 prefixEnd_1835158 139602686065753506605225 := by
  unfold tailWord_1835158
  simp only [CollatzResearch.WordTrace]
  refine ⟨4183356942846466304929133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44622474057028973919244085 4183356942846466304929133)
  ·
    refine ⟨1568758853567424864348425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4183356942846466304929133 1568758853567424864348425)
    ·
      refine ⟨1176569140175568648261319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1568758853567424864348425 1176569140175568648261319)
      ·
        refine ⟨1764853710263352972391979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1176569140175568648261319 1764853710263352972391979)
        ·
          refine ⟨2647280565395029458587969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1764853710263352972391979 2647280565395029458587969)
          ·
            refine ⟨1985460424046272093940977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2647280565395029458587969 1985460424046272093940977)
            ·
              refine ⟨1489095318034704070455733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1985460424046272093940977 1489095318034704070455733)
              ·
                refine ⟨139602686065753506605225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1489095318034704070455733 139602686065753506605225)
                ·
                  rfl

theorem cell21_1835158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 2, 5].length) (baseStart_1835158 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1835158 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1835158 prefixEnd_1835158 := by exact prefixLift 1835158
  have htrace : WordTrace (prefixWord ++ tailWord_1835158) baseStart_1835158 baseEnd_1835158 := by
    simpa [prefixWord, tailWord_1835158, baseEnd_1835158] using wordTrace_append hprefix tailTrace_1835158
  have hstable : (prefixWord ++ tailWord_1835158).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835158).length < 2 ^ (prefixWord ++ tailWord_1835158).sum := by decide
  have hdescent : baseEnd_1835158 < baseStart_1835158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835166 : List Nat := [4, 3, 1, 1, 3, 1, 1, 7]
def baseStart_1835166 : Nat := 118140960795 + 1835166 * 2 ^ 59
def prefixEnd_1835166 : Nat := 4983230072969 + 3 ^ 40 * 1835166 * 2
def baseEnd_1835166 : Nat := 139603294635418094560775

theorem tailTrace_1835166 : CollatzResearch.WordTrace tailWord_1835166 prefixEnd_1835166 139603294635418094560775 := by
  unfold tailWord_1835166
  simp only [CollatzResearch.WordTrace]
  refine ⟨8366750358689309780644669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44622668579676318830104901 8366750358689309780644669)
  ·
    refine ⟨3137531384508491167741751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8366750358689309780644669 3137531384508491167741751)
    ·
      refine ⟨4706297076762736751612627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3137531384508491167741751 4706297076762736751612627)
      ·
        refine ⟨7059445615144105127418941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4706297076762736751612627 7059445615144105127418941)
        ·
          refine ⟨2647292105679039422782103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7059445615144105127418941 2647292105679039422782103)
          ·
            refine ⟨3970938158518559134173155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2647292105679039422782103 3970938158518559134173155)
            ·
              refine ⟨5956407237777838701259733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3970938158518559134173155 5956407237777838701259733)
              ·
                refine ⟨139603294635418094560775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5956407237777838701259733 139603294635418094560775)
                ·
                  rfl

theorem cell21_1835166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 7].length) (baseStart_1835166 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1835166 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1835166 prefixEnd_1835166 := by exact prefixLift 1835166
  have htrace : WordTrace (prefixWord ++ tailWord_1835166) baseStart_1835166 baseEnd_1835166 := by
    simpa [prefixWord, tailWord_1835166, baseEnd_1835166] using wordTrace_append hprefix tailTrace_1835166
  have hstable : (prefixWord ++ tailWord_1835166).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835166).length < 2 ^ (prefixWord ++ tailWord_1835166).sum := by decide
  have hdescent : baseEnd_1835166 < baseStart_1835166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835304 : List Nat := [2, 1, 5, 1, 3, 2, 1, 2, 4]
def baseStart_1835304 : Nat := 118140960795 + 1835304 * 2 ^ 59
def prefixEnd_1835304 : Nat := 4983230072969 + 3 ^ 40 * 1835304 * 2
def baseEnd_1835304 : Nat := 418841377386396710382043

theorem tailTrace_1835304 : CollatzResearch.WordTrace tailWord_1835304 prefixEnd_1835304 418841377386396710382043 := by
  unfold tailWord_1835304
  simp only [CollatzResearch.WordTrace]
  refine ⟨33469518071507263906840483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44626024095343018542453977 33469518071507263906840483)
  ·
    refine ⟨50204277107260895860260725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33469518071507263906840483 50204277107260895860260725)
    ·
      refine ⟨4706650978805708986899443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50204277107260895860260725 4706650978805708986899443)
      ·
        refine ⟨7059976468208563480349165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4706650978805708986899443 7059976468208563480349165)
        ·
          refine ⟨2647491175578211305130937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7059976468208563480349165 2647491175578211305130937)
          ·
            refine ⟨1985618381683658478848203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2647491175578211305130937 1985618381683658478848203)
            ·
              refine ⟨2978427572525487718272305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1985618381683658478848203 2978427572525487718272305)
              ·
                refine ⟨2233820679394115788704229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2978427572525487718272305 2233820679394115788704229)
                ·
                  refine ⟨418841377386396710382043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2233820679394115788704229 418841377386396710382043)
                  ·
                    rfl

theorem cell21_1835304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 2, 4].length) (baseStart_1835304 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1835304 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1835304 prefixEnd_1835304 := by exact prefixLift 1835304
  have htrace : WordTrace (prefixWord ++ tailWord_1835304) baseStart_1835304 baseEnd_1835304 := by
    simpa [prefixWord, tailWord_1835304, baseEnd_1835304] using wordTrace_append hprefix tailTrace_1835304
  have hstable : (prefixWord ++ tailWord_1835304).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835304).length < 2 ^ (prefixWord ++ tailWord_1835304).sum := by decide
  have hdescent : baseEnd_1835304 < baseStart_1835304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835315 : List Nat := [1, 1, 1, 2, 5, 1, 4, 1, 5]
def baseStart_1835315 : Nat := 118140960795 + 1835315 * 2 ^ 59
def prefixEnd_1835315 : Nat := 4983230072969 + 3 ^ 40 * 1835315 * 2
def baseEnd_1835315 : Nat := 418843887736263135698687

theorem tailTrace_1835315 : CollatzResearch.WordTrace tailWord_1835315 prefixEnd_1835315 418843887736263135698687 := by
  unfold tailWord_1835315
  simp only [CollatzResearch.WordTrace]
  refine ⟨66939437345974676692331399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44626291563983117794887599 66939437345974676692331399)
  ·
    refine ⟨100409156018962015038497099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66939437345974676692331399 100409156018962015038497099)
    ·
      refine ⟨150613734028443022557745649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100409156018962015038497099 150613734028443022557745649)
      ·
        refine ⟨112960300521332266918309237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150613734028443022557745649 112960300521332266918309237)
        ·
          refine ⟨10590028173874900023591491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 112960300521332266918309237 10590028173874900023591491)
          ·
            refine ⟨15885042260812350035387237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10590028173874900023591491 15885042260812350035387237)
            ·
              refine ⟨2978445423902315631635107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15885042260812350035387237 2978445423902315631635107)
              ·
                refine ⟨4467668135853473447452661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2978445423902315631635107 4467668135853473447452661)
                ·
                  refine ⟨418843887736263135698687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4467668135853473447452661 418843887736263135698687)
                  ·
                    rfl

theorem cell21_1835315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 1, 5].length) (baseStart_1835315 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1835315 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1835315 prefixEnd_1835315 := by exact prefixLift 1835315
  have htrace : WordTrace (prefixWord ++ tailWord_1835315) baseStart_1835315 baseEnd_1835315 := by
    simpa [prefixWord, tailWord_1835315, baseEnd_1835315] using wordTrace_append hprefix tailTrace_1835315
  have hstable : (prefixWord ++ tailWord_1835315).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835315).length < 2 ^ (prefixWord ++ tailWord_1835315).sum := by decide
  have hdescent : baseEnd_1835315 < baseStart_1835315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835414 : List Nat := [5, 3, 1, 2, 1, 1, 2, 2, 4]
def baseStart_1835414 : Nat := 118140960795 + 1835414 * 2 ^ 59
def prefixEnd_1835414 : Nat := 4983230072969 + 3 ^ 40 * 1835414 * 2
def baseEnd_1835414 : Nat := 418866480885060963548485

theorem tailTrace_1835414 : CollatzResearch.WordTrace tailWord_1835414 prefixEnd_1835414 418866480885060963548485 := by
  unfold tailWord_1835414
  simp only [CollatzResearch.WordTrace]
  refine ⟨4183940510788501037511581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44628698781744011066790197 4183940510788501037511581)
  ·
    refine ⟨1568977691545687889066843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4183940510788501037511581 1568977691545687889066843)
    ·
      refine ⟨2353466537318531833600265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1568977691545687889066843 2353466537318531833600265)
      ·
        refine ⟨1765099902988898875200199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2353466537318531833600265 1765099902988898875200199)
        ·
          refine ⟨2647649854483348312800299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1765099902988898875200199 2647649854483348312800299)
          ·
            refine ⟨3971474781725022469200449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2647649854483348312800299 3971474781725022469200449)
            ·
              refine ⟨2978606086293766851900337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3971474781725022469200449 2978606086293766851900337)
              ·
                refine ⟨2233954564720325138925253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2978606086293766851900337 2233954564720325138925253)
                ·
                  refine ⟨418866480885060963548485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2233954564720325138925253 418866480885060963548485)
                  ·
                    rfl

theorem cell21_1835414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_1835414 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1835414 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1835414 prefixEnd_1835414 := by exact prefixLift 1835414
  have htrace : WordTrace (prefixWord ++ tailWord_1835414) baseStart_1835414 baseEnd_1835414 := by
    simpa [prefixWord, tailWord_1835414, baseEnd_1835414] using wordTrace_append hprefix tailTrace_1835414
  have hstable : (prefixWord ++ tailWord_1835414).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835414).length < 2 ^ (prefixWord ++ tailWord_1835414).sum := by decide
  have hdescent : baseEnd_1835414 < baseStart_1835414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835453 : List Nat := [1, 4, 1, 2, 2, 3, 3, 5]
def baseStart_1835453 : Nat := 118140960795 + 1835453 * 2 ^ 59
def prefixEnd_1835453 : Nat := 4983230072969 + 3 ^ 40 * 1835453 * 2
def baseEnd_1835453 : Nat := 139625127072135187466135

theorem tailTrace_1835453 : CollatzResearch.WordTrace tailWord_1835453 prefixEnd_1835453 139625127072135187466135 := by
  unfold tailWord_1835453
  simp only [CollatzResearch.WordTrace]
  refine ⟨66944470619474726260855013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44629647079649817507236675 66944470619474726260855013)
  ·
    refine ⟨12552088241151511173910315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66944470619474726260855013 12552088241151511173910315)
    ·
      refine ⟨18828132361727266760865473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12552088241151511173910315 18828132361727266760865473)
      ·
        refine ⟨14121099271295450070649105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18828132361727266760865473 14121099271295450070649105)
        ·
          refine ⟨10590824453471587552986829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14121099271295450070649105 10590824453471587552986829)
          ·
            refine ⟨3971559170051845332370061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10590824453471587552986829 3971559170051845332370061)
            ·
              refine ⟨1489334688769441999638773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3971559170051845332370061 1489334688769441999638773)
              ·
                refine ⟨139625127072135187466135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1489334688769441999638773 139625127072135187466135)
                ·
                  rfl

theorem cell21_1835453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 3, 5].length) (baseStart_1835453 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1835453 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1835453 prefixEnd_1835453 := by exact prefixLift 1835453
  have htrace : WordTrace (prefixWord ++ tailWord_1835453) baseStart_1835453 baseEnd_1835453 := by
    simpa [prefixWord, tailWord_1835453, baseEnd_1835453] using wordTrace_append hprefix tailTrace_1835453
  have hstable : (prefixWord ++ tailWord_1835453).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835453).length < 2 ^ (prefixWord ++ tailWord_1835453).sum := by decide
  have hdescent : baseEnd_1835453 < baseStart_1835453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835481 : List Nat := [1, 2, 1, 2, 4, 1, 3, 1, 6]
def baseStart_1835481 : Nat := 118140960795 + 1835481 * 2 ^ 59
def prefixEnd_1835481 : Nat := 4983230072969 + 3 ^ 40 * 1835481 * 2
def baseEnd_1835481 : Nat := 418881771197883735931681

theorem tailTrace_1835481 : CollatzResearch.WordTrace tailWord_1835481 prefixEnd_1835481 418881771197883735931681 := by
  unfold tailWord_1835481
  simp only [CollatzResearch.WordTrace]
  refine ⟨66945491863373287042874297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44630327908915524695249531 66945491863373287042874297)
  ·
    refine ⟨50209118897529965282155723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66945491863373287042874297 50209118897529965282155723)
    ·
      refine ⟨75313678346294947923233585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50209118897529965282155723 75313678346294947923233585)
      ·
        refine ⟨56485258759721210942425189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75313678346294947923233585 56485258759721210942425189)
        ·
          refine ⟨10590986017447727051704723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56485258759721210942425189 10590986017447727051704723)
          ·
            refine ⟨15886479026171590577557085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10590986017447727051704723 15886479026171590577557085)
            ·
              refine ⟨5957429634814346466583907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15886479026171590577557085 5957429634814346466583907)
              ·
                refine ⟨8936144452221519699875861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5957429634814346466583907 8936144452221519699875861)
                ·
                  refine ⟨418881771197883735931681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8936144452221519699875861 418881771197883735931681)
                  ·
                    rfl

theorem cell21_1835481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 6].length) (baseStart_1835481 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1835481 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1835481 prefixEnd_1835481 := by exact prefixLift 1835481
  have htrace : WordTrace (prefixWord ++ tailWord_1835481) baseStart_1835481 baseEnd_1835481 := by
    simpa [prefixWord, tailWord_1835481, baseEnd_1835481] using wordTrace_append hprefix tailTrace_1835481
  have hstable : (prefixWord ++ tailWord_1835481).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835481).length < 2 ^ (prefixWord ++ tailWord_1835481).sum := by decide
  have hdescent : baseEnd_1835481 < baseStart_1835481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835571 : List Nat := [1, 1, 1, 2, 4, 2, 1, 9]
def baseStart_1835571 : Nat := 118140960795 + 1835571 * 2 ^ 59
def prefixEnd_1835571 : Nat := 4983230072969 + 3 ^ 40 * 1835571 * 2
def baseEnd_1835571 : Nat := 139634103474687859810499

theorem tailTrace_1835571 : CollatzResearch.WordTrace tailWord_1835571 prefixEnd_1835571 139634103474687859810499 := by
  unfold tailWord_1835571
  simp only [CollatzResearch.WordTrace]
  refine ⟨66948774433047232413650567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44632516288698154942433711 66948774433047232413650567)
  ·
    refine ⟨100423161649570848620475851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66948774433047232413650567 100423161649570848620475851)
    ·
      refine ⟨150634742474356272930713777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100423161649570848620475851 150634742474356272930713777)
      ·
        refine ⟨112976056855767204698035333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150634742474356272930713777 112976056855767204698035333)
        ·
          refine ⟨21183010660456350880881625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112976056855767204698035333 21183010660456350880881625)
          ·
            refine ⟨15887257995342263160661219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21183010660456350880881625 15887257995342263160661219)
            ·
              refine ⟨23830886993013394740991829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15887257995342263160661219 23830886993013394740991829)
              ·
                refine ⟨139634103474687859810499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23830886993013394740991829 139634103474687859810499)
                ·
                  rfl

theorem cell21_1835571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 9].length) (baseStart_1835571 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1835571 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1835571 prefixEnd_1835571 := by exact prefixLift 1835571
  have htrace : WordTrace (prefixWord ++ tailWord_1835571) baseStart_1835571 baseEnd_1835571 := by
    simpa [prefixWord, tailWord_1835571, baseEnd_1835571] using wordTrace_append hprefix tailTrace_1835571
  have hstable : (prefixWord ++ tailWord_1835571).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835571).length < 2 ^ (prefixWord ++ tailWord_1835571).sum := by decide
  have hdescent : baseEnd_1835571 < baseStart_1835571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835687 : List Nat := [1, 1, 6, 3, 2, 1, 1, 3, 3]
def baseStart_1835687 : Nat := 118140960795 + 1835687 * 2 ^ 59
def prefixEnd_1835687 : Nat := 4983230072969 + 3 ^ 40 * 1835687 * 2
def baseEnd_1835687 : Nat := 418928783204473155497927

theorem tailTrace_1835687 : CollatzResearch.WordTrace tailWord_1835687 prefixEnd_1835687 418928783204473155497927 := by
  unfold tailWord_1835687
  simp only [CollatzResearch.WordTrace]
  refine ⟨66953005300626984224873315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44635336867084656149915543 66953005300626984224873315)
  ·
    refine ⟨100429507950940476337309973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66953005300626984224873315 100429507950940476337309973)
    ·
      refine ⟨4707633185200334828311405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 100429507950940476337309973 4707633185200334828311405)
      ·
        refine ⟨1765362444450125560616777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4707633185200334828311405 1765362444450125560616777)
        ·
          refine ⟨1324021833337594170462583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1765362444450125560616777 1324021833337594170462583)
          ·
            refine ⟨1986032750006391255693875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1324021833337594170462583 1986032750006391255693875)
            ·
              refine ⟨2979049125009586883540813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1986032750006391255693875 2979049125009586883540813)
              ·
                refine ⟨1117143421878595081327805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2979049125009586883540813 1117143421878595081327805)
                ·
                  refine ⟨418928783204473155497927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1117143421878595081327805 418928783204473155497927)
                  ·
                    rfl

theorem cell21_1835687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 3, 3].length) (baseStart_1835687 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1835687 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1835687 prefixEnd_1835687 := by exact prefixLift 1835687
  have htrace : WordTrace (prefixWord ++ tailWord_1835687) baseStart_1835687 baseEnd_1835687 := by
    simpa [prefixWord, tailWord_1835687, baseEnd_1835687] using wordTrace_append hprefix tailTrace_1835687
  have hstable : (prefixWord ++ tailWord_1835687).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835687).length < 2 ^ (prefixWord ++ tailWord_1835687).sum := by decide
  have hdescent : baseEnd_1835687 < baseStart_1835687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835709 : List Nat := [1, 4, 1, 2, 1, 3, 2, 1, 6]
def baseStart_1835709 : Nat := 118140960795 + 1835709 * 2 ^ 59
def prefixEnd_1835709 : Nat := 4983230072969 + 3 ^ 40 * 1835709 * 2
def baseEnd_1835709 : Nat := 418933803904206006131215

theorem tailTrace_1835709 : CollatzResearch.WordTrace tailWord_1835709 prefixEnd_1835709 418933803904206006131215 := by
  unfold tailWord_1835709
  simp only [CollatzResearch.WordTrace]
  refine ⟨66953807706547281982174181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44635871804364854654782787 66953807706547281982174181)
  ·
    refine ⟨12553838944977615371657659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66953807706547281982174181 12553838944977615371657659)
    ·
      refine ⟨18830758417466423057486489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12553838944977615371657659 18830758417466423057486489)
      ·
        refine ⟨14123068813099817293114867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18830758417466423057486489 14123068813099817293114867)
        ·
          refine ⟨21184603219649725939672301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14123068813099817293114867 21184603219649725939672301)
          ·
            refine ⟨7944226207368647227377113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21184603219649725939672301 7944226207368647227377113)
            ·
              refine ⟨5958169655526485420532835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7944226207368647227377113 5958169655526485420532835)
              ·
                refine ⟨8937254483289728130799253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5958169655526485420532835 8937254483289728130799253)
                ·
                  refine ⟨418933803904206006131215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8937254483289728130799253 418933803904206006131215)
                  ·
                    rfl

theorem cell21_1835709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 6].length) (baseStart_1835709 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1835709 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1835709 prefixEnd_1835709 := by exact prefixLift 1835709
  have htrace : WordTrace (prefixWord ++ tailWord_1835709) baseStart_1835709 baseEnd_1835709 := by
    simpa [prefixWord, tailWord_1835709, baseEnd_1835709] using wordTrace_append hprefix tailTrace_1835709
  have hstable : (prefixWord ++ tailWord_1835709).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835709).length < 2 ^ (prefixWord ++ tailWord_1835709).sum := by decide
  have hdescent : baseEnd_1835709 < baseStart_1835709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835718 : List Nat := [6, 1, 2, 1, 2, 2, 2, 1, 4]
def baseStart_1835718 : Nat := 118140960795 + 1835718 * 2 ^ 59
def prefixEnd_1835718 : Nat := 4983230072969 + 3 ^ 40 * 1835718 * 2
def baseEnd_1835718 : Nat := 418935857826823990481197

theorem tailTrace_1835718 : CollatzResearch.WordTrace tailWord_1835718 prefixEnd_1835718 418935857826823990481197 := by
  unfold tailWord_1835718
  simp only [CollatzResearch.WordTrace]
  refine ⟨2092316748859833641226619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 44636090642343117679501205 2092316748859833641226619)
  ·
    refine ⟨3138475123289750461839929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2092316748859833641226619 3138475123289750461839929)
    ·
      refine ⟨2353856342467312846379947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3138475123289750461839929 2353856342467312846379947)
      ·
        refine ⟨3530784513700969269569921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2353856342467312846379947 3530784513700969269569921)
        ·
          refine ⟨2648088385275726952177441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3530784513700969269569921 2648088385275726952177441)
          ·
            refine ⟨1986066288956795214133081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2648088385275726952177441 1986066288956795214133081)
            ·
              refine ⟨1489549716717596410599811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1986066288956795214133081 1489549716717596410599811)
              ·
                refine ⟨2234324575076394615899717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1489549716717596410599811 2234324575076394615899717)
                ·
                  refine ⟨418935857826823990481197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2234324575076394615899717 418935857826823990481197)
                  ·
                    rfl

theorem cell21_1835718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_1835718 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1835718 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1835718 prefixEnd_1835718 := by exact prefixLift 1835718
  have htrace : WordTrace (prefixWord ++ tailWord_1835718) baseStart_1835718 baseEnd_1835718 := by
    simpa [prefixWord, tailWord_1835718, baseEnd_1835718] using wordTrace_append hprefix tailTrace_1835718
  have hstable : (prefixWord ++ tailWord_1835718).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835718).length < 2 ^ (prefixWord ++ tailWord_1835718).sum := by decide
  have hdescent : baseEnd_1835718 < baseStart_1835718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835726 : List Nat := [4, 1, 1, 1, 3, 3, 1, 3, 4]
def baseStart_1835726 : Nat := 118140960795 + 1835726 * 2 ^ 59
def prefixEnd_1835726 : Nat := 4983230072969 + 3 ^ 40 * 1835726 * 2
def baseEnd_1835726 : Nat := 418937683535817754347847

theorem tailTrace_1835726 : CollatzResearch.WordTrace tailWord_1835726 prefixEnd_1835726 418937683535817754347847 := by
  unfold tailWord_1835726
  simp only [CollatzResearch.WordTrace]
  refine ⟨8369303468435711735692879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44636285164990462590362021 8369303468435711735692879)
  ·
    refine ⟨12553955202653567603539319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8369303468435711735692879 12553955202653567603539319)
    ·
      refine ⟨18830932803980351405308979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12553955202653567603539319 18830932803980351405308979)
      ·
        refine ⟨28246399205970527107963469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18830932803980351405308979 28246399205970527107963469)
        ·
          refine ⟨10592399702238947665486301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28246399205970527107963469 10592399702238947665486301)
          ·
            refine ⟨3972149888339605374557363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10592399702238947665486301 3972149888339605374557363)
            ·
              refine ⟨5958224832509408061836045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3972149888339605374557363 5958224832509408061836045)
              ·
                refine ⟨2234334312191028023188517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5958224832509408061836045 2234334312191028023188517)
                ·
                  refine ⟨418937683535817754347847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2234334312191028023188517 418937683535817754347847)
                  ·
                    rfl

theorem cell21_1835726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 3, 4].length) (baseStart_1835726 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1835726 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1835726 prefixEnd_1835726 := by exact prefixLift 1835726
  have htrace : WordTrace (prefixWord ++ tailWord_1835726) baseStart_1835726 baseEnd_1835726 := by
    simpa [prefixWord, tailWord_1835726, baseEnd_1835726] using wordTrace_append hprefix tailTrace_1835726
  have hstable : (prefixWord ++ tailWord_1835726).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835726).length < 2 ^ (prefixWord ++ tailWord_1835726).sum := by decide
  have hdescent : baseEnd_1835726 < baseStart_1835726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835785 : List Nat := [1, 2, 1, 1, 3, 2, 4, 3, 4]
def baseStart_1835785 : Nat := 118140960795 + 1835785 * 2 ^ 59
def prefixEnd_1835785 : Nat := 4983230072969 + 3 ^ 40 * 1835785 * 2
def baseEnd_1835785 : Nat := 418951148139646762864393

theorem tailTrace_1835785 : CollatzResearch.WordTrace tailWord_1835785 prefixEnd_1835785 418951148139646762864393 := by
  unfold tailWord_1835785
  simp only [CollatzResearch.WordTrace]
  refine ⟨66956579654271946961940809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44637719769514631307960539 66956579654271946961940809)
  ·
    refine ⟨50217434740703960221455607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66956579654271946961940809 50217434740703960221455607)
    ·
      refine ⟨75326152111055940332183411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50217434740703960221455607 75326152111055940332183411)
      ·
        refine ⟨112989228166583910498275117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75326152111055940332183411 112989228166583910498275117)
        ·
          refine ⟨42370960562468966436853169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112989228166583910498275117 42370960562468966436853169)
          ·
            refine ⟨31778220421851724827639877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42370960562468966436853169 31778220421851724827639877)
            ·
              refine ⟨5958416329097198405182477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31778220421851724827639877 5958416329097198405182477)
              ·
                refine ⟨2234406123411449401943429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5958416329097198405182477 2234406123411449401943429)
                ·
                  refine ⟨418951148139646762864393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2234406123411449401943429 418951148139646762864393)
                  ·
                    rfl

theorem cell21_1835785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 3, 4].length) (baseStart_1835785 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1835785 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1835785 prefixEnd_1835785 := by exact prefixLift 1835785
  have htrace : WordTrace (prefixWord ++ tailWord_1835785) baseStart_1835785 baseEnd_1835785 := by
    simpa [prefixWord, tailWord_1835785, baseEnd_1835785] using wordTrace_append hprefix tailTrace_1835785
  have hstable : (prefixWord ++ tailWord_1835785).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835785).length < 2 ^ (prefixWord ++ tailWord_1835785).sum := by decide
  have hdescent : baseEnd_1835785 < baseStart_1835785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835875 : List Nat := [1, 1, 1, 5, 3, 1, 9]
def baseStart_1835875 : Nat := 118140960795 + 1835875 * 2 ^ 59
def prefixEnd_1835875 : Nat := 4983230072969 + 3 ^ 40 * 1835875 * 2
def baseEnd_1835875 : Nat := 46552409707314067373801

theorem tailTrace_1835875 : CollatzResearch.WordTrace tailWord_1835875 prefixEnd_1835875 46552409707314067373801 := by
  unfold tailWord_1835875
  simp only [CollatzResearch.WordTrace]
  refine ⟨66959862223945892332717079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44639908149297261555144719 66959862223945892332717079)
  ·
    refine ⟨100439793335918838499075619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66959862223945892332717079 100439793335918838499075619)
    ·
      refine ⟨150659690003878257748613429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100439793335918838499075619 150659690003878257748613429)
      ·
        refine ⟨14124345937863586663932509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 150659690003878257748613429 14124345937863586663932509)
        ·
          refine ⟨5296629726698844998974691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14124345937863586663932509 5296629726698844998974691)
          ·
            refine ⟨7944944590048267498462037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5296629726698844998974691 7944944590048267498462037)
            ·
              refine ⟨46552409707314067373801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7944944590048267498462037 46552409707314067373801)
              ·
                rfl

theorem cell21_1835875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 9].length) (baseStart_1835875 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1835875 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1835875 prefixEnd_1835875 := by exact prefixLift 1835875
  have htrace : WordTrace (prefixWord ++ tailWord_1835875) baseStart_1835875 baseEnd_1835875 := by
    simpa [prefixWord, tailWord_1835875, baseEnd_1835875] using wordTrace_append hprefix tailTrace_1835875
  have hstable : (prefixWord ++ tailWord_1835875).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835875).length < 2 ^ (prefixWord ++ tailWord_1835875).sum := by decide
  have hdescent : baseEnd_1835875 < baseStart_1835875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835968 : List Nat := [2, 1, 1, 2, 3, 4, 3, 5]
def baseStart_1835968 : Nat := 118140960795 + 1835968 * 2 ^ 59
def prefixEnd_1835968 : Nat := 4983230072969 + 3 ^ 40 * 1835968 * 2
def baseEnd_1835968 : Nat := 139664303744293037104673

theorem tailTrace_1835968 : CollatzResearch.WordTrace tailWord_1835968 prefixEnd_1835968 139664303744293037104673 := by
  unfold tailWord_1835968
  simp only [CollatzResearch.WordTrace]
  refine ⟨33481627106304484607926279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44642169475072646143901705 33481627106304484607926279)
  ·
    refine ⟨50222440659456726911889419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33481627106304484607926279 50222440659456726911889419)
    ·
      refine ⟨75333660989185090367834129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50222440659456726911889419 75333660989185090367834129)
      ·
        refine ⟨56500245741888817775875597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75333660989185090367834129 56500245741888817775875597)
        ·
          refine ⟨21187592153208306665953349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56500245741888817775875597 21187592153208306665953349)
          ·
            refine ⟨3972673528726557499866253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21187592153208306665953349 3972673528726557499866253)
            ·
              refine ⟨1489752573272459062449845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3972673528726557499866253 1489752573272459062449845)
              ·
                refine ⟨139664303744293037104673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1489752573272459062449845 139664303744293037104673)
                ·
                  rfl

theorem cell21_1835968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 3, 5].length) (baseStart_1835968 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1835968 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1835968 prefixEnd_1835968 := by exact prefixLift 1835968
  have htrace : WordTrace (prefixWord ++ tailWord_1835968) baseStart_1835968 baseEnd_1835968 := by
    simpa [prefixWord, tailWord_1835968, baseEnd_1835968] using wordTrace_append hprefix tailTrace_1835968
  have hstable : (prefixWord ++ tailWord_1835968).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835968).length < 2 ^ (prefixWord ++ tailWord_1835968).sum := by decide
  have hdescent : baseEnd_1835968 < baseStart_1835968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835999 : List Nat := [1, 1, 2, 3, 5, 1, 2, 1, 5]
def baseStart_1835999 : Nat := 118140960795 + 1835999 * 2 ^ 59
def prefixEnd_1835999 : Nat := 4983230072969 + 3 ^ 40 * 1835999 * 2
def baseEnd_1835999 : Nat := 418999985855229946297289

theorem tailTrace_1835999 : CollatzResearch.WordTrace tailWord_1835999 prefixEnd_1835999 418999985855229946297289 := by
  unfold tailWord_1835999
  simp only [CollatzResearch.WordTrace]
  refine ⟨66964384875496661510231051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44642923250331107673487367 66964384875496661510231051)
  ·
    refine ⟨100446577313244992265346577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66964384875496661510231051 100446577313244992265346577)
    ·
      refine ⟨75334932984933744199009933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100446577313244992265346577 75334932984933744199009933)
      ·
        refine ⟨28250599869350154074628725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75334932984933744199009933 28250599869350154074628725)
        ·
          refine ⟨2648493737751576944496443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28250599869350154074628725 2648493737751576944496443)
          ·
            refine ⟨3972740606627365416744665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2648493737751576944496443 3972740606627365416744665)
            ·
              refine ⟨2979555454970524062558499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3972740606627365416744665 2979555454970524062558499)
              ·
                refine ⟨4469333182455786093837749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2979555454970524062558499 4469333182455786093837749)
                ·
                  refine ⟨418999985855229946297289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4469333182455786093837749 418999985855229946297289)
                  ·
                    rfl

theorem cell21_1835999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 1, 5].length) (baseStart_1835999 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1835999 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1835999 prefixEnd_1835999 := by exact prefixLift 1835999
  have htrace : WordTrace (prefixWord ++ tailWord_1835999) baseStart_1835999 baseEnd_1835999 := by
    simpa [prefixWord, tailWord_1835999, baseEnd_1835999] using wordTrace_append hprefix tailTrace_1835999
  have hstable : (prefixWord ++ tailWord_1835999).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835999).length < 2 ^ (prefixWord ++ tailWord_1835999).sum := by decide
  have hdescent : baseEnd_1835999 < baseStart_1835999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836041 : List Nat := [1, 2, 1, 1, 3, 1, 1, 4, 7]
def baseStart_1836041 : Nat := 118140960795 + 1836041 * 2 ^ 59
def prefixEnd_1836041 : Nat := 4983230072969 + 3 ^ 40 * 1836041 * 2
def baseEnd_1836041 : Nat := 419009570827447206597203

theorem tailTrace_1836041 : CollatzResearch.WordTrace tailWord_1836041 prefixEnd_1836041 419009570827447206597203 := by
  unfold tailWord_1836041
  simp only [CollatzResearch.WordTrace]
  refine ⟨66965916741344502683259977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44643944494229668455506651 66965916741344502683259977)
  ·
    refine ⟨50224437556008377012444983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66965916741344502683259977 50224437556008377012444983)
    ·
      refine ⟨75336656334012565518667475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50224437556008377012444983 75336656334012565518667475)
      ·
        refine ⟨113004984501018848278001213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75336656334012565518667475 113004984501018848278001213)
        ·
          refine ⟨42376869187882068104250455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113004984501018848278001213 42376869187882068104250455)
          ·
            refine ⟨63565303781823102156375683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42376869187882068104250455 63565303781823102156375683)
            ·
              refine ⟨95347955672734653234563525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63565303781823102156375683 95347955672734653234563525)
              ·
                refine ⟨17877741688637747481480661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95347955672734653234563525 17877741688637747481480661)
                ·
                  refine ⟨419009570827447206597203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17877741688637747481480661 419009570827447206597203)
                  ·
                    rfl

theorem cell21_1836041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 7].length) (baseStart_1836041 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1836041 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1836041 prefixEnd_1836041 := by exact prefixLift 1836041
  have htrace : WordTrace (prefixWord ++ tailWord_1836041) baseStart_1836041 baseEnd_1836041 := by
    simpa [prefixWord, tailWord_1836041, baseEnd_1836041] using wordTrace_append hprefix tailTrace_1836041
  have hstable : (prefixWord ++ tailWord_1836041).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836041).length < 2 ^ (prefixWord ++ tailWord_1836041).sum := by decide
  have hdescent : baseEnd_1836041 < baseStart_1836041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836050 : List Nat := [3, 2, 5, 1, 1, 2, 1, 1, 5]
def baseStart_1836050 : Nat := 118140960795 + 1836050 * 2 ^ 59
def prefixEnd_1836050 : Nat := 4983230072969 + 3 ^ 40 * 1836050 * 2
def baseEnd_1836050 : Nat := 419011624750065190947185

theorem tailTrace_1836050 : CollatzResearch.WordTrace tailWord_1836050 prefixEnd_1836050 419011624750065190947185 := by
  unfold tailWord_1836050
  simp only [CollatzResearch.WordTrace]
  refine ⟨16741561249577974305084401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44644163332207931480225069 16741561249577974305084401)
  ·
    refine ⟨12556170937183480728813301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16741561249577974305084401 12556170937183480728813301)
    ·
      refine ⟨1177141025360951318326247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12556170937183480728813301 1177141025360951318326247)
      ·
        refine ⟨1765711538041426977489371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1177141025360951318326247 1765711538041426977489371)
        ·
          refine ⟨2648567307062140466234057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1765711538041426977489371 2648567307062140466234057)
          ·
            refine ⟨1986425480296605349675543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2648567307062140466234057 1986425480296605349675543)
            ·
              refine ⟨2979638220444908024513315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1986425480296605349675543 2979638220444908024513315)
              ·
                refine ⟨4469457330667362036769973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2979638220444908024513315 4469457330667362036769973)
                ·
                  refine ⟨419011624750065190947185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4469457330667362036769973 419011624750065190947185)
                  ·
                    rfl

theorem cell21_1836050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 1, 5].length) (baseStart_1836050 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1836050 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1836050 prefixEnd_1836050 := by exact prefixLift 1836050
  have htrace : WordTrace (prefixWord ++ tailWord_1836050) baseStart_1836050 baseEnd_1836050 := by
    simpa [prefixWord, tailWord_1836050, baseEnd_1836050] using wordTrace_append hprefix tailTrace_1836050
  have hstable : (prefixWord ++ tailWord_1836050).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836050).length < 2 ^ (prefixWord ++ tailWord_1836050).sum := by decide
  have hdescent : baseEnd_1836050 < baseStart_1836050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836064 : List Nat := [2, 1, 1, 7, 1, 2, 2, 1, 4]
def baseStart_1836064 : Nat := 118140960795 + 1836064 * 2 ^ 59
def prefixEnd_1836064 : Nat := 4983230072969 + 3 ^ 40 * 1836064 * 2
def baseEnd_1836064 : Nat := 419014819740804277713823

theorem tailTrace_1836064 : CollatzResearch.WordTrace tailWord_1836064 prefixEnd_1836064 419014819740804277713823 := by
  unfold tailWord_1836064
  simp only [CollatzResearch.WordTrace]
  refine ⟨33483377810130588805673623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44644503746840785074231497 33483377810130588805673623)
  ·
    refine ⟨50225066715195883208510435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33483377810130588805673623 50225066715195883208510435)
    ·
      refine ⟨75337600072793824812765653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50225066715195883208510435 75337600072793824812765653)
      ·
        refine ⟨1765725001706105269049195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 75337600072793824812765653 1765725001706105269049195)
        ·
          refine ⟨2648587502559157903573793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1765725001706105269049195 2648587502559157903573793)
          ·
            refine ⟨1986440626919368427680345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2648587502559157903573793 1986440626919368427680345)
            ·
              refine ⟨1489830470189526320760259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1986440626919368427680345 1489830470189526320760259)
              ·
                refine ⟨2234745705284289481140389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1489830470189526320760259 2234745705284289481140389)
                ·
                  refine ⟨419014819740804277713823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2234745705284289481140389 419014819740804277713823)
                  ·
                    rfl

theorem cell21_1836064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 2, 1, 4].length) (baseStart_1836064 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1836064 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1836064 prefixEnd_1836064 := by exact prefixLift 1836064
  have htrace : WordTrace (prefixWord ++ tailWord_1836064) baseStart_1836064 baseEnd_1836064 := by
    simpa [prefixWord, tailWord_1836064, baseEnd_1836064] using wordTrace_append hprefix tailTrace_1836064
  have hstable : (prefixWord ++ tailWord_1836064).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836064).length < 2 ^ (prefixWord ++ tailWord_1836064).sum := by decide
  have hdescent : baseEnd_1836064 < baseStart_1836064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836109 : List Nat := [1, 6, 1, 1, 1, 2, 4, 2, 3]
def baseStart_1836109 : Nat := 118140960795 + 1836109 * 2 ^ 59
def prefixEnd_1836109 : Nat := 4983230072969 + 3 ^ 40 * 1836109 * 2
def baseEnd_1836109 : Nat := 419025089353894199463731

theorem tailTrace_1836109 : CollatzResearch.WordTrace tailWord_1836109 prefixEnd_1836109 419025089353894199463731 := by
  unfold tailWord_1836109
  simp only [CollatzResearch.WordTrace]
  refine ⟨66968396905098150296735381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44645597936732100197823587 66968396905098150296735381)
  ·
    refine ⟨3139143604926475795159471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 66968396905098150296735381 3139143604926475795159471)
    ·
      refine ⟨4708715407389713692739207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3139143604926475795159471 4708715407389713692739207)
      ·
        refine ⟨7063073111084570539108811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4708715407389713692739207 7063073111084570539108811)
        ·
          refine ⟨10594609666626855808663217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7063073111084570539108811 10594609666626855808663217)
          ·
            refine ⟨7945957249970141856497413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10594609666626855808663217 7945957249970141856497413)
            ·
              refine ⟨1489866984369401598093265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7945957249970141856497413 1489866984369401598093265)
              ·
                refine ⟨1117400238277051198569949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1489866984369401598093265 1117400238277051198569949)
                ·
                  refine ⟨419025089353894199463731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1117400238277051198569949 419025089353894199463731)
                  ·
                    rfl

theorem cell21_1836109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_1836109 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1836109 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1836109 prefixEnd_1836109 := by exact prefixLift 1836109
  have htrace : WordTrace (prefixWord ++ tailWord_1836109) baseStart_1836109 baseEnd_1836109 := by
    simpa [prefixWord, tailWord_1836109, baseEnd_1836109] using wordTrace_append hprefix tailTrace_1836109
  have hstable : (prefixWord ++ tailWord_1836109).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836109).length < 2 ^ (prefixWord ++ tailWord_1836109).sum := by decide
  have hdescent : baseEnd_1836109 < baseStart_1836109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836151 : List Nat := [1, 1, 3, 1, 1, 4, 4, 3, 3]
def baseStart_1836151 : Nat := 118140960795 + 1836151 * 2 ^ 59
def prefixEnd_1836151 : Nat := 4983230072969 + 3 ^ 40 * 1836151 * 2
def baseEnd_1836151 : Nat := 419034674326111459763645

theorem tailTrace_1836151 : CollatzResearch.WordTrace tailWord_1836151 prefixEnd_1836151 419034674326111459763645 := by
  unfold tailWord_1836151
  simp only [CollatzResearch.WordTrace]
  refine ⟨66969928770945991469764307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44646619180630660979842871 66969928770945991469764307)
  ·
    refine ⟨100454893156418987204646461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66969928770945991469764307 100454893156418987204646461)
    ·
      refine ⟨37670584933657120201742423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100454893156418987204646461 37670584933657120201742423)
      ·
        refine ⟨56505877400485680302613635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37670584933657120201742423 56505877400485680302613635)
        ·
          refine ⟨84758816100728520453920453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56505877400485680302613635 84758816100728520453920453)
          ·
            refine ⟨15892278018886597585110085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84758816100728520453920453 15892278018886597585110085)
            ·
              refine ⟨2979802128541237047208141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15892278018886597585110085 2979802128541237047208141)
              ·
                refine ⟨1117425798202963892703053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2979802128541237047208141 1117425798202963892703053)
                ·
                  refine ⟨419034674326111459763645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1117425798202963892703053 419034674326111459763645)
                  ·
                    rfl

theorem cell21_1836151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 3, 3].length) (baseStart_1836151 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1836151 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1836151 prefixEnd_1836151 := by exact prefixLift 1836151
  have htrace : WordTrace (prefixWord ++ tailWord_1836151) baseStart_1836151 baseEnd_1836151 := by
    simpa [prefixWord, tailWord_1836151, baseEnd_1836151] using wordTrace_append hprefix tailTrace_1836151
  have hstable : (prefixWord ++ tailWord_1836151).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836151).length < 2 ^ (prefixWord ++ tailWord_1836151).sum := by decide
  have hdescent : baseEnd_1836151 < baseStart_1836151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836165 : List Nat := [1, 3, 1, 1, 6, 1, 1, 1, 6]
def baseStart_1836165 : Nat := 118140960795 + 1836165 * 2 ^ 59
def prefixEnd_1836165 : Nat := 4983230072969 + 3 ^ 40 * 1836165 * 2
def baseEnd_1836165 : Nat := 419037869316850546530283

theorem tailTrace_1836165 : CollatzResearch.WordTrace tailWord_1836165 prefixEnd_1836165 419037869316850546530283 := by
  unfold tailWord_1836165
  simp only [CollatzResearch.WordTrace]
  refine ⟨66970439392895271860773949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44646959595263514573849299 66970439392895271860773949)
  ·
    refine ⟨25113914772335726947790231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66970439392895271860773949 25113914772335726947790231)
    ·
      refine ⟨37670872158503590421685347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25113914772335726947790231 37670872158503590421685347)
      ·
        refine ⟨56506308237755385632528021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37670872158503590421685347 56506308237755385632528021)
        ·
          refine ⟨2648733198644783701524751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 56506308237755385632528021 2648733198644783701524751)
          ·
            refine ⟨3973099797967175552287127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2648733198644783701524751 3973099797967175552287127)
            ·
              refine ⟨5959649696950763328430691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3973099797967175552287127 5959649696950763328430691)
              ·
                refine ⟨8939474545426144992646037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5959649696950763328430691 8939474545426144992646037)
                ·
                  refine ⟨419037869316850546530283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8939474545426144992646037 419037869316850546530283)
                  ·
                    rfl

theorem cell21_1836165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 6].length) (baseStart_1836165 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1836165 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1836165 prefixEnd_1836165 := by exact prefixLift 1836165
  have htrace : WordTrace (prefixWord ++ tailWord_1836165) baseStart_1836165 baseEnd_1836165 := by
    simpa [prefixWord, tailWord_1836165, baseEnd_1836165] using wordTrace_append hprefix tailTrace_1836165
  have hstable : (prefixWord ++ tailWord_1836165).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836165).length < 2 ^ (prefixWord ++ tailWord_1836165).sum := by decide
  have hdescent : baseEnd_1836165 < baseStart_1836165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836196 : List Nat := [2, 3, 1, 2, 3, 1, 4, 5]
def baseStart_1836196 : Nat := 118140960795 + 1836196 * 2 ^ 59
def prefixEnd_1836196 : Nat := 4983230072969 + 3 ^ 40 * 1836196 * 2
def baseEnd_1836196 : Nat := 139681647979733793837851

theorem tailTrace_1836196 : CollatzResearch.WordTrace tailWord_1836196 prefixEnd_1836196 139681647979733793837851 := by
  unfold tailWord_1836196
  simp only [CollatzResearch.WordTrace]
  refine ⟨33485785027891482077576221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44647713370521976103434961 33485785027891482077576221)
  ·
    refine ⟨12557169385459305779091083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33485785027891482077576221 12557169385459305779091083)
    ·
      refine ⟨18835754078188958668636625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12557169385459305779091083 18835754078188958668636625)
      ·
        refine ⟨14126815558641719001477469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18835754078188958668636625 14126815558641719001477469)
        ·
          refine ⟨5297555834490644625554051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14126815558641719001477469 5297555834490644625554051)
          ·
            refine ⟨7946333751735966938331077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5297555834490644625554051 7946333751735966938331077)
            ·
              refine ⟨1489937578450493800937077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7946333751735966938331077 1489937578450493800937077)
              ·
                refine ⟨139681647979733793837851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1489937578450493800937077 139681647979733793837851)
                ·
                  rfl

theorem cell21_1836196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 4, 5].length) (baseStart_1836196 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1836196 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1836196 prefixEnd_1836196 := by exact prefixLift 1836196
  have htrace : WordTrace (prefixWord ++ tailWord_1836196) baseStart_1836196 baseEnd_1836196 := by
    simpa [prefixWord, tailWord_1836196, baseEnd_1836196] using wordTrace_append hprefix tailTrace_1836196
  have hstable : (prefixWord ++ tailWord_1836196).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836196).length < 2 ^ (prefixWord ++ tailWord_1836196).sum := by decide
  have hdescent : baseEnd_1836196 < baseStart_1836196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836306 : List Nat := [3, 2, 4, 2, 1, 1, 3, 5]
def baseStart_1836306 : Nat := 118140960795 + 1836306 * 2 ^ 59
def prefixEnd_1836306 : Nat := 4983230072969 + 3 ^ 40 * 1836306 * 2
def baseEnd_1836306 : Nat := 139690015812621878226665

theorem tailTrace_1836306 : CollatzResearch.WordTrace tailWord_1836306 prefixEnd_1836306 139690015812621878226665 := by
  unfold tailWord_1836306
  simp only [CollatzResearch.WordTrace]
  refine ⟨16743895521346113235414193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44650388056922968627771181 16743895521346113235414193)
  ·
    refine ⟨12557921641009584926560645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16743895521346113235414193 12557921641009584926560645)
    ·
      refine ⟨2354610307689297173730121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12557921641009584926560645 2354610307689297173730121)
      ·
        refine ⟨1765957730766972880297591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2354610307689297173730121 1765957730766972880297591)
        ·
          refine ⟨2648936596150459320446387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1765957730766972880297591 2648936596150459320446387)
          ·
            refine ⟨3973404894225688980669581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2648936596150459320446387 3973404894225688980669581)
            ·
              refine ⟨1490026835334633367751093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3973404894225688980669581 1490026835334633367751093)
              ·
                refine ⟨139690015812621878226665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1490026835334633367751093 139690015812621878226665)
                ·
                  rfl

theorem cell21_1836306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 3, 5].length) (baseStart_1836306 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1836306 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1836306 prefixEnd_1836306 := by exact prefixLift 1836306
  have htrace : WordTrace (prefixWord ++ tailWord_1836306) baseStart_1836306 baseEnd_1836306 := by
    simpa [prefixWord, tailWord_1836306, baseEnd_1836306] using wordTrace_append hprefix tailTrace_1836306
  have hstable : (prefixWord ++ tailWord_1836306).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836306).length < 2 ^ (prefixWord ++ tailWord_1836306).sum := by decide
  have hdescent : baseEnd_1836306 < baseStart_1836306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836320 : List Nat := [2, 1, 1, 5, 3, 1, 2, 3, 3]
def baseStart_1836320 : Nat := 118140960795 + 1836320 * 2 ^ 59
def prefixEnd_1836320 : Nat := 4983230072969 + 3 ^ 40 * 1836320 * 2
def baseEnd_1836320 : Nat := 419073242428604721446633

theorem tailTrace_1836320 : CollatzResearch.WordTrace tailWord_1836320 prefixEnd_1836320 419073242428604721446633 := by
  unfold tailWord_1836320
  simp only [CollatzResearch.WordTrace]
  refine ⟨33488046353666866666333207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44650728471555822221777609 33488046353666866666333207)
  ·
    refine ⟨50232069530500299999499811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33488046353666866666333207 50232069530500299999499811)
    ·
      refine ⟨75348104295750449999249717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50232069530500299999499811 75348104295750449999249717)
      ·
        refine ⟨7063884777726604687429661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75348104295750449999249717 7063884777726604687429661)
        ·
          refine ⟨2648956791647476757786123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7063884777726604687429661 2648956791647476757786123)
          ·
            refine ⟨3973435187471215136679185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2648956791647476757786123 3973435187471215136679185)
            ·
              refine ⟨2980076390603411352509389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3973435187471215136679185 2980076390603411352509389)
              ·
                refine ⟨1117528646476279257191021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2980076390603411352509389 1117528646476279257191021)
                ·
                  refine ⟨419073242428604721446633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1117528646476279257191021 419073242428604721446633)
                  ·
                    rfl

theorem cell21_1836320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 3, 3].length) (baseStart_1836320 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1836320 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1836320 prefixEnd_1836320 := by exact prefixLift 1836320
  have htrace : WordTrace (prefixWord ++ tailWord_1836320) baseStart_1836320 baseEnd_1836320 := by
    simpa [prefixWord, tailWord_1836320, baseEnd_1836320] using wordTrace_append hprefix tailTrace_1836320
  have hstable : (prefixWord ++ tailWord_1836320).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836320).length < 2 ^ (prefixWord ++ tailWord_1836320).sum := by decide
  have hdescent : baseEnd_1836320 < baseStart_1836320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836365 : List Nat := [1, 6, 1, 3, 1, 1, 1, 7]
def baseStart_1836365 : Nat := 118140960795 + 1836365 * 2 ^ 59
def prefixEnd_1836365 : Nat := 4983230072969 + 3 ^ 40 * 1836365 * 2
def baseEnd_1836365 : Nat := 139694504013898214398847

theorem tailTrace_1836365 : CollatzResearch.WordTrace tailWord_1836365 prefixEnd_1836365 139694504013898214398847 := by
  unfold tailWord_1836365
  simp only [CollatzResearch.WordTrace]
  refine ⟨66977733992170706018054549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44651822661447137345369699 66977733992170706018054549)
  ·
    refine ⟨3139581280883001844596307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 66977733992170706018054549 3139581280883001844596307)
    ·
      refine ⟨4709371921324502766894461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3139581280883001844596307 4709371921324502766894461)
      ·
        refine ⟨1766014470496688537585423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4709371921324502766894461 1766014470496688537585423)
        ·
          refine ⟨2649021705745032806378135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1766014470496688537585423 2649021705745032806378135)
          ·
            refine ⟨3973532558617549209567203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2649021705745032806378135 3973532558617549209567203)
            ·
              refine ⟨5960298837926323814350805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3973532558617549209567203 5960298837926323814350805)
              ·
                refine ⟨139694504013898214398847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5960298837926323814350805 139694504013898214398847)
                ·
                  rfl

theorem cell21_1836365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 7].length) (baseStart_1836365 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1836365 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1836365 prefixEnd_1836365 := by exact prefixLift 1836365
  have htrace : WordTrace (prefixWord ++ tailWord_1836365) baseStart_1836365 baseEnd_1836365 := by
    simpa [prefixWord, tailWord_1836365, baseEnd_1836365] using wordTrace_append hprefix tailTrace_1836365
  have hstable : (prefixWord ++ tailWord_1836365).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836365).length < 2 ^ (prefixWord ++ tailWord_1836365).sum := by decide
  have hdescent : baseEnd_1836365 < baseStart_1836365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836396 : List Nat := [2, 2, 1, 1, 5, 2, 3, 2, 3]
def baseStart_1836396 : Nat := 118140960795 + 1836396 * 2 ^ 59
def prefixEnd_1836396 : Nat := 4983230072969 + 3 ^ 40 * 1836396 * 2
def baseEnd_1836396 : Nat := 419090586664045478179811

theorem tailTrace_1836396 : CollatzResearch.WordTrace tailWord_1836396 prefixEnd_1836396 419090586664045478179811 := by
  unfold tailWord_1836396
  simp only [CollatzResearch.WordTrace]
  refine ⟨33489432327529199156216521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44652576436705598874955361 33489432327529199156216521)
  ·
    refine ⟨25117074245646899367162391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33489432327529199156216521 25117074245646899367162391)
    ·
      refine ⟨37675611368470349050743587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25117074245646899367162391 37675611368470349050743587)
      ·
        refine ⟨56513417052705523576115381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37675611368470349050743587 56513417052705523576115381)
        ·
          refine ⟨5298132848691142835260817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56513417052705523576115381 5298132848691142835260817)
          ·
            refine ⟨3973599636518357126445613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5298132848691142835260817 3973599636518357126445613)
            ·
              refine ⟨1490099863694383922417105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3973599636518357126445613 1490099863694383922417105)
              ·
                refine ⟨1117574897770787941812829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1490099863694383922417105 1117574897770787941812829)
                ·
                  refine ⟨419090586664045478179811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1117574897770787941812829 419090586664045478179811)
                  ·
                    rfl

theorem cell21_1836396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 3, 2, 3].length) (baseStart_1836396 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1836396 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1836396 prefixEnd_1836396 := by exact prefixLift 1836396
  have htrace : WordTrace (prefixWord ++ tailWord_1836396) baseStart_1836396 baseEnd_1836396 := by
    simpa [prefixWord, tailWord_1836396, baseEnd_1836396] using wordTrace_append hprefix tailTrace_1836396
  have hstable : (prefixWord ++ tailWord_1836396).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836396).length < 2 ^ (prefixWord ++ tailWord_1836396).sum := by decide
  have hdescent : baseEnd_1836396 < baseStart_1836396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836421 : List Nat := [1, 3, 1, 1, 3, 1, 2, 4, 5]
def baseStart_1836421 : Nat := 118140960795 + 1836421 * 2 ^ 59
def prefixEnd_1836421 : Nat := 4983230072969 + 3 ^ 40 * 1836421 * 2
def baseEnd_1836421 : Nat := 419096292004650990263093

theorem tailTrace_1836421 : CollatzResearch.WordTrace tailWord_1836421 prefixEnd_1836421 419096292004650990263093 := by
  unfold tailWord_1836421
  simp only [CollatzResearch.WordTrace]
  refine ⟨66979776479967827582093117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44653184319978551721395411 66979776479967827582093117)
  ·
    refine ⟨25117416179987935343284919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66979776479967827582093117 25117416179987935343284919)
    ·
      refine ⟨37676124269981903014927379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25117416179987935343284919 37676124269981903014927379)
      ·
        refine ⟨56514186404972854522391069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37676124269981903014927379 56514186404972854522391069)
        ·
          refine ⟨21192819901864820445896651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56514186404972854522391069 21192819901864820445896651)
          ·
            refine ⟨31789229852797230668844977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21192819901864820445896651 31789229852797230668844977)
            ·
              refine ⟨23841922389597923001633733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31789229852797230668844977 23841922389597923001633733)
              ·
                refine ⟨4470360448049610562806325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23841922389597923001633733 4470360448049610562806325)
                ·
                  refine ⟨419096292004650990263093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4470360448049610562806325 419096292004650990263093)
                  ·
                    rfl

theorem cell21_1836421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 4, 5].length) (baseStart_1836421 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1836421 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1836421 prefixEnd_1836421 := by exact prefixLift 1836421
  have htrace : WordTrace (prefixWord ++ tailWord_1836421) baseStart_1836421 baseEnd_1836421 := by
    simpa [prefixWord, tailWord_1836421, baseEnd_1836421] using wordTrace_append hprefix tailTrace_1836421
  have hstable : (prefixWord ++ tailWord_1836421).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836421).length < 2 ^ (prefixWord ++ tailWord_1836421).sum := by decide
  have hdescent : baseEnd_1836421 < baseStart_1836421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836455 : List Nat := [1, 1, 6, 1, 1, 1, 3, 4, 3]
def baseStart_1836455 : Nat := 118140960795 + 1836455 * 2 ^ 59
def prefixEnd_1836455 : Nat := 4983230072969 + 3 ^ 40 * 1836455 * 2
def baseEnd_1836455 : Nat := 419104051267874486696357

theorem tailTrace_1836455 : CollatzResearch.WordTrace tailWord_1836455 prefixEnd_1836455 419104051267874486696357 := by
  unfold tailWord_1836455
  simp only [CollatzResearch.WordTrace]
  refine ⟨66981016561844651388830819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44654011041229767592553879 66981016561844651388830819)
  ·
    refine ⟨100471524842766977083246229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66981016561844651388830819 100471524842766977083246229)
    ·
      refine ⟨4709602727004702050777167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 100471524842766977083246229 4709602727004702050777167)
      ·
        refine ⟨7064404090507053076165751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4709602727004702050777167 7064404090507053076165751)
        ·
          refine ⟨10596606135760579614248627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7064404090507053076165751 10596606135760579614248627)
          ·
            refine ⟨15894909203640869421372941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10596606135760579614248627 15894909203640869421372941)
            ·
              refine ⟨5960590951365326033014853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15894909203640869421372941 5960590951365326033014853)
              ·
                refine ⟨1117610803380998631190285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5960590951365326033014853 1117610803380998631190285)
                ·
                  refine ⟨419104051267874486696357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1117610803380998631190285 419104051267874486696357)
                  ·
                    rfl

theorem cell21_1836455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 4, 3].length) (baseStart_1836455 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1836455 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1836455 prefixEnd_1836455 := by exact prefixLift 1836455
  have htrace : WordTrace (prefixWord ++ tailWord_1836455) baseStart_1836455 baseEnd_1836455 := by
    simpa [prefixWord, tailWord_1836455, baseEnd_1836455] using wordTrace_append hprefix tailTrace_1836455
  have hstable : (prefixWord ++ tailWord_1836455).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836455).length < 2 ^ (prefixWord ++ tailWord_1836455).sum := by decide
  have hdescent : baseEnd_1836455 < baseStart_1836455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836466 : List Nat := [3, 2, 1, 1, 1, 1, 2, 10]
def baseStart_1836466 : Nat := 118140960795 + 1836466 * 2 ^ 59
def prefixEnd_1836466 : Nat := 4983230072969 + 3 ^ 40 * 1836466 * 2
def baseEnd_1836466 : Nat := 139702187205913637337667

theorem tailTrace_1836466 : CollatzResearch.WordTrace tailWord_1836466 prefixEnd_1836466 139702187205913637337667 := by
  unfold tailWord_1836466
  simp only [CollatzResearch.WordTrace]
  refine ⟨16745354441201200066870313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44654278509869866844987501 16745354441201200066870313)
  ·
    refine ⟨12559015830900900050152735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16745354441201200066870313 12559015830900900050152735)
    ·
      refine ⟨18838523746351350075229103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12559015830900900050152735 18838523746351350075229103)
      ·
        refine ⟨28257785619527025112843655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18838523746351350075229103 28257785619527025112843655)
        ·
          refine ⟨42386678429290537669265483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28257785619527025112843655 42386678429290537669265483)
          ·
            refine ⟨63580017643935806503898225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42386678429290537669265483 63580017643935806503898225)
            ·
              refine ⟨47685013232951854877923669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63580017643935806503898225 47685013232951854877923669)
              ·
                refine ⟨139702187205913637337667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 47685013232951854877923669 139702187205913637337667)
                ·
                  rfl

theorem cell21_1836466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 10].length) (baseStart_1836466 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1836466 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1836466 prefixEnd_1836466 := by exact prefixLift 1836466
  have htrace : WordTrace (prefixWord ++ tailWord_1836466) baseStart_1836466 baseEnd_1836466 := by
    simpa [prefixWord, tailWord_1836466, baseEnd_1836466] using wordTrace_append hprefix tailTrace_1836466
  have hstable : (prefixWord ++ tailWord_1836466).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836466).length < 2 ^ (prefixWord ++ tailWord_1836466).sum := by decide
  have hdescent : baseEnd_1836466 < baseStart_1836466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836469 : List Nat := [1, 3, 3, 2, 2, 1, 2, 3, 4]
def baseStart_1836469 : Nat := 118140960795 + 1836469 * 2 ^ 59
def prefixEnd_1836469 : Nat := 4983230072969 + 3 ^ 40 * 1836469 * 2
def baseEnd_1836469 : Nat := 419107246258613573462995

theorem tailTrace_1836469 : CollatzResearch.WordTrace tailWord_1836469 prefixEnd_1836469 419107246258613573462995 := by
  unfold tailWord_1836469
  simp only [CollatzResearch.WordTrace]
  refine ⟨66981527183793931779840461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44654351455862621186560307 66981527183793931779840461)
  ·
    refine ⟨25118072693922724417440173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66981527183793931779840461 25118072693922724417440173)
    ·
      refine ⟨9419277260221021656540065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25118072693922724417440173 9419277260221021656540065)
      ·
        refine ⟨7064457945165766242405049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9419277260221021656540065 7064457945165766242405049)
        ·
          refine ⟨5298343458874324681803787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7064457945165766242405049 5298343458874324681803787)
          ·
            refine ⟨7947515188311487022705681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5298343458874324681803787 7947515188311487022705681)
            ·
              refine ⟨5960636391233615267029261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7947515188311487022705681 5960636391233615267029261)
              ·
                refine ⟨2235238646712605725135973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5960636391233615267029261 2235238646712605725135973)
                ·
                  refine ⟨419107246258613573462995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2235238646712605725135973 419107246258613573462995)
                  ·
                    rfl

theorem cell21_1836469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 3, 4].length) (baseStart_1836469 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1836469 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1836469 prefixEnd_1836469 := by exact prefixLift 1836469
  have htrace : WordTrace (prefixWord ++ tailWord_1836469) baseStart_1836469 baseEnd_1836469 := by
    simpa [prefixWord, tailWord_1836469, baseEnd_1836469] using wordTrace_append hprefix tailTrace_1836469
  have hstable : (prefixWord ++ tailWord_1836469).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836469).length < 2 ^ (prefixWord ++ tailWord_1836469).sum := by decide
  have hdescent : baseEnd_1836469 < baseStart_1836469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836579 : List Nat := [1, 1, 1, 4, 6, 1, 2, 1, 4]
def baseStart_1836579 : Nat := 118140960795 + 1836579 * 2 ^ 59
def prefixEnd_1836579 : Nat := 4983230072969 + 3 ^ 40 * 1836579 * 2
def baseEnd_1836579 : Nat := 419132349757277826629437

theorem tailTrace_1836579 : CollatzResearch.WordTrace tailWord_1836579 prefixEnd_1836579 419132349757277826629437 := by
  unfold tailWord_1836579
  simp only [CollatzResearch.WordTrace]
  refine ⟨66985539213395420566344791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44657026142263613710896527 66985539213395420566344791)
  ·
    refine ⟨100478308820093130849517187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66985539213395420566344791 100478308820093130849517187)
    ·
      refine ⟨150717463230139696274275781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100478308820093130849517187 150717463230139696274275781)
      ·
        refine ⟨28259524355651193051426709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150717463230139696274275781 28259524355651193051426709)
        ·
          refine ⟨1324665204171149674285627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 28259524355651193051426709 1324665204171149674285627)
          ·
            refine ⟨1986997806256724511428441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1324665204171149674285627 1986997806256724511428441)
            ·
              refine ⟨1490248354692543383571331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1986997806256724511428441 1490248354692543383571331)
              ·
                refine ⟨2235372532038815075356997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1490248354692543383571331 2235372532038815075356997)
                ·
                  refine ⟨419132349757277826629437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2235372532038815075356997 419132349757277826629437)
                  ·
                    rfl

theorem cell21_1836579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 2, 1, 4].length) (baseStart_1836579 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1836579 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1836579 prefixEnd_1836579 := by exact prefixLift 1836579
  have htrace : WordTrace (prefixWord ++ tailWord_1836579) baseStart_1836579 baseEnd_1836579 := by
    simpa [prefixWord, tailWord_1836579, baseEnd_1836579] using wordTrace_append hprefix tailTrace_1836579
  have hstable : (prefixWord ++ tailWord_1836579).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836579).length < 2 ^ (prefixWord ++ tailWord_1836579).sum := by decide
  have hdescent : baseEnd_1836579 < baseStart_1836579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836663 : List Nat := [1, 1, 3, 1, 1, 3, 1, 4, 6]
def baseStart_1836663 : Nat := 118140960795 + 1836663 * 2 ^ 59
def prefixEnd_1836663 : Nat := 4983230072969 + 3 ^ 40 * 1836663 * 2
def baseEnd_1836663 : Nat := 419151519701712347229265

theorem tailTrace_1836663 : CollatzResearch.WordTrace tailWord_1836663 prefixEnd_1836663 419151519701712347229265 := by
  unfold tailWord_1836663
  simp only [CollatzResearch.WordTrace]
  refine ⟨66988602945091102912402643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44659068630060735274935095 66988602945091102912402643)
  ·
    refine ⟨100482904417636654368603965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66988602945091102912402643 100482904417636654368603965)
    ·
      refine ⟨37681089156613745388226487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100482904417636654368603965 37681089156613745388226487)
      ·
        refine ⟨56521633734920618082339731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37681089156613745388226487 56521633734920618082339731)
        ·
          refine ⟨84782450602380927123509597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56521633734920618082339731 84782450602380927123509597)
          ·
            refine ⟨31793418975892847671316099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84782450602380927123509597 31793418975892847671316099)
            ·
              refine ⟨47690128463839271506974149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31793418975892847671316099 47690128463839271506974149)
              ·
                refine ⟨8941899086969863407557653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47690128463839271506974149 8941899086969863407557653)
                ·
                  refine ⟨419151519701712347229265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8941899086969863407557653 419151519701712347229265)
                  ·
                    rfl

theorem cell21_1836663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 6].length) (baseStart_1836663 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1836663 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1836663 prefixEnd_1836663 := by exact prefixLift 1836663
  have htrace : WordTrace (prefixWord ++ tailWord_1836663) baseStart_1836663 baseEnd_1836663 := by
    simpa [prefixWord, tailWord_1836663, baseEnd_1836663] using wordTrace_append hprefix tailTrace_1836663
  have hstable : (prefixWord ++ tailWord_1836663).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836663).length < 2 ^ (prefixWord ++ tailWord_1836663).sum := by decide
  have hdescent : baseEnd_1836663 < baseStart_1836663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836784 : List Nat := [2, 1, 1, 1, 3, 1, 2, 1, 9]
def baseStart_1836784 : Nat := 118140960795 + 1836784 * 2 ^ 59
def prefixEnd_1836784 : Nat := 4983230072969 + 3 ^ 40 * 1836784 * 2
def baseEnd_1836784 : Nat := 419179133550243025712351

theorem tailTrace_1836784 : CollatzResearch.WordTrace tailWord_1836784 prefixEnd_1836784 419179133550243025712351 := by
  unfold tailWord_1836784
  simp only [CollatzResearch.WordTrace]
  refine ⟨33496508088826370288778703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44662010785101827051704937 33496508088826370288778703)
  ·
    refine ⟨50244762133239555433168055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33496508088826370288778703 50244762133239555433168055)
    ·
      refine ⟨75367143199859333149752083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50244762133239555433168055 75367143199859333149752083)
      ·
        refine ⟨113050714799788999724628125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75367143199859333149752083 113050714799788999724628125)
        ·
          refine ⟨42394018049920874896735547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113050714799788999724628125 42394018049920874896735547)
          ·
            refine ⟨63591027074881312345103321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42394018049920874896735547 63591027074881312345103321)
            ·
              refine ⟨47693270306160984258827491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63591027074881312345103321 47693270306160984258827491)
              ·
                refine ⟨71539905459241476388241237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47693270306160984258827491 71539905459241476388241237)
                ·
                  refine ⟨419179133550243025712351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 71539905459241476388241237 419179133550243025712351)
                  ·
                    rfl

theorem cell21_1836784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 9].length) (baseStart_1836784 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1836784 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1836784 prefixEnd_1836784 := by exact prefixLift 1836784
  have htrace : WordTrace (prefixWord ++ tailWord_1836784) baseStart_1836784 baseEnd_1836784 := by
    simpa [prefixWord, tailWord_1836784, baseEnd_1836784] using wordTrace_append hprefix tailTrace_1836784
  have hstable : (prefixWord ++ tailWord_1836784).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836784).length < 2 ^ (prefixWord ++ tailWord_1836784).sum := by decide
  have hdescent : baseEnd_1836784 < baseStart_1836784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836818 : List Nat := [3, 2, 4, 1, 1, 1, 1, 1, 7]
def baseStart_1836818 : Nat := 118140960795 + 1836818 * 2 ^ 59
def prefixEnd_1836818 : Nat := 4983230072969 + 3 ^ 40 * 1836818 * 2
def baseEnd_1836818 : Nat := 419186892813466522145615

theorem tailTrace_1836818 : CollatzResearch.WordTrace tailWord_1836818 prefixEnd_1836818 419186892813466522145615 := by
  unfold tailWord_1836818
  simp only [CollatzResearch.WordTrace]
  refine ⟨16748564064882391096073777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44662837506353042922863405 16748564064882391096073777)
  ·
    refine ⟨12561423048661793322055333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16748564064882391096073777 12561423048661793322055333)
    ·
      refine ⟨2355266821624086247885375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12561423048661793322055333 2355266821624086247885375)
      ·
        refine ⟨3532900232436129371828063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2355266821624086247885375 3532900232436129371828063)
        ·
          refine ⟨5299350348654194057742095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3532900232436129371828063 5299350348654194057742095)
          ·
            refine ⟨7949025522981291086613143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5299350348654194057742095 7949025522981291086613143)
            ·
              refine ⟨11923538284471936629919715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7949025522981291086613143 11923538284471936629919715)
              ·
                refine ⟨17885307426707904944879573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11923538284471936629919715 17885307426707904944879573)
                ·
                  refine ⟨419186892813466522145615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17885307426707904944879573 419186892813466522145615)
                  ·
                    rfl

theorem cell21_1836818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 7].length) (baseStart_1836818 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1836818 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1836818 prefixEnd_1836818 := by exact prefixLift 1836818
  have htrace : WordTrace (prefixWord ++ tailWord_1836818) baseStart_1836818 baseEnd_1836818 := by
    simpa [prefixWord, tailWord_1836818, baseEnd_1836818] using wordTrace_append hprefix tailTrace_1836818
  have hstable : (prefixWord ++ tailWord_1836818).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836818).length < 2 ^ (prefixWord ++ tailWord_1836818).sum := by decide
  have hdescent : baseEnd_1836818 < baseStart_1836818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836849 : List Nat := [1, 2, 2, 3, 2, 4, 1, 2, 4]
def baseStart_1836849 : Nat := 118140960795 + 1836849 * 2 ^ 59
def prefixEnd_1836849 : Nat := 4983230072969 + 3 ^ 40 * 1836849 * 2
def baseEnd_1836849 : Nat := 419193967435817357128885

theorem tailTrace_1836849 : CollatzResearch.WordTrace tailWord_1836849 prefixEnd_1836849 419193967435817357128885 := by
  unfold tailWord_1836849
  simp only [CollatzResearch.WordTrace]
  refine ⟨66995386922417256678673601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44663591281611504452449067 66995386922417256678673601)
  ·
    refine ⟨50246540191812942509005201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66995386922417256678673601 50246540191812942509005201)
    ·
      refine ⟨37684905143859706881753901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50246540191812942509005201 37684905143859706881753901)
      ·
        refine ⟨14131839428947390080657713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37684905143859706881753901 14131839428947390080657713)
        ·
          refine ⟨10598879571710542560493285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14131839428947390080657713 10598879571710542560493285)
          ·
            refine ⟨1987289919695726730092491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10598879571710542560493285 1987289919695726730092491)
            ·
              refine ⟨2980934879543590095138737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1987289919695726730092491 2980934879543590095138737)
              ·
                refine ⟨2235701159657692571354053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2980934879543590095138737 2235701159657692571354053)
                ·
                  refine ⟨419193967435817357128885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2235701159657692571354053 419193967435817357128885)
                  ·
                    rfl

theorem cell21_1836849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 2, 4].length) (baseStart_1836849 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1836849 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1836849 prefixEnd_1836849 := by exact prefixLift 1836849
  have htrace : WordTrace (prefixWord ++ tailWord_1836849) baseStart_1836849 baseEnd_1836849 := by
    simpa [prefixWord, tailWord_1836849, baseEnd_1836849] using wordTrace_append hprefix tailTrace_1836849
  have hstable : (prefixWord ++ tailWord_1836849).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836849).length < 2 ^ (prefixWord ++ tailWord_1836849).sum := by decide
  have hdescent : baseEnd_1836849 < baseStart_1836849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837018 : List Nat := [3, 1, 1, 2, 6, 1, 1, 2, 4]
def baseStart_1837018 : Nat := 118140960795 + 1837018 * 2 ^ 59
def prefixEnd_1837018 : Nat := 4983230072969 + 3 ^ 40 * 1837018 * 2
def baseEnd_1837018 : Nat := 419232535538310618811873

theorem tailTrace_1837018 : CollatzResearch.WordTrace tailWord_1837018 prefixEnd_1837018 419232535538310618811873 := by
  unfold tailWord_1837018
  simp only [CollatzResearch.WordTrace]
  refine ⟨16750387714701249635393927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44667700572536665694383805 16750387714701249635393927)
  ·
    refine ⟨25125581572051874453090891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16750387714701249635393927 25125581572051874453090891)
    ·
      refine ⟨37688372358077811679636337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25125581572051874453090891 37688372358077811679636337)
      ·
        refine ⟨28266279268558358759727253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37688372358077811679636337 28266279268558358759727253)
        ·
          refine ⟨1324981840713673066862215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 28266279268558358759727253 1324981840713673066862215)
          ·
            refine ⟨1987472761070509600293323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1324981840713673066862215 1987472761070509600293323)
            ·
              refine ⟨2981209141605764400439985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1987472761070509600293323 2981209141605764400439985)
              ·
                refine ⟨2235906856204323300329989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2981209141605764400439985 2235906856204323300329989)
                ·
                  refine ⟨419232535538310618811873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2235906856204323300329989 419232535538310618811873)
                  ·
                    rfl

theorem cell21_1837018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 2, 4].length) (baseStart_1837018 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1837018 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1837018 prefixEnd_1837018 := by exact prefixLift 1837018
  have htrace : WordTrace (prefixWord ++ tailWord_1837018) baseStart_1837018 baseEnd_1837018 := by
    simpa [prefixWord, tailWord_1837018, baseEnd_1837018] using wordTrace_append hprefix tailTrace_1837018
  have hstable : (prefixWord ++ tailWord_1837018).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837018).length < 2 ^ (prefixWord ++ tailWord_1837018).sum := by decide
  have hdescent : baseEnd_1837018 < baseStart_1837018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837043 : List Nat := [1, 1, 1, 2, 2, 2, 1, 7, 4]
def baseStart_1837043 : Nat := 118140960795 + 1837043 * 2 ^ 59
def prefixEnd_1837043 : Nat := 4983230072969 + 3 ^ 40 * 1837043 * 2
def baseEnd_1837043 : Nat := 419238240878916130895155

theorem tailTrace_1837043 : CollatzResearch.WordTrace tailWord_1837043 prefixEnd_1837043 419238240878916130895155 := by
  unfold tailWord_1837043
  simp only [CollatzResearch.WordTrace]
  refine ⟨67002462683714427811235783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44668308455809618540823855 67002462683714427811235783)
  ·
    refine ⟨100503694025571641716853675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67002462683714427811235783 100503694025571641716853675)
    ·
      refine ⟨150755541038357462575280513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100503694025571641716853675 150755541038357462575280513)
      ·
        refine ⟨113066655778768096931460385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150755541038357462575280513 113066655778768096931460385)
        ·
          refine ⟨84799991834076072698595289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113066655778768096931460385 84799991834076072698595289)
          ·
            refine ⟨63599993875557054523946467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84799991834076072698595289 63599993875557054523946467)
            ·
              refine ⟨95399990813335581785919701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63599993875557054523946467 95399990813335581785919701)
              ·
                refine ⟨2235937284687552698107493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 95399990813335581785919701 2235937284687552698107493)
                ·
                  refine ⟨419238240878916130895155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2235937284687552698107493 419238240878916130895155)
                  ·
                    rfl

theorem cell21_1837043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 7, 4].length) (baseStart_1837043 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1837043 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1837043 prefixEnd_1837043 := by exact prefixLift 1837043
  have htrace : WordTrace (prefixWord ++ tailWord_1837043) baseStart_1837043 baseEnd_1837043 := by
    simpa [prefixWord, tailWord_1837043, baseEnd_1837043] using wordTrace_append hprefix tailTrace_1837043
  have hstable : (prefixWord ++ tailWord_1837043).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837043).length < 2 ^ (prefixWord ++ tailWord_1837043).sum := by decide
  have hdescent : baseEnd_1837043 < baseStart_1837043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837063 : List Nat := [1, 1, 4, 3, 1, 4, 1, 3, 3]
def baseStart_1837063 : Nat := 118140960795 + 1837063 * 2 ^ 59
def prefixEnd_1837063 : Nat := 4983230072969 + 3 ^ 40 * 1837063 * 2
def baseEnd_1837063 : Nat := 419242805151400540561781

theorem tailTrace_1837063 : CollatzResearch.WordTrace tailWord_1837063 prefixEnd_1837063 419242805151400540561781 := by
  unfold tailWord_1837063
  simp only [CollatzResearch.WordTrace]
  refine ⟨67003192143641971226963843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44668794762427980817975895 67003192143641971226963843)
  ·
    refine ⟨100504788215462956840445765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67003192143641971226963843 100504788215462956840445765)
    ·
      refine ⟨18844647790399304407583581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100504788215462956840445765 18844647790399304407583581)
      ·
        refine ⟨7066742921399739152843843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18844647790399304407583581 7066742921399739152843843)
        ·
          refine ⟨10600114382099608729265765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7066742921399739152843843 10600114382099608729265765)
          ·
            refine ⟨1987521446643676636737331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10600114382099608729265765 1987521446643676636737331)
            ·
              refine ⟨2981282169965514955105997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1987521446643676636737331 2981282169965514955105997)
              ·
                refine ⟨1117980813737068108164749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2981282169965514955105997 1117980813737068108164749)
                ·
                  refine ⟨419242805151400540561781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1117980813737068108164749 419242805151400540561781)
                  ·
                    rfl

theorem cell21_1837063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 3, 3].length) (baseStart_1837063 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1837063 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1837063 prefixEnd_1837063 := by exact prefixLift 1837063
  have htrace : WordTrace (prefixWord ++ tailWord_1837063) baseStart_1837063 baseEnd_1837063 := by
    simpa [prefixWord, tailWord_1837063, baseEnd_1837063] using wordTrace_append hprefix tailTrace_1837063
  have hstable : (prefixWord ++ tailWord_1837063).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837063).length < 2 ^ (prefixWord ++ tailWord_1837063).sum := by decide
  have hdescent : baseEnd_1837063 < baseStart_1837063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837164 : List Nat := [2, 2, 1, 1, 3, 3, 1, 1, 7]
def baseStart_1837164 : Nat := 118140960795 + 1837164 * 2 ^ 59
def prefixEnd_1837164 : Nat := 4983230072969 + 3 ^ 40 * 1837164 * 2
def baseEnd_1837164 : Nat := 419265854727446809378241

theorem tailTrace_1837164 : CollatzResearch.WordTrace tailWord_1837164 prefixEnd_1837164 419265854727446809378241 := by
  unfold tailWord_1837164
  simp only [CollatzResearch.WordTrace]
  refine ⟨33503437958138032738195273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44671250610850710317593697 33503437958138032738195273)
  ·
    refine ⟨25127578468603524553646455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33503437958138032738195273 25127578468603524553646455)
    ·
      refine ⟨37691367702905286830469683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25127578468603524553646455 37691367702905286830469683)
      ·
        refine ⟨56537051554357930245704525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37691367702905286830469683 56537051554357930245704525)
        ·
          refine ⟨21201394332884223842139197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56537051554357930245704525 21201394332884223842139197)
          ·
            refine ⟨7950522874831583940802199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21201394332884223842139197 7950522874831583940802199)
            ·
              refine ⟨11925784312247375911203299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7950522874831583940802199 11925784312247375911203299)
              ·
                refine ⟨17888676468371063866804949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11925784312247375911203299 17888676468371063866804949)
                ·
                  refine ⟨419265854727446809378241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17888676468371063866804949 419265854727446809378241)
                  ·
                    rfl

theorem cell21_1837164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 7].length) (baseStart_1837164 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1837164 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1837164 prefixEnd_1837164 := by exact prefixLift 1837164
  have htrace : WordTrace (prefixWord ++ tailWord_1837164) baseStart_1837164 baseEnd_1837164 := by
    simpa [prefixWord, tailWord_1837164, baseEnd_1837164] using wordTrace_append hprefix tailTrace_1837164
  have hstable : (prefixWord ++ tailWord_1837164).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837164).length < 2 ^ (prefixWord ++ tailWord_1837164).sum := by decide
  have hdescent : baseEnd_1837164 < baseStart_1837164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837198 : List Nat := [4, 1, 1, 3, 3, 1, 2, 1, 5]
def baseStart_1837198 : Nat := 118140960795 + 1837198 * 2 ^ 59
def prefixEnd_1837198 : Nat := 4983230072969 + 3 ^ 40 * 1837198 * 2
def baseEnd_1837198 : Nat := 419273613990670305811505

theorem tailTrace_1837198 : CollatzResearch.WordTrace tailWord_1837198 prefixEnd_1837198 419273613990670305811505 := by
  unfold tailWord_1837198
  simp only [CollatzResearch.WordTrace]
  refine ⟨8376014499769111160391031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44672077332101926188752165 8376014499769111160391031)
  ·
    refine ⟨12564021749653666740586547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8376014499769111160391031 12564021749653666740586547)
    ·
      refine ⟨18846032624480500110879821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12564021749653666740586547 18846032624480500110879821)
      ·
        refine ⟨7067262234180187541579933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18846032624480500110879821 7067262234180187541579933)
        ·
          refine ⟨2650223337817570328092475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7067262234180187541579933 2650223337817570328092475)
          ·
            refine ⟨3975335006726355492138713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2650223337817570328092475 3975335006726355492138713)
            ·
              refine ⟨2981501255044766619104035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3975335006726355492138713 2981501255044766619104035)
              ·
                refine ⟨4472251882567149928656053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2981501255044766619104035 4472251882567149928656053)
                ·
                  refine ⟨419273613990670305811505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4472251882567149928656053 419273613990670305811505)
                  ·
                    rfl

theorem cell21_1837198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 1, 5].length) (baseStart_1837198 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1837198 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1837198 prefixEnd_1837198 := by exact prefixLift 1837198
  have htrace : WordTrace (prefixWord ++ tailWord_1837198) baseStart_1837198 baseEnd_1837198 := by
    simpa [prefixWord, tailWord_1837198, baseEnd_1837198] using wordTrace_append hprefix tailTrace_1837198
  have hstable : (prefixWord ++ tailWord_1837198).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837198).length < 2 ^ (prefixWord ++ tailWord_1837198).sum := by decide
  have hdescent : baseEnd_1837198 < baseStart_1837198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837364 : List Nat := [2, 5, 1, 1, 1, 3, 1, 1, 6]
def baseStart_1837364 : Nat := 118140960795 + 1837364 * 2 ^ 59
def prefixEnd_1837364 : Nat := 4983230072969 + 3 ^ 40 * 1837364 * 2
def baseEnd_1837364 : Nat := 419311497452290906044499

theorem tailTrace_1837364 : CollatzResearch.WordTrace tailWord_1837364 prefixEnd_1837364 419311497452290906044499 := by
  unfold tailWord_1837364
  simp only [CollatzResearch.WordTrace]
  refine ⟨33507085257775749816835573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44676113677034333089114097 33507085257775749816835573)
  ·
    refine ⟨3141289242916476545328335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33507085257775749816835573 3141289242916476545328335)
    ·
      refine ⟨4711933864374714817992503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3141289242916476545328335 4711933864374714817992503)
      ·
        refine ⟨7067900796562072226988755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4711933864374714817992503 7067900796562072226988755)
        ·
          refine ⟨10601851194843108340483133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7067900796562072226988755 10601851194843108340483133)
          ·
            refine ⟨3975694198066165627681175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10601851194843108340483133 3975694198066165627681175)
            ·
              refine ⟨5963541297099248441521763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3975694198066165627681175 5963541297099248441521763)
              ·
                refine ⟨8945311945648872662282645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5963541297099248441521763 8945311945648872662282645)
                ·
                  refine ⟨419311497452290906044499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8945311945648872662282645 419311497452290906044499)
                  ·
                    rfl

theorem cell21_1837364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_1837364 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1837364 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1837364 prefixEnd_1837364 := by exact prefixLift 1837364
  have htrace : WordTrace (prefixWord ++ tailWord_1837364) baseStart_1837364 baseEnd_1837364 := by
    simpa [prefixWord, tailWord_1837364, baseEnd_1837364] using wordTrace_append hprefix tailTrace_1837364
  have hstable : (prefixWord ++ tailWord_1837364).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837364).length < 2 ^ (prefixWord ++ tailWord_1837364).sum := by decide
  have hdescent : baseEnd_1837364 < baseStart_1837364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837392 : List Nat := [2, 1, 1, 1, 1, 6, 2, 2, 5]
def baseStart_1837392 : Nat := 118140960795 + 1837392 * 2 ^ 59
def prefixEnd_1837392 : Nat := 4983230072969 + 3 ^ 40 * 1837392 * 2
def baseEnd_1837392 : Nat := 419317887433769079577775

theorem tailTrace_1837392 : CollatzResearch.WordTrace tailWord_1837392 prefixEnd_1837392 419317887433769079577775 := by
  unfold tailWord_1837392
  simp only [CollatzResearch.WordTrace]
  refine ⟨33507595879725030207845215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44676794506300040277126953 33507595879725030207845215)
  ·
    refine ⟨50261393819587545311767823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33507595879725030207845215 50261393819587545311767823)
    ·
      refine ⟨75392090729381317967651735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50261393819587545311767823 75392090729381317967651735)
      ·
        refine ⟨113088136094071976951477603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75392090729381317967651735 113088136094071976951477603)
        ·
          refine ⟨169632204141107965427216405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113088136094071976951477603 169632204141107965427216405)
          ·
            refine ⟨7951509569114435879400769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 169632204141107965427216405 7951509569114435879400769)
            ·
              refine ⟨5963632176835826909550577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7951509569114435879400769 5963632176835826909550577)
              ·
                refine ⟨4472724132626870182162933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5963632176835826909550577 4472724132626870182162933)
                ·
                  refine ⟨419317887433769079577775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4472724132626870182162933 419317887433769079577775)
                  ·
                    rfl

theorem cell21_1837392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 2, 5].length) (baseStart_1837392 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1837392 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1837392 prefixEnd_1837392 := by exact prefixLift 1837392
  have htrace : WordTrace (prefixWord ++ tailWord_1837392) baseStart_1837392 baseEnd_1837392 := by
    simpa [prefixWord, tailWord_1837392, baseEnd_1837392] using wordTrace_append hprefix tailTrace_1837392
  have hstable : (prefixWord ++ tailWord_1837392).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837392).length < 2 ^ (prefixWord ++ tailWord_1837392).sum := by decide
  have hdescent : baseEnd_1837392 < baseStart_1837392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837437 : List Nat := [1, 4, 1, 1, 2, 3, 1, 8]
def baseStart_1837437 : Nat := 118140960795 + 1837437 * 2 ^ 59
def prefixEnd_1837437 : Nat := 4983230072969 + 3 ^ 40 * 1837437 * 2
def baseEnd_1837437 : Nat := 139776052348953000442561

theorem tailTrace_1837437 : CollatzResearch.WordTrace tailWord_1837437 prefixEnd_1837437 139776052348953000442561 := by
  unfold tailWord_1837437
  simp only [CollatzResearch.WordTrace]
  refine ⟨67016833044287033101078565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44677888696191355400719043 67016833044287033101078565)
  ·
    refine ⟨12565656195803818706452231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67016833044287033101078565 12565656195803818706452231)
    ·
      refine ⟨18848484293705728059678347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12565656195803818706452231 18848484293705728059678347)
      ·
        refine ⟨28272726440558592089517521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18848484293705728059678347 28272726440558592089517521)
        ·
          refine ⟨21204544830418944067138141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28272726440558592089517521 21204544830418944067138141)
          ·
            refine ⟨7951704311407104025176803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21204544830418944067138141 7951704311407104025176803)
            ·
              refine ⟨11927556467110656037765205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7951704311407104025176803 11927556467110656037765205)
              ·
                refine ⟨139776052348953000442561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11927556467110656037765205 139776052348953000442561)
                ·
                  rfl

theorem cell21_1837437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 8].length) (baseStart_1837437 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1837437 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1837437 prefixEnd_1837437 := by exact prefixLift 1837437
  have htrace : WordTrace (prefixWord ++ tailWord_1837437) baseStart_1837437 baseEnd_1837437 := by
    simpa [prefixWord, tailWord_1837437, baseEnd_1837437] using wordTrace_append hprefix tailTrace_1837437
  have hstable : (prefixWord ++ tailWord_1837437).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837437).length < 2 ^ (prefixWord ++ tailWord_1837437).sum := by decide
  have hdescent : baseEnd_1837437 < baseStart_1837437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837454 : List Nat := [4, 1, 1, 4, 1, 1, 2, 7]
def baseStart_1837454 : Nat := 118140960795 + 1837454 * 2 ^ 59
def prefixEnd_1837454 : Nat := 4983230072969 + 3 ^ 40 * 1837454 * 2
def baseEnd_1837454 : Nat := 139777345559490249848105

theorem tailTrace_1837454 : CollatzResearch.WordTrace tailWord_1837454 prefixEnd_1837454 139777345559490249848105 := by
  unfold tailWord_1837454
  simp only [CollatzResearch.WordTrace]
  refine ⟨8377181635653180625555927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44678302056816963336298277 8377181635653180625555927)
  ·
    refine ⟨12565772453479770938333891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8377181635653180625555927 12565772453479770938333891)
    ·
      refine ⟨18848658680219656407500837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12565772453479770938333891 18848658680219656407500837)
      ·
        refine ⟨3534123502541185576406407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18848658680219656407500837 3534123502541185576406407)
        ·
          refine ⟨5301185253811778364609611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3534123502541185576406407 5301185253811778364609611)
          ·
            refine ⟨7951777880717667546914417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5301185253811778364609611 7951777880717667546914417)
            ·
              refine ⟨5963833410538250660185813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7951777880717667546914417 5963833410538250660185813)
              ·
                refine ⟨139777345559490249848105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5963833410538250660185813 139777345559490249848105)
                ·
                  rfl

theorem cell21_1837454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 7].length) (baseStart_1837454 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1837454 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1837454 prefixEnd_1837454 := by exact prefixLift 1837454
  have htrace : WordTrace (prefixWord ++ tailWord_1837454) baseStart_1837454 baseEnd_1837454 := by
    simpa [prefixWord, tailWord_1837454, baseEnd_1837454] using wordTrace_append hprefix tailTrace_1837454
  have hstable : (prefixWord ++ tailWord_1837454).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837454).length < 2 ^ (prefixWord ++ tailWord_1837454).sum := by decide
  have hdescent : baseEnd_1837454 < baseStart_1837454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837505 : List Nat := [1, 2, 7, 1, 1, 1, 3, 5]
def baseStart_1837505 : Nat := 118140960795 + 1837505 * 2 ^ 59
def prefixEnd_1837505 : Nat := 4983230072969 + 3 ^ 40 * 1837505 * 2
def baseEnd_1837505 : Nat := 139781225191101998064737

theorem tailTrace_1837505 : CollatzResearch.WordTrace tailWord_1837505 prefixEnd_1837505 139781225191101998064737 := by
  unfold tailWord_1837505
  simp only [CollatzResearch.WordTrace]
  refine ⟨67019313208040680714553969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44679542138693787143035979 67019313208040680714553969)
  ·
    refine ⟨50264484906030510535915477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67019313208040680714553969 50264484906030510535915477)
    ·
      refine ⟨1178073864985090090685519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 50264484906030510535915477 1178073864985090090685519)
      ·
        refine ⟨1767110797477635136028279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1178073864985090090685519 1767110797477635136028279)
        ·
          refine ⟨2650666196216452704042419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1767110797477635136028279 2650666196216452704042419)
          ·
            refine ⟨3975999294324679056063629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2650666196216452704042419 3975999294324679056063629)
            ·
              refine ⟨1490999735371754646023861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3975999294324679056063629 1490999735371754646023861)
              ·
                refine ⟨139781225191101998064737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1490999735371754646023861 139781225191101998064737)
                ·
                  rfl

theorem cell21_1837505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 3, 5].length) (baseStart_1837505 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1837505 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1837505 prefixEnd_1837505 := by exact prefixLift 1837505
  have htrace : WordTrace (prefixWord ++ tailWord_1837505) baseStart_1837505 baseEnd_1837505 := by
    simpa [prefixWord, tailWord_1837505, baseEnd_1837505] using wordTrace_append hprefix tailTrace_1837505
  have hstable : (prefixWord ++ tailWord_1837505).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837505).length < 2 ^ (prefixWord ++ tailWord_1837505).sum := by decide
  have hdescent : baseEnd_1837505 < baseStart_1837505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837544 : List Nat := [2, 1, 4, 1, 1, 3, 1, 3, 5]
def baseStart_1837544 : Nat := 118140960795 + 1837544 * 2 ^ 59
def prefixEnd_1837544 : Nat := 4983230072969 + 3 ^ 40 * 1837544 * 2
def baseEnd_1837544 : Nat := 419352575904650593044131

theorem tailTrace_1837544 : CollatzResearch.WordTrace tailWord_1837544 prefixEnd_1837544 419352575904650593044131 := by
  unfold tailWord_1837544
  simp only [CollatzResearch.WordTrace]
  refine ⟨33510367827449695187611843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44680490436599593583482457 33510367827449695187611843)
  ·
    refine ⟨50265551741174542781417765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33510367827449695187611843 50265551741174542781417765)
    ·
      refine ⟨9424790951470226771515831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50265551741174542781417765 9424790951470226771515831)
      ·
        refine ⟨14137186427205340157273747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9424790951470226771515831 14137186427205340157273747)
        ·
          refine ⟨21205779640808010235910621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14137186427205340157273747 21205779640808010235910621)
          ·
            refine ⟨7952167365303003838466483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21205779640808010235910621 7952167365303003838466483)
            ·
              refine ⟨11928251047954505757699725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7952167365303003838466483 11928251047954505757699725)
              ·
                refine ⟨4473094142982939659137397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11928251047954505757699725 4473094142982939659137397)
                ·
                  refine ⟨419352575904650593044131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4473094142982939659137397 419352575904650593044131)
                  ·
                    rfl

theorem cell21_1837544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 3, 5].length) (baseStart_1837544 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1837544 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1837544 prefixEnd_1837544 := by exact prefixLift 1837544
  have htrace : WordTrace (prefixWord ++ tailWord_1837544) baseStart_1837544 baseEnd_1837544 := by
    simpa [prefixWord, tailWord_1837544, baseEnd_1837544] using wordTrace_append hprefix tailTrace_1837544
  have hstable : (prefixWord ++ tailWord_1837544).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837544).length < 2 ^ (prefixWord ++ tailWord_1837544).sum := by decide
  have hdescent : baseEnd_1837544 < baseStart_1837544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837665 : List Nat := [1, 2, 3, 1, 1, 4, 3, 6]
def baseStart_1837665 : Nat := 118140960795 + 1837665 * 2 ^ 59
def prefixEnd_1837665 : Nat := 4983230072969 + 3 ^ 40 * 1837665 * 2
def baseEnd_1837665 : Nat := 139793396584393757175739

theorem tailTrace_1837665 : CollatzResearch.WordTrace tailWord_1837665 prefixEnd_1837665 139793396584393757175739 := by
  unfold tailWord_1837665
  simp only [CollatzResearch.WordTrace]
  refine ⟨67025148887461028040378449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44683432591640685360252299 67025148887461028040378449)
  ·
    refine ⟨50268861665595771030283837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67025148887461028040378449 50268861665595771030283837)
    ·
      refine ⟨18850823124598414136356439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50268861665595771030283837 18850823124598414136356439)
      ·
        refine ⟨28276234686897621204534659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18850823124598414136356439 28276234686897621204534659)
        ·
          refine ⟨42414352030346431806801989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28276234686897621204534659 42414352030346431806801989)
          ·
            refine ⟨7952691005689955963775373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42414352030346431806801989 7952691005689955963775373)
            ·
              refine ⟨2982259127133733486415765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7952691005689955963775373 2982259127133733486415765)
              ·
                refine ⟨139793396584393757175739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2982259127133733486415765 139793396584393757175739)
                ·
                  rfl

theorem cell21_1837665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 6].length) (baseStart_1837665 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1837665 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1837665 prefixEnd_1837665 := by exact prefixLift 1837665
  have htrace : WordTrace (prefixWord ++ tailWord_1837665) baseStart_1837665 baseEnd_1837665 := by
    simpa [prefixWord, tailWord_1837665, baseEnd_1837665] using wordTrace_append hprefix tailTrace_1837665
  have hstable : (prefixWord ++ tailWord_1837665).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837665).length < 2 ^ (prefixWord ++ tailWord_1837665).sum := by decide
  have hdescent : baseEnd_1837665 < baseStart_1837665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837679 : List Nat := [1, 1, 2, 1, 3, 2, 3, 1, 7]
def baseStart_1837679 : Nat := 118140960795 + 1837679 * 2 ^ 59
def prefixEnd_1837679 : Nat := 4983230072969 + 3 ^ 40 * 1837679 * 2
def baseEnd_1837679 : Nat := 419383384743920358293855

theorem tailTrace_1837679 : CollatzResearch.WordTrace tailWord_1837679 prefixEnd_1837679 419383384743920358293855 := by
  unfold tailWord_1837679
  simp only [CollatzResearch.WordTrace]
  refine ⟨67025659509410308431388091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44683773006273538954258727 67025659509410308431388091)
  ·
    refine ⟨100538489264115462647082137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67025659509410308431388091 100538489264115462647082137)
    ·
      refine ⟨75403866948086596985311603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100538489264115462647082137 75403866948086596985311603)
      ·
        refine ⟨113105800422129895477967405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75403866948086596985311603 113105800422129895477967405)
        ·
          refine ⟨42414675158298710804237777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113105800422129895477967405 42414675158298710804237777)
          ·
            refine ⟨31811006368724033103178333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42414675158298710804237777 31811006368724033103178333)
            ·
              refine ⟨11929127388271512413691875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31811006368724033103178333 11929127388271512413691875)
              ·
                refine ⟨17893691082407268620537813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11929127388271512413691875 17893691082407268620537813)
                ·
                  refine ⟨419383384743920358293855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17893691082407268620537813 419383384743920358293855)
                  ·
                    rfl

theorem cell21_1837679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 7].length) (baseStart_1837679 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1837679 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1837679 prefixEnd_1837679 := by exact prefixLift 1837679
  have htrace : WordTrace (prefixWord ++ tailWord_1837679) baseStart_1837679 baseEnd_1837679 := by
    simpa [prefixWord, tailWord_1837679, baseEnd_1837679] using wordTrace_append hprefix tailTrace_1837679
  have hstable : (prefixWord ++ tailWord_1837679).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837679).length < 2 ^ (prefixWord ++ tailWord_1837679).sum := by decide
  have hdescent : baseEnd_1837679 < baseStart_1837679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837778 : List Nat := [3, 2, 2, 2, 4, 1, 2, 1, 4]
def baseStart_1837778 : Nat := 118140960795 + 1837778 * 2 ^ 59
def prefixEnd_1837778 : Nat := 4983230072969 + 3 ^ 40 * 1837778 * 2
def baseEnd_1837778 : Nat := 419405977892718186143653

theorem tailTrace_1837778 : CollatzResearch.WordTrace tailWord_1837778 prefixEnd_1837778 419405977892718186143653 := by
  unfold tailWord_1837778
  simp only [CollatzResearch.WordTrace]
  refine ⟨16757317584012912084810497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44686180224034432226161325 16757317584012912084810497)
  ·
    refine ⟨12567988188009684063607873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16757317584012912084810497 12567988188009684063607873)
    ·
      refine ⟨9425991141007263047705905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12567988188009684063607873 9425991141007263047705905)
      ·
        refine ⟨7069493355755447285779429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9425991141007263047705905 7069493355755447285779429)
        ·
          refine ⟨1325530004204146366083643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7069493355755447285779429 1325530004204146366083643)
          ·
            refine ⟨1988295006306219549125465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1325530004204146366083643 1988295006306219549125465)
            ·
              refine ⟨1491221254729664661844099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1988295006306219549125465 1491221254729664661844099)
              ·
                refine ⟨2236831882094496992766149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1491221254729664661844099 2236831882094496992766149)
                ·
                  refine ⟨419405977892718186143653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2236831882094496992766149 419405977892718186143653)
                  ·
                    rfl

theorem cell21_1837778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 2, 1, 4].length) (baseStart_1837778 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1837778 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1837778 prefixEnd_1837778 := by exact prefixLift 1837778
  have htrace : WordTrace (prefixWord ++ tailWord_1837778) baseStart_1837778 baseEnd_1837778 := by
    simpa [prefixWord, tailWord_1837778, baseEnd_1837778] using wordTrace_append hprefix tailTrace_1837778
  have hstable : (prefixWord ++ tailWord_1837778).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837778).length < 2 ^ (prefixWord ++ tailWord_1837778).sum := by decide
  have hdescent : baseEnd_1837778 < baseStart_1837778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837938 : List Nat := [3, 2, 1, 2, 1, 1, 4, 1, 6]
def baseStart_1837938 : Nat := 118140960795 + 1837938 * 2 ^ 59
def prefixEnd_1837938 : Nat := 4983230072969 + 3 ^ 40 * 1837938 * 2
def baseEnd_1837938 : Nat := 419442492072593463476659

theorem tailTrace_1837938 : CollatzResearch.WordTrace tailWord_1837938 prefixEnd_1837938 419442492072593463476659 := by
  unfold tailWord_1837938
  simp only [CollatzResearch.WordTrace]
  refine ⟨16758776503867998916266617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44690070676981330443377645 16758776503867998916266617)
  ·
    refine ⟨12569082377900999187199963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16758776503867998916266617 12569082377900999187199963)
    ·
      refine ⟨18853623566851498780799945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12569082377900999187199963 18853623566851498780799945)
      ·
        refine ⟨14140217675138624085599959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18853623566851498780799945 14140217675138624085599959)
        ·
          refine ⟨21210326512707936128399939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14140217675138624085599959 21210326512707936128399939)
          ·
            refine ⟨31815489769061904192599909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21210326512707936128399939 31815489769061904192599909)
            ·
              refine ⟨5965404331699107036112483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31815489769061904192599909 5965404331699107036112483)
              ·
                refine ⟨8948106497548660554168725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5965404331699107036112483 8948106497548660554168725)
                ·
                  refine ⟨419442492072593463476659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8948106497548660554168725 419442492072593463476659)
                  ·
                    rfl

theorem cell21_1837938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 6].length) (baseStart_1837938 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1837938 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1837938 prefixEnd_1837938 := by exact prefixLift 1837938
  have htrace : WordTrace (prefixWord ++ tailWord_1837938) baseStart_1837938 baseEnd_1837938 := by
    simpa [prefixWord, tailWord_1837938, baseEnd_1837938] using wordTrace_append hprefix tailTrace_1837938
  have hstable : (prefixWord ++ tailWord_1837938).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837938).length < 2 ^ (prefixWord ++ tailWord_1837938).sum := by decide
  have hdescent : baseEnd_1837938 < baseStart_1837938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837941 : List Nat := [1, 3, 4, 1, 1, 4, 1, 1, 5]
def baseStart_1837941 : Nat := 118140960795 + 1837941 * 2 ^ 59
def prefixEnd_1837941 : Nat := 4983230072969 + 3 ^ 40 * 1837941 * 2
def baseEnd_1837941 : Nat := 419443176713466124926653

theorem tailTrace_1837941 : CollatzResearch.WordTrace tailWord_1837941 prefixEnd_1837941 419443176713466124926653 := by
  unfold tailWord_1837941
  simp only [CollatzResearch.WordTrace]
  refine ⟨67035215434461127177425677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44690143622974084784950451 67035215434461127177425677)
  ·
    refine ⟨25138205787922922691534629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67035215434461127177425677 25138205787922922691534629)
    ·
      refine ⟨4713413585235548004662743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25138205787922922691534629 4713413585235548004662743)
      ·
        refine ⟨7070120377853322006994115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4713413585235548004662743 7070120377853322006994115)
        ·
          refine ⟨10605180566779983010491173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7070120377853322006994115 10605180566779983010491173)
          ·
            refine ⟨1988471356271246814467095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10605180566779983010491173 1988471356271246814467095)
            ·
              refine ⟨2982707034406870221700643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1988471356271246814467095 2982707034406870221700643)
              ·
                refine ⟨4474060551610305332550965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2982707034406870221700643 4474060551610305332550965)
                ·
                  refine ⟨419443176713466124926653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4474060551610305332550965 419443176713466124926653)
                  ·
                    rfl

theorem cell21_1837941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 1, 5].length) (baseStart_1837941 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1837941 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1837941 prefixEnd_1837941 := by exact prefixLift 1837941
  have htrace : WordTrace (prefixWord ++ tailWord_1837941) baseStart_1837941 baseEnd_1837941 := by
    simpa [prefixWord, tailWord_1837941, baseEnd_1837941] using wordTrace_append hprefix tailTrace_1837941
  have hstable : (prefixWord ++ tailWord_1837941).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837941).length < 2 ^ (prefixWord ++ tailWord_1837941).sum := by decide
  have hdescent : baseEnd_1837941 < baseStart_1837941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838034 : List Nat := [3, 2, 2, 3, 1, 2, 2, 3, 3]
def baseStart_1838034 : Nat := 118140960795 + 1838034 * 2 ^ 59
def prefixEnd_1838034 : Nat := 4983230072969 + 3 ^ 40 * 1838034 * 2
def baseEnd_1838034 : Nat := 419464400580518629876463

theorem tailTrace_1838034 : CollatzResearch.WordTrace tailWord_1838034 prefixEnd_1838034 419464400580518629876463 := by
  unfold tailWord_1838034
  simp only [CollatzResearch.WordTrace]
  refine ⟨16759651855781051015140289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44692404948749469373707437 16759651855781051015140289)
  ·
    refine ⟨12569738891835788261355217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16759651855781051015140289 12569738891835788261355217)
    ·
      refine ⟨9427304168876841196016413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12569738891835788261355217 9427304168876841196016413)
      ·
        refine ⟨3535239063328815448506155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9427304168876841196016413 3535239063328815448506155)
        ·
          refine ⟨5302858594993223172759233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3535239063328815448506155 5302858594993223172759233)
          ·
            refine ⟨3977143946244917379569425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5302858594993223172759233 3977143946244917379569425)
            ·
              refine ⟨2982857959683688034677069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3977143946244917379569425 2982857959683688034677069)
              ·
                refine ⟨1118571734881383013003901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2982857959683688034677069 1118571734881383013003901)
                ·
                  refine ⟨419464400580518629876463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1118571734881383013003901 419464400580518629876463)
                  ·
                    rfl

theorem cell21_1838034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 3, 3].length) (baseStart_1838034 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1838034 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1838034 prefixEnd_1838034 := by exact prefixLift 1838034
  have htrace : WordTrace (prefixWord ++ tailWord_1838034) baseStart_1838034 baseEnd_1838034 := by
    simpa [prefixWord, tailWord_1838034, baseEnd_1838034] using wordTrace_append hprefix tailTrace_1838034
  have hstable : (prefixWord ++ tailWord_1838034).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838034).length < 2 ^ (prefixWord ++ tailWord_1838034).sum := by decide
  have hdescent : baseEnd_1838034 < baseStart_1838034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838045 : List Nat := [1, 4, 3, 1, 2, 2, 8]
def baseStart_1838045 : Nat := 118140960795 + 1838045 * 2 ^ 59
def prefixEnd_1838045 : Nat := 4983230072969 + 3 ^ 40 * 1838045 * 2
def baseEnd_1838045 : Nat := 46607434547820561688123

theorem tailTrace_1838045 : CollatzResearch.WordTrace tailWord_1838045 prefixEnd_1838045 46607434547820561688123 := by
  unfold tailWord_1838045
  simp only [CollatzResearch.WordTrace]
  refine ⟨67039008626084352939211589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44692672417389568626141059 67039008626084352939211589)
  ·
    refine ⟨12569814117390816176102173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67039008626084352939211589 12569814117390816176102173)
    ·
      refine ⟨4713680294021556066038315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12569814117390816176102173 4713680294021556066038315)
      ·
        refine ⟨7070520441032334099057473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4713680294021556066038315 7070520441032334099057473)
        ·
          refine ⟨5302890330774250574293105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7070520441032334099057473 5302890330774250574293105)
          ·
            refine ⟨3977167748080687930719829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5302890330774250574293105 3977167748080687930719829)
            ·
              refine ⟨46607434547820561688123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3977167748080687930719829 46607434547820561688123)
              ·
                rfl

theorem cell21_1838045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 8].length) (baseStart_1838045 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1838045 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1838045 prefixEnd_1838045 := by exact prefixLift 1838045
  have htrace : WordTrace (prefixWord ++ tailWord_1838045) baseStart_1838045 baseEnd_1838045 := by
    simpa [prefixWord, tailWord_1838045, baseEnd_1838045] using wordTrace_append hprefix tailTrace_1838045
  have hstable : (prefixWord ++ tailWord_1838045).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838045).length < 2 ^ (prefixWord ++ tailWord_1838045).sum := by decide
  have hdescent : baseEnd_1838045 < baseStart_1838045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838090 : List Nat := [3, 1, 2, 2, 3, 1, 1, 2, 6]
def baseStart_1838090 : Nat := 118140960795 + 1838090 * 2 ^ 59
def prefixEnd_1838090 : Nat := 4983230072969 + 3 ^ 40 * 1838090 * 2
def baseEnd_1838090 : Nat := 419477180543474976943015

theorem tailTrace_1838090 : CollatzResearch.WordTrace tailWord_1838090 prefixEnd_1838090 419477180543474976943015 := by
  unfold tailWord_1838090
  simp only [CollatzResearch.WordTrace]
  refine ⟨16760162477730331406149931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44693766607280883749733149 16760162477730331406149931)
  ·
    refine ⟨25140243716595497109224897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16760162477730331406149931 25140243716595497109224897)
    ·
      refine ⟨18855182787446622831918673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25140243716595497109224897 18855182787446622831918673)
      ·
        refine ⟨14141387090584967123939005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18855182787446622831918673 14141387090584967123939005)
        ·
          refine ⟨5303020158969362671477127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14141387090584967123939005 5303020158969362671477127)
          ·
            refine ⟨7954530238454044007215691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5303020158969362671477127 7954530238454044007215691)
            ·
              refine ⟨11931795357681066010823537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7954530238454044007215691 11931795357681066010823537)
              ·
                refine ⟨8948846518260799508117653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11931795357681066010823537 8948846518260799508117653)
                ·
                  refine ⟨419477180543474976943015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8948846518260799508117653 419477180543474976943015)
                  ·
                    rfl

theorem cell21_1838090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 6].length) (baseStart_1838090 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1838090 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1838090 prefixEnd_1838090 := by exact prefixLift 1838090
  have htrace : WordTrace (prefixWord ++ tailWord_1838090) baseStart_1838090 baseEnd_1838090 := by
    simpa [prefixWord, tailWord_1838090, baseEnd_1838090] using wordTrace_append hprefix tailTrace_1838090
  have hstable : (prefixWord ++ tailWord_1838090).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838090).length < 2 ^ (prefixWord ++ tailWord_1838090).sum := by decide
  have hdescent : baseEnd_1838090 < baseStart_1838090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838104 : List Nat := [2, 1, 2, 3, 2, 2, 9]
def baseStart_1838104 : Nat := 118140960795 + 1838104 * 2 ^ 59
def prefixEnd_1838104 : Nat := 4983230072969 + 3 ^ 40 * 1838104 * 2
def baseEnd_1838104 : Nat := 46608930614912673745517

theorem tailTrace_1838104 : CollatzResearch.WordTrace tailWord_1838104 prefixEnd_1838104 46608930614912673745517 := by
  unfold tailWord_1838104
  simp only [CollatzResearch.WordTrace]
  refine ⟨33520580266435303007804683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44694107021913737343739577 33520580266435303007804683)
  ·
    refine ⟨50280870399652954511707025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33520580266435303007804683 50280870399652954511707025)
    ·
      refine ⟨37710652799739715883780269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50280870399652954511707025 37710652799739715883780269)
      ·
        refine ⟨14141494799902393456417601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37710652799739715883780269 14141494799902393456417601)
        ·
          refine ⟨10606121099926795092313201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14141494799902393456417601 10606121099926795092313201)
          ·
            refine ⟨7954590824945096319234901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10606121099926795092313201 7954590824945096319234901)
            ·
              refine ⟨46608930614912673745517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7954590824945096319234901 46608930614912673745517)
              ·
                rfl

theorem cell21_1838104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 9].length) (baseStart_1838104 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1838104 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1838104 prefixEnd_1838104 := by exact prefixLift 1838104
  have htrace : WordTrace (prefixWord ++ tailWord_1838104) baseStart_1838104 baseEnd_1838104 := by
    simpa [prefixWord, tailWord_1838104, baseEnd_1838104] using wordTrace_append hprefix tailTrace_1838104
  have hstable : (prefixWord ++ tailWord_1838104).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838104).length < 2 ^ (prefixWord ++ tailWord_1838104).sum := by decide
  have hdescent : baseEnd_1838104 < baseStart_1838104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838149 : List Nat := [1, 3, 1, 1, 1, 3, 2, 1, 8]
def baseStart_1838149 : Nat := 118140960795 + 1838149 * 2 ^ 59
def prefixEnd_1838149 : Nat := 4983230072969 + 3 ^ 40 * 1838149 * 2
def baseEnd_1838149 : Nat := 419490645147303985459561

theorem tailTrace_1838149 : CollatzResearch.WordTrace tailWord_1838149 prefixEnd_1838149 419490645147303985459561 := by
  unfold tailWord_1838149
  simp only [CollatzResearch.WordTrace]
  refine ⟨67042801817707578700997501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44695201211805052467331667 67042801817707578700997501)
  ·
    refine ⟨25141050681640342012874063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67042801817707578700997501 25141050681640342012874063)
    ·
      refine ⟨37711576022460513019311095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25141050681640342012874063 37711576022460513019311095)
      ·
        refine ⟨56567364033690769528966643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37711576022460513019311095 56567364033690769528966643)
        ·
          refine ⟨84851046050536154293449965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56567364033690769528966643 84851046050536154293449965)
          ·
            refine ⟨31819142268951057860043737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84851046050536154293449965 31819142268951057860043737)
            ·
              refine ⟨23864356701713293395032803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31819142268951057860043737 23864356701713293395032803)
              ·
                refine ⟨35796535052569940092549205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23864356701713293395032803 35796535052569940092549205)
                ·
                  refine ⟨419490645147303985459561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35796535052569940092549205 419490645147303985459561)
                  ·
                    rfl

theorem cell21_1838149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 8].length) (baseStart_1838149 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1838149 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1838149 prefixEnd_1838149 := by exact prefixLift 1838149
  have htrace : WordTrace (prefixWord ++ tailWord_1838149) baseStart_1838149 baseEnd_1838149 := by
    simpa [prefixWord, tailWord_1838149, baseEnd_1838149] using wordTrace_append hprefix tailTrace_1838149
  have hstable : (prefixWord ++ tailWord_1838149).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838149).length < 2 ^ (prefixWord ++ tailWord_1838149).sum := by decide
  have hdescent : baseEnd_1838149 < baseStart_1838149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838152 : List Nat := [2, 1, 3, 1, 1, 1, 4, 5, 3]
def baseStart_1838152 : Nat := 118140960795 + 1838152 * 2 ^ 59
def prefixEnd_1838152 : Nat := 4983230072969 + 3 ^ 40 * 1838152 * 2
def baseEnd_1838152 : Nat := 419491329788176646909555

theorem tailTrace_1838152 : CollatzResearch.WordTrace tailWord_1838152 prefixEnd_1838152 419491329788176646909555 := by
  unfold tailWord_1838152
  simp only [CollatzResearch.WordTrace]
  refine ⟨33521455618348355106678355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44695274157797806808904473 33521455618348355106678355)
  ·
    refine ⟨50282183427522532660017533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33521455618348355106678355 50282183427522532660017533)
    ·
      refine ⟨18855818785320949747506575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50282183427522532660017533 18855818785320949747506575)
      ·
        refine ⟨28283728177981424621259863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18855818785320949747506575 28283728177981424621259863)
        ·
          refine ⟨42425592266972136931889795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28283728177981424621259863 42425592266972136931889795)
          ·
            refine ⟨63638388400458205397834693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42425592266972136931889795 63638388400458205397834693)
            ·
              refine ⟨11932197825085913512094005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63638388400458205397834693 11932197825085913512094005)
              ·
                refine ⟨1118643546101804391758813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11932197825085913512094005 1118643546101804391758813)
                ·
                  refine ⟨419491329788176646909555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1118643546101804391758813 419491329788176646909555)
                  ·
                    rfl

theorem cell21_1838152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 5, 3].length) (baseStart_1838152 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1838152 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1838152 prefixEnd_1838152 := by exact prefixLift 1838152
  have htrace : WordTrace (prefixWord ++ tailWord_1838152) baseStart_1838152 baseEnd_1838152 := by
    simpa [prefixWord, tailWord_1838152, baseEnd_1838152] using wordTrace_append hprefix tailTrace_1838152
  have hstable : (prefixWord ++ tailWord_1838152).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838152).length < 2 ^ (prefixWord ++ tailWord_1838152).sum := by decide
  have hdescent : baseEnd_1838152 < baseStart_1838152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838273 : List Nat := [1, 2, 6, 1, 1, 1, 9]
def baseStart_1838273 : Nat := 118140960795 + 1838273 * 2 ^ 59
def prefixEnd_1838273 : Nat := 4983230072969 + 3 ^ 40 * 1838273 * 2
def baseEnd_1838273 : Nat := 46613215959634147265849

theorem tailTrace_1838273 : CollatzResearch.WordTrace tailWord_1838273 prefixEnd_1838273 46613215959634147265849 := by
  unfold tailWord_1838273
  simp only [CollatzResearch.WordTrace]
  refine ⟨67047324469258347878511473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44698216312838898585674315 67047324469258347878511473)
  ·
    refine ⟨50285493351943760908883605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67047324469258347878511473 50285493351943760908883605)
    ·
      refine ⟨2357132500872363792603919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 50285493351943760908883605 2357132500872363792603919)
      ·
        refine ⟨3535698751308545688905879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2357132500872363792603919 3535698751308545688905879)
        ·
          refine ⟨5303548126962818533358819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3535698751308545688905879 5303548126962818533358819)
          ·
            refine ⟨7955322190444227800038229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5303548126962818533358819 7955322190444227800038229)
            ·
              refine ⟨46613215959634147265849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7955322190444227800038229 46613215959634147265849)
              ·
                rfl

theorem cell21_1838273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 9].length) (baseStart_1838273 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1838273 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1838273 prefixEnd_1838273 := by exact prefixLift 1838273
  have htrace : WordTrace (prefixWord ++ tailWord_1838273) baseStart_1838273 baseEnd_1838273 := by
    simpa [prefixWord, tailWord_1838273, baseEnd_1838273] using wordTrace_append hprefix tailTrace_1838273
  have hstable : (prefixWord ++ tailWord_1838273).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838273).length < 2 ^ (prefixWord ++ tailWord_1838273).sum := by decide
  have hdescent : baseEnd_1838273 < baseStart_1838273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838332 : List Nat := [2, 2, 2, 1, 5, 9]
def baseStart_1838332 : Nat := 118140960795 + 1838332 * 2 ^ 59
def prefixEnd_1838332 : Nat := 4983230072969 + 3 ^ 40 * 1838332 * 2
def baseEnd_1838332 : Nat := 15538237342242086441081

theorem tailTrace_1838332 : CollatzResearch.WordTrace tailWord_1838332 prefixEnd_1838332 15538237342242086441081 := by
  unfold tailWord_1838332
  simp only [CollatzResearch.WordTrace]
  refine ⟨33524738188022300477454625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44699650917363067303272833 33524738188022300477454625)
  ·
    refine ⟨25143553641016725358090969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33524738188022300477454625 25143553641016725358090969)
    ·
      refine ⟨18857665230762544018568227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25143553641016725358090969 18857665230762544018568227)
      ·
        refine ⟨28286497846143816027852341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18857665230762544018568227 28286497846143816027852341)
        ·
          refine ⟨2651859173075982752611157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28286497846143816027852341 2651859173075982752611157)
          ·
            refine ⟨15538237342242086441081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2651859173075982752611157 15538237342242086441081)
            ·
              rfl

theorem cell21_1838332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 9].length) (baseStart_1838332 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1838332 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1838332 prefixEnd_1838332 := by exact prefixLift 1838332
  have htrace : WordTrace (prefixWord ++ tailWord_1838332) baseStart_1838332 baseEnd_1838332 := by
    simpa [prefixWord, tailWord_1838332, baseEnd_1838332] using wordTrace_append hprefix tailTrace_1838332
  have hstable : (prefixWord ++ tailWord_1838332).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838332).length < 2 ^ (prefixWord ++ tailWord_1838332).sum := by decide
  have hdescent : baseEnd_1838332 < baseStart_1838332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838338 : List Nat := [3, 4, 1, 1, 3, 1, 1, 4, 3]
def baseStart_1838338 : Nat := 118140960795 + 1838338 * 2 ^ 59
def prefixEnd_1838338 : Nat := 4983230072969 + 3 ^ 40 * 1838338 * 2
def baseEnd_1838338 : Nat := 419533777522281656809175

theorem tailTrace_1838338 : CollatzResearch.WordTrace tailWord_1838338 prefixEnd_1838338 419533777522281656809175 := by
  unfold tailWord_1838338
  simp only [CollatzResearch.WordTrace]
  refine ⟨16762423803505715994906917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44699796809348575986418445 16762423803505715994906917)
  ·
    refine ⟨3142954463157321749045047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16762423803505715994906917 3142954463157321749045047)
    ·
      refine ⟨4714431694735982623567571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3142954463157321749045047 4714431694735982623567571)
      ·
        refine ⟨7071647542103973935351357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4714431694735982623567571 7071647542103973935351357)
        ·
          refine ⟨2651867828288990225756759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7071647542103973935351357 2651867828288990225756759)
          ·
            refine ⟨3977801742433485338635139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2651867828288990225756759 3977801742433485338635139)
            ·
              refine ⟨5966702613650228007952709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3977801742433485338635139 5966702613650228007952709)
              ·
                refine ⟨1118756740059417751491133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5966702613650228007952709 1118756740059417751491133)
                ·
                  refine ⟨419533777522281656809175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1118756740059417751491133 419533777522281656809175)
                  ·
                    rfl

theorem cell21_1838338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_1838338 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1838338 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1838338 prefixEnd_1838338 := by exact prefixLift 1838338
  have htrace : WordTrace (prefixWord ++ tailWord_1838338) baseStart_1838338 baseEnd_1838338 := by
    simpa [prefixWord, tailWord_1838338, baseEnd_1838338] using wordTrace_append hprefix tailTrace_1838338
  have hstable : (prefixWord ++ tailWord_1838338).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838338).length < 2 ^ (prefixWord ++ tailWord_1838338).sum := by decide
  have hdescent : baseEnd_1838338 < baseStart_1838338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838397 : List Nat := [1, 4, 1, 5, 1, 1, 2, 1, 5]
def baseStart_1838397 : Nat := 118140960795 + 1838397 * 2 ^ 59
def prefixEnd_1838397 : Nat := 4983230072969 + 3 ^ 40 * 1838397 * 2
def baseEnd_1838397 : Nat := 419547242126110665325721

theorem tailTrace_1838397 : CollatzResearch.WordTrace tailWord_1838397 prefixEnd_1838397 419547242126110665325721 := by
  unfold tailWord_1838397
  simp only [CollatzResearch.WordTrace]
  refine ⟨67051847120809117056025445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44701231413872744704016963 67051847120809117056025445)
  ·
    refine ⟨12572221335151709448004771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67051847120809117056025445 12572221335151709448004771)
    ·
      refine ⟨18858332002727564172007157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12572221335151709448004771 18858332002727564172007157)
      ·
        refine ⟨1767968625255709141125671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18858332002727564172007157 1767968625255709141125671)
        ·
          refine ⟨2651952937883563711688507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1767968625255709141125671 2651952937883563711688507)
          ·
            refine ⟨3977929406825345567532761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2651952937883563711688507 3977929406825345567532761)
            ·
              refine ⟨2983447055119009175649571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3977929406825345567532761 2983447055119009175649571)
              ·
                refine ⟨4475170582678513763474357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2983447055119009175649571 4475170582678513763474357)
                ·
                  refine ⟨419547242126110665325721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4475170582678513763474357 419547242126110665325721)
                  ·
                    rfl

theorem cell21_1838397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 1, 5].length) (baseStart_1838397 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1838397 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1838397 prefixEnd_1838397 := by exact prefixLift 1838397
  have htrace : WordTrace (prefixWord ++ tailWord_1838397) baseStart_1838397 baseEnd_1838397 := by
    simpa [prefixWord, tailWord_1838397, baseEnd_1838397] using wordTrace_append hprefix tailTrace_1838397
  have hstable : (prefixWord ++ tailWord_1838397).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838397).length < 2 ^ (prefixWord ++ tailWord_1838397).sum := by decide
  have hdescent : baseEnd_1838397 < baseStart_1838397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838442 : List Nat := [3, 1, 3, 3, 3, 1, 7]
def baseStart_1838442 : Nat := 118140960795 + 1838442 * 2 ^ 59
def prefixEnd_1838442 : Nat := 4983230072969 + 3 ^ 40 * 1838442 * 2
def baseEnd_1838442 : Nat := 46617501304355620786181

theorem tailTrace_1838442 : CollatzResearch.WordTrace tailWord_1838442 prefixEnd_1838442 46617501304355620786181 := by
  unfold tailWord_1838442
  simp only [CollatzResearch.WordTrace]
  refine ⟨16763372101411522435353395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44702325603764059827609053 16763372101411522435353395)
  ·
    refine ⟨25145058152117283653030093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16763372101411522435353395 25145058152117283653030093)
    ·
      refine ⟨9429396807043981369886285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25145058152117283653030093 9429396807043981369886285)
      ·
        refine ⟨3536023802641493013707357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9429396807043981369886285 3536023802641493013707357)
        ·
          refine ⟨1326008925990559880140259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3536023802641493013707357 1326008925990559880140259)
          ·
            refine ⟨1989013388985839820210389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1326008925990559880140259 1989013388985839820210389)
            ·
              refine ⟨46617501304355620786181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1989013388985839820210389 46617501304355620786181)
              ·
                rfl

theorem cell21_1838442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 7].length) (baseStart_1838442 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1838442 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1838442 prefixEnd_1838442 := by exact prefixLift 1838442
  have htrace : WordTrace (prefixWord ++ tailWord_1838442) baseStart_1838442 baseEnd_1838442 := by
    simpa [prefixWord, tailWord_1838442, baseEnd_1838442] using wordTrace_append hprefix tailTrace_1838442
  have hstable : (prefixWord ++ tailWord_1838442).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838442).length < 2 ^ (prefixWord ++ tailWord_1838442).sum := by decide
  have hdescent : baseEnd_1838442 < baseStart_1838442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838462 : List Nat := [4, 2, 3, 2, 1, 2, 2, 1, 4]
def baseStart_1838462 : Nat := 118140960795 + 1838462 * 2 ^ 59
def prefixEnd_1838462 : Nat := 4983230072969 + 3 ^ 40 * 1838462 * 2
def baseEnd_1838462 : Nat := 419562076011684996742255

theorem tailTrace_1838462 : CollatzResearch.WordTrace tailWord_1838462 prefixEnd_1838462 419562076011684996742255 := by
  unfold tailWord_1838462
  simp only [CollatzResearch.WordTrace]
  refine ⟨8381777233196704144642705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44702811910382422104761093 8381777233196704144642705)
  ·
    refine ⟨6286332924897528108482029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8381777233196704144642705 6286332924897528108482029)
    ·
      refine ⟨2357374846836573040680761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6286332924897528108482029 2357374846836573040680761)
      ·
        refine ⟨1768031135127429780510571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2357374846836573040680761 1768031135127429780510571)
        ·
          refine ⟨2652046702691144670765857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1768031135127429780510571 2652046702691144670765857)
          ·
            refine ⟨1989035027018358503074393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2652046702691144670765857 1989035027018358503074393)
            ·
              refine ⟨1491776270263768877305795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1989035027018358503074393 1491776270263768877305795)
              ·
                refine ⟨2237664405395653315958693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1491776270263768877305795 2237664405395653315958693)
                ·
                  refine ⟨419562076011684996742255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2237664405395653315958693 419562076011684996742255)
                  ·
                    rfl

theorem cell21_1838462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_1838462 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1838462 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1838462 prefixEnd_1838462 := by exact prefixLift 1838462
  have htrace : WordTrace (prefixWord ++ tailWord_1838462) baseStart_1838462 baseEnd_1838462 := by
    simpa [prefixWord, tailWord_1838462, baseEnd_1838462] using wordTrace_append hprefix tailTrace_1838462
  have hstable : (prefixWord ++ tailWord_1838462).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838462).length < 2 ^ (prefixWord ++ tailWord_1838462).sum := by decide
  have hdescent : baseEnd_1838462 < baseStart_1838462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838504 : List Nat := [2, 1, 6, 1, 2, 1, 2, 2, 4]
def baseStart_1838504 : Nat := 118140960795 + 1838504 * 2 ^ 59
def prefixEnd_1838504 : Nat := 4983230072969 + 3 ^ 40 * 1838504 * 2
def baseEnd_1838504 : Nat := 419571660983902257042169

theorem tailTrace_1838504 : CollatzResearch.WordTrace tailWord_1838504 prefixEnd_1838504 419571660983902257042169 := by
  unfold tailWord_1838504
  simp only [CollatzResearch.WordTrace]
  refine ⟨33527874865710737165085283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44703833154280982886780377 33527874865710737165085283)
  ·
    refine ⟨50291812298566105747627925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33527874865710737165085283 50291812298566105747627925)
    ·
      refine ⟨2357428701495286206920059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 50291812298566105747627925 2357428701495286206920059)
      ·
        refine ⟨3536143052242929310380089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2357428701495286206920059 3536143052242929310380089)
        ·
          refine ⟨2652107289182196982785067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3536143052242929310380089 2652107289182196982785067)
          ·
            refine ⟨3978160933773295474177601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2652107289182196982785067 3978160933773295474177601)
            ·
              refine ⟨2983620700329971605633201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3978160933773295474177601 2983620700329971605633201)
              ·
                refine ⟨2237715525247478704224901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2983620700329971605633201 2237715525247478704224901)
                ·
                  refine ⟨419571660983902257042169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2237715525247478704224901 419571660983902257042169)
                  ·
                    rfl

theorem cell21_1838504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 2, 4].length) (baseStart_1838504 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1838504 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1838504 prefixEnd_1838504 := by exact prefixLift 1838504
  have htrace : WordTrace (prefixWord ++ tailWord_1838504) baseStart_1838504 baseEnd_1838504 := by
    simpa [prefixWord, tailWord_1838504, baseEnd_1838504] using wordTrace_append hprefix tailTrace_1838504
  have hstable : (prefixWord ++ tailWord_1838504).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838504).length < 2 ^ (prefixWord ++ tailWord_1838504).sum := by decide
  have hdescent : baseEnd_1838504 < baseStart_1838504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838532 : List Nat := [2, 3, 3, 2, 1, 2, 1, 2, 5]
def baseStart_1838532 : Nat := 118140960795 + 1838532 * 2 ^ 59
def prefixEnd_1838532 : Nat := 4983230072969 + 3 ^ 40 * 1838532 * 2
def baseEnd_1838532 : Nat := 419578050965380430575445

theorem tailTrace_1838532 : CollatzResearch.WordTrace tailWord_1838532 prefixEnd_1838532 419578050965380430575445 := by
  unfold tailWord_1838532
  simp only [CollatzResearch.WordTrace]
  refine ⟨33528385487660017556094925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44704513983546690074793233 33528385487660017556094925)
  ·
    refine ⟨12573144557872506583535597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33528385487660017556094925 12573144557872506583535597)
    ·
      refine ⟨4714929209202189968825849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12573144557872506583535597 4714929209202189968825849)
      ·
        refine ⟨3536196906901642476619387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4714929209202189968825849 3536196906901642476619387)
        ·
          refine ⟨5304295360352463714929081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3536196906901642476619387 5304295360352463714929081)
          ·
            refine ⟨3978221520264347786196811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5304295360352463714929081 3978221520264347786196811)
            ·
              refine ⟨5967332280396521679295217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3978221520264347786196811 5967332280396521679295217)
              ·
                refine ⟨4475499210297391259471413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5967332280396521679295217 4475499210297391259471413)
                ·
                  refine ⟨419578050965380430575445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4475499210297391259471413 419578050965380430575445)
                  ·
                    rfl

theorem cell21_1838532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 2, 5].length) (baseStart_1838532 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1838532 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1838532 prefixEnd_1838532 := by exact prefixLift 1838532
  have htrace : WordTrace (prefixWord ++ tailWord_1838532) baseStart_1838532 baseEnd_1838532 := by
    simpa [prefixWord, tailWord_1838532, baseEnd_1838532] using wordTrace_append hprefix tailTrace_1838532
  have hstable : (prefixWord ++ tailWord_1838532).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838532).length < 2 ^ (prefixWord ++ tailWord_1838532).sum := by decide
  have hdescent : baseEnd_1838532 < baseStart_1838532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838543 : List Nat := [1, 1, 2, 1, 1, 4, 2, 9]
def baseStart_1838543 : Nat := 118140960795 + 1838543 * 2 ^ 59
def prefixEnd_1838543 : Nat := 4983230072969 + 3 ^ 40 * 1838543 * 2
def baseEnd_1838543 : Nat := 139860187105082285297363

theorem tailTrace_1838543 : CollatzResearch.WordTrace tailWord_1838543 prefixEnd_1838543 139860187105082285297363 := by
  unfold tailWord_1838543
  simp only [CollatzResearch.WordTrace]
  refine ⟨67057172178280183990840283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44704781452186789327226855 67057172178280183990840283)
  ·
    refine ⟨100585758267420275986260425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67057172178280183990840283 100585758267420275986260425)
    ·
      refine ⟨75439318700565206989695319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100585758267420275986260425 75439318700565206989695319)
      ·
        refine ⟨113158978050847810484542979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75439318700565206989695319 113158978050847810484542979)
        ·
          refine ⟨169738467076271715726814469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113158978050847810484542979 169738467076271715726814469)
          ·
            refine ⟨31825962576800946698777713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 169738467076271715726814469 31825962576800946698777713)
            ·
              refine ⟨23869471932600710024083285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31825962576800946698777713 23869471932600710024083285)
              ·
                refine ⟨139860187105082285297363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23869471932600710024083285 139860187105082285297363)
                ·
                  rfl

theorem cell21_1838543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 9].length) (baseStart_1838543 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1838543 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1838543 prefixEnd_1838543 := by exact prefixLift 1838543
  have htrace : WordTrace (prefixWord ++ tailWord_1838543) baseStart_1838543 baseEnd_1838543 := by
    simpa [prefixWord, tailWord_1838543, baseEnd_1838543] using wordTrace_append hprefix tailTrace_1838543
  have hstable : (prefixWord ++ tailWord_1838543).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838543).length < 2 ^ (prefixWord ++ tailWord_1838543).sum := by decide
  have hdescent : baseEnd_1838543 < baseStart_1838543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838563 : List Nat := [1, 1, 1, 6, 2, 3, 1, 2, 4]
def baseStart_1838563 : Nat := 118140960795 + 1838563 * 2 ^ 59
def prefixEnd_1838563 : Nat := 4983230072969 + 3 ^ 40 * 1838563 * 2
def baseEnd_1838563 : Nat := 419585125587731265558715

theorem tailTrace_1838563 : CollatzResearch.WordTrace tailWord_1838563 prefixEnd_1838563 419585125587731265558715 := by
  unfold tailWord_1838563
  simp only [CollatzResearch.WordTrace]
  refine ⟨67057901638207727406568343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44705267758805151604378895 67057901638207727406568343)
  ·
    refine ⟨100586852457311591109852515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67057901638207727406568343 100586852457311591109852515)
    ·
      refine ⟨150880278685967386664778773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100586852457311591109852515 150880278685967386664778773)
      ·
        refine ⟨7072513063404721249911505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 150880278685967386664778773 7072513063404721249911505)
        ·
          refine ⟨5304384797553540937433629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7072513063404721249911505 5304384797553540937433629)
          ·
            refine ⟨1989144299082577851537611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5304384797553540937433629 1989144299082577851537611)
            ·
              refine ⟨2983716448623866777306417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1989144299082577851537611 2983716448623866777306417)
              ·
                refine ⟨2237787336467900082979813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2983716448623866777306417 2237787336467900082979813)
                ·
                  refine ⟨419585125587731265558715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2237787336467900082979813 419585125587731265558715)
                  ·
                    rfl

theorem cell21_1838563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 2, 4].length) (baseStart_1838563 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1838563 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1838563 prefixEnd_1838563 := by exact prefixLift 1838563
  have htrace : WordTrace (prefixWord ++ tailWord_1838563) baseStart_1838563 baseEnd_1838563 := by
    simpa [prefixWord, tailWord_1838563, baseEnd_1838563] using wordTrace_append hprefix tailTrace_1838563
  have hstable : (prefixWord ++ tailWord_1838563).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838563).length < 2 ^ (prefixWord ++ tailWord_1838563).sum := by decide
  have hdescent : baseEnd_1838563 < baseStart_1838563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838594 : List Nat := [3, 4, 1, 2, 1, 1, 4, 5]
def baseStart_1838594 : Nat := 118140960795 + 1838594 * 2 ^ 59
def prefixEnd_1838594 : Nat := 4983230072969 + 3 ^ 40 * 1838594 * 2
def baseEnd_1838594 : Nat := 139864066736694033513995

theorem tailTrace_1838594 : CollatzResearch.WordTrace tailWord_1838594 prefixEnd_1838594 139864066736694033513995 := by
  unfold tailWord_1838594
  simp only [CollatzResearch.WordTrace]
  refine ⟨16764758075273854925236709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44706021534063613133964557 16764758075273854925236709)
  ·
    refine ⟨3143392139113847798481883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16764758075273854925236709 3143392139113847798481883)
    ·
      refine ⟨4715088208670771697722825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3143392139113847798481883 4715088208670771697722825)
      ·
        refine ⟨3536316156503078773292119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4715088208670771697722825 3536316156503078773292119)
        ·
          refine ⟨5304474234754618159938179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3536316156503078773292119 5304474234754618159938179)
          ·
            refine ⟨7956711352131927239907269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5304474234754618159938179 7956711352131927239907269)
            ·
              refine ⟨1491883378524736357482613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7956711352131927239907269 1491883378524736357482613)
              ·
                refine ⟨139864066736694033513995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1491883378524736357482613 139864066736694033513995)
                ·
                  rfl

theorem cell21_1838594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 4, 5].length) (baseStart_1838594 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1838594 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1838594 prefixEnd_1838594 := by exact prefixLift 1838594
  have htrace : WordTrace (prefixWord ++ tailWord_1838594) baseStart_1838594 baseEnd_1838594 := by
    simpa [prefixWord, tailWord_1838594, baseEnd_1838594] using wordTrace_append hprefix tailTrace_1838594
  have hstable : (prefixWord ++ tailWord_1838594).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838594).length < 2 ^ (prefixWord ++ tailWord_1838594).sum := by decide
  have hdescent : baseEnd_1838594 < baseStart_1838594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838625 : List Nat := [1, 2, 3, 2, 2, 3, 3, 2, 3]
def baseStart_1838625 : Nat := 118140960795 + 1838625 * 2 ^ 59
def prefixEnd_1838625 : Nat := 4983230072969 + 3 ^ 40 * 1838625 * 2
def baseEnd_1838625 : Nat := 419599274832432935525255

theorem tailTrace_1838625 : CollatzResearch.WordTrace tailWord_1838625 prefixEnd_1838625 419599274832432935525255 := by
  unfold tailWord_1838625
  simp only [CollatzResearch.WordTrace]
  refine ⟨67060162963983111995325329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44706775309322074663550219 67060162963983111995325329)
  ·
    refine ⟨50295122222987333996493997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67060162963983111995325329 50295122222987333996493997)
    ·
      refine ⟨18860670833620250248685249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50295122222987333996493997 18860670833620250248685249)
      ·
        refine ⟨14145503125215187686513937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18860670833620250248685249 14145503125215187686513937)
        ·
          refine ⟨10609127343911390764885453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14145503125215187686513937 10609127343911390764885453)
          ·
            refine ⟨3978422753966771536832045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10609127343911390764885453 3978422753966771536832045)
            ·
              refine ⟨1491908532737539326312017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3978422753966771536832045 1491908532737539326312017)
              ·
                refine ⟨1118931399553154494734013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1491908532737539326312017 1118931399553154494734013)
                ·
                  refine ⟨419599274832432935525255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1118931399553154494734013 419599274832432935525255)
                  ·
                    rfl

theorem cell21_1838625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 3, 2, 3].length) (baseStart_1838625 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1838625 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1838625 prefixEnd_1838625 := by exact prefixLift 1838625
  have htrace : WordTrace (prefixWord ++ tailWord_1838625) baseStart_1838625 baseEnd_1838625 := by
    simpa [prefixWord, tailWord_1838625, baseEnd_1838625] using wordTrace_append hprefix tailTrace_1838625
  have hstable : (prefixWord ++ tailWord_1838625).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838625).length < 2 ^ (prefixWord ++ tailWord_1838625).sum := by decide
  have hdescent : baseEnd_1838625 < baseStart_1838625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838650 : List Nat := [3, 1, 1, 1, 3, 2, 2, 1, 7]
def baseStart_1838650 : Nat := 118140960795 + 1838650 * 2 ^ 59
def prefixEnd_1838650 : Nat := 4983230072969 + 3 ^ 40 * 1838650 * 2
def baseEnd_1838650 : Nat := 419604980173038447608537

theorem tailTrace_1838650 : CollatzResearch.WordTrace tailWord_1838650 prefixEnd_1838650 419604980173038447608537 := by
  unfold tailWord_1838650
  simp only [CollatzResearch.WordTrace]
  refine ⟨16765268697223135316246351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44707383192595027509990269 16765268697223135316246351)
  ·
    refine ⟨25147903045834702974369527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16765268697223135316246351 25147903045834702974369527)
    ·
      refine ⟨37721854568752054461554291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25147903045834702974369527 37721854568752054461554291)
      ·
        refine ⟨56582781853128081692331437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37721854568752054461554291 56582781853128081692331437)
        ·
          refine ⟨21218543194923030634624289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56582781853128081692331437 21218543194923030634624289)
          ·
            refine ⟨15913907396192272975968217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21218543194923030634624289 15913907396192272975968217)
            ·
              refine ⟨11935430547144204731976163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15913907396192272975968217 11935430547144204731976163)
              ·
                refine ⟨17903145820716307097964245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11935430547144204731976163 17903145820716307097964245)
                ·
                  refine ⟨419604980173038447608537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17903145820716307097964245 419604980173038447608537)
                  ·
                    rfl

theorem cell21_1838650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 7].length) (baseStart_1838650 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1838650 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1838650 prefixEnd_1838650 := by exact prefixLift 1838650
  have htrace : WordTrace (prefixWord ++ tailWord_1838650) baseStart_1838650 baseEnd_1838650 := by
    simpa [prefixWord, tailWord_1838650, baseEnd_1838650] using wordTrace_append hprefix tailTrace_1838650
  have hstable : (prefixWord ++ tailWord_1838650).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838650).length < 2 ^ (prefixWord ++ tailWord_1838650).sum := by decide
  have hdescent : baseEnd_1838650 < baseStart_1838650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838667 : List Nat := [1, 1, 1, 1, 3, 1, 3, 7, 3]
def baseStart_1838667 : Nat := 118140960795 + 1838667 * 2 ^ 59
def prefixEnd_1838667 : Nat := 4983230072969 + 3 ^ 40 * 1838667 * 2
def baseEnd_1838667 : Nat := 419608859804650195825169

theorem tailTrace_1838667 : CollatzResearch.WordTrace tailWord_1838667 prefixEnd_1838667 419608859804650195825169 := by
  unfold tailWord_1838667
  simp only [CollatzResearch.WordTrace]
  refine ⟨67061694829830953168354255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44707796553220635445569503 67061694829830953168354255)
  ·
    refine ⟨100592542244746429752531383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67061694829830953168354255 100592542244746429752531383)
    ·
      refine ⟨150888813367119644628797075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100592542244746429752531383 150888813367119644628797075)
      ·
        refine ⟨226333220050679466943195613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150888813367119644628797075 226333220050679466943195613)
        ·
          refine ⟨84874957519004800103698355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226333220050679466943195613 84874957519004800103698355)
          ·
            refine ⟨127312436278507200155547533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84874957519004800103698355 127312436278507200155547533)
            ·
              refine ⟨47742163604440200058330325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127312436278507200155547533 47742163604440200058330325)
              ·
                refine ⟨1118956959479067188867117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 47742163604440200058330325 1118956959479067188867117)
                ·
                  refine ⟨419608859804650195825169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1118956959479067188867117 419608859804650195825169)
                  ·
                    rfl

theorem cell21_1838667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 7, 3].length) (baseStart_1838667 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1838667 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1838667 prefixEnd_1838667 := by exact prefixLift 1838667
  have htrace : WordTrace (prefixWord ++ tailWord_1838667) baseStart_1838667 baseEnd_1838667 := by
    simpa [prefixWord, tailWord_1838667, baseEnd_1838667] using wordTrace_append hprefix tailTrace_1838667
  have hstable : (prefixWord ++ tailWord_1838667).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838667).length < 2 ^ (prefixWord ++ tailWord_1838667).sum := by decide
  have hdescent : baseEnd_1838667 < baseStart_1838667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838698 : List Nat := [3, 1, 3, 2, 1, 2, 2, 3, 4]
def baseStart_1838698 : Nat := 118140960795 + 1838698 * 2 ^ 59
def prefixEnd_1838698 : Nat := 4983230072969 + 3 ^ 40 * 1838698 * 2
def baseEnd_1838698 : Nat := 419615934427001030808439

theorem tailTrace_1838698 : CollatzResearch.WordTrace tailWord_1838698 prefixEnd_1838698 419615934427001030808439 := by
  unfold tailWord_1838698
  simp only [CollatzResearch.WordTrace]
  refine ⟨16765706373179661365683187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44708550328479096975155165 16765706373179661365683187)
  ·
    refine ⟨25148559559769492048524781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16765706373179661365683187 25148559559769492048524781)
    ·
      refine ⟨9430709834913559518196793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25148559559769492048524781 9430709834913559518196793)
      ·
        refine ⟨7073032376185169638647595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9430709834913559518196793 7073032376185169638647595)
        ·
          refine ⟨10609548564277754457971393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7073032376185169638647595 10609548564277754457971393)
          ·
            refine ⟨7957161423208315843478545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10609548564277754457971393 7957161423208315843478545)
            ·
              refine ⟨5967871067406236882608909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7957161423208315843478545 5967871067406236882608909)
              ·
                refine ⟨2237951650277338830978341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5967871067406236882608909 2237951650277338830978341)
                ·
                  refine ⟨419615934427001030808439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2237951650277338830978341 419615934427001030808439)
                  ·
                    rfl

theorem cell21_1838698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 3, 4].length) (baseStart_1838698 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1838698 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1838698 prefixEnd_1838698 := by exact prefixLift 1838698
  have htrace : WordTrace (prefixWord ++ tailWord_1838698) baseStart_1838698 baseEnd_1838698 := by
    simpa [prefixWord, tailWord_1838698, baseEnd_1838698] using wordTrace_append hprefix tailTrace_1838698
  have hstable : (prefixWord ++ tailWord_1838698).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838698).length < 2 ^ (prefixWord ++ tailWord_1838698).sum := by decide
  have hdescent : baseEnd_1838698 < baseStart_1838698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838743 : List Nat := [1, 1, 3, 3, 2, 3, 2, 1, 5]
def baseStart_1838743 : Nat := 118140960795 + 1838743 * 2 ^ 59
def prefixEnd_1838743 : Nat := 4983230072969 + 3 ^ 40 * 1838743 * 2
def baseEnd_1838743 : Nat := 419626204040090952558347

theorem tailTrace_1838743 : CollatzResearch.WordTrace tailWord_1838743 prefixEnd_1838743 419626204040090952558347 := by
  unfold tailWord_1838743
  simp only [CollatzResearch.WordTrace]
  refine ⟨67064466777555618148120883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44709644518370412098747255 67064466777555618148120883)
  ·
    refine ⟨100596700166333427222181325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67064466777555618148120883 100596700166333427222181325)
    ·
      refine ⟨37723762562375035208317997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100596700166333427222181325 37723762562375035208317997)
      ·
        refine ⟨14146410960890638203119249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37723762562375035208317997 14146410960890638203119249)
        ·
          refine ⟨10609808220667978652339437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14146410960890638203119249 10609808220667978652339437)
          ·
            refine ⟨3978678082750491994627289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10609808220667978652339437 3978678082750491994627289)
            ·
              refine ⟨2984008562062868995970467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3978678082750491994627289 2984008562062868995970467)
              ·
                refine ⟨4476012843094303493955701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2984008562062868995970467 4476012843094303493955701)
                ·
                  refine ⟨419626204040090952558347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4476012843094303493955701 419626204040090952558347)
                  ·
                    rfl

theorem cell21_1838743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 1, 5].length) (baseStart_1838743 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1838743 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1838743 prefixEnd_1838743 := by exact prefixLift 1838743
  have htrace : WordTrace (prefixWord ++ tailWord_1838743) baseStart_1838743 baseEnd_1838743 := by
    simpa [prefixWord, tailWord_1838743, baseEnd_1838743] using wordTrace_append hprefix tailTrace_1838743
  have hstable : (prefixWord ++ tailWord_1838743).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838743).length < 2 ^ (prefixWord ++ tailWord_1838743).sum := by decide
  have hdescent : baseEnd_1838743 < baseStart_1838743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838757 : List Nat := [1, 3, 1, 2, 1, 2, 2, 5, 4]
def baseStart_1838757 : Nat := 118140960795 + 1838757 * 2 ^ 59
def prefixEnd_1838757 : Nat := 4983230072969 + 3 ^ 40 * 1838757 * 2
def baseEnd_1838757 : Nat := 419629399030830039324985

theorem tailTrace_1838757 : CollatzResearch.WordTrace tailWord_1838757 prefixEnd_1838757 419629399030830039324985 := by
  unfold tailWord_1838757
  simp only [CollatzResearch.WordTrace]
  refine ⟨67064977399504898539130525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44709984933003265692753683 67064977399504898539130525)
  ·
    refine ⟨25149366524814336952173947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67064977399504898539130525 25149366524814336952173947)
    ·
      refine ⟨37724049787221505428260921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25149366524814336952173947 37724049787221505428260921)
      ·
        refine ⟨28293037340416129071195691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37724049787221505428260921 28293037340416129071195691)
        ·
          refine ⟨42439556010624193606793537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28293037340416129071195691 42439556010624193606793537)
          ·
            refine ⟨31829667007968145205095153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42439556010624193606793537 31829667007968145205095153)
            ·
              refine ⟨23872250255976108903821365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31829667007968145205095153 23872250255976108903821365)
              ·
                refine ⟨2238023461497760209733253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23872250255976108903821365 2238023461497760209733253)
                ·
                  refine ⟨419629399030830039324985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2238023461497760209733253 419629399030830039324985)
                  ·
                    rfl

theorem cell21_1838757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 5, 4].length) (baseStart_1838757 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1838757 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1838757 prefixEnd_1838757 := by exact prefixLift 1838757
  have htrace : WordTrace (prefixWord ++ tailWord_1838757) baseStart_1838757 baseEnd_1838757 := by
    simpa [prefixWord, tailWord_1838757, baseEnd_1838757] using wordTrace_append hprefix tailTrace_1838757
  have hstable : (prefixWord ++ tailWord_1838757).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838757).length < 2 ^ (prefixWord ++ tailWord_1838757).sum := by decide
  have hdescent : baseEnd_1838757 < baseStart_1838757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838771 : List Nat := [1, 1, 1, 2, 3, 3, 3, 7]
def baseStart_1838771 : Nat := 118140960795 + 1838771 * 2 ^ 59
def prefixEnd_1838771 : Nat := 4983230072969 + 3 ^ 40 * 1838771 * 2
def baseEnd_1838771 : Nat := 139877531340523042030541

theorem tailTrace_1838771 : CollatzResearch.WordTrace tailWord_1838771 prefixEnd_1838771 139877531340523042030541 := by
  unfold tailWord_1838771
  simp only [CollatzResearch.WordTrace]
  refine ⟨67065488021454178930140167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44710325347636119286760111 67065488021454178930140167)
  ·
    refine ⟨100598232032181268395210251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67065488021454178930140167 100598232032181268395210251)
    ·
      refine ⟨150897348048271902592815377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100598232032181268395210251 150897348048271902592815377)
      ·
        refine ⟨113173011036203926944611533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150897348048271902592815377 113173011036203926944611533)
        ·
          refine ⟨42439879138576472604229325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113173011036203926944611533 42439879138576472604229325)
          ·
            refine ⟨15914954676966177226585997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42439879138576472604229325 15914954676966177226585997)
            ·
              refine ⟨5968108003862316459969749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15914954676966177226585997 5968108003862316459969749)
              ·
                refine ⟨139877531340523042030541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5968108003862316459969749 139877531340523042030541)
                ·
                  rfl

theorem cell21_1838771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 7].length) (baseStart_1838771 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1838771 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1838771 prefixEnd_1838771 := by exact prefixLift 1838771
  have htrace : WordTrace (prefixWord ++ tailWord_1838771) baseStart_1838771 baseEnd_1838771 := by
    simpa [prefixWord, tailWord_1838771, baseEnd_1838771] using wordTrace_append hprefix tailTrace_1838771
  have hstable : (prefixWord ++ tailWord_1838771).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838771).length < 2 ^ (prefixWord ++ tailWord_1838771).sum := by decide
  have hdescent : baseEnd_1838771 < baseStart_1838771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838977 : List Nat := [1, 2, 4, 4, 2, 1, 2, 1, 4]
def baseStart_1838977 : Nat := 118140960795 + 1838977 * 2 ^ 59
def prefixEnd_1838977 : Nat := 4983230072969 + 3 ^ 40 * 1838977 * 2
def baseEnd_1838977 : Nat := 419679606028158545657869

theorem tailTrace_1838977 : CollatzResearch.WordTrace tailWord_1838977 prefixEnd_1838977 419679606028158545657869 := by
  unfold tailWord_1838977
  simp only [CollatzResearch.WordTrace]
  refine ⟨67073001458707876112139185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44715334305805250741426123 67073001458707876112139185)
  ·
    refine ⟨50304751094030907084104389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67073001458707876112139185 50304751094030907084104389)
    ·
      refine ⟨9432140830130795078269573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50304751094030907084104389 9432140830130795078269573)
      ·
        refine ⟨1768526405649524077175545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9432140830130795078269573 1768526405649524077175545)
        ·
          refine ⟨1326394804237143057881659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1768526405649524077175545 1326394804237143057881659)
          ·
            refine ⟨1989592206355714586822489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1326394804237143057881659 1989592206355714586822489)
            ·
              refine ⟨1492194154766785940116867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1989592206355714586822489 1492194154766785940116867)
              ·
                refine ⟨2238291232150178910175301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1492194154766785940116867 2238291232150178910175301)
                ·
                  refine ⟨419679606028158545657869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2238291232150178910175301 419679606028158545657869)
                  ·
                    rfl

theorem cell21_1838977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 2, 1, 4].length) (baseStart_1838977 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1838977 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1838977 prefixEnd_1838977 := by exact prefixLift 1838977
  have htrace : WordTrace (prefixWord ++ tailWord_1838977) baseStart_1838977 baseEnd_1838977 := by
    simpa [prefixWord, tailWord_1838977, baseEnd_1838977] using wordTrace_append hprefix tailTrace_1838977
  have hstable : (prefixWord ++ tailWord_1838977).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838977).length < 2 ^ (prefixWord ++ tailWord_1838977).sum := by decide
  have hdescent : baseEnd_1838977 < baseStart_1838977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838985 : List Nat := [1, 2, 1, 1, 5, 1, 3, 3, 4]
def baseStart_1838985 : Nat := 118140960795 + 1838985 * 2 ^ 59
def prefixEnd_1838985 : Nat := 4983230072969 + 3 ^ 40 * 1838985 * 2
def baseEnd_1838985 : Nat := 419681431737152309524519

theorem tailTrace_1838985 : CollatzResearch.WordTrace tailWord_1838985 prefixEnd_1838985 419681431737152309524519 := by
  unfold tailWord_1838985
  simp only [CollatzResearch.WordTrace]
  refine ⟨67073293242678893478430409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44715528828452595652286939 67073293242678893478430409)
  ·
    refine ⟨50304969932009170108822807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67073293242678893478430409 50304969932009170108822807)
    ·
      refine ⟨75457454898013755163234211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50304969932009170108822807 75457454898013755163234211)
      ·
        refine ⟨113186182347020632744851317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75457454898013755163234211 113186182347020632744851317)
        ·
          refine ⟨10611204595033184319829811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 113186182347020632744851317 10611204595033184319829811)
          ·
            refine ⟨15916806892549776479744717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10611204595033184319829811 15916806892549776479744717)
            ·
              refine ⟨5968802584706166179904269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15916806892549776479744717 5968802584706166179904269)
              ·
                refine ⟨2238300969264812317464101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5968802584706166179904269 2238300969264812317464101)
                ·
                  refine ⟨419681431737152309524519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2238300969264812317464101 419681431737152309524519)
                  ·
                    rfl

theorem cell21_1838985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 3, 4].length) (baseStart_1838985 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1838985 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1838985 prefixEnd_1838985 := by exact prefixLift 1838985
  have htrace : WordTrace (prefixWord ++ tailWord_1838985) baseStart_1838985 baseEnd_1838985 := by
    simpa [prefixWord, tailWord_1838985, baseEnd_1838985] using wordTrace_append hprefix tailTrace_1838985
  have hstable : (prefixWord ++ tailWord_1838985).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838985).length < 2 ^ (prefixWord ++ tailWord_1838985).sum := by decide
  have hdescent : baseEnd_1838985 < baseStart_1838985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838999 : List Nat := [1, 1, 3, 3, 1, 3, 2, 7]
def baseStart_1838999 : Nat := 118140960795 + 1838999 * 2 ^ 59
def prefixEnd_1838999 : Nat := 4983230072969 + 3 ^ 40 * 1838999 * 2
def baseEnd_1838999 : Nat := 139894875575963798763719

theorem tailTrace_1838999 : CollatzResearch.WordTrace tailWord_1838999 prefixEnd_1838999 139894875575963798763719 := by
  unfold tailWord_1838999
  simp only [CollatzResearch.WordTrace]
  refine ⟨67073803864628173869440051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44715869243085449246293367 67073803864628173869440051)
  ·
    refine ⟨100610705796942260804160077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67073803864628173869440051 100610705796942260804160077)
    ·
      refine ⟨37729014673853347801560029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100610705796942260804160077 37729014673853347801560029)
      ·
        refine ⟨14148380502695005425585011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37729014673853347801560029 14148380502695005425585011)
        ·
          refine ⟨21222570754042508138377517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14148380502695005425585011 21222570754042508138377517)
          ·
            refine ⟨7958464032765940551891569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21222570754042508138377517 7958464032765940551891569)
            ·
              refine ⟨5968848024574455413918677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7958464032765940551891569 5968848024574455413918677)
              ·
                refine ⟨139894875575963798763719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5968848024574455413918677 139894875575963798763719)
                ·
                  rfl

theorem cell21_1838999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 7].length) (baseStart_1838999 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1838999 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1838999 prefixEnd_1838999 := by exact prefixLift 1838999
  have htrace : WordTrace (prefixWord ++ tailWord_1838999) baseStart_1838999 baseEnd_1838999 := by
    simpa [prefixWord, tailWord_1838999, baseEnd_1838999] using wordTrace_append hprefix tailTrace_1838999
  have hstable : (prefixWord ++ tailWord_1838999).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838999).length < 2 ^ (prefixWord ++ tailWord_1838999).sum := by decide
  have hdescent : baseEnd_1838999 < baseStart_1838999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839016 : List Nat := [2, 1, 6, 2, 10]
def baseStart_1839016 : Nat := 118140960795 + 1839016 * 2 ^ 59
def prefixEnd_1839016 : Nat := 4983230072969 + 3 ^ 40 * 1839016 * 2
def baseEnd_1839016 : Nat := 5181339584685224006269

theorem tailTrace_1839016 : CollatzResearch.WordTrace tailWord_1839016 prefixEnd_1839016 5181339584685224006269 := by
  unfold tailWord_1839016
  simp only [CollatzResearch.WordTrace]
  refine ⟨33537211952783292886404451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44716282603711057181872601 33537211952783292886404451)
  ·
    refine ⟨50305817929174939329606677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33537211952783292886404451 50305817929174939329606677)
    ·
      refine ⟨2358085215430075281075313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 50305817929174939329606677 2358085215430075281075313)
      ·
        refine ⟨1768563911572556460806485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2358085215430075281075313 1768563911572556460806485)
        ·
          refine ⟨5181339584685224006269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1768563911572556460806485 5181339584685224006269)
          ·
            rfl

theorem cell21_1839016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 10].length) (baseStart_1839016 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1839016 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1839016 prefixEnd_1839016 := by exact prefixLift 1839016
  have htrace : WordTrace (prefixWord ++ tailWord_1839016) baseStart_1839016 baseEnd_1839016 := by
    simpa [prefixWord, tailWord_1839016, baseEnd_1839016] using wordTrace_append hprefix tailTrace_1839016
  have hstable : (prefixWord ++ tailWord_1839016).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839016).length < 2 ^ (prefixWord ++ tailWord_1839016).sum := by decide
  have hdescent : baseEnd_1839016 < baseStart_1839016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839075 : List Nat := [1, 1, 1, 6, 1, 3, 8]
def baseStart_1839075 : Nat := 118140960795 + 1839075 * 2 ^ 59
def prefixEnd_1839075 : Nat := 4983230072969 + 3 ^ 40 * 1839075 * 2
def baseEnd_1839075 : Nat := 46633552329259128113815

theorem tailTrace_1839075 : CollatzResearch.WordTrace tailWord_1839075 prefixEnd_1839075 46633552329259128113815 := by
  unfold tailWord_1839075
  simp only [CollatzResearch.WordTrace]
  refine ⟨67076575812352838849206679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44717717208235225899471119 67076575812352838849206679)
  ·
    refine ⟨100614863718529258273810019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67076575812352838849206679 100614863718529258273810019)
    ·
      refine ⟨150922295577793887410715029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100614863718529258273810019 150922295577793887410715029)
      ·
        refine ⟨7074482605209088472377267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 150922295577793887410715029 7074482605209088472377267)
        ·
          refine ⟨10611723907813632708565901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7074482605209088472377267 10611723907813632708565901)
          ·
            refine ⟨3979396465430112265712213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10611723907813632708565901 3979396465430112265712213)
            ·
              refine ⟨46633552329259128113815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3979396465430112265712213 46633552329259128113815)
              ·
                rfl

theorem cell21_1839075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 8].length) (baseStart_1839075 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1839075 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1839075 prefixEnd_1839075 := by exact prefixLift 1839075
  have htrace : WordTrace (prefixWord ++ tailWord_1839075) baseStart_1839075 baseEnd_1839075 := by
    simpa [prefixWord, tailWord_1839075, baseEnd_1839075] using wordTrace_append hprefix tailTrace_1839075
  have hstable : (prefixWord ++ tailWord_1839075).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839075).length < 2 ^ (prefixWord ++ tailWord_1839075).sum := by decide
  have hdescent : baseEnd_1839075 < baseStart_1839075 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839123 : List Nat := [1, 1, 1, 2, 1, 4, 5, 3, 3]
def baseStart_1839123 : Nat := 118140960795 + 1839123 * 2 ^ 59
def prefixEnd_1839123 : Nat := 4983230072969 + 3 ^ 40 * 1839123 * 2
def baseEnd_1839123 : Nat := 419712925217294736224237

theorem tailTrace_1839123 : CollatzResearch.WordTrace tailWord_1839123 prefixEnd_1839123 419712925217294736224237 := by
  unfold tailWord_1839123
  simp only [CollatzResearch.WordTrace]
  refine ⟨67078326516178943046954023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44718884344119295364636015 67078326516178943046954023)
  ·
    refine ⟨100617489774268414570431035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67078326516178943046954023 100617489774268414570431035)
    ·
      refine ⟨150926234661402621855646553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100617489774268414570431035 150926234661402621855646553)
      ·
        refine ⟨113194675996051966391734915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150926234661402621855646553 113194675996051966391734915)
        ·
          refine ⟨169792013994077949587602373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113194675996051966391734915 169792013994077949587602373)
          ·
            refine ⟨31836002623889615547675445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 169792013994077949587602373 31836002623889615547675445)
            ·
              refine ⟨2984625245989651457594573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31836002623889615547675445 2984625245989651457594573)
              ·
                refine ⟨1119234467246119296597965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2984625245989651457594573 1119234467246119296597965)
                ·
                  refine ⟨419712925217294736224237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1119234467246119296597965 419712925217294736224237)
                  ·
                    rfl

theorem cell21_1839123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 3, 3].length) (baseStart_1839123 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1839123 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1839123 prefixEnd_1839123 := by exact prefixLift 1839123
  have htrace : WordTrace (prefixWord ++ tailWord_1839123) baseStart_1839123 baseEnd_1839123 := by
    simpa [prefixWord, tailWord_1839123, baseEnd_1839123] using wordTrace_append hprefix tailTrace_1839123
  have hstable : (prefixWord ++ tailWord_1839123).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839123).length < 2 ^ (prefixWord ++ tailWord_1839123).sum := by decide
  have hdescent : baseEnd_1839123 < baseStart_1839123 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839140 : List Nat := [2, 3, 1, 4, 2, 2, 1, 1, 5]
def baseStart_1839140 : Nat := 118140960795 + 1839140 * 2 ^ 59
def prefixEnd_1839140 : Nat := 4983230072969 + 3 ^ 40 * 1839140 * 2
def baseEnd_1839140 : Nat := 419716804848906484440869

theorem tailTrace_1839140 : CollatzResearch.WordTrace tailWord_1839140 prefixEnd_1839140 419716804848906484440869 := by
  unfold tailWord_1839140
  simp only [CollatzResearch.WordTrace]
  refine ⟨33539473278558677475161437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44719297704744903300215249 33539473278558677475161437)
  ·
    refine ⟨12577302479459504053185539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33539473278558677475161437 12577302479459504053185539)
    ·
      refine ⟨18865953719189256079778309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12577302479459504053185539 18865953719189256079778309)
      ·
        refine ⟨3537366322347985514958433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18865953719189256079778309 3537366322347985514958433)
        ·
          refine ⟨2653024741760989136218825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3537366322347985514958433 2653024741760989136218825)
          ·
            refine ⟨1989768556320741852164119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2653024741760989136218825 1989768556320741852164119)
            ·
              refine ⟨2984652834481112778246179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1989768556320741852164119 2984652834481112778246179)
              ·
                refine ⟨4476979251721669167369269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2984652834481112778246179 4476979251721669167369269)
                ·
                  refine ⟨419716804848906484440869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4476979251721669167369269 419716804848906484440869)
                  ·
                    rfl

theorem cell21_1839140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 1, 5].length) (baseStart_1839140 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1839140 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1839140 prefixEnd_1839140 := by exact prefixLift 1839140
  have htrace : WordTrace (prefixWord ++ tailWord_1839140) baseStart_1839140 baseEnd_1839140 := by
    simpa [prefixWord, tailWord_1839140, baseEnd_1839140] using wordTrace_append hprefix tailTrace_1839140
  have hstable : (prefixWord ++ tailWord_1839140).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839140).length < 2 ^ (prefixWord ++ tailWord_1839140).sum := by decide
  have hdescent : baseEnd_1839140 < baseStart_1839140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839154 : List Nat := [3, 2, 1, 1, 2, 3, 4, 1, 4]
def baseStart_1839154 : Nat := 118140960795 + 1839154 * 2 ^ 59
def prefixEnd_1839154 : Nat := 4983230072969 + 3 ^ 40 * 1839154 * 2
def baseEnd_1839154 : Nat := 419719999839645571207507

theorem tailTrace_1839154 : CollatzResearch.WordTrace tailWord_1839154 prefixEnd_1839154 419719999839645571207507 := by
  unfold tailWord_1839154
  simp only [CollatzResearch.WordTrace]
  refine ⟨16769864294766658835333129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44719638119377756894221677 16769864294766658835333129)
  ·
    refine ⟨12577398221074994126499847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16769864294766658835333129 12577398221074994126499847)
    ·
      refine ⟨18866097331612491189749771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12577398221074994126499847 18866097331612491189749771)
      ·
        refine ⟨28299145997418736784624657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18866097331612491189749771 28299145997418736784624657)
        ·
          refine ⟨21224359498064052588468493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28299145997418736784624657 21224359498064052588468493)
          ·
            refine ⟨7959134811774019720675685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21224359498064052588468493 7959134811774019720675685)
            ·
              refine ⟨1492337777207628697626691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7959134811774019720675685 1492337777207628697626691)
              ·
                refine ⟨2238506665811443046440037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1492337777207628697626691 2238506665811443046440037)
                ·
                  refine ⟨419719999839645571207507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2238506665811443046440037 419719999839645571207507)
                  ·
                    rfl

theorem cell21_1839154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 4, 1, 4].length) (baseStart_1839154 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1839154 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1839154 prefixEnd_1839154 := by exact prefixLift 1839154
  have htrace : WordTrace (prefixWord ++ tailWord_1839154) baseStart_1839154 baseEnd_1839154 := by
    simpa [prefixWord, tailWord_1839154, baseEnd_1839154] using wordTrace_append hprefix tailTrace_1839154
  have hstable : (prefixWord ++ tailWord_1839154).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839154).length < 2 ^ (prefixWord ++ tailWord_1839154).sum := by decide
  have hdescent : baseEnd_1839154 < baseStart_1839154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839202 : List Nat := [3, 3, 2, 2, 3, 1, 1, 6]
def baseStart_1839202 : Nat := 118140960795 + 1839202 * 2 ^ 59
def prefixEnd_1839202 : Nat := 4983230072969 + 3 ^ 40 * 1839202 * 2
def baseEnd_1839202 : Nat := 139910318031202718135803

theorem tailTrace_1839202 : CollatzResearch.WordTrace tailWord_1839202 prefixEnd_1839202 139910318031202718135803 := by
  unfold tailWord_1839202
  simp only [CollatzResearch.WordTrace]
  refine ⟨16770301970723184884769965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44720805255261826359386573 16770301970723184884769965)
  ·
    refine ⟨6288863239021194331788737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16770301970723184884769965 6288863239021194331788737)
    ·
      refine ⟨4716647429265895748841553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6288863239021194331788737 4716647429265895748841553)
      ·
        refine ⟨3537485571949421811631165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4716647429265895748841553 3537485571949421811631165)
        ·
          refine ⟨1326557089481033179361687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3537485571949421811631165 1326557089481033179361687)
          ·
            refine ⟨1989835634221549769042531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1326557089481033179361687 1989835634221549769042531)
            ·
              refine ⟨2984753451332324653563797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1989835634221549769042531 2984753451332324653563797)
              ·
                refine ⟨139910318031202718135803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2984753451332324653563797 139910318031202718135803)
                ·
                  rfl

theorem cell21_1839202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 6].length) (baseStart_1839202 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1839202 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1839202 prefixEnd_1839202 := by exact prefixLift 1839202
  have htrace : WordTrace (prefixWord ++ tailWord_1839202) baseStart_1839202 baseEnd_1839202 := by
    simpa [prefixWord, tailWord_1839202, baseEnd_1839202] using wordTrace_append hprefix tailTrace_1839202
  have hstable : (prefixWord ++ tailWord_1839202).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839202).length < 2 ^ (prefixWord ++ tailWord_1839202).sum := by decide
  have hdescent : baseEnd_1839202 < baseStart_1839202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839213 : List Nat := [1, 5, 1, 1, 2, 1, 1, 5, 4]
def baseStart_1839213 : Nat := 118140960795 + 1839213 * 2 ^ 59
def prefixEnd_1839213 : Nat := 4983230072969 + 3 ^ 40 * 1839213 * 2
def baseEnd_1839213 : Nat := 419733464443474579724053

theorem tailTrace_1839213 : CollatzResearch.WordTrace tailWord_1839213 prefixEnd_1839213 419733464443474579724053 := by
  unfold tailWord_1839213
  simp only [CollatzResearch.WordTrace]
  refine ⟨67081609085852888417730293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44721072723901925611820195 67081609085852888417730293)
  ·
    refine ⟨6288900851798708289162215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67081609085852888417730293 6288900851798708289162215)
    ·
      refine ⟨9433351277698062433743323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6288900851798708289162215 9433351277698062433743323)
      ·
        refine ⟨14150026916547093650614985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9433351277698062433743323 14150026916547093650614985)
        ·
          refine ⟨10612520187410320237961239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14150026916547093650614985 10612520187410320237961239)
          ·
            refine ⟨15918780281115480356941859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10612520187410320237961239 15918780281115480356941859)
            ·
              refine ⟨23878170421673220535412789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15918780281115480356941859 23878170421673220535412789)
              ·
                refine ⟨2238578477031864425194949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23878170421673220535412789 2238578477031864425194949)
                ·
                  refine ⟨419733464443474579724053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2238578477031864425194949 419733464443474579724053)
                  ·
                    rfl

theorem cell21_1839213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_1839213 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1839213 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1839213 prefixEnd_1839213 := by exact prefixLift 1839213
  have htrace : WordTrace (prefixWord ++ tailWord_1839213) baseStart_1839213 baseEnd_1839213 := by
    simpa [prefixWord, tailWord_1839213, baseEnd_1839213] using wordTrace_append hprefix tailTrace_1839213
  have hstable : (prefixWord ++ tailWord_1839213).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839213).length < 2 ^ (prefixWord ++ tailWord_1839213).sum := by decide
  have hdescent : baseEnd_1839213 < baseStart_1839213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839241 : List Nat := [1, 2, 1, 1, 4, 2, 1, 2, 7]
def baseStart_1839241 : Nat := 118140960795 + 1839241 * 2 ^ 59
def prefixEnd_1839241 : Nat := 4983230072969 + 3 ^ 40 * 1839241 * 2
def baseEnd_1839241 : Nat := 419739854424952753257329

theorem tailTrace_1839241 : CollatzResearch.WordTrace tailWord_1839241 prefixEnd_1839241 419739854424952753257329 := by
  unfold tailWord_1839241
  simp only [CollatzResearch.WordTrace]
  refine ⟨67082630329751449199749577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44721753553167632799833051 67082630329751449199749577)
  ·
    refine ⟨50311972747313586899812183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67082630329751449199749577 50311972747313586899812183)
    ·
      refine ⟨75467959120970380349718275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50311972747313586899812183 75467959120970380349718275)
      ·
        refine ⟨113201938681455570524577413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75467959120970380349718275 113201938681455570524577413)
        ·
          refine ⟨21225363502772919473358265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113201938681455570524577413 21225363502772919473358265)
          ·
            refine ⟨15919022627079689605018699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21225363502772919473358265 15919022627079689605018699)
            ·
              refine ⟨23878533940619534407528049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15919022627079689605018699 23878533940619534407528049)
              ·
                refine ⟨17908900455464650805646037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23878533940619534407528049 17908900455464650805646037)
                ·
                  refine ⟨419739854424952753257329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17908900455464650805646037 419739854424952753257329)
                  ·
                    rfl

theorem cell21_1839241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 7].length) (baseStart_1839241 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1839241 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1839241 prefixEnd_1839241 := by exact prefixLift 1839241
  have htrace : WordTrace (prefixWord ++ tailWord_1839241) baseStart_1839241 baseEnd_1839241 := by
    simpa [prefixWord, tailWord_1839241, baseEnd_1839241] using wordTrace_append hprefix tailTrace_1839241
  have hstable : (prefixWord ++ tailWord_1839241).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839241).length < 2 ^ (prefixWord ++ tailWord_1839241).sum := by decide
  have hdescent : baseEnd_1839241 < baseStart_1839241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839284 : List Nat := [2, 5, 3, 1, 2, 1, 1, 3, 3]
def baseStart_1839284 : Nat := 118140960795 + 1839284 * 2 ^ 59
def prefixEnd_1839284 : Nat := 4983230072969 + 3 ^ 40 * 1839284 * 2
def baseEnd_1839284 : Nat := 419749667610794234040575

theorem tailTrace_1839284 : CollatzResearch.WordTrace tailWord_1839284 prefixEnd_1839284 419749667610794234040575 := by
  unfold tailWord_1839284
  simp only [CollatzResearch.WordTrace]
  refine ⟨33542099334297833771782453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44722799112397111695709937 33542099334297833771782453)
  ·
    refine ⟨3144571812590421916104605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33542099334297833771782453 3144571812590421916104605)
    ·
      refine ⟨1179214429721408218539227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3144571812590421916104605 1179214429721408218539227)
      ·
        refine ⟨1768821644582112327808841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1179214429721408218539227 1768821644582112327808841)
        ·
          refine ⟨1326616233436584245856631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1768821644582112327808841 1326616233436584245856631)
          ·
            refine ⟨1989924350154876368784947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1326616233436584245856631 1989924350154876368784947)
            ·
              refine ⟨2984886525232314553177421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1989924350154876368784947 2984886525232314553177421)
              ·
                refine ⟨1119332446962117957441533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2984886525232314553177421 1119332446962117957441533)
                ·
                  refine ⟨419749667610794234040575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1119332446962117957441533 419749667610794234040575)
                  ·
                    rfl

theorem cell21_1839284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_1839284 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1839284 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1839284 prefixEnd_1839284 := by exact prefixLift 1839284
  have htrace : WordTrace (prefixWord ++ tailWord_1839284) baseStart_1839284 baseEnd_1839284 := by
    simpa [prefixWord, tailWord_1839284, baseEnd_1839284] using wordTrace_append hprefix tailTrace_1839284
  have hstable : (prefixWord ++ tailWord_1839284).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839284).length < 2 ^ (prefixWord ++ tailWord_1839284).sum := by decide
  have hdescent : baseEnd_1839284 < baseStart_1839284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839368 : List Nat := [2, 1, 3, 2, 3, 1, 4, 2, 3]
def baseStart_1839368 : Nat := 118140960795 + 1839368 * 2 ^ 59
def prefixEnd_1839368 : Nat := 4983230072969 + 3 ^ 40 * 1839368 * 2
def baseEnd_1839368 : Nat := 419768837555228754640403

theorem tailTrace_1839368 : CollatzResearch.WordTrace tailWord_1839368 prefixEnd_1839368 419768837555228754640403 := by
  unfold tailWord_1839368
  simp only [CollatzResearch.WordTrace]
  refine ⟨33543631200145674944811379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44724841600194233259748505 33543631200145674944811379)
  ·
    refine ⟨50315446800218512417217069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33543631200145674944811379 50315446800218512417217069)
    ·
      refine ⟨18868292550081942156456401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50315446800218512417217069 18868292550081942156456401)
      ·
        refine ⟨14151219412561456617342301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18868292550081942156456401 14151219412561456617342301)
        ·
          refine ⟨5306707279710546231503363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14151219412561456617342301 5306707279710546231503363)
          ·
            refine ⟨7960060919565819347255045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5306707279710546231503363 7960060919565819347255045)
            ·
              refine ⟨1492511422418591127610321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7960060919565819347255045 1492511422418591127610321)
              ·
                refine ⟨1119383566813943345707741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1492511422418591127610321 1119383566813943345707741)
                ·
                  refine ⟨419768837555228754640403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1119383566813943345707741 419768837555228754640403)
                  ·
                    rfl

theorem cell21_1839368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 4, 2, 3].length) (baseStart_1839368 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1839368 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1839368 prefixEnd_1839368 := by exact prefixLift 1839368
  have htrace : WordTrace (prefixWord ++ tailWord_1839368) baseStart_1839368 baseEnd_1839368 := by
    simpa [prefixWord, tailWord_1839368, baseEnd_1839368] using wordTrace_append hprefix tailTrace_1839368
  have hstable : (prefixWord ++ tailWord_1839368).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839368).length < 2 ^ (prefixWord ++ tailWord_1839368).sum := by decide
  have hdescent : baseEnd_1839368 < baseStart_1839368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839393 : List Nat := [1, 2, 3, 2, 1, 1, 3, 1, 7]
def baseStart_1839393 : Nat := 118140960795 + 1839393 * 2 ^ 59
def prefixEnd_1839393 : Nat := 4983230072969 + 3 ^ 40 * 1839393 * 2
def baseEnd_1839393 : Nat := 419774542895834266723685

theorem tailTrace_1839393 : CollatzResearch.WordTrace tailWord_1839393 prefixEnd_1839393 419774542895834266723685 := by
  unfold tailWord_1839393
  simp only [CollatzResearch.WordTrace]
  refine ⟨67088174225200779159282833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44725449483467186106188555 67088174225200779159282833)
  ·
    refine ⟨50316130668900584369462125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67088174225200779159282833 50316130668900584369462125)
    ·
      refine ⟨18868549000837719138548297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50316130668900584369462125 18868549000837719138548297)
      ·
        refine ⟨14151411750628289353911223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18868549000837719138548297 14151411750628289353911223)
        ·
          refine ⟨21227117625942434030866835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14151411750628289353911223 21227117625942434030866835)
          ·
            refine ⟨31840676438913651046300253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21227117625942434030866835 31840676438913651046300253)
            ·
              refine ⟨11940253664592619142362595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31840676438913651046300253 11940253664592619142362595)
              ·
                refine ⟨17910380496888928713543893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11940253664592619142362595 17910380496888928713543893)
                ·
                  refine ⟨419774542895834266723685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17910380496888928713543893 419774542895834266723685)
                  ·
                    rfl

theorem cell21_1839393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 7].length) (baseStart_1839393 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1839393 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1839393 prefixEnd_1839393 := by exact prefixLift 1839393
  have htrace : WordTrace (prefixWord ++ tailWord_1839393) baseStart_1839393 baseEnd_1839393 := by
    simpa [prefixWord, tailWord_1839393, baseEnd_1839393] using wordTrace_append hprefix tailTrace_1839393
  have hstable : (prefixWord ++ tailWord_1839393).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839393).length < 2 ^ (prefixWord ++ tailWord_1839393).sum := by decide
  have hdescent : baseEnd_1839393 < baseStart_1839393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839396 : List Nat := [2, 3, 1, 3, 1, 3, 3, 5]
def baseStart_1839396 : Nat := 118140960795 + 1839396 * 2 ^ 59
def prefixEnd_1839396 : Nat := 4983230072969 + 3 ^ 40 * 1839396 * 2
def baseEnd_1839396 : Nat := 139925075845568976057893

theorem tailTrace_1839396 : CollatzResearch.WordTrace tailWord_1839396 prefixEnd_1839396 139925075845568976057893 := by
  unfold tailWord_1839396
  simp only [CollatzResearch.WordTrace]
  refine ⟨33544141822094955335821021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44725522429459940447761361 33544141822094955335821021)
  ·
    refine ⟨12579053183285608250932883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33544141822094955335821021 12579053183285608250932883)
    ·
      refine ⟨18868579774928412376399325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12579053183285608250932883 18868579774928412376399325)
      ·
        refine ⟨7075717415598154641149747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18868579774928412376399325 7075717415598154641149747)
        ·
          refine ⟨10613576123397231961724621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7075717415598154641149747 10613576123397231961724621)
          ·
            refine ⟨3980091046273961985646733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10613576123397231961724621 3980091046273961985646733)
            ·
              refine ⟨1492534142352735744617525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3980091046273961985646733 1492534142352735744617525)
              ·
                refine ⟨139925075845568976057893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1492534142352735744617525 139925075845568976057893)
                ·
                  rfl

theorem cell21_1839396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 3, 5].length) (baseStart_1839396 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1839396 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1839396 prefixEnd_1839396 := by exact prefixLift 1839396
  have htrace : WordTrace (prefixWord ++ tailWord_1839396) baseStart_1839396 baseEnd_1839396 := by
    simpa [prefixWord, tailWord_1839396, baseEnd_1839396] using wordTrace_append hprefix tailTrace_1839396
  have hstable : (prefixWord ++ tailWord_1839396).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839396).length < 2 ^ (prefixWord ++ tailWord_1839396).sum := by decide
  have hdescent : baseEnd_1839396 < baseStart_1839396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839424 : List Nat := [2, 1, 1, 2, 2, 1, 2, 6, 4]
def baseStart_1839424 : Nat := 118140960795 + 1839424 * 2 ^ 59
def prefixEnd_1839424 : Nat := 4983230072969 + 3 ^ 40 * 1839424 * 2
def baseEnd_1839424 : Nat := 419781617518185101706955

theorem tailTrace_1839424 : CollatzResearch.WordTrace tailWord_1839424 prefixEnd_1839424 419781617518185101706955 := by
  unfold tailWord_1839424
  simp only [CollatzResearch.WordTrace]
  refine ⟨33544652444044235726830663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44726203258725647635774217 33544652444044235726830663)
  ·
    refine ⟨50316978666066353590245995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33544652444044235726830663 50316978666066353590245995)
    ·
      refine ⟨75475467999099530385368993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50316978666066353590245995 75475467999099530385368993)
      ·
        refine ⟨56606600999324647789026745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75475467999099530385368993 56606600999324647789026745)
        ·
          refine ⟨42454950749493485841770059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56606600999324647789026745 42454950749493485841770059)
          ·
            refine ⟨63682426124240228762655089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42454950749493485841770059 63682426124240228762655089)
            ·
              refine ⟨47761819593180171571991317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63682426124240228762655089 47761819593180171571991317)
              ·
                refine ⟨2238835293430320542437093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 47761819593180171571991317 2238835293430320542437093)
                ·
                  refine ⟨419781617518185101706955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2238835293430320542437093 419781617518185101706955)
                  ·
                    rfl

theorem cell21_1839424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 6, 4].length) (baseStart_1839424 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1839424 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1839424 prefixEnd_1839424 := by exact prefixLift 1839424
  have htrace : WordTrace (prefixWord ++ tailWord_1839424) baseStart_1839424 baseEnd_1839424 := by
    simpa [prefixWord, tailWord_1839424, baseEnd_1839424] using wordTrace_append hprefix tailTrace_1839424
  have hstable : (prefixWord ++ tailWord_1839424).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839424).length < 2 ^ (prefixWord ++ tailWord_1839424).sum := by decide
  have hdescent : baseEnd_1839424 < baseStart_1839424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839455 : List Nat := [1, 1, 2, 3, 1, 2, 6, 5]
def baseStart_1839455 : Nat := 118140960795 + 1839455 * 2 ^ 59
def prefixEnd_1839455 : Nat := 4983230072969 + 3 ^ 40 * 1839455 * 2
def baseEnd_1839455 : Nat := 139929564046845312230075

theorem tailTrace_1839455 : CollatzResearch.WordTrace tailWord_1839455 prefixEnd_1839455 139929564046845312230075 := by
  unfold tailWord_1839455
  simp only [CollatzResearch.WordTrace]
  refine ⟨67090435550976163748039819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44726957033984109165359879 67090435550976163748039819)
  ·
    refine ⟨100635653326464245622059729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67090435550976163748039819 100635653326464245622059729)
    ·
      refine ⟨75476739994848184216544797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100635653326464245622059729 75476739994848184216544797)
      ·
        refine ⟨28303777498068069081204299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75476739994848184216544797 28303777498068069081204299)
        ·
          refine ⟨42455666247102103621806449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28303777498068069081204299 42455666247102103621806449)
          ·
            refine ⟨31841749685326577716354837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42455666247102103621806449 31841749685326577716354837)
            ·
              refine ⟨1492582016499683330454133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 31841749685326577716354837 1492582016499683330454133)
              ·
                refine ⟨139929564046845312230075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1492582016499683330454133 139929564046845312230075)
                ·
                  rfl

theorem cell21_1839455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 6, 5].length) (baseStart_1839455 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1839455 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1839455 prefixEnd_1839455 := by exact prefixLift 1839455
  have htrace : WordTrace (prefixWord ++ tailWord_1839455) baseStart_1839455 baseEnd_1839455 := by
    simpa [prefixWord, tailWord_1839455, baseEnd_1839455] using wordTrace_append hprefix tailTrace_1839455
  have hstable : (prefixWord ++ tailWord_1839455).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839455).length < 2 ^ (prefixWord ++ tailWord_1839455).sum := by decide
  have hdescent : baseEnd_1839455 < baseStart_1839455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839478 : List Nat := [5, 1, 1, 4, 1, 1, 3, 2, 3]
def baseStart_1839478 : Nat := 118140960795 + 1839478 * 2 ^ 59
def prefixEnd_1839478 : Nat := 4983230072969 + 3 ^ 40 * 1839478 * 2
def baseEnd_1839478 : Nat := 419793941053893007806845

theorem tailTrace_1839478 : CollatzResearch.WordTrace tailWord_1839478 prefixEnd_1839478 419793941053893007806845 := by
  unfold tailWord_1839478
  simp only [CollatzResearch.WordTrace]
  refine ⟨4193204651868302417257943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44727516286595225784084725 4193204651868302417257943)
  ·
    refine ⟨6289806977802453625886915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4193204651868302417257943 6289806977802453625886915)
    ·
      refine ⟨9434710466703680438830373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6289806977802453625886915 9434710466703680438830373)
      ·
        refine ⟨1769008212506940082280695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9434710466703680438830373 1769008212506940082280695)
        ·
          refine ⟨2653512318760410123421043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1769008212506940082280695 2653512318760410123421043)
          ·
            refine ⟨3980268478140615185131565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2653512318760410123421043 3980268478140615185131565)
            ·
              refine ⟨1492600679302730694424337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3980268478140615185131565 1492600679302730694424337)
              ·
                refine ⟨1119450509477048020818253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1492600679302730694424337 1119450509477048020818253)
                ·
                  refine ⟨419793941053893007806845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1119450509477048020818253 419793941053893007806845)
                  ·
                    rfl

theorem cell21_1839478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 3, 2, 3].length) (baseStart_1839478 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1839478 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1839478 prefixEnd_1839478 := by exact prefixLift 1839478
  have htrace : WordTrace (prefixWord ++ tailWord_1839478) baseStart_1839478 baseEnd_1839478 := by
    simpa [prefixWord, tailWord_1839478, baseEnd_1839478] using wordTrace_append hprefix tailTrace_1839478
  have hstable : (prefixWord ++ tailWord_1839478).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839478).length < 2 ^ (prefixWord ++ tailWord_1839478).sum := by decide
  have hdescent : baseEnd_1839478 < baseStart_1839478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839548 : List Nat := [2, 2, 2, 4, 1, 3, 1, 6]
def baseStart_1839548 : Nat := 118140960795 + 1839548 * 2 ^ 59
def prefixEnd_1839548 : Nat := 4983230072969 + 3 ^ 40 * 1839548 * 2
def baseEnd_1839548 : Nat := 139936638669196147213345

theorem tailTrace_1839548 : CollatzResearch.WordTrace tailWord_1839548 prefixEnd_1839548 139936638669196147213345 := by
  unfold tailWord_1839548
  simp only [CollatzResearch.WordTrace]
  refine ⟨33546913769819620315587649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44729218359759493754116865 33546913769819620315587649)
  ·
    refine ⟨25160185327364715236690737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33546913769819620315587649 25160185327364715236690737)
    ·
      refine ⟨18870138995523536427518053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25160185327364715236690737 18870138995523536427518053)
      ·
        refine ⟨3538151061660663080159635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18870138995523536427518053 3538151061660663080159635)
        ·
          refine ⟨5307226592490994620239453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3538151061660663080159635 5307226592490994620239453)
          ·
            refine ⟨1990209972184122982589795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5307226592490994620239453 1990209972184122982589795)
            ·
              refine ⟨2985314958276184473884693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1990209972184122982589795 2985314958276184473884693)
              ·
                refine ⟨139936638669196147213345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2985314958276184473884693 139936638669196147213345)
                ·
                  rfl

theorem cell21_1839548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 6].length) (baseStart_1839548 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1839548 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1839548 prefixEnd_1839548 := by exact prefixLift 1839548
  have htrace : WordTrace (prefixWord ++ tailWord_1839548) baseStart_1839548 baseEnd_1839548 := by
    simpa [prefixWord, tailWord_1839548, baseEnd_1839548] using wordTrace_append hprefix tailTrace_1839548
  have hstable : (prefixWord ++ tailWord_1839548).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839548).length < 2 ^ (prefixWord ++ tailWord_1839548).sum := by decide
  have hdescent : baseEnd_1839548 < baseStart_1839548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839621 : List Nat := [1, 3, 1, 1, 2, 2, 4, 2, 5]
def baseStart_1839621 : Nat := 118140960795 + 1839621 * 2 ^ 59
def prefixEnd_1839621 : Nat := 4983230072969 + 3 ^ 40 * 1839621 * 2
def baseEnd_1839621 : Nat := 419826575602156536923219

theorem tailTrace_1839621 : CollatzResearch.WordTrace tailWord_1839621 prefixEnd_1839621 419826575602156536923219 := by
  unfold tailWord_1839621
  simp only [CollatzResearch.WordTrace]
  refine ⟨67096490068374774098582717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44730993378916516065721811 67096490068374774098582717)
  ·
    refine ⟨25161183775640540286968519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67096490068374774098582717 25161183775640540286968519)
    ·
      refine ⟨37741775663460810430452779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25161183775640540286968519 37741775663460810430452779)
      ·
        refine ⟨56612663495191215645679169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37741775663460810430452779 56612663495191215645679169)
        ·
          refine ⟨42459497621393411734259377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56612663495191215645679169 42459497621393411734259377)
          ·
            refine ⟨31844623216045058800694533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42459497621393411734259377 31844623216045058800694533)
            ·
              refine ⟨5970866853008448525130225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31844623216045058800694533 5970866853008448525130225)
              ·
                refine ⟨4478150139756336393847669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5970866853008448525130225 4478150139756336393847669)
                ·
                  refine ⟨419826575602156536923219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4478150139756336393847669 419826575602156536923219)
                  ·
                    rfl

theorem cell21_1839621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 2, 5].length) (baseStart_1839621 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1839621 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1839621 prefixEnd_1839621 := by exact prefixLift 1839621
  have htrace : WordTrace (prefixWord ++ tailWord_1839621) baseStart_1839621 baseEnd_1839621 := by
    simpa [prefixWord, tailWord_1839621, baseEnd_1839621] using wordTrace_append hprefix tailTrace_1839621
  have hstable : (prefixWord ++ tailWord_1839621).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839621).length < 2 ^ (prefixWord ++ tailWord_1839621).sum := by decide
  have hdescent : baseEnd_1839621 < baseStart_1839621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839635 : List Nat := [1, 1, 1, 2, 1, 5, 1, 1, 8]
def baseStart_1839635 : Nat := 118140960795 + 1839635 * 2 ^ 59
def prefixEnd_1839635 : Nat := 4983230072969 + 3 ^ 40 * 1839635 * 2
def baseEnd_1839635 : Nat := 419829770592895623689857

theorem tailTrace_1839635 : CollatzResearch.WordTrace tailWord_1839635 prefixEnd_1839635 419829770592895623689857 := by
  unfold tailWord_1839635
  simp only [CollatzResearch.WordTrace]
  refine ⟨67097000690324054489592359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44731333793549369659728239 67097000690324054489592359)
  ·
    refine ⟨100645501035486081734388539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67097000690324054489592359 100645501035486081734388539)
    ·
      refine ⟨150968251553229122601582809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100645501035486081734388539 150968251553229122601582809)
      ·
        refine ⟨113226188664921841951187107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150968251553229122601582809 113226188664921841951187107)
        ·
          refine ⟨169839282997382762926780661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113226188664921841951187107 169839282997382762926780661)
          ·
            refine ⟨15922432781004634024385687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 169839282997382762926780661 15922432781004634024385687)
            ·
              refine ⟨23883649171506951036578531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15922432781004634024385687 23883649171506951036578531)
              ·
                refine ⟨35825473757260426554867797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23883649171506951036578531 35825473757260426554867797)
                ·
                  refine ⟨419829770592895623689857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35825473757260426554867797 419829770592895623689857)
                  ·
                    rfl

theorem cell21_1839635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 8].length) (baseStart_1839635 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1839635 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1839635 prefixEnd_1839635 := by exact prefixLift 1839635
  have htrace : WordTrace (prefixWord ++ tailWord_1839635) baseStart_1839635 baseEnd_1839635 := by
    simpa [prefixWord, tailWord_1839635, baseEnd_1839635] using wordTrace_append hprefix tailTrace_1839635
  have hstable : (prefixWord ++ tailWord_1839635).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839635).length < 2 ^ (prefixWord ++ tailWord_1839635).sum := by decide
  have hdescent : baseEnd_1839635 < baseStart_1839635 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839661 : List Nat := [1, 5, 4, 1, 1, 2, 2, 1, 4]
def baseStart_1839661 : Nat := 118140960795 + 1839661 * 2 ^ 59
def prefixEnd_1839661 : Nat := 4983230072969 + 3 ^ 40 * 1839661 * 2
def baseEnd_1839661 : Nat := 419835704147125356256471

theorem tailTrace_1839661 : CollatzResearch.WordTrace tailWord_1839661 prefixEnd_1839661 419835704147125356256471 := by
  unfold tailWord_1839661
  simp only [CollatzResearch.WordTrace]
  refine ⟨67097948988229860930038837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44731965992153240620025891 67097948988229860930038837)
  ·
    refine ⟨6290432717646549462191141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67097948988229860930038837 6290432717646549462191141)
    ·
      refine ⟨1179456134558728024160839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6290432717646549462191141 1179456134558728024160839)
      ·
        refine ⟨1769184201838092036241259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1179456134558728024160839 1769184201838092036241259)
        ·
          refine ⟨2653776302757138054361889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1769184201838092036241259 2653776302757138054361889)
          ·
            refine ⟨1990332227067853540771417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2653776302757138054361889 1990332227067853540771417)
            ·
              refine ⟨1492749170300890155578563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1990332227067853540771417 1492749170300890155578563)
              ·
                refine ⟨2239123755451335233367845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1492749170300890155578563 2239123755451335233367845)
                ·
                  refine ⟨419835704147125356256471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2239123755451335233367845 419835704147125356256471)
                  ·
                    rfl

theorem cell21_1839661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 2, 1, 4].length) (baseStart_1839661 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1839661 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1839661 prefixEnd_1839661 := by exact prefixLift 1839661
  have htrace : WordTrace (prefixWord ++ tailWord_1839661) baseStart_1839661 baseEnd_1839661 := by
    simpa [prefixWord, tailWord_1839661, baseEnd_1839661] using wordTrace_append hprefix tailTrace_1839661
  have hstable : (prefixWord ++ tailWord_1839661).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839661).length < 2 ^ (prefixWord ++ tailWord_1839661).sum := by decide
  have hdescent : baseEnd_1839661 < baseStart_1839661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839666 : List Nat := [3, 2, 1, 1, 2, 1, 3, 8]
def baseStart_1839666 : Nat := 118140960795 + 1839666 * 2 ^ 59
def prefixEnd_1839666 : Nat := 4983230072969 + 3 ^ 40 * 1839666 * 2
def baseEnd_1839666 : Nat := 139945615071748819557709

theorem tailTrace_1839666 : CollatzResearch.WordTrace tailWord_1839666 prefixEnd_1839666 139945615071748819557709 := by
  unfold tailWord_1839666
  simp only [CollatzResearch.WordTrace]
  refine ⟨16774532838302936695992713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44732087568807831189313901 16774532838302936695992713)
  ·
    refine ⟨12580899628727202521994535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16774532838302936695992713 12580899628727202521994535)
    ·
      refine ⟨18871349443090803782991803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12580899628727202521994535 18871349443090803782991803)
      ·
        refine ⟨28307024164636205674487705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18871349443090803782991803 28307024164636205674487705)
        ·
          refine ⟨21230268123477154255865779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28307024164636205674487705 21230268123477154255865779)
          ·
            refine ⟨31845402185215731383798669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21230268123477154255865779 31845402185215731383798669)
            ·
              refine ⟨11942025819455899268924501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31845402185215731383798669 11942025819455899268924501)
              ·
                refine ⟨139945615071748819557709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11942025819455899268924501 139945615071748819557709)
                ·
                  rfl

theorem cell21_1839666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 8].length) (baseStart_1839666 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1839666 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1839666 prefixEnd_1839666 := by exact prefixLift 1839666
  have htrace : WordTrace (prefixWord ++ tailWord_1839666) baseStart_1839666 baseEnd_1839666 := by
    simpa [prefixWord, tailWord_1839666, baseEnd_1839666] using wordTrace_append hprefix tailTrace_1839666
  have hstable : (prefixWord ++ tailWord_1839666).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839666).length < 2 ^ (prefixWord ++ tailWord_1839666).sum := by decide
  have hdescent : baseEnd_1839666 < baseStart_1839666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839711 : List Nat := [1, 1, 2, 3, 1, 1, 1, 5, 6]
def baseStart_1839711 : Nat := 118140960795 + 1839711 * 2 ^ 59
def prefixEnd_1839711 : Nat := 4983230072969 + 3 ^ 40 * 1839711 * 2
def baseEnd_1839711 : Nat := 419847114828336380423035

theorem tailTrace_1839711 : CollatzResearch.WordTrace tailWord_1839711 prefixEnd_1839711 419847114828336380423035 := by
  unfold tailWord_1839711
  simp only [CollatzResearch.WordTrace]
  refine ⟨67099772638048719469358987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44733181758699146312905991 67099772638048719469358987)
  ·
    refine ⟨100649658957073079204038481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67099772638048719469358987 100649658957073079204038481)
    ·
      refine ⟨75487244217804809403028861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100649658957073079204038481 75487244217804809403028861)
      ·
        refine ⟨28307716581676803526135823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75487244217804809403028861 28307716581676803526135823)
        ·
          refine ⟨42461574872515205289203735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28307716581676803526135823 42461574872515205289203735)
          ·
            refine ⟨63692362308772807933805603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42461574872515205289203735 63692362308772807933805603)
            ·
              refine ⟨95538543463159211900708405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63692362308772807933805603 95538543463159211900708405)
              ·
                refine ⟨8956738449671176115691413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 95538543463159211900708405 8956738449671176115691413)
                ·
                  refine ⟨419847114828336380423035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8956738449671176115691413 419847114828336380423035)
                  ·
                    rfl

theorem cell21_1839711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 6].length) (baseStart_1839711 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1839711 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1839711 prefixEnd_1839711 := by exact prefixLift 1839711
  have htrace : WordTrace (prefixWord ++ tailWord_1839711) baseStart_1839711 baseEnd_1839711 := by
    simpa [prefixWord, tailWord_1839711, baseEnd_1839711] using wordTrace_append hprefix tailTrace_1839711
  have hstable : (prefixWord ++ tailWord_1839711).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839711).length < 2 ^ (prefixWord ++ tailWord_1839711).sum := by decide
  have hdescent : baseEnd_1839711 < baseStart_1839711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839762 : List Nat := [3, 2, 3, 1, 2, 3, 1, 2, 4]
def baseStart_1839762 : Nat := 118140960795 + 1839762 * 2 ^ 59
def prefixEnd_1839762 : Nat := 4983230072969 + 3 ^ 40 * 1839762 * 2
def baseEnd_1839762 : Nat := 419858753723171625072931

theorem tailTrace_1839762 : CollatzResearch.WordTrace tailWord_1839762 prefixEnd_1839762 419858753723171625072931 := by
  unfold tailWord_1839762
  simp only [CollatzResearch.WordTrace]
  refine ⟨16775408190215988794866385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44734421840575970119643693 16775408190215988794866385)
  ·
    refine ⟨12581556142661991596149789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16775408190215988794866385 12581556142661991596149789)
    ·
      refine ⟨4718083553498246848556171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12581556142661991596149789 4718083553498246848556171)
      ·
        refine ⟨7077125330247370272834257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4718083553498246848556171 7077125330247370272834257)
        ·
          refine ⟨5307843997685527704625693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7077125330247370272834257 5307843997685527704625693)
          ·
            refine ⟨1990441499132072889234635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5307843997685527704625693 1990441499132072889234635)
            ·
              refine ⟨2985662248698109333851953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1990441499132072889234635 2985662248698109333851953)
              ·
                refine ⟨2239246686523582000388965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2985662248698109333851953 2239246686523582000388965)
                ·
                  refine ⟨419858753723171625072931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2239246686523582000388965 419858753723171625072931)
                  ·
                    rfl

theorem cell21_1839762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 2, 4].length) (baseStart_1839762 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1839762 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1839762 prefixEnd_1839762 := by exact prefixLift 1839762
  have htrace : WordTrace (prefixWord ++ tailWord_1839762) baseStart_1839762 baseEnd_1839762 := by
    simpa [prefixWord, tailWord_1839762, baseEnd_1839762] using wordTrace_append hprefix tailTrace_1839762
  have hstable : (prefixWord ++ tailWord_1839762).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839762).length < 2 ^ (prefixWord ++ tailWord_1839762).sum := by decide
  have hdescent : baseEnd_1839762 < baseStart_1839762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839773 : List Nat := [1, 4, 2, 1, 1, 1, 3, 3, 5]
def baseStart_1839773 : Nat := 118140960795 + 1839773 * 2 ^ 59
def prefixEnd_1839773 : Nat := 4983230072969 + 3 ^ 40 * 1839773 * 2
def baseEnd_1839773 : Nat := 419861264073038050389575

theorem tailTrace_1839773 : CollatzResearch.WordTrace tailWord_1839773 prefixEnd_1839773 419861264073038050389575 := by
  unfold tailWord_1839773
  simp only [CollatzResearch.WordTrace]
  refine ⟨67102033963824104058115973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44734689309216069372077315 67102033963824104058115973)
  ·
    refine ⟨12581631368217019510896745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67102033963824104058115973 12581631368217019510896745)
    ·
      refine ⟨9436223526162764633172559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12581631368217019510896745 9436223526162764633172559)
      ·
        refine ⟨14154335289244146949758839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9436223526162764633172559 14154335289244146949758839)
        ·
          refine ⟨21231502933866220424638259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14154335289244146949758839 21231502933866220424638259)
          ·
            refine ⟨31847254400799330636957389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21231502933866220424638259 31847254400799330636957389)
            ·
              refine ⟨11942720400299748988859021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31847254400799330636957389 11942720400299748988859021)
              ·
                refine ⟨4478520150112405870822133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11942720400299748988859021 4478520150112405870822133)
                ·
                  refine ⟨419861264073038050389575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4478520150112405870822133 419861264073038050389575)
                  ·
                    rfl

theorem cell21_1839773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_1839773 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1839773 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1839773 prefixEnd_1839773 := by exact prefixLift 1839773
  have htrace : WordTrace (prefixWord ++ tailWord_1839773) baseStart_1839773 baseEnd_1839773 := by
    simpa [prefixWord, tailWord_1839773, baseEnd_1839773] using wordTrace_append hprefix tailTrace_1839773
  have hstable : (prefixWord ++ tailWord_1839773).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839773).length < 2 ^ (prefixWord ++ tailWord_1839773).sum := by decide
  have hdescent : baseEnd_1839773 < baseStart_1839773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839793 : List Nat := [1, 2, 2, 6, 1, 2, 2, 5]
def baseStart_1839793 : Nat := 118140960795 + 1839793 * 2 ^ 59
def prefixEnd_1839793 : Nat := 4983230072969 + 3 ^ 40 * 1839793 * 2
def baseEnd_1839793 : Nat := 139955276115174153352067

theorem tailTrace_1839793 : CollatzResearch.WordTrace tailWord_1839793 prefixEnd_1839793 139955276115174153352067 := by
  unfold tailWord_1839793
  simp only [CollatzResearch.WordTrace]
  refine ⟨67102763423751647473844033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44735175615834431649229355 67102763423751647473844033)
  ·
    refine ⟨50327072567813735605383025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67102763423751647473844033 50327072567813735605383025)
    ·
      refine ⟨37745304425860301704037269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50327072567813735605383025 37745304425860301704037269)
      ·
        refine ⟨1769311144962201642376747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 37745304425860301704037269 1769311144962201642376747)
        ·
          refine ⟨2653966717443302463565121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1769311144962201642376747 2653966717443302463565121)
          ·
            refine ⟨1990475038082476847673841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2653966717443302463565121 1990475038082476847673841)
            ·
              refine ⟨1492856278561857635755381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1990475038082476847673841 1492856278561857635755381)
              ·
                refine ⟨139955276115174153352067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1492856278561857635755381 139955276115174153352067)
                ·
                  rfl

theorem cell21_1839793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 2, 5].length) (baseStart_1839793 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1839793 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1839793 prefixEnd_1839793 := by exact prefixLift 1839793
  have htrace : WordTrace (prefixWord ++ tailWord_1839793) baseStart_1839793 baseEnd_1839793 := by
    simpa [prefixWord, tailWord_1839793, baseEnd_1839793] using wordTrace_append hprefix tailTrace_1839793
  have hstable : (prefixWord ++ tailWord_1839793).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839793).length < 2 ^ (prefixWord ++ tailWord_1839793).sum := by decide
  have hdescent : baseEnd_1839793 < baseStart_1839793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839807 : List Nat := [1, 1, 2, 2, 2, 6, 1, 3, 3]
def baseStart_1839807 : Nat := 118140960795 + 1839807 * 2 ^ 59
def prefixEnd_1839807 : Nat := 4983230072969 + 3 ^ 40 * 1839807 * 2
def baseEnd_1839807 : Nat := 419869023336261546822839

theorem tailTrace_1839807 : CollatzResearch.WordTrace tailWord_1839807 prefixEnd_1839807 419869023336261546822839 := by
  unfold tailWord_1839807
  simp only [CollatzResearch.WordTrace]
  refine ⟨67103274045700927864853675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44735516030467285243235783 67103274045700927864853675)
  ·
    refine ⟨100654911068551391797280513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67103274045700927864853675 100654911068551391797280513)
    ·
      refine ⟨75491183301413543847960385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100654911068551391797280513 75491183301413543847960385)
      ·
        refine ⟨56618387476060157885970289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75491183301413543847960385 56618387476060157885970289)
        ·
          refine ⟨42463790607045118414477717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56618387476060157885970289 42463790607045118414477717)
          ·
            refine ⟨1990490184705239925678643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 42463790607045118414477717 1990490184705239925678643)
            ·
              refine ⟨2985735277057859888517965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1990490184705239925678643 2985735277057859888517965)
              ·
                refine ⟨1119650728896697458194237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2985735277057859888517965 1119650728896697458194237)
                ·
                  refine ⟨419869023336261546822839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1119650728896697458194237 419869023336261546822839)
                  ·
                    rfl

theorem cell21_1839807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 3, 3].length) (baseStart_1839807 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1839807 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1839807 prefixEnd_1839807 := by exact prefixLift 1839807
  have htrace : WordTrace (prefixWord ++ tailWord_1839807) baseStart_1839807 baseEnd_1839807 := by
    simpa [prefixWord, tailWord_1839807, baseEnd_1839807] using wordTrace_append hprefix tailTrace_1839807
  have hstable : (prefixWord ++ tailWord_1839807).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839807).length < 2 ^ (prefixWord ++ tailWord_1839807).sum := by decide
  have hdescent : baseEnd_1839807 < baseStart_1839807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839818 : List Nat := [3, 1, 2, 1, 4, 1, 9]
def baseStart_1839818 : Nat := 118140960795 + 1839818 * 2 ^ 59
def prefixEnd_1839818 : Nat := 4983230072969 + 3 ^ 40 * 1839818 * 2
def baseEnd_1839818 : Nat := 46652392631791996904387

theorem tailTrace_1839818 : CollatzResearch.WordTrace tailWord_1839818 prefixEnd_1839818 46652392631791996904387 := by
  unfold tailWord_1839818
  simp only [CollatzResearch.WordTrace]
  refine ⟨16775918812165269185876027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44735783499107384495669405 16775918812165269185876027)
  ·
    refine ⟨25163878218247903778814041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16775918812165269185876027 25163878218247903778814041)
    ·
      refine ⟨18872908663685927834110531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25163878218247903778814041 18872908663685927834110531)
      ·
        refine ⟨28309362995528891751165797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18872908663685927834110531 28309362995528891751165797)
        ·
          refine ⟨5308005561661667203343587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28309362995528891751165797 5308005561661667203343587)
          ·
            refine ⟨7962008342492500805015381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5308005561661667203343587 7962008342492500805015381)
            ·
              refine ⟨46652392631791996904387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7962008342492500805015381 46652392631791996904387)
              ·
                rfl

theorem cell21_1839818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 9].length) (baseStart_1839818 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1839818 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1839818 prefixEnd_1839818 := by exact prefixLift 1839818
  have htrace : WordTrace (prefixWord ++ tailWord_1839818) baseStart_1839818 baseEnd_1839818 := by
    simpa [prefixWord, tailWord_1839818, baseEnd_1839818] using wordTrace_append hprefix tailTrace_1839818
  have hstable : (prefixWord ++ tailWord_1839818).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839818).length < 2 ^ (prefixWord ++ tailWord_1839818).sum := by decide
  have hdescent : baseEnd_1839818 < baseStart_1839818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839880 : List Nat := [2, 1, 3, 2, 2, 2, 1, 4, 4]
def baseStart_1839880 : Nat := 118140960795 + 1839880 * 2 ^ 59
def prefixEnd_1839880 : Nat := 4983230072969 + 3 ^ 40 * 1839880 * 2
def baseEnd_1839880 : Nat := 419885682930829642106023

theorem tailTrace_1839880 : CollatzResearch.WordTrace tailWord_1839880 prefixEnd_1839880 419885682930829642106023 := by
  unfold tailWord_1839880
  simp only [CollatzResearch.WordTrace]
  refine ⟨33552968287218230666130547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44737291049624307554840729 33552968287218230666130547)
  ·
    refine ⟨50329452430827345999195821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33552968287218230666130547 50329452430827345999195821)
    ·
      refine ⟨18873544661560254749698433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50329452430827345999195821 18873544661560254749698433)
      ·
        refine ⟨14155158496170191062273825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18873544661560254749698433 14155158496170191062273825)
        ·
          refine ⟨10616368872127643296705369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14155158496170191062273825 10616368872127643296705369)
          ·
            refine ⟨7962276654095732472529027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10616368872127643296705369 7962276654095732472529027)
            ·
              refine ⟨11943414981143598708793541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7962276654095732472529027 11943414981143598708793541)
              ·
                refine ⟨2239390308964424757898789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11943414981143598708793541 2239390308964424757898789)
                ·
                  refine ⟨419885682930829642106023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2239390308964424757898789 419885682930829642106023)
                  ·
                    rfl

theorem cell21_1839880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 4, 4].length) (baseStart_1839880 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1839880 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1839880 prefixEnd_1839880 := by exact prefixLift 1839880
  have htrace : WordTrace (prefixWord ++ tailWord_1839880) baseStart_1839880 baseEnd_1839880 := by
    simpa [prefixWord, tailWord_1839880, baseEnd_1839880] using wordTrace_append hprefix tailTrace_1839880
  have hstable : (prefixWord ++ tailWord_1839880).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839880).length < 2 ^ (prefixWord ++ tailWord_1839880).sum := by decide
  have hdescent : baseEnd_1839880 < baseStart_1839880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839917 : List Nat := [1, 5, 3, 2, 1, 1, 2, 3, 3]
def baseStart_1839917 : Nat := 118140960795 + 1839917 * 2 ^ 59
def prefixEnd_1839917 : Nat := 4983230072969 + 3 ^ 40 * 1839917 * 2
def baseEnd_1839917 : Nat := 419894126834925799989281

theorem tailTrace_1839917 : CollatzResearch.WordTrace tailWord_1839917 prefixEnd_1839917 419894126834925799989281 := by
  unfold tailWord_1839917
  simp only [CollatzResearch.WordTrace]
  refine ⟨67107286075302416651358005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44738190716868277767572003 67107286075302416651358005)
  ·
    refine ⟨6291308069559601561064813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67107286075302416651358005 6291308069559601561064813)
    ·
      refine ⟨2359240526084850585399305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6291308069559601561064813 2359240526084850585399305)
      ·
        refine ⟨1769430394563637939049479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2359240526084850585399305 1769430394563637939049479)
        ·
          refine ⟨2654145591845456908574219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1769430394563637939049479 2654145591845456908574219)
          ·
            refine ⟨3981218387768185362861329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2654145591845456908574219 3981218387768185362861329)
            ·
              refine ⟨2985913790826139022145997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3981218387768185362861329 2985913790826139022145997)
              ·
                refine ⟨1119717671559802133304749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2985913790826139022145997 1119717671559802133304749)
                ·
                  refine ⟨419894126834925799989281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1119717671559802133304749 419894126834925799989281)
                  ·
                    rfl

theorem cell21_1839917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 3, 3].length) (baseStart_1839917 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1839917 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1839917 prefixEnd_1839917 := by exact prefixLift 1839917
  have htrace : WordTrace (prefixWord ++ tailWord_1839917) baseStart_1839917 baseEnd_1839917 := by
    simpa [prefixWord, tailWord_1839917, baseEnd_1839917] using wordTrace_append hprefix tailTrace_1839917
  have hstable : (prefixWord ++ tailWord_1839917).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839917).length < 2 ^ (prefixWord ++ tailWord_1839917).sum := by decide
  have hdescent : baseEnd_1839917 < baseStart_1839917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839939 : List Nat := [1, 1, 1, 3, 1, 4, 3, 1, 6]
def baseStart_1839939 : Nat := 118140960795 + 1839939 * 2 ^ 59
def prefixEnd_1839939 : Nat := 4983230072969 + 3 ^ 40 * 1839939 * 2
def baseEnd_1839939 : Nat := 419899147534658650622569

theorem tailTrace_1839939 : CollatzResearch.WordTrace tailWord_1839939 prefixEnd_1839939 419899147534658650622569 := by
  unfold tailWord_1839939
  simp only [CollatzResearch.WordTrace]
  refine ⟨67108088481222714408658871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44738725654148476272439247 67108088481222714408658871)
  ·
    refine ⟨100662132721834071612988307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67108088481222714408658871 100662132721834071612988307)
    ·
      refine ⟨150993199082751107419482461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100662132721834071612988307 150993199082751107419482461)
      ·
        refine ⟨56622449656031665282305923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150993199082751107419482461 56622449656031665282305923)
        ·
          refine ⟨84933674484047497923458885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56622449656031665282305923 84933674484047497923458885)
          ·
            refine ⟨15925063965758905860648541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84933674484047497923458885 15925063965758905860648541)
            ·
              refine ⟨5971898987159589697743203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15925063965758905860648541 5971898987159589697743203)
              ·
                refine ⟨8957848480739384546614805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5971898987159589697743203 8957848480739384546614805)
                ·
                  refine ⟨419899147534658650622569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8957848480739384546614805 419899147534658650622569)
                  ·
                    rfl

theorem cell21_1839939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 6].length) (baseStart_1839939 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1839939 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1839939 prefixEnd_1839939 := by exact prefixLift 1839939
  have htrace : WordTrace (prefixWord ++ tailWord_1839939) baseStart_1839939 baseEnd_1839939 := by
    simpa [prefixWord, tailWord_1839939, baseEnd_1839939] using wordTrace_append hprefix tailTrace_1839939
  have hstable : (prefixWord ++ tailWord_1839939).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839939).length < 2 ^ (prefixWord ++ tailWord_1839939).sum := by decide
  have hdescent : baseEnd_1839939 < baseStart_1839939 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839984 : List Nat := [2, 1, 1, 1, 4, 1, 2, 2, 7]
def baseStart_1839984 : Nat := 118140960795 + 1839984 * 2 ^ 59
def prefixEnd_1839984 : Nat := 4983230072969 + 3 ^ 40 * 1839984 * 2
def baseEnd_1839984 : Nat := 419909417147748572372477

theorem tailTrace_1839984 : CollatzResearch.WordTrace tailWord_1839984 prefixEnd_1839984 419909417147748572372477 := by
  unfold tailWord_1839984
  simp only [CollatzResearch.WordTrace]
  refine ⟨33554864883029843547023503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44739819844039791396031337 33554864883029843547023503)
  ·
    refine ⟨50332297324544765320535255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33554864883029843547023503 50332297324544765320535255)
    ·
      refine ⟨75498445986817147980802883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50332297324544765320535255 75498445986817147980802883)
      ·
        refine ⟨113247668980225721971204325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75498445986817147980802883 113247668980225721971204325)
        ·
          refine ⟨21233937933792322869600811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113247668980225721971204325 21233937933792322869600811)
          ·
            refine ⟨31850906900688484304401217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21233937933792322869600811 31850906900688484304401217)
            ·
              refine ⟨23888180175516363228300913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31850906900688484304401217 23888180175516363228300913)
              ·
                refine ⟨17916135131637272421225685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23888180175516363228300913 17916135131637272421225685)
                ·
                  refine ⟨419909417147748572372477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17916135131637272421225685 419909417147748572372477)
                  ·
                    rfl

theorem cell21_1839984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 7].length) (baseStart_1839984 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1839984 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1839984 prefixEnd_1839984 := by exact prefixLift 1839984
  have htrace : WordTrace (prefixWord ++ tailWord_1839984) baseStart_1839984 baseEnd_1839984 := by
    simpa [prefixWord, tailWord_1839984, baseEnd_1839984] using wordTrace_append hprefix tailTrace_1839984
  have hstable : (prefixWord ++ tailWord_1839984).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839984).length < 2 ^ (prefixWord ++ tailWord_1839984).sum := by decide
  have hdescent : baseEnd_1839984 < baseStart_1839984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840049 : List Nat := [1, 2, 2, 4, 3, 1, 2, 2, 4]
def baseStart_1840049 : Nat := 118140960795 + 1840049 * 2 ^ 59
def prefixEnd_1840049 : Nat := 4983230072969 + 3 ^ 40 * 1840049 * 2
def baseEnd_1840049 : Nat := 419924251033322903789011

theorem tailTrace_1840049 : CollatzResearch.WordTrace tailWord_1840049 prefixEnd_1840049 419924251033322903789011 := by
  unfold tailWord_1840049
  simp only [CollatzResearch.WordTrace]
  refine ⟨67112100510824203195163201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44741400340549468796775467 67112100510824203195163201)
  ·
    refine ⟨50334075383118152396372401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67112100510824203195163201 50334075383118152396372401)
    ·
      refine ⟨37750556537338614297279301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50334075383118152396372401 37750556537338614297279301)
      ·
        refine ⟨7078229350750990180739869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37750556537338614297279301 7078229350750990180739869)
        ·
          refine ⟨2654336006531621317777451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7078229350750990180739869 2654336006531621317777451)
          ·
            refine ⟨3981504009797431976666177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2654336006531621317777451 3981504009797431976666177)
            ·
              refine ⟨2986128007348073982499633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3981504009797431976666177 2986128007348073982499633)
              ·
                refine ⟨2239596005511055486874725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2986128007348073982499633 2239596005511055486874725)
                ·
                  refine ⟨419924251033322903789011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2239596005511055486874725 419924251033322903789011)
                  ·
                    rfl

theorem cell21_1840049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 2, 4].length) (baseStart_1840049 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1840049 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1840049 prefixEnd_1840049 := by exact prefixLift 1840049
  have htrace : WordTrace (prefixWord ++ tailWord_1840049) baseStart_1840049 baseEnd_1840049 := by
    simpa [prefixWord, tailWord_1840049, baseEnd_1840049] using wordTrace_append hprefix tailTrace_1840049
  have hstable : (prefixWord ++ tailWord_1840049).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840049).length < 2 ^ (prefixWord ++ tailWord_1840049).sum := by decide
  have hdescent : baseEnd_1840049 < baseStart_1840049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840052 : List Nat := [2, 5, 2, 1, 1, 2, 1, 4, 3]
def baseStart_1840052 : Nat := 118140960795 + 1840052 * 2 ^ 59
def prefixEnd_1840052 : Nat := 4983230072969 + 3 ^ 40 * 1840052 * 2
def baseEnd_1840052 : Nat := 419924935674195565239005

theorem tailTrace_1840052 : CollatzResearch.WordTrace tailWord_1840052 prefixEnd_1840052 419924935674195565239005 := by
  unfold tailWord_1840052
  simp only [CollatzResearch.WordTrace]
  refine ⟨33556104964906667353761205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44741473286542223138348273 33556104964906667353761205)
  ·
    refine ⟨3145884840460000064415113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33556104964906667353761205 3145884840460000064415113)
    ·
      refine ⟨2359413630345000048311335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3145884840460000064415113 2359413630345000048311335)
      ·
        refine ⟨3539120445517500072467003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2359413630345000048311335 3539120445517500072467003)
        ·
          refine ⟨5308680668276250108700505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3539120445517500072467003 5308680668276250108700505)
          ·
            refine ⟨3981510501207187581525379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5308680668276250108700505 3981510501207187581525379)
            ·
              refine ⟨5972265751810781372288069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3981510501207187581525379 5972265751810781372288069)
              ·
                refine ⟨1119799828464521507304013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5972265751810781372288069 1119799828464521507304013)
                ·
                  refine ⟨419924935674195565239005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1119799828464521507304013 419924935674195565239005)
                  ·
                    rfl

theorem cell21_1840052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_1840052 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1840052 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1840052 prefixEnd_1840052 := by exact prefixLift 1840052
  have htrace : WordTrace (prefixWord ++ tailWord_1840052) baseStart_1840052 baseEnd_1840052 := by
    simpa [prefixWord, tailWord_1840052, baseEnd_1840052] using wordTrace_append hprefix tailTrace_1840052
  have hstable : (prefixWord ++ tailWord_1840052).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840052).length < 2 ^ (prefixWord ++ tailWord_1840052).sum := by decide
  have hdescent : baseEnd_1840052 < baseStart_1840052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840139 : List Nat := [1, 1, 1, 1, 6, 4, 2, 5]
def baseStart_1840139 : Nat := 118140960795 + 1840139 * 2 ^ 59
def prefixEnd_1840139 : Nat := 4983230072969 + 3 ^ 40 * 1840139 * 2
def baseEnd_1840139 : Nat := 139981596753167582429609

theorem tailTrace_1840139 : CollatzResearch.WordTrace tailWord_1840139 prefixEnd_1840139 139981596753167582429609 := by
  unfold tailWord_1840139
  simp only [CollatzResearch.WordTrace]
  refine ⟨67115383080498148565939471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44743588720332099043959647 67115383080498148565939471)
  ·
    refine ⟨100673074620747222848909207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67115383080498148565939471 100673074620747222848909207)
    ·
      refine ⟨151009611931120834273363811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100673074620747222848909207 151009611931120834273363811)
      ·
        refine ⟨226514417896681251410045717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151009611931120834273363811 226514417896681251410045717)
        ·
          refine ⟨10617863338906933659845893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 226514417896681251410045717 10617863338906933659845893)
          ·
            refine ⟨1990849376045050061221105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10617863338906933659845893 1990849376045050061221105)
            ·
              refine ⟨1493137032033787545915829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1990849376045050061221105 1493137032033787545915829)
              ·
                refine ⟨139981596753167582429609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1493137032033787545915829 139981596753167582429609)
                ·
                  rfl

theorem cell21_1840139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 2, 5].length) (baseStart_1840139 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1840139 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1840139 prefixEnd_1840139 := by exact prefixLift 1840139
  have htrace : WordTrace (prefixWord ++ tailWord_1840139) baseStart_1840139 baseEnd_1840139 := by
    simpa [prefixWord, tailWord_1840139, baseEnd_1840139] using wordTrace_append hprefix tailTrace_1840139
  have hstable : (prefixWord ++ tailWord_1840139).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840139).length < 2 ^ (prefixWord ++ tailWord_1840139).sum := by decide
  have hdescent : baseEnd_1840139 < baseStart_1840139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840184 : List Nat := [2, 1, 2, 1, 5, 2, 1, 3, 4]
def baseStart_1840184 : Nat := 118140960795 + 1840184 * 2 ^ 59
def prefixEnd_1840184 : Nat := 4983230072969 + 3 ^ 40 * 1840184 * 2
def baseEnd_1840184 : Nat := 419955059872592669038735

theorem tailTrace_1840184 : CollatzResearch.WordTrace tailWord_1840184 prefixEnd_1840184 419955059872592669038735 := by
  unfold tailWord_1840184
  simp only [CollatzResearch.WordTrace]
  refine ⟨33558512182667560625663803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44744682910223414167551737 33558512182667560625663803)
  ·
    refine ⟨50337768274001340938495705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33558512182667560625663803 50337768274001340938495705)
    ·
      refine ⟨37753326205501005703871779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50337768274001340938495705 37753326205501005703871779)
      ·
        refine ⟨56629989308251508555807669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37753326205501005703871779 56629989308251508555807669)
        ·
          refine ⟨5309061497648578927106969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56629989308251508555807669 5309061497648578927106969)
          ·
            refine ⟨3981796123236434195330227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5309061497648578927106969 3981796123236434195330227)
            ·
              refine ⟨5972694184854651292995341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3981796123236434195330227 5972694184854651292995341)
              ·
                refine ⟨2239760319320494234873253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5972694184854651292995341 2239760319320494234873253)
                ·
                  refine ⟨419955059872592669038735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2239760319320494234873253 419955059872592669038735)
                  ·
                    rfl

theorem cell21_1840184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 3, 4].length) (baseStart_1840184 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1840184 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1840184 prefixEnd_1840184 := by exact prefixLift 1840184
  have htrace : WordTrace (prefixWord ++ tailWord_1840184) baseStart_1840184 baseEnd_1840184 := by
    simpa [prefixWord, tailWord_1840184, baseEnd_1840184] using wordTrace_append hprefix tailTrace_1840184
  have hstable : (prefixWord ++ tailWord_1840184).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840184).length < 2 ^ (prefixWord ++ tailWord_1840184).sum := by decide
  have hdescent : baseEnd_1840184 < baseStart_1840184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840221 : List Nat := [1, 4, 4, 1, 2, 2, 2, 2, 3]
def baseStart_1840221 : Nat := 118140960795 + 1840221 * 2 ^ 59
def prefixEnd_1840221 : Nat := 4983230072969 + 3 ^ 40 * 1840221 * 2
def baseEnd_1840221 : Nat := 419963503776688826921993

theorem tailTrace_1840221 : CollatzResearch.WordTrace tailWord_1840221 prefixEnd_1840221 419963503776688826921993 := by
  unfold tailWord_1840221
  simp only [CollatzResearch.WordTrace]
  refine ⟨67118373866201076570424517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44745582577467384380283011 67118373866201076570424517)
  ·
    refine ⟨12584695099912701856954597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67118373866201076570424517 12584695099912701856954597)
    ·
      refine ⟨2359630331233631598178987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12584695099912701856954597 2359630331233631598178987)
      ·
        refine ⟨3539445496850447397268481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2359630331233631598178987 3539445496850447397268481)
        ·
          refine ⟨2654584122637835547951361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3539445496850447397268481 2654584122637835547951361)
          ·
            refine ⟨1990938091978376660963521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2654584122637835547951361 1990938091978376660963521)
            ·
              refine ⟨1493203568983782495722641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1990938091978376660963521 1493203568983782495722641)
              ·
                refine ⟨1119902676737836871791981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1493203568983782495722641 1119902676737836871791981)
                ·
                  refine ⟨419963503776688826921993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1119902676737836871791981 419963503776688826921993)
                  ·
                    rfl

theorem cell21_1840221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 2, 2, 3].length) (baseStart_1840221 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1840221 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1840221 prefixEnd_1840221 := by exact prefixLift 1840221
  have htrace : WordTrace (prefixWord ++ tailWord_1840221) baseStart_1840221 baseEnd_1840221 := by
    simpa [prefixWord, tailWord_1840221, baseEnd_1840221] using wordTrace_append hprefix tailTrace_1840221
  have hstable : (prefixWord ++ tailWord_1840221).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840221).length < 2 ^ (prefixWord ++ tailWord_1840221).sum := by decide
  have hdescent : baseEnd_1840221 < baseStart_1840221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840232 : List Nat := [2, 1, 4, 4, 1, 2, 1, 6]
def baseStart_1840232 : Nat := 118140960795 + 1840232 * 2 ^ 59
def prefixEnd_1840232 : Nat := 4983230072969 + 3 ^ 40 * 1840232 * 2
def baseEnd_1840232 : Nat := 139988671375518417412879

theorem tailTrace_1840232 : CollatzResearch.WordTrace tailWord_1840232 prefixEnd_1840232 139988671375518417412879 := by
  unfold tailWord_1840232
  simp only [CollatzResearch.WordTrace]
  refine ⟨33559387534580612724537475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44745850046107483632716633 33559387534580612724537475)
  ·
    refine ⟨50339081301870919086806213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33559387534580612724537475 50339081301870919086806213)
    ·
      refine ⟨9438577744100797328776165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50339081301870919086806213 9438577744100797328776165)
      ·
        refine ⟨1769733327018899499145531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9438577744100797328776165 1769733327018899499145531)
        ·
          refine ⟨2654599990528349248718297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1769733327018899499145531 2654599990528349248718297)
          ·
            refine ⟨1990949992896261936538723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2654599990528349248718297 1990949992896261936538723)
            ·
              refine ⟨2986424989344392904808085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1990949992896261936538723 2986424989344392904808085)
              ·
                refine ⟨139988671375518417412879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2986424989344392904808085 139988671375518417412879)
                ·
                  rfl

theorem cell21_1840232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 6].length) (baseStart_1840232 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1840232 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1840232 prefixEnd_1840232 := by exact prefixLift 1840232
  have htrace : WordTrace (prefixWord ++ tailWord_1840232) baseStart_1840232 baseEnd_1840232 := by
    simpa [prefixWord, tailWord_1840232, baseEnd_1840232] using wordTrace_append hprefix tailTrace_1840232
  have hstable : (prefixWord ++ tailWord_1840232).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840232).length < 2 ^ (prefixWord ++ tailWord_1840232).sum := by decide
  have hdescent : baseEnd_1840232 < baseStart_1840232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840274 : List Nat := [3, 2, 3, 1, 1, 3, 8]
def baseStart_1840274 : Nat := 118140960795 + 1840274 * 2 ^ 59
def prefixEnd_1840274 : Nat := 4983230072969 + 3 ^ 40 * 1840274 * 2
def baseEnd_1840274 : Nat := 46663955455419168059839

theorem tailTrace_1840274 : CollatzResearch.WordTrace tailWord_1840274 prefixEnd_1840274 46663955455419168059839 := by
  unfold tailWord_1840274
  simp only [CollatzResearch.WordTrace]
  refine ⟨16780076733752266655525969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44746871290006044414735917 16780076733752266655525969)
  ·
    refine ⟨12585057550314199991644477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16780076733752266655525969 12585057550314199991644477)
    ·
      refine ⟨4719396581367824996866679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12585057550314199991644477 4719396581367824996866679)
      ·
        refine ⟨7079094872051737495300019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4719396581367824996866679 7079094872051737495300019)
        ·
          refine ⟨10618642308077606242950029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7079094872051737495300019 10618642308077606242950029)
          ·
            refine ⟨3981990865529102341106261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10618642308077606242950029 3981990865529102341106261)
            ·
              refine ⟨46663955455419168059839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3981990865529102341106261 46663955455419168059839)
              ·
                rfl

theorem cell21_1840274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 8].length) (baseStart_1840274 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1840274 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1840274 prefixEnd_1840274 := by exact prefixLift 1840274
  have htrace : WordTrace (prefixWord ++ tailWord_1840274) baseStart_1840274 baseEnd_1840274 := by
    simpa [prefixWord, tailWord_1840274, baseEnd_1840274] using wordTrace_append hprefix tailTrace_1840274
  have hstable : (prefixWord ++ tailWord_1840274).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840274).length < 2 ^ (prefixWord ++ tailWord_1840274).sum := by decide
  have hdescent : baseEnd_1840274 < baseStart_1840274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840305 : List Nat := [1, 2, 2, 5, 1, 1, 2, 2, 5]
def baseStart_1840305 : Nat := 118140960795 + 1840305 * 2 ^ 59
def prefixEnd_1840305 : Nat := 4983230072969 + 3 ^ 40 * 1840305 * 2
def baseEnd_1840305 : Nat := 419982673721123347521821

theorem tailTrace_1840305 : CollatzResearch.WordTrace tailWord_1840305 prefixEnd_1840305 419982673721123347521821 := by
  unfold tailWord_1840305
  simp only [CollatzResearch.WordTrace]
  refine ⟨67121437597896758916482369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44747625065264505944321579 67121437597896758916482369)
  ·
    refine ⟨50341078198422569187361777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67121437597896758916482369 50341078198422569187361777)
    ·
      refine ⟨37755808648816926890521333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50341078198422569187361777 37755808648816926890521333)
      ·
        refine ⟨3539607060826586895986375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37755808648816926890521333 3539607060826586895986375)
        ·
          refine ⟨5309410591239880343979563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3539607060826586895986375 5309410591239880343979563)
          ·
            refine ⟨7964115886859820515969345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5309410591239880343979563 7964115886859820515969345)
            ·
              refine ⟨5973086915144865386977009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7964115886859820515969345 5973086915144865386977009)
              ·
                refine ⟨4479815186358649040232757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5973086915144865386977009 4479815186358649040232757)
                ·
                  refine ⟨419982673721123347521821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4479815186358649040232757 419982673721123347521821)
                  ·
                    rfl

theorem cell21_1840305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 2, 5].length) (baseStart_1840305 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1840305 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1840305 prefixEnd_1840305 := by exact prefixLift 1840305
  have htrace : WordTrace (prefixWord ++ tailWord_1840305) baseStart_1840305 baseEnd_1840305 := by
    simpa [prefixWord, tailWord_1840305, baseEnd_1840305] using wordTrace_append hprefix tailTrace_1840305
  have hstable : (prefixWord ++ tailWord_1840305).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840305).length < 2 ^ (prefixWord ++ tailWord_1840305).sum := by decide
  have hdescent : baseEnd_1840305 < baseStart_1840305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840353 : List Nat := [1, 2, 3, 1, 3, 4, 2, 1, 4]
def baseStart_1840353 : Nat := 118140960795 + 1840353 * 2 ^ 59
def prefixEnd_1840353 : Nat := 4983230072969 + 3 ^ 40 * 1840353 * 2
def baseEnd_1840353 : Nat := 419993627975085930721723

theorem tailTrace_1840353 : CollatzResearch.WordTrace tailWord_1840353 prefixEnd_1840353 419993627975085930721723 := by
  unfold tailWord_1840353
  simp only [CollatzResearch.WordTrace]
  refine ⟨67123188301722863114229713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44748792201148575409486475 67123188301722863114229713)
  ·
    refine ⟨50342391226292147335672285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67123188301722863114229713 50342391226292147335672285)
    ·
      refine ⟨18878396709859555250877107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50342391226292147335672285 18878396709859555250877107)
      ·
        refine ⟨28317595064789332876315661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18878396709859555250877107 28317595064789332876315661)
        ·
          refine ⟨10619098149295999828618373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28317595064789332876315661 10619098149295999828618373)
          ·
            refine ⟨1991080902992999967865945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10619098149295999828618373 1991080902992999967865945)
            ·
              refine ⟨1493310677244749975899459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1991080902992999967865945 1493310677244749975899459)
              ·
                refine ⟨2239966015867124963849189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1493310677244749975899459 2239966015867124963849189)
                ·
                  refine ⟨419993627975085930721723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2239966015867124963849189 419993627975085930721723)
                  ·
                    rfl

theorem cell21_1840353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 2, 1, 4].length) (baseStart_1840353 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1840353 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1840353 prefixEnd_1840353 := by exact prefixLift 1840353
  have htrace : WordTrace (prefixWord ++ tailWord_1840353) baseStart_1840353 baseEnd_1840353 := by
    simpa [prefixWord, tailWord_1840353, baseEnd_1840353] using wordTrace_append hprefix tailTrace_1840353
  have hstable : (prefixWord ++ tailWord_1840353).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840353).length < 2 ^ (prefixWord ++ tailWord_1840353).sum := by decide
  have hdescent : baseEnd_1840353 < baseStart_1840353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840395 : List Nat := [1, 1, 1, 1, 5, 3, 1, 4, 4]
def baseStart_1840395 : Nat := 118140960795 + 1840395 * 2 ^ 59
def prefixEnd_1840395 : Nat := 4983230072969 + 3 ^ 40 * 1840395 * 2
def baseEnd_1840395 : Nat := 420003212947303191021637

theorem tailTrace_1840395 : CollatzResearch.WordTrace tailWord_1840395 prefixEnd_1840395 420003212947303191021637 := by
  unfold tailWord_1840395
  simp only [CollatzResearch.WordTrace]
  refine ⟨67124720167570704287258639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44749813445047136191505759 67124720167570704287258639)
  ·
    refine ⟨100687080251356056430887959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67124720167570704287258639 100687080251356056430887959)
    ·
      refine ⟨151030620377034084646331939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100687080251356056430887959 151030620377034084646331939)
      ·
        refine ⟨226545930565551126969497909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151030620377034084646331939 226545930565551126969497909)
        ·
          refine ⟨21238680990520418153390429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 226545930565551126969497909 21238680990520418153390429)
          ·
            refine ⟨7964505371445156807521411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21238680990520418153390429 7964505371445156807521411)
            ·
              refine ⟨11946758057167735211282117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7964505371445156807521411 11946758057167735211282117)
              ·
                refine ⟨2240017135718950352115397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11946758057167735211282117 2240017135718950352115397)
                ·
                  refine ⟨420003212947303191021637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2240017135718950352115397 420003212947303191021637)
                  ·
                    rfl

theorem cell21_1840395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 4, 4].length) (baseStart_1840395 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1840395 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1840395 prefixEnd_1840395 := by exact prefixLift 1840395
  have htrace : WordTrace (prefixWord ++ tailWord_1840395) baseStart_1840395 baseEnd_1840395 := by
    simpa [prefixWord, tailWord_1840395, baseEnd_1840395] using wordTrace_append hprefix tailTrace_1840395
  have hstable : (prefixWord ++ tailWord_1840395).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840395).length < 2 ^ (prefixWord ++ tailWord_1840395).sum := by decide
  have hdescent : baseEnd_1840395 < baseStart_1840395 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840398 : List Nat := [4, 1, 1, 2, 1, 4, 1, 4, 3]
def baseStart_1840398 : Nat := 118140960795 + 1840398 * 2 ^ 59
def prefixEnd_1840398 : Nat := 4983230072969 + 3 ^ 40 * 1840398 * 2
def baseEnd_1840398 : Nat := 420003897588175852471631

theorem tailTrace_1840398 : CollatzResearch.WordTrace tailWord_1840398 prefixEnd_1840398 420003897588175852471631 := by
  unfold tailWord_1840398
  simp only [CollatzResearch.WordTrace]
  refine ⟨8390603698319979474952231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44749886391039890533078565 8390603698319979474952231)
  ·
    refine ⟨12585905547479969212428347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8390603698319979474952231 12585905547479969212428347)
    ·
      refine ⟨18878858321219953818642521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12585905547479969212428347 18878858321219953818642521)
      ·
        refine ⟨14159143740914965363981891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18878858321219953818642521 14159143740914965363981891)
        ·
          refine ⟨21238715611372448045972837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14159143740914965363981891 21238715611372448045972837)
          ·
            refine ⟨3982259177132334008619907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21238715611372448045972837 3982259177132334008619907)
            ·
              refine ⟨5973388765698501012929861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3982259177132334008619907 5973388765698501012929861)
              ·
                refine ⟨1120010393568468939924349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5973388765698501012929861 1120010393568468939924349)
                ·
                  refine ⟨420003897588175852471631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1120010393568468939924349 420003897588175852471631)
                  ·
                    rfl

theorem cell21_1840398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 4, 3].length) (baseStart_1840398 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1840398 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1840398 prefixEnd_1840398 := by exact prefixLift 1840398
  have htrace : WordTrace (prefixWord ++ tailWord_1840398) baseStart_1840398 baseEnd_1840398 := by
    simpa [prefixWord, tailWord_1840398, baseEnd_1840398] using wordTrace_append hprefix tailTrace_1840398
  have hstable : (prefixWord ++ tailWord_1840398).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840398).length < 2 ^ (prefixWord ++ tailWord_1840398).sum := by decide
  have hdescent : baseEnd_1840398 < baseStart_1840398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840457 : List Nat := [1, 2, 1, 1, 2, 3, 4, 4, 3]
def baseStart_1840457 : Nat := 118140960795 + 1840457 * 2 ^ 59
def prefixEnd_1840457 : Nat := 4983230072969 + 3 ^ 40 * 1840457 * 2
def baseEnd_1840457 : Nat := 420017362192004860988177

theorem tailTrace_1840457 : CollatzResearch.WordTrace tailWord_1840457 prefixEnd_1840457 420017362192004860988177 := by
  unfold tailWord_1840457
  simp only [CollatzResearch.WordTrace]
  refine ⟨67126981493346088876015625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44751320995564059250677083 67126981493346088876015625)
  ·
    refine ⟨50345236120009566657011719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67126981493346088876015625 50345236120009566657011719)
    ·
      refine ⟨75517854180014349985517579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50345236120009566657011719 75517854180014349985517579)
      ·
        refine ⟨113276781270021524978276369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75517854180014349985517579 113276781270021524978276369)
        ·
          refine ⟨84957585952516143733707277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113276781270021524978276369 84957585952516143733707277)
          ·
            refine ⟨31859094732193553900140229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84957585952516143733707277 31859094732193553900140229)
            ·
              refine ⟨5973580262286291356276293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31859094732193553900140229 5973580262286291356276293)
              ·
                refine ⟨1120046299178679629301805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5973580262286291356276293 1120046299178679629301805)
                ·
                  refine ⟨420017362192004860988177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1120046299178679629301805 420017362192004860988177)
                  ·
                    rfl

theorem cell21_1840457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 4, 3].length) (baseStart_1840457 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1840457 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1840457 prefixEnd_1840457 := by exact prefixLift 1840457
  have htrace : WordTrace (prefixWord ++ tailWord_1840457) baseStart_1840457 baseEnd_1840457 := by
    simpa [prefixWord, tailWord_1840457, baseEnd_1840457] using wordTrace_append hprefix tailTrace_1840457
  have hstable : (prefixWord ++ tailWord_1840457).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840457).length < 2 ^ (prefixWord ++ tailWord_1840457).sum := by decide
  have hdescent : baseEnd_1840457 < baseStart_1840457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840485 : List Nat := [1, 3, 1, 3, 1, 2, 3, 7]
def baseStart_1840485 : Nat := 118140960795 + 1840485 * 2 ^ 59
def prefixEnd_1840485 : Nat := 4983230072969 + 3 ^ 40 * 1840485 * 2
def baseEnd_1840485 : Nat := 140007917391161011507151

theorem tailTrace_1840485 : CollatzResearch.WordTrace tailWord_1840485 prefixEnd_1840485 140007917391161011507151 := by
  unfold tailWord_1840485
  simp only [CollatzResearch.WordTrace]
  refine ⟨67128002737244649658034909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44752001824829766438689939 67128002737244649658034909)
  ·
    refine ⟨25173001026466743621763091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67128002737244649658034909 25173001026466743621763091)
    ·
      refine ⟨37759501539700115432644637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25173001026466743621763091 37759501539700115432644637)
      ·
        refine ⟨14159813077387543287241739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37759501539700115432644637 14159813077387543287241739)
        ·
          refine ⟨21239719616081314930862609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14159813077387543287241739 21239719616081314930862609)
          ·
            refine ⟨15929789712060986198146957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21239719616081314930862609 15929789712060986198146957)
            ·
              refine ⟨5973671142022869824305109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15929789712060986198146957 5973671142022869824305109)
              ·
                refine ⟨140007917391161011507151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5973671142022869824305109 140007917391161011507151)
                ·
                  rfl

theorem cell21_1840485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 7].length) (baseStart_1840485 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1840485 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1840485 prefixEnd_1840485 := by exact prefixLift 1840485
  have htrace : WordTrace (prefixWord ++ tailWord_1840485) baseStart_1840485 baseEnd_1840485 := by
    simpa [prefixWord, tailWord_1840485, baseEnd_1840485] using wordTrace_append hprefix tailTrace_1840485
  have hstable : (prefixWord ++ tailWord_1840485).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840485).length < 2 ^ (prefixWord ++ tailWord_1840485).sum := by decide
  have hdescent : baseEnd_1840485 < baseStart_1840485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840575 : List Nat := [1, 1, 2, 2, 2, 1, 1, 2, 9]
def baseStart_1840575 : Nat := 118140960795 + 1840575 * 2 ^ 59
def prefixEnd_1840575 : Nat := 4983230072969 + 3 ^ 40 * 1840575 * 2
def baseEnd_1840575 : Nat := 420044291399662878021269

theorem tailTrace_1840575 : CollatzResearch.WordTrace tailWord_1840575 prefixEnd_1840575 420044291399662878021269 := by
  unfold tailWord_1840575
  simp only [CollatzResearch.WordTrace]
  refine ⟨67131285306918595028811179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44754190204612396685874119 67131285306918595028811179)
  ·
    refine ⟨100696927960377892543216769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67131285306918595028811179 100696927960377892543216769)
    ·
      refine ⟨75522695970283419407412577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100696927960377892543216769 75522695970283419407412577)
      ·
        refine ⟨56642021977712564555559433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75522695970283419407412577 56642021977712564555559433)
        ·
          refine ⟨42481516483284423416669575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56642021977712564555559433 42481516483284423416669575)
          ·
            refine ⟨63722274724926635125004363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42481516483284423416669575 63722274724926635125004363)
            ·
              refine ⟨95583412087389952687506545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63722274724926635125004363 95583412087389952687506545)
              ·
                refine ⟨71687559065542464515629909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95583412087389952687506545 71687559065542464515629909)
                ·
                  refine ⟨420044291399662878021269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 71687559065542464515629909 420044291399662878021269)
                  ·
                    rfl

theorem cell21_1840575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 9].length) (baseStart_1840575 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1840575 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1840575 prefixEnd_1840575 := by exact prefixLift 1840575
  have htrace : WordTrace (prefixWord ++ tailWord_1840575) baseStart_1840575 baseEnd_1840575 := by
    simpa [prefixWord, tailWord_1840575, baseEnd_1840575] using wordTrace_append hprefix tailTrace_1840575
  have hstable : (prefixWord ++ tailWord_1840575).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840575).length < 2 ^ (prefixWord ++ tailWord_1840575).sum := by decide
  have hdescent : baseEnd_1840575 < baseStart_1840575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840609 : List Nat := [1, 2, 3, 1, 2, 3, 1, 5, 3]
def baseStart_1840609 : Nat := 118140960795 + 1840609 * 2 ^ 59
def prefixEnd_1840609 : Nat := 4983230072969 + 3 ^ 40 * 1840609 * 2
def baseEnd_1840609 : Nat := 420052050662886374454533

theorem tailTrace_1840609 : CollatzResearch.WordTrace tailWord_1840609 prefixEnd_1840609 420052050662886374454533 := by
  unfold tailWord_1840609
  simp only [CollatzResearch.WordTrace]
  refine ⟨67132525388795418835548881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44755016925863612557032587 67132525388795418835548881)
  ·
    refine ⟨50349394041596564126661661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67132525388795418835548881 50349394041596564126661661)
    ·
      refine ⟨18881022765598711547498123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50349394041596564126661661 18881022765598711547498123)
      ·
        refine ⟨28321534148398067321247185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18881022765598711547498123 28321534148398067321247185)
        ·
          refine ⟨21241150611298550490935389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28321534148398067321247185 21241150611298550490935389)
          ·
            refine ⟨7965431479236956434100771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21241150611298550490935389 7965431479236956434100771)
            ·
              refine ⟨11948147218855434651151157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7965431479236956434100771 11948147218855434651151157)
              ·
                refine ⟨1120138801767696998545421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11948147218855434651151157 1120138801767696998545421)
                ·
                  refine ⟨420052050662886374454533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1120138801767696998545421 420052050662886374454533)
                  ·
                    rfl

theorem cell21_1840609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 5, 3].length) (baseStart_1840609 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1840609 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1840609 prefixEnd_1840609 := by exact prefixLift 1840609
  have htrace : WordTrace (prefixWord ++ tailWord_1840609) baseStart_1840609 baseEnd_1840609 := by
    simpa [prefixWord, tailWord_1840609, baseEnd_1840609] using wordTrace_append hprefix tailTrace_1840609
  have hstable : (prefixWord ++ tailWord_1840609).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840609).length < 2 ^ (prefixWord ++ tailWord_1840609).sum := by decide
  have hdescent : baseEnd_1840609 < baseStart_1840609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840623 : List Nat := [1, 1, 2, 1, 4, 1, 5, 2, 4]
def baseStart_1840623 : Nat := 118140960795 + 1840623 * 2 ^ 59
def prefixEnd_1840623 : Nat := 4983230072969 + 3 ^ 40 * 1840623 * 2
def baseEnd_1840623 : Nat := 420055245653625461221171

theorem tailTrace_1840623 : CollatzResearch.WordTrace tailWord_1840623 prefixEnd_1840623 420055245653625461221171 := by
  unfold tailWord_1840623
  simp only [CollatzResearch.WordTrace]
  refine ⟨67133036010744699226558523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44755357340496466151039015 67133036010744699226558523)
  ·
    refine ⟨100699554016117048839837785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67133036010744699226558523 100699554016117048839837785)
    ·
      refine ⟨75524665512087786629878339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100699554016117048839837785 75524665512087786629878339)
      ·
        refine ⟨113286998268131679944817509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75524665512087786629878339 113286998268131679944817509)
        ·
          refine ⟨21241312175274689989653283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113286998268131679944817509 21241312175274689989653283)
          ·
            refine ⟨31861968262912034984479925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21241312175274689989653283 31861968262912034984479925)
            ·
              refine ⟨2987059524648003279794993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31861968262912034984479925 2987059524648003279794993)
              ·
                refine ⟨2240294643486002459846245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2987059524648003279794993 2240294643486002459846245)
                ·
                  refine ⟨420055245653625461221171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2240294643486002459846245 420055245653625461221171)
                  ·
                    rfl

theorem cell21_1840623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 2, 4].length) (baseStart_1840623 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1840623 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1840623 prefixEnd_1840623 := by exact prefixLift 1840623
  have htrace : WordTrace (prefixWord ++ tailWord_1840623) baseStart_1840623 baseEnd_1840623 := by
    simpa [prefixWord, tailWord_1840623, baseEnd_1840623] using wordTrace_append hprefix tailTrace_1840623
  have hstable : (prefixWord ++ tailWord_1840623).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840623).length < 2 ^ (prefixWord ++ tailWord_1840623).sum := by decide
  have hdescent : baseEnd_1840623 < baseStart_1840623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840626 : List Nat := [3, 2, 1, 4, 1, 1, 2, 4, 3]
def baseStart_1840626 : Nat := 118140960795 + 1840626 * 2 ^ 59
def prefixEnd_1840626 : Nat := 4983230072969 + 3 ^ 40 * 1840626 * 2
def baseEnd_1840626 : Nat := 420055930294498122671165

theorem tailTrace_1840626 : CollatzResearch.WordTrace tailWord_1840626 prefixEnd_1840626 420055930294498122671165 := by
  unfold tailWord_1840626
  simp only [CollatzResearch.WordTrace]
  refine ⟨16783286357433457684729433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44755430286489220492611821 16783286357433457684729433)
  ·
    refine ⟨12587464768075093263547075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16783286357433457684729433 12587464768075093263547075)
    ·
      refine ⟨18881197152112639895320613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12587464768075093263547075 18881197152112639895320613)
      ·
        refine ⟨3540224466021119980372615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18881197152112639895320613 3540224466021119980372615)
        ·
          refine ⟨5310336699031679970558923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3540224466021119980372615 5310336699031679970558923)
          ·
            refine ⟨7965505048547519955838385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5310336699031679970558923 7965505048547519955838385)
            ·
              refine ⟨5974128786410639966878789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7965505048547519955838385 5974128786410639966878789)
              ·
                refine ⟨1120149147451994993789773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5974128786410639966878789 1120149147451994993789773)
                ·
                  refine ⟨420055930294498122671165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1120149147451994993789773 420055930294498122671165)
                  ·
                    rfl

theorem cell21_1840626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 4, 3].length) (baseStart_1840626 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1840626 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1840626 prefixEnd_1840626 := by exact prefixLift 1840626
  have htrace : WordTrace (prefixWord ++ tailWord_1840626) baseStart_1840626 baseEnd_1840626 := by
    simpa [prefixWord, tailWord_1840626, baseEnd_1840626] using wordTrace_append hprefix tailTrace_1840626
  have hstable : (prefixWord ++ tailWord_1840626).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840626).length < 2 ^ (prefixWord ++ tailWord_1840626).sum := by decide
  have hdescent : baseEnd_1840626 < baseStart_1840626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840646 : List Nat := [6, 2, 1, 1, 2, 2, 2, 5]
def baseStart_1840646 : Nat := 118140960795 + 1840646 * 2 ^ 59
def prefixEnd_1840646 : Nat := 4983230072969 + 3 ^ 40 * 1840646 * 2
def baseEnd_1840646 : Nat := 140020164855660844112597

theorem tailTrace_1840646 : CollatzResearch.WordTrace tailWord_1840646 prefixEnd_1840646 140020164855660844112597 := by
  unfold tailWord_1840646
  simp only [CollatzResearch.WordTrace]
  refine ⟨2097933590301917942332681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 44755916593107582769763861 2097933590301917942332681)
  ·
    refine ⟨1573450192726438456749511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2097933590301917942332681 1573450192726438456749511)
    ·
      refine ⟨2360175289089657685124267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1573450192726438456749511 2360175289089657685124267)
      ·
        refine ⟨3540262933634486527686401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2360175289089657685124267 3540262933634486527686401)
        ·
          refine ⟨2655197200225864895764801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3540262933634486527686401 2655197200225864895764801)
          ·
            refine ⟨1991397900169398671823601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2655197200225864895764801 1991397900169398671823601)
            ·
              refine ⟨1493548425127049003867701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1991397900169398671823601 1493548425127049003867701)
              ·
                refine ⟨140020164855660844112597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1493548425127049003867701 140020164855660844112597)
                ·
                  rfl

theorem cell21_1840646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_1840646 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1840646 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1840646 prefixEnd_1840646 := by exact prefixLift 1840646
  have htrace : WordTrace (prefixWord ++ tailWord_1840646) baseStart_1840646 baseEnd_1840646 := by
    simpa [prefixWord, tailWord_1840646, baseEnd_1840646] using wordTrace_append hprefix tailTrace_1840646
  have hstable : (prefixWord ++ tailWord_1840646).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840646).length < 2 ^ (prefixWord ++ tailWord_1840646).sum := by decide
  have hdescent : baseEnd_1840646 < baseStart_1840646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840654 : List Nat := [4, 1, 1, 2, 4, 1, 1, 7]
def baseStart_1840654 : Nat := 118140960795 + 1840654 * 2 ^ 59
def prefixEnd_1840654 : Nat := 4983230072969 + 3 ^ 40 * 1840654 * 2
def baseEnd_1840654 : Nat := 140020773425325432068147

theorem tailTrace_1840654 : CollatzResearch.WordTrace tailWord_1840654 prefixEnd_1840654 140020773425325432068147 := by
  unfold tailWord_1840654
  simp only [CollatzResearch.WordTrace]
  refine ⟨8391770834204048940117127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44756111115754927680624677 8391770834204048940117127)
  ·
    refine ⟨12587656251306073410175691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8391770834204048940117127 12587656251306073410175691)
    ·
      refine ⟨18881484376959110115263537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12587656251306073410175691 18881484376959110115263537)
      ·
        refine ⟨14161113282719332586447653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18881484376959110115263537 14161113282719332586447653)
        ·
          refine ⟨2655208740509874859958935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14161113282719332586447653 2655208740509874859958935)
          ·
            refine ⟨3982813110764812289938403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2655208740509874859958935 3982813110764812289938403)
            ·
              refine ⟨5974219666147218434907605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3982813110764812289938403 5974219666147218434907605)
              ·
                refine ⟨140020773425325432068147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5974219666147218434907605 140020773425325432068147)
                ·
                  rfl

theorem cell21_1840654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 7].length) (baseStart_1840654 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1840654 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1840654 prefixEnd_1840654 := by exact prefixLift 1840654
  have htrace : WordTrace (prefixWord ++ tailWord_1840654) baseStart_1840654 baseEnd_1840654 := by
    simpa [prefixWord, tailWord_1840654, baseEnd_1840654] using wordTrace_append hprefix tailTrace_1840654
  have hstable : (prefixWord ++ tailWord_1840654).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840654).length < 2 ^ (prefixWord ++ tailWord_1840654).sum := by decide
  have hdescent : baseEnd_1840654 < baseStart_1840654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840660 : List Nat := [2, 4, 3, 1, 2, 2, 1, 3, 3]
def baseStart_1840660 : Nat := 118140960795 + 1840660 * 2 ^ 59
def prefixEnd_1840660 : Nat := 4983230072969 + 3 ^ 40 * 1840660 * 2
def baseEnd_1840660 : Nat := 420063689557721619104429

theorem tailTrace_1840660 : CollatzResearch.WordTrace tailWord_1840660 prefixEnd_1840660 420063689557721619104429 := by
  unfold tailWord_1840660
  simp only [CollatzResearch.WordTrace]
  refine ⟨33567192755805327272827717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44756257007740436363770289 33567192755805327272827717)
  ·
    refine ⟨6293848641713498863655197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33567192755805327272827717 6293848641713498863655197)
    ·
      refine ⟨2360193240642562073870699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6293848641713498863655197 2360193240642562073870699)
      ·
        refine ⟨3540289860963843110806049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2360193240642562073870699 3540289860963843110806049)
        ·
          refine ⟨2655217395722882333104537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3540289860963843110806049 2655217395722882333104537)
          ·
            refine ⟨1991413046792161749828403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2655217395722882333104537 1991413046792161749828403)
            ·
              refine ⟨2987119570188242624742605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1991413046792161749828403 2987119570188242624742605)
              ·
                refine ⟨1120169838820590984278477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2987119570188242624742605 1120169838820590984278477)
                ·
                  refine ⟨420063689557721619104429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1120169838820590984278477 420063689557721619104429)
                  ·
                    rfl

theorem cell21_1840660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 3, 3].length) (baseStart_1840660 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1840660 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1840660 prefixEnd_1840660 := by exact prefixLift 1840660
  have htrace : WordTrace (prefixWord ++ tailWord_1840660) baseStart_1840660 baseEnd_1840660 := by
    simpa [prefixWord, tailWord_1840660, baseEnd_1840660] using wordTrace_append hprefix tailTrace_1840660
  have hstable : (prefixWord ++ tailWord_1840660).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840660).length < 2 ^ (prefixWord ++ tailWord_1840660).sum := by decide
  have hdescent : baseEnd_1840660 < baseStart_1840660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840778 : List Nat := [3, 1, 2, 3, 2, 2, 2, 3, 3]
def baseStart_1840778 : Nat := 118140960795 + 1840778 * 2 ^ 59
def prefixEnd_1840778 : Nat := 4983230072969 + 3 ^ 40 * 1840778 * 2
def baseEnd_1840778 : Nat := 420090618765379636137521

theorem tailTrace_1840778 : CollatzResearch.WordTrace tailWord_1840778 prefixEnd_1840778 420090618765379636137521 := by
  unfold tailWord_1840778
  simp only [CollatzResearch.WordTrace]
  refine ⟨16784672331295790174612747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44759126216788773798967325 16784672331295790174612747)
  ·
    refine ⟨25177008496943685261919121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16784672331295790174612747 25177008496943685261919121)
    ·
      refine ⟨18882756372707763946439341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25177008496943685261919121 18882756372707763946439341)
      ·
        refine ⟨7081033639765411479914753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18882756372707763946439341 7081033639765411479914753)
        ·
          refine ⟨5310775229824058609936065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7081033639765411479914753 5310775229824058609936065)
          ·
            refine ⟨3983081422368043957452049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5310775229824058609936065 3983081422368043957452049)
            ·
              refine ⟨2987311066776032968089037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3983081422368043957452049 2987311066776032968089037)
              ·
                refine ⟨1120241650041012363033389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2987311066776032968089037 1120241650041012363033389)
                ·
                  refine ⟨420090618765379636137521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1120241650041012363033389 420090618765379636137521)
                  ·
                    rfl

theorem cell21_1840778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 3, 3].length) (baseStart_1840778 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1840778 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1840778 prefixEnd_1840778 := by exact prefixLift 1840778
  have htrace : WordTrace (prefixWord ++ tailWord_1840778) baseStart_1840778 baseEnd_1840778 := by
    simpa [prefixWord, tailWord_1840778, baseEnd_1840778] using wordTrace_append hprefix tailTrace_1840778
  have hstable : (prefixWord ++ tailWord_1840778).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840778).length < 2 ^ (prefixWord ++ tailWord_1840778).sum := by decide
  have hdescent : baseEnd_1840778 < baseStart_1840778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840792 : List Nat := [2, 1, 2, 4, 1, 4, 1, 2, 4]
def baseStart_1840792 : Nat := 118140960795 + 1840792 * 2 ^ 59
def prefixEnd_1840792 : Nat := 4983230072969 + 3 ^ 40 * 1840792 * 2
def baseEnd_1840792 : Nat := 420093813756118722904159

theorem tailTrace_1840792 : CollatzResearch.WordTrace tailWord_1840792 prefixEnd_1840792 420093813756118722904159 := by
  unfold tailWord_1840792
  simp only [CollatzResearch.WordTrace]
  refine ⟨33569599973566220544730315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44759466631421627392973753 33569599973566220544730315)
  ·
    refine ⟨50354399960349330817095473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33569599973566220544730315 50354399960349330817095473)
    ·
      refine ⟨37765799970261998112821605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50354399960349330817095473 37765799970261998112821605)
      ·
        refine ⟨7081087494424124646154051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37765799970261998112821605 7081087494424124646154051)
        ·
          refine ⟨10621631241636186969231077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7081087494424124646154051 10621631241636186969231077)
          ·
            refine ⟨1991555857806785056730827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10621631241636186969231077 1991555857806785056730827)
            ·
              refine ⟨2987333786710177585096241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1991555857806785056730827 2987333786710177585096241)
              ·
                refine ⟨2240500340032633188822181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2987333786710177585096241 2240500340032633188822181)
                ·
                  refine ⟨420093813756118722904159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2240500340032633188822181 420093813756118722904159)
                  ·
                    rfl

theorem cell21_1840792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 2, 4].length) (baseStart_1840792 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1840792 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1840792 prefixEnd_1840792 := by exact prefixLift 1840792
  have htrace : WordTrace (prefixWord ++ tailWord_1840792) baseStart_1840792 baseEnd_1840792 := by
    simpa [prefixWord, tailWord_1840792, baseEnd_1840792] using wordTrace_append hprefix tailTrace_1840792
  have hstable : (prefixWord ++ tailWord_1840792).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840792).length < 2 ^ (prefixWord ++ tailWord_1840792).sum := by decide
  have hdescent : baseEnd_1840792 < baseStart_1840792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840879 : List Nat := [1, 1, 2, 1, 5, 1, 2, 1, 7]
def baseStart_1840879 : Nat := 118140960795 + 1840879 * 2 ^ 59
def prefixEnd_1840879 : Nat := 4983230072969 + 3 ^ 40 * 1840879 * 2
def baseEnd_1840879 : Nat := 420113668341425904953981

theorem tailTrace_1840879 : CollatzResearch.WordTrace tailWord_1840879 prefixEnd_1840879 420113668341425904953981 := by
  unfold tailWord_1840879
  simp only [CollatzResearch.WordTrace]
  refine ⟨67142373097817254947877691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44761582065211503298585127 67142373097817254947877691)
  ·
    refine ⟨100713559646725882421816537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67142373097817254947877691 100713559646725882421816537)
    ·
      refine ⟨75535169735044411816362403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100713559646725882421816537 75535169735044411816362403)
      ·
        refine ⟨113302754602566617724543605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75535169735044411816362403 113302754602566617724543605)
        ·
          refine ⟨10622133243990620411675963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 113302754602566617724543605 10622133243990620411675963)
          ·
            refine ⟨15933199865985930617513945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10622133243990620411675963 15933199865985930617513945)
            ·
              refine ⟨11949899899489447963135459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15933199865985930617513945 11949899899489447963135459)
              ·
                refine ⟨17924849849234171944703189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11949899899489447963135459 17924849849234171944703189)
                ·
                  refine ⟨420113668341425904953981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17924849849234171944703189 420113668341425904953981)
                  ·
                    rfl

theorem cell21_1840879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 7].length) (baseStart_1840879 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1840879 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1840879 prefixEnd_1840879 := by exact prefixLift 1840879
  have htrace : WordTrace (prefixWord ++ tailWord_1840879) baseStart_1840879 baseEnd_1840879 := by
    simpa [prefixWord, tailWord_1840879, baseEnd_1840879] using wordTrace_append hprefix tailTrace_1840879
  have hstable : (prefixWord ++ tailWord_1840879).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840879).length < 2 ^ (prefixWord ++ tailWord_1840879).sum := by decide
  have hdescent : baseEnd_1840879 < baseStart_1840879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840910 : List Nat := [4, 1, 1, 2, 1, 1, 2, 3, 6]
def baseStart_1840910 : Nat := 118140960795 + 1840910 * 2 ^ 59
def prefixEnd_1840910 : Nat := 4983230072969 + 3 ^ 40 * 1840910 * 2
def baseEnd_1840910 : Nat := 420120742963776739937251

theorem tailTrace_1840910 : CollatzResearch.WordTrace tailWord_1840910 prefixEnd_1840910 420120742963776739937251 := by
  unfold tailWord_1840910
  simp only [CollatzResearch.WordTrace]
  refine ⟨8392937970088118405282023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44762335840469964828170789 8392937970088118405282023)
  ·
    refine ⟨12589406955132177607923035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8392937970088118405282023 12589406955132177607923035)
    ·
      refine ⟨18884110432698266411884553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12589406955132177607923035 18884110432698266411884553)
      ·
        refine ⟨14163082824523699808913415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18884110432698266411884553 14163082824523699808913415)
        ·
          refine ⟨21244624236785549713370123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14163082824523699808913415 21244624236785549713370123)
          ·
            refine ⟨31866936355178324570055185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21244624236785549713370123 31866936355178324570055185)
            ·
              refine ⟨23900202266383743427541389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31866936355178324570055185 23900202266383743427541389)
              ·
                refine ⟨8962575849893903785328021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23900202266383743427541389 8962575849893903785328021)
                ·
                  refine ⟨420120742963776739937251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8962575849893903785328021 420120742963776739937251)
                  ·
                    rfl

theorem cell21_1840910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_1840910 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1840910 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1840910 prefixEnd_1840910 := by exact prefixLift 1840910
  have htrace : WordTrace (prefixWord ++ tailWord_1840910) baseStart_1840910 baseEnd_1840910 := by
    simpa [prefixWord, tailWord_1840910, baseEnd_1840910] using wordTrace_append hprefix tailTrace_1840910
  have hstable : (prefixWord ++ tailWord_1840910).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840910).length < 2 ^ (prefixWord ++ tailWord_1840910).sum := by decide
  have hdescent : baseEnd_1840910 < baseStart_1840910 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841006 : List Nat := [4, 1, 2, 3, 1, 1, 3, 3, 3]
def baseStart_1841006 : Nat := 118140960795 + 1841006 * 2 ^ 59
def prefixEnd_1841006 : Nat := 4983230072969 + 3 ^ 40 * 1841006 * 2
def baseEnd_1841006 : Nat := 420142651471701906337055

theorem tailTrace_1841006 : CollatzResearch.WordTrace tailWord_1841006 prefixEnd_1841006 420142651471701906337055 := by
  unfold tailWord_1841006
  simp only [CollatzResearch.WordTrace]
  refine ⟨8393375646044644454718859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44764670112238103758500581 8393375646044644454718859)
  ·
    refine ⟨12590063469066966682078289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8393375646044644454718859 12590063469066966682078289)
    ·
      refine ⟨9442547601800225011558717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12590063469066966682078289 9442547601800225011558717)
      ·
        refine ⟨3540955350675084379334519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9442547601800225011558717 3540955350675084379334519)
        ·
          refine ⟨5311433026012626569001779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3540955350675084379334519 5311433026012626569001779)
          ·
            refine ⟨7967149539018939853502669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5311433026012626569001779 7967149539018939853502669)
            ·
              refine ⟨2987681077132102445063501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7967149539018939853502669 2987681077132102445063501)
              ·
                refine ⟨1120380403924538416898813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2987681077132102445063501 1120380403924538416898813)
                ·
                  refine ⟨420142651471701906337055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1120380403924538416898813 420142651471701906337055)
                  ·
                    rfl

theorem cell21_1841006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 3, 3].length) (baseStart_1841006 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1841006 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1841006 prefixEnd_1841006 := by exact prefixLift 1841006
  have htrace : WordTrace (prefixWord ++ tailWord_1841006) baseStart_1841006 baseEnd_1841006 := by
    simpa [prefixWord, tailWord_1841006, baseEnd_1841006] using wordTrace_append hprefix tailTrace_1841006
  have hstable : (prefixWord ++ tailWord_1841006).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841006).length < 2 ^ (prefixWord ++ tailWord_1841006).sum := by decide
  have hdescent : baseEnd_1841006 < baseStart_1841006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841034 : List Nat := [3, 1, 2, 4, 2, 1, 2, 6]
def baseStart_1841034 : Nat := 118140960795 + 1841034 * 2 ^ 59
def prefixEnd_1841034 : Nat := 4983230072969 + 3 ^ 40 * 1841034 * 2
def baseEnd_1841034 : Nat := 140049680484393359956777

theorem tailTrace_1841034 : CollatzResearch.WordTrace tailWord_1841034 prefixEnd_1841034 140049680484393359956777 := by
  unfold tailWord_1841034
  simp only [CollatzResearch.WordTrace]
  refine ⟨16787006603063929104942539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44765350941503810946513437 16787006603063929104942539)
  ·
    refine ⟨25180509904595893657413809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16787006603063929104942539 25180509904595893657413809)
    ·
      refine ⟨18885382428446920243060357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25180509904595893657413809 18885382428446920243060357)
      ·
        refine ⟨3541009205333797545573817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18885382428446920243060357 3541009205333797545573817)
        ·
          refine ⟨2655756904000348159180363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3541009205333797545573817 2655756904000348159180363)
          ·
            refine ⟨3983635356000522238770545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2655756904000348159180363 3983635356000522238770545)
            ·
              refine ⟨2987726517000391679077909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3983635356000522238770545 2987726517000391679077909)
              ·
                refine ⟨140049680484393359956777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2987726517000391679077909 140049680484393359956777)
                ·
                  rfl

theorem cell21_1841034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 6].length) (baseStart_1841034 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1841034 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1841034 prefixEnd_1841034 := by exact prefixLift 1841034
  have htrace : WordTrace (prefixWord ++ tailWord_1841034) baseStart_1841034 baseEnd_1841034 := by
    simpa [prefixWord, tailWord_1841034, baseEnd_1841034] using wordTrace_append hprefix tailTrace_1841034
  have hstable : (prefixWord ++ tailWord_1841034).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841034).length < 2 ^ (prefixWord ++ tailWord_1841034).sum := by decide
  have hdescent : baseEnd_1841034 < baseStart_1841034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841116 : List Nat := [2, 2, 6, 1, 1, 1, 2, 3, 3]
def baseStart_1841116 : Nat := 118140960795 + 1841116 * 2 ^ 59
def prefixEnd_1841116 : Nat := 4983230072969 + 3 ^ 40 * 1841116 * 2
def baseEnd_1841116 : Nat := 420167754970366159503497

theorem tailTrace_1841116 : CollatzResearch.WordTrace tailWord_1841116 prefixEnd_1841116 420167754970366159503497 := by
  unfold tailWord_1841116
  simp only [CollatzResearch.WordTrace]
  refine ⟨33575508598979322212127601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44767344798639096282836801 33575508598979322212127601)
  ·
    refine ⟨25181631449234491659095701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33575508598979322212127601 25181631449234491659095701)
    ·
      refine ⟨1180388974182866796520111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 25181631449234491659095701 1180388974182866796520111)
      ·
        refine ⟨1770583461274300194780167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1180388974182866796520111 1770583461274300194780167)
        ·
          refine ⟨2655875191911450292170251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1770583461274300194780167 2655875191911450292170251)
          ·
            refine ⟨3983812787867175438255377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2655875191911450292170251 3983812787867175438255377)
            ·
              refine ⟨2987859590900381578691533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3983812787867175438255377 2987859590900381578691533)
              ·
                refine ⟨1120447346587643092009325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2987859590900381578691533 1120447346587643092009325)
                ·
                  refine ⟨420167754970366159503497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1120447346587643092009325 420167754970366159503497)
                  ·
                    rfl

theorem cell21_1841116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 3, 3].length) (baseStart_1841116 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1841116 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1841116 prefixEnd_1841116 := by exact prefixLift 1841116
  have htrace : WordTrace (prefixWord ++ tailWord_1841116) baseStart_1841116 baseEnd_1841116 := by
    simpa [prefixWord, tailWord_1841116, baseEnd_1841116] using wordTrace_append hprefix tailTrace_1841116
  have hstable : (prefixWord ++ tailWord_1841116).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841116).length < 2 ^ (prefixWord ++ tailWord_1841116).sum := by decide
  have hdescent : baseEnd_1841116 < baseStart_1841116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841175 : List Nat := [1, 1, 3, 5, 3, 1, 1, 3, 3]
def baseStart_1841175 : Nat := 118140960795 + 1841175 * 2 ^ 59
def prefixEnd_1841175 : Nat := 4983230072969 + 3 ^ 40 * 1841175 * 2
def baseEnd_1841175 : Nat := 420181219574195168020043

theorem tailTrace_1841175 : CollatzResearch.WordTrace tailWord_1841175 prefixEnd_1841175 420181219574195168020043 := by
  unfold tailWord_1841175
  simp only [CollatzResearch.WordTrace]
  refine ⟨67153169104744897500652979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44768779403163265000435319 67153169104744897500652979)
  ·
    refine ⟨100729753657117346250979469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67153169104744897500652979 100729753657117346250979469)
    ·
      refine ⟨37773657621419004844117301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100729753657117346250979469 37773657621419004844117301)
      ·
        refine ⟨3541280402008031704135997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37773657621419004844117301 3541280402008031704135997)
        ·
          refine ⟨1327980150753011889050999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3541280402008031704135997 1327980150753011889050999)
          ·
            refine ⟨1991970226129517833576499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1327980150753011889050999 1991970226129517833576499)
            ·
              refine ⟨2987955339194276750364749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1991970226129517833576499 2987955339194276750364749)
              ·
                refine ⟨1120483252197853781386781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2987955339194276750364749 1120483252197853781386781)
                ·
                  refine ⟨420181219574195168020043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1120483252197853781386781 420181219574195168020043)
                  ·
                    rfl

theorem cell21_1841175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 3, 3].length) (baseStart_1841175 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1841175 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1841175 prefixEnd_1841175 := by exact prefixLift 1841175
  have htrace : WordTrace (prefixWord ++ tailWord_1841175) baseStart_1841175 baseEnd_1841175 := by
    simpa [prefixWord, tailWord_1841175, baseEnd_1841175] using wordTrace_append hprefix tailTrace_1841175
  have hstable : (prefixWord ++ tailWord_1841175).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841175).length < 2 ^ (prefixWord ++ tailWord_1841175).sum := by decide
  have hdescent : baseEnd_1841175 < baseStart_1841175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841200 : List Nat := [2, 1, 1, 1, 2, 7, 1, 1, 5]
def baseStart_1841200 : Nat := 118140960795 + 1841200 * 2 ^ 59
def prefixEnd_1841200 : Nat := 4983230072969 + 3 ^ 40 * 1841200 * 2
def baseEnd_1841200 : Nat := 420186924914800680103325

theorem tailTrace_1841200 : CollatzResearch.WordTrace tailWord_1841200 prefixEnd_1841200 420186924914800680103325 := by
  unfold tailWord_1841200
  simp only [CollatzResearch.WordTrace]
  refine ⟨33577040464827163385156527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44769387286436217846875369 33577040464827163385156527)
  ·
    refine ⟨50365560697240745077734791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33577040464827163385156527 50365560697240745077734791)
    ·
      refine ⟨75548341045861117616602187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50365560697240745077734791 75548341045861117616602187)
      ·
        refine ⟨113322511568791676424903281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75548341045861117616602187 113322511568791676424903281)
        ·
          refine ⟨84991883676593757318677461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113322511568791676424903281 84991883676593757318677461)
          ·
            refine ⟨1991997273670166187156503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 84991883676593757318677461 1991997273670166187156503)
            ·
              refine ⟨2987995910505249280734755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1991997273670166187156503 2987995910505249280734755)
              ·
                refine ⟨4481993865757873921102133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2987995910505249280734755 4481993865757873921102133)
                ·
                  refine ⟨420186924914800680103325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4481993865757873921102133 420186924914800680103325)
                  ·
                    rfl

theorem cell21_1841200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 1, 5].length) (baseStart_1841200 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1841200 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1841200 prefixEnd_1841200 := by exact prefixLift 1841200
  have htrace : WordTrace (prefixWord ++ tailWord_1841200) baseStart_1841200 baseEnd_1841200 := by
    simpa [prefixWord, tailWord_1841200, baseEnd_1841200] using wordTrace_append hprefix tailTrace_1841200
  have hstable : (prefixWord ++ tailWord_1841200).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841200).length < 2 ^ (prefixWord ++ tailWord_1841200).sum := by decide
  have hdescent : baseEnd_1841200 < baseStart_1841200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841228 : List Nat := [2, 2, 1, 3, 1, 1, 4, 7]
def baseStart_1841228 : Nat := 118140960795 + 1841228 * 2 ^ 59
def prefixEnd_1841228 : Nat := 4983230072969 + 3 ^ 40 * 1841228 * 2
def baseEnd_1841228 : Nat := 140064438298759617878867

theorem tailTrace_1841228 : CollatzResearch.WordTrace tailWord_1841228 prefixEnd_1841228 140064438298759617878867 := by
  unfold tailWord_1841228
  simp only [CollatzResearch.WordTrace]
  refine ⟨33577551086776443776166169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44770068115701925034888225 33577551086776443776166169)
  ·
    refine ⟨25183163315082332832124627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33577551086776443776166169 25183163315082332832124627)
    ·
      refine ⟨37774744972623499248186941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25183163315082332832124627 37774744972623499248186941)
      ·
        refine ⟨14165529364733812218070103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37774744972623499248186941 14165529364733812218070103)
        ·
          refine ⟨21248294047100718327105155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14165529364733812218070103 21248294047100718327105155)
          ·
            refine ⟨31872441070651077490657733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21248294047100718327105155 31872441070651077490657733)
            ·
              refine ⟨5976082700747077029498325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31872441070651077490657733 5976082700747077029498325)
              ·
                refine ⟨140064438298759617878867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5976082700747077029498325 140064438298759617878867)
                ·
                  rfl

theorem cell21_1841228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 7].length) (baseStart_1841228 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1841228 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1841228 prefixEnd_1841228 := by exact prefixLift 1841228
  have htrace : WordTrace (prefixWord ++ tailWord_1841228) baseStart_1841228 baseEnd_1841228 := by
    simpa [prefixWord, tailWord_1841228, baseEnd_1841228] using wordTrace_append hprefix tailTrace_1841228
  have hstable : (prefixWord ++ tailWord_1841228).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841228).length < 2 ^ (prefixWord ++ tailWord_1841228).sum := by decide
  have hdescent : baseEnd_1841228 < baseStart_1841228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
