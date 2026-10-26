import V185TrunkScan21Chunk076

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_932060 : List Nat := [2, 2, 5, 2, 1, 2, 2, 2, 3]
def baseStart_932060 : Nat := 118140960795 + 932060 * 2 ^ 59
def prefixEnd_932060 : Nat := 4983230072969 + 3 ^ 40 * 932060 * 2
def baseEnd_932060 : Nat := 212708790590990464294907

theorem tailTrace_932060 : CollatzResearch.WordTrace tailWord_932060 prefixEnd_932060 212708790590990464294907 := by
  unfold tailWord_932060
  simp only [CollatzResearch.WordTrace]
  refine ⟨16997510501656639009944817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22663347335542185346593089 16997510501656639009944817)
  ·
    refine ⟨12748132876242479257458613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16997510501656639009944817 12748132876242479257458613)
    ·
      refine ⟨1195137457147732430386745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12748132876242479257458613 1195137457147732430386745)
      ·
        refine ⟨896353092860799322790059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1195137457147732430386745 896353092860799322790059)
        ·
          refine ⟨1344529639291198984185089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 896353092860799322790059 1344529639291198984185089)
          ·
            refine ⟨1008397229468399238138817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1344529639291198984185089 1008397229468399238138817)
            ·
              refine ⟨756297922101299428604113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1008397229468399238138817 756297922101299428604113)
              ·
                refine ⟨567223441575974571453085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 756297922101299428604113 567223441575974571453085)
                ·
                  refine ⟨212708790590990464294907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 567223441575974571453085 212708790590990464294907)
                  ·
                    rfl

theorem cell21_932060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 2, 2, 3].length) (baseStart_932060 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_932060 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_932060 prefixEnd_932060 := by exact prefixLift 932060
  have htrace : WordTrace (prefixWord ++ tailWord_932060) baseStart_932060 baseEnd_932060 := by
    simpa [prefixWord, tailWord_932060, baseEnd_932060] using wordTrace_append hprefix tailTrace_932060
  have hstable : (prefixWord ++ tailWord_932060).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932060).length < 2 ^ (prefixWord ++ tailWord_932060).sum := by decide
  have hdescent : baseEnd_932060 < baseStart_932060 := by decide
  rcases family_descends (prefixWord ++ tailWord_932060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932127 : List Nat := [1, 1, 2, 4, 3, 1, 1, 3, 5]
def baseStart_932127 : Nat := 118140960795 + 932127 * 2 ^ 59
def prefixEnd_932127 : Nat := 4983230072969 + 3 ^ 40 * 932127 * 2
def baseEnd_932127 : Nat := 212724080903813236678103

theorem tailTrace_932127 : CollatzResearch.WordTrace tailWord_932127 prefixEnd_932127 212724080903813236678103 := by
  unfold tailWord_932127
  simp only [CollatzResearch.WordTrace]
  refine ⟨33997464694070548462578635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22664976462713698975052423 33997464694070548462578635)
  ·
    refine ⟨50996197041105822693867953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33997464694070548462578635 50996197041105822693867953)
    ·
      refine ⟨38247147780829367020400965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50996197041105822693867953 38247147780829367020400965)
      ·
        refine ⟨7171340208905506316325181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38247147780829367020400965 7171340208905506316325181)
        ·
          refine ⟨2689252578339564868621943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7171340208905506316325181 2689252578339564868621943)
          ·
            refine ⟨4033878867509347302932915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2689252578339564868621943 4033878867509347302932915)
            ·
              refine ⟨6050818301264020954399373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4033878867509347302932915 6050818301264020954399373)
              ·
                refine ⟨2269056862974007857899765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6050818301264020954399373 2269056862974007857899765)
                ·
                  refine ⟨212724080903813236678103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2269056862974007857899765 212724080903813236678103)
                  ·
                    rfl

theorem cell21_932127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 3, 5].length) (baseStart_932127 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_932127 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_932127 prefixEnd_932127 := by exact prefixLift 932127
  have htrace : WordTrace (prefixWord ++ tailWord_932127) baseStart_932127 baseEnd_932127 := by
    simpa [prefixWord, tailWord_932127, baseEnd_932127] using wordTrace_append hprefix tailTrace_932127
  have hstable : (prefixWord ++ tailWord_932127).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932127).length < 2 ^ (prefixWord ++ tailWord_932127).sum := by decide
  have hdescent : baseEnd_932127 < baseStart_932127 := by decide
  rcases family_descends (prefixWord ++ tailWord_932127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932158 : List Nat := [4, 2, 1, 2, 1, 2, 1, 2, 6]
def baseStart_932158 : Nat := 118140960795 + 932158 * 2 ^ 59
def prefixEnd_932158 : Nat := 4983230072969 + 3 ^ 40 * 932158 * 2
def baseEnd_932158 : Nat := 212731155526164071661373

theorem tailTrace_932158 : CollatzResearch.WordTrace tailWord_932158 prefixEnd_932158 212731155526164071661373 := by
  unfold tailWord_932158
  simp only [CollatzResearch.WordTrace]
  refine ⟨4249824419619780094619641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22665730237972160504638085 4249824419619780094619641)
  ·
    refine ⟨3187368314714835070964731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4249824419619780094619641 3187368314714835070964731)
    ·
      refine ⟨4781052472072252606447097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3187368314714835070964731 4781052472072252606447097)
      ·
        refine ⟨3585789354054189454835323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4781052472072252606447097 3585789354054189454835323)
        ·
          refine ⟨5378684031081284182252985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3585789354054189454835323 5378684031081284182252985)
          ·
            refine ⟨4034013023310963136689739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5378684031081284182252985 4034013023310963136689739)
            ·
              refine ⟨6051019534966444705034609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4034013023310963136689739 6051019534966444705034609)
              ·
                refine ⟨4538264651224833528775957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6051019534966444705034609 4538264651224833528775957)
                ·
                  refine ⟨212731155526164071661373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4538264651224833528775957 212731155526164071661373)
                  ·
                    rfl

theorem cell21_932158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_932158 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_932158 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_932158 prefixEnd_932158 := by exact prefixLift 932158
  have htrace : WordTrace (prefixWord ++ tailWord_932158) baseStart_932158 baseEnd_932158 := by
    simpa [prefixWord, tailWord_932158, baseEnd_932158] using wordTrace_append hprefix tailTrace_932158
  have hstable : (prefixWord ++ tailWord_932158).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932158).length < 2 ^ (prefixWord ++ tailWord_932158).sum := by decide
  have hdescent : baseEnd_932158 < baseStart_932158 := by decide
  rcases family_descends (prefixWord ++ tailWord_932158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932192 : List Nat := [2, 1, 1, 3, 5, 2, 2, 1, 4]
def baseStart_932192 : Nat := 118140960795 + 932192 * 2 ^ 59
def prefixEnd_932192 : Nat := 4983230072969 + 3 ^ 40 * 932192 * 2
def baseEnd_932192 : Nat := 212738914789387568094637

theorem tailTrace_932192 : CollatzResearch.WordTrace tailWord_932192 prefixEnd_932192 212738914789387568094637 := by
  unfold tailWord_932192
  simp only [CollatzResearch.WordTrace]
  refine ⟨16999917719417532281847415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22666556959223376375796553 16999917719417532281847415)
  ·
    refine ⟨25499876579126298422771123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16999917719417532281847415 25499876579126298422771123)
    ·
      refine ⟨38249814868689447634156685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25499876579126298422771123 38249814868689447634156685)
      ·
        refine ⟨14343680575758542862808757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38249814868689447634156685 14343680575758542862808757)
        ·
          refine ⟨1344720053977363393388321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14343680575758542862808757 1344720053977363393388321)
          ·
            refine ⟨1008540040483022545041241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1344720053977363393388321 1008540040483022545041241)
            ·
              refine ⟨756405030362266908780931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1008540040483022545041241 756405030362266908780931)
              ·
                refine ⟨1134607545543400363171397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 756405030362266908780931 1134607545543400363171397)
                ·
                  refine ⟨212738914789387568094637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1134607545543400363171397 212738914789387568094637)
                  ·
                    rfl

theorem cell21_932192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 2, 1, 4].length) (baseStart_932192 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_932192 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_932192 prefixEnd_932192 := by exact prefixLift 932192
  have htrace : WordTrace (prefixWord ++ tailWord_932192) baseStart_932192 baseEnd_932192 := by
    simpa [prefixWord, tailWord_932192, baseEnd_932192] using wordTrace_append hprefix tailTrace_932192
  have hstable : (prefixWord ++ tailWord_932192).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932192).length < 2 ^ (prefixWord ++ tailWord_932192).sum := by decide
  have hdescent : baseEnd_932192 < baseStart_932192 := by decide
  rcases family_descends (prefixWord ++ tailWord_932192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932296 : List Nat := [2, 1, 3, 1, 3, 2, 2, 4, 3]
def baseStart_932296 : Nat := 118140960795 + 932296 * 2 ^ 59
def prefixEnd_932296 : Nat := 4983230072969 + 3 ^ 40 * 932296 * 2
def baseEnd_932296 : Nat := 212762649006306498361091

theorem tailTrace_932296 : CollatzResearch.WordTrace tailWord_932296 prefixEnd_932296 212762649006306498361091 := by
  unfold tailWord_932296
  simp only [CollatzResearch.WordTrace]
  refine ⟨17001814315229145162740371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22669085753638860216987161 17001814315229145162740371)
  ·
    refine ⟨25502721472843717744110557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17001814315229145162740371 25502721472843717744110557)
    ·
      refine ⟨9563520552316394154041459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25502721472843717744110557 9563520552316394154041459)
      ·
        refine ⟨14345280828474591231062189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9563520552316394154041459 14345280828474591231062189)
        ·
          refine ⟨5379480310677971711648321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14345280828474591231062189 5379480310677971711648321)
          ·
            refine ⟨4034610233008478783736241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5379480310677971711648321 4034610233008478783736241)
            ·
              refine ⟨3025957674756359087802181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4034610233008478783736241 3025957674756359087802181)
              ·
                refine ⟨567367064016817328962909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3025957674756359087802181 567367064016817328962909)
                ·
                  refine ⟨212762649006306498361091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 567367064016817328962909 212762649006306498361091)
                  ·
                    rfl

theorem cell21_932296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 4, 3].length) (baseStart_932296 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_932296 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_932296 prefixEnd_932296 := by exact prefixLift 932296
  have htrace : WordTrace (prefixWord ++ tailWord_932296) baseStart_932296 baseEnd_932296 := by
    simpa [prefixWord, tailWord_932296, baseEnd_932296] using wordTrace_append hprefix tailTrace_932296
  have hstable : (prefixWord ++ tailWord_932296).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932296).length < 2 ^ (prefixWord ++ tailWord_932296).sum := by decide
  have hdescent : baseEnd_932296 < baseStart_932296 := by decide
  rcases family_descends (prefixWord ++ tailWord_932296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932406 : List Nat := [5, 1, 2, 1, 2, 1, 4, 2, 3]
def baseStart_932406 : Nat := 118140960795 + 932406 * 2 ^ 59
def prefixEnd_932406 : Nat := 4983230072969 + 3 ^ 40 * 932406 * 2
def baseEnd_932406 : Nat := 212787752504970751527533

theorem tailTrace_932406 : CollatzResearch.WordTrace tailWord_932406 prefixEnd_932406 212787752504970751527533 := by
  unfold tailWord_932406
  simp only [CollatzResearch.WordTrace]
  refine ⟨2125477541253736194499067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22671760440039852741323381 2125477541253736194499067)
  ·
    refine ⟨3188216311880604291748601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2125477541253736194499067 3188216311880604291748601)
    ·
      refine ⟨2391162233910453218811451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3188216311880604291748601 2391162233910453218811451)
      ·
        refine ⟨3586743350865679828217177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2391162233910453218811451 3586743350865679828217177)
        ·
          refine ⟨2690057513149259871162883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3586743350865679828217177 2690057513149259871162883)
          ·
            refine ⟨4035086269723889806744325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2690057513149259871162883 4035086269723889806744325)
            ·
              refine ⟨756578675573229338764561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4035086269723889806744325 756578675573229338764561)
              ·
                refine ⟨567434006679922004073421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 756578675573229338764561 567434006679922004073421)
                ·
                  refine ⟨212787752504970751527533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 567434006679922004073421 212787752504970751527533)
                  ·
                    rfl

theorem cell21_932406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 4, 2, 3].length) (baseStart_932406 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_932406 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_932406 prefixEnd_932406 := by exact prefixLift 932406
  have htrace : WordTrace (prefixWord ++ tailWord_932406) baseStart_932406 baseEnd_932406 := by
    simpa [prefixWord, tailWord_932406, baseEnd_932406] using wordTrace_append hprefix tailTrace_932406
  have hstable : (prefixWord ++ tailWord_932406).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932406).length < 2 ^ (prefixWord ++ tailWord_932406).sum := by decide
  have hdescent : baseEnd_932406 < baseStart_932406 := by decide
  rcases family_descends (prefixWord ++ tailWord_932406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932417 : List Nat := [1, 2, 5, 1, 1, 4, 1, 6]
def baseStart_932417 : Nat := 118140960795 + 932417 * 2 ^ 59
def prefixEnd_932417 : Nat := 4983230072969 + 3 ^ 40 * 932417 * 2
def baseEnd_932417 : Nat := 70930087618279058948059

theorem tailTrace_932417 : CollatzResearch.WordTrace tailWord_932417 prefixEnd_932417 70930087618279058948059 := by
  unfold tailWord_932417
  simp only [CollatzResearch.WordTrace]
  refine ⟨34008041863019927990635505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22672027908679951993757003 34008041863019927990635505)
  ·
    refine ⟨25506031397264945992976629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34008041863019927990635505 25506031397264945992976629)
    ·
      refine ⟨2391190443493588686841559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25506031397264945992976629 2391190443493588686841559)
      ·
        refine ⟨3586785665240383030262339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2391190443493588686841559 3586785665240383030262339)
        ·
          refine ⟨5380178497860574545393509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3586785665240383030262339 5380178497860574545393509)
          ·
            refine ⟨1008783468348857727261283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5380178497860574545393509 1008783468348857727261283)
            ·
              refine ⟨1513175202523286590891925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1008783468348857727261283 1513175202523286590891925)
              ·
                refine ⟨70930087618279058948059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1513175202523286590891925 70930087618279058948059)
                ·
                  rfl

theorem cell21_932417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 6].length) (baseStart_932417 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_932417 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_932417 prefixEnd_932417 := by exact prefixLift 932417
  have htrace : WordTrace (prefixWord ++ tailWord_932417) baseStart_932417 baseEnd_932417 := by
    simpa [prefixWord, tailWord_932417, baseEnd_932417] using wordTrace_append hprefix tailTrace_932417
  have hstable : (prefixWord ++ tailWord_932417).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932417).length < 2 ^ (prefixWord ++ tailWord_932417).sum := by decide
  have hdescent : baseEnd_932417 < baseStart_932417 := by decide
  rcases family_descends (prefixWord ++ tailWord_932417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932462 : List Nat := [4, 1, 2, 2, 2, 2, 1, 1, 6]
def baseStart_932462 : Nat := 118140960795 + 932462 * 2 ^ 59
def prefixEnd_932462 : Nat := 4983230072969 + 3 ^ 40 * 932462 * 2
def baseEnd_932462 : Nat := 212800532467927098594085

theorem tailTrace_932462 : CollatzResearch.WordTrace tailWord_932462 prefixEnd_932462 212800532467927098594085 := by
  unfold tailWord_932462
  simp only [CollatzResearch.WordTrace]
  refine ⟨4251210393482112584502955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22673122098571267117349093 4251210393482112584502955)
  ·
    refine ⟨6376815590223168876754433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4251210393482112584502955 6376815590223168876754433)
    ·
      refine ⟨4782611692667376657565825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6376815590223168876754433 4782611692667376657565825)
      ·
        refine ⟨3586958769500532493174369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4782611692667376657565825 3586958769500532493174369)
        ·
          refine ⟨2690219077125399369880777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3586958769500532493174369 2690219077125399369880777)
          ·
            refine ⟨2017664307844049527410583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2690219077125399369880777 2017664307844049527410583)
            ·
              refine ⟨3026496461766074291115875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2017664307844049527410583 3026496461766074291115875)
              ·
                refine ⟨4539744692649111436673813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3026496461766074291115875 4539744692649111436673813)
                ·
                  refine ⟨212800532467927098594085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4539744692649111436673813 212800532467927098594085)
                  ·
                    rfl

theorem cell21_932462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 6].length) (baseStart_932462 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_932462 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_932462 prefixEnd_932462 := by exact prefixLift 932462
  have htrace : WordTrace (prefixWord ++ tailWord_932462) baseStart_932462 baseEnd_932462 := by
    simpa [prefixWord, tailWord_932462, baseEnd_932462] using wordTrace_append hprefix tailTrace_932462
  have hstable : (prefixWord ++ tailWord_932462).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932462).length < 2 ^ (prefixWord ++ tailWord_932462).sum := by decide
  have hdescent : baseEnd_932462 < baseStart_932462 := by decide
  rcases family_descends (prefixWord ++ tailWord_932462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932631 : List Nat := [1, 1, 3, 4, 3, 2, 1, 2, 4]
def baseStart_932631 : Nat := 118140960795 + 932631 * 2 ^ 59
def prefixEnd_932631 : Nat := 4983230072969 + 3 ^ 40 * 932631 * 2
def baseEnd_932631 : Nat := 212839100570420360277073

theorem tailTrace_932631 : CollatzResearch.WordTrace tailWord_932631 prefixEnd_932631 212839100570420360277073 := by
  unfold tailWord_932631
  simp only [CollatzResearch.WordTrace]
  refine ⟨34015847084244642538925747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22677231389496428359283831 34015847084244642538925747)
  ·
    refine ⟨51023770626366963808388621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34015847084244642538925747 51023770626366963808388621)
    ·
      refine ⟨19133913984887611428145733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51023770626366963808388621 19133913984887611428145733)
      ·
        refine ⟨3587608872166427142777325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19133913984887611428145733 3587608872166427142777325)
        ·
          refine ⟨1345353327062410178541497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3587608872166427142777325 1345353327062410178541497)
          ·
            refine ⟨1009014995296807633906123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1345353327062410178541497 1009014995296807633906123)
            ·
              refine ⟨1513522492945211450859185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1009014995296807633906123 1513522492945211450859185)
              ·
                refine ⟨1135141869708908588144389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1513522492945211450859185 1135141869708908588144389)
                ·
                  refine ⟨212839100570420360277073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1135141869708908588144389 212839100570420360277073)
                  ·
                    rfl

theorem cell21_932631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 2, 4].length) (baseStart_932631 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_932631 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_932631 prefixEnd_932631 := by exact prefixLift 932631
  have htrace : WordTrace (prefixWord ++ tailWord_932631) baseStart_932631 baseEnd_932631 := by
    simpa [prefixWord, tailWord_932631, baseEnd_932631] using wordTrace_append hprefix tailTrace_932631
  have hstable : (prefixWord ++ tailWord_932631).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932631).length < 2 ^ (prefixWord ++ tailWord_932631).sum := by decide
  have hdescent : baseEnd_932631 < baseStart_932631 := by decide
  rcases family_descends (prefixWord ++ tailWord_932631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932707 : List Nat := [1, 1, 1, 5, 3, 3, 2, 1, 4]
def baseStart_932707 : Nat := 118140960795 + 932707 * 2 ^ 59
def prefixEnd_932707 : Nat := 4983230072969 + 3 ^ 40 * 932707 * 2
def baseEnd_932707 : Nat := 212856444805861117010251

theorem tailTrace_932707 : CollatzResearch.WordTrace tailWord_932707 prefixEnd_932707 212856444805861117010251 := by
  unfold tailWord_932707
  simp only [CollatzResearch.WordTrace]
  refine ⟨34018619031969307518692375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22679079354646205012461583 34018619031969307518692375)
  ·
    refine ⟨51027928547953961278038563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34018619031969307518692375 51027928547953961278038563)
    ·
      refine ⟨76541892821930941917057845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51027928547953961278038563 76541892821930941917057845)
      ·
        refine ⟨7175802452056025804724173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76541892821930941917057845 7175802452056025804724173)
        ·
          refine ⟨2690925919521009676771565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7175802452056025804724173 2690925919521009676771565)
          ·
            refine ⟨1009097219820378628789337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2690925919521009676771565 1009097219820378628789337)
            ·
              refine ⟨756822914865283971592003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1009097219820378628789337 756822914865283971592003)
              ·
                refine ⟨1135234372297925957388005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 756822914865283971592003 1135234372297925957388005)
                ·
                  refine ⟨212856444805861117010251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1135234372297925957388005 212856444805861117010251)
                  ·
                    rfl

theorem cell21_932707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 2, 1, 4].length) (baseStart_932707 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_932707 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_932707 prefixEnd_932707 := by exact prefixLift 932707
  have htrace : WordTrace (prefixWord ++ tailWord_932707) baseStart_932707 baseEnd_932707 := by
    simpa [prefixWord, tailWord_932707, baseEnd_932707] using wordTrace_append hprefix tailTrace_932707
  have hstable : (prefixWord ++ tailWord_932707).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932707).length < 2 ^ (prefixWord ++ tailWord_932707).sum := by decide
  have hdescent : baseEnd_932707 < baseStart_932707 := by decide
  rcases family_descends (prefixWord ++ tailWord_932707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932732 : List Nat := [2, 2, 2, 1, 1, 1, 1, 3, 8]
def baseStart_932732 : Nat := 118140960795 + 932732 * 2 ^ 59
def prefixEnd_932732 : Nat := 4983230072969 + 3 ^ 40 * 932732 * 2
def baseEnd_932732 : Nat := 212862150146466629093533

theorem tailTrace_932732 : CollatzResearch.WordTrace tailWord_932732 prefixEnd_932732 212862150146466629093533 := by
  unfold tailWord_932732
  simp only [CollatzResearch.WordTrace]
  refine ⟨17009765428439368394176225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22679687237919157858901633 17009765428439368394176225)
  ·
    refine ⟨12757324071329526295632169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17009765428439368394176225 12757324071329526295632169)
    ·
      refine ⟨9567993053497144721724127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12757324071329526295632169 9567993053497144721724127)
      ·
        refine ⟨14351989580245717082586191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9567993053497144721724127 14351989580245717082586191)
        ·
          refine ⟨21527984370368575623879287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14351989580245717082586191 21527984370368575623879287)
          ·
            refine ⟨32291976555552863435818931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21527984370368575623879287 32291976555552863435818931)
            ·
              refine ⟨48437964833329295153728397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32291976555552863435818931 48437964833329295153728397)
              ·
                refine ⟨18164236812498485682648149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48437964833329295153728397 18164236812498485682648149)
                ·
                  refine ⟨212862150146466629093533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18164236812498485682648149 212862150146466629093533)
                  ·
                    rfl

theorem cell21_932732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 8].length) (baseStart_932732 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_932732 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_932732 prefixEnd_932732 := by exact prefixLift 932732
  have htrace : WordTrace (prefixWord ++ tailWord_932732) baseStart_932732 baseEnd_932732 := by
    simpa [prefixWord, tailWord_932732, baseEnd_932732] using wordTrace_append hprefix tailTrace_932732
  have hstable : (prefixWord ++ tailWord_932732).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932732).length < 2 ^ (prefixWord ++ tailWord_932732).sum := by decide
  have hdescent : baseEnd_932732 < baseStart_932732 := by decide
  rcases family_descends (prefixWord ++ tailWord_932732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932738 : List Nat := [3, 4, 2, 2, 2, 8]
def baseStart_932738 : Nat := 118140960795 + 932738 * 2 ^ 59
def prefixEnd_932738 : Nat := 4983230072969 + 3 ^ 40 * 932738 * 2
def baseEnd_932738 : Nat := 7883834052896738962723

theorem tailTrace_932738 : CollatzResearch.WordTrace tailWord_932738 prefixEnd_932738 7883834052896738962723 := by
  unfold tailWord_932738
  simp only [CollatzResearch.WordTrace]
  refine ⟨8504937423714249953267717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22679833129904666542047245 8504937423714249953267717)
  ·
    refine ⟨1594675766946421866237697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8504937423714249953267717 1594675766946421866237697)
    ·
      refine ⟨1196006825209816399678273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1594675766946421866237697 1196006825209816399678273)
      ·
        refine ⟨897005118907362299758705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1196006825209816399678273 897005118907362299758705)
        ·
          refine ⟨672753839180521724819029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 897005118907362299758705 672753839180521724819029)
          ·
            refine ⟨7883834052896738962723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 672753839180521724819029 7883834052896738962723)
            ·
              rfl

theorem cell21_932738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 8].length) (baseStart_932738 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_932738 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_932738 prefixEnd_932738 := by exact prefixLift 932738
  have htrace : WordTrace (prefixWord ++ tailWord_932738) baseStart_932738 baseEnd_932738 := by
    simpa [prefixWord, tailWord_932738, baseEnd_932738] using wordTrace_append hprefix tailTrace_932738
  have hstable : (prefixWord ++ tailWord_932738).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932738).length < 2 ^ (prefixWord ++ tailWord_932738).sum := by decide
  have hdescent : baseEnd_932738 < baseStart_932738 := by decide
  rcases family_descends (prefixWord ++ tailWord_932738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932811 : List Nat := [1, 1, 1, 1, 3, 5, 2, 4, 3]
def baseStart_932811 : Nat := 118140960795 + 932811 * 2 ^ 59
def prefixEnd_932811 : Nat := 4983230072969 + 3 ^ 40 * 932811 * 2
def baseEnd_932811 : Nat := 212880179022780047276705

theorem tailTrace_932811 : CollatzResearch.WordTrace tailWord_932811 prefixEnd_932811 212880179022780047276705 := by
  unfold tailWord_932811
  simp only [CollatzResearch.WordTrace]
  refine ⟨34022412223592533280478287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22681608149061688853652191 34022412223592533280478287)
  ·
    refine ⟨51033618335388799920717431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34022412223592533280478287 51033618335388799920717431)
    ·
      refine ⟨76550427503083199881076147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51033618335388799920717431 76550427503083199881076147)
      ·
        refine ⟨114825641254624799821614221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76550427503083199881076147 114825641254624799821614221)
        ·
          refine ⟨43059615470484299933105333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114825641254624799821614221 43059615470484299933105333)
          ·
            refine ⟨4036838950357903118728625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43059615470484299933105333 4036838950357903118728625)
            ·
              refine ⟨3027629212768427339046469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4036838950357903118728625 3027629212768427339046469)
              ·
                refine ⟨567680477394080126071213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3027629212768427339046469 567680477394080126071213)
                ·
                  refine ⟨212880179022780047276705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 567680477394080126071213 212880179022780047276705)
                  ·
                    rfl

theorem cell21_932811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 4, 3].length) (baseStart_932811 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_932811 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_932811 prefixEnd_932811 := by exact prefixLift 932811
  have htrace : WordTrace (prefixWord ++ tailWord_932811) baseStart_932811 baseEnd_932811 := by
    simpa [prefixWord, tailWord_932811, baseEnd_932811] using wordTrace_append hprefix tailTrace_932811
  have hstable : (prefixWord ++ tailWord_932811).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932811).length < 2 ^ (prefixWord ++ tailWord_932811).sum := by decide
  have hdescent : baseEnd_932811 < baseStart_932811 := by decide
  rcases family_descends (prefixWord ++ tailWord_932811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932862 : List Nat := [4, 2, 2, 2, 2, 1, 3, 2, 3]
def baseStart_932862 : Nat := 118140960795 + 932862 * 2 ^ 59
def prefixEnd_932862 : Nat := 4983230072969 + 3 ^ 40 * 932862 * 2
def baseEnd_932862 : Nat := 212891817917615291926601

theorem tailTrace_932862 : CollatzResearch.WordTrace tailWord_932862 prefixEnd_932862 212891817917615291926601 := by
  unfold tailWord_932862
  simp only [CollatzResearch.WordTrace]
  refine ⟨4253034043300971123823105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22682848230938512660389893 4253034043300971123823105)
  ·
    refine ⟨3189775532475728342867329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4253034043300971123823105 3189775532475728342867329)
    ·
      refine ⟨2392331649356796257150497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3189775532475728342867329 2392331649356796257150497)
      ·
        refine ⟨1794248737017597192862873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2392331649356796257150497 1794248737017597192862873)
        ·
          refine ⟨1345686552763197894647155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1794248737017597192862873 1345686552763197894647155)
          ·
            refine ⟨2018529829144796841970733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1345686552763197894647155 2018529829144796841970733)
            ·
              refine ⟨756948685929298815739025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2018529829144796841970733 756948685929298815739025)
              ·
                refine ⟨567711514446974111804269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 756948685929298815739025 567711514446974111804269)
                ·
                  refine ⟨212891817917615291926601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 567711514446974111804269 212891817917615291926601)
                  ·
                    rfl

theorem cell21_932862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 3, 2, 3].length) (baseStart_932862 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_932862 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_932862 prefixEnd_932862 := by exact prefixLift 932862
  have htrace : WordTrace (prefixWord ++ tailWord_932862) baseStart_932862 baseEnd_932862 := by
    simpa [prefixWord, tailWord_932862, baseEnd_932862] using wordTrace_append hprefix tailTrace_932862
  have hstable : (prefixWord ++ tailWord_932862).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932862).length < 2 ^ (prefixWord ++ tailWord_932862).sum := by decide
  have hdescent : baseEnd_932862 < baseStart_932862 := by decide
  rcases family_descends (prefixWord ++ tailWord_932862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932918 : List Nat := [5, 1, 2, 1, 1, 2, 1, 4, 4]
def baseStart_932918 : Nat := 118140960795 + 932918 * 2 ^ 59
def prefixEnd_932918 : Nat := 4983230072969 + 3 ^ 40 * 932918 * 2
def baseEnd_932918 : Nat := 212904597880571638993153

theorem tailTrace_932918 : CollatzResearch.WordTrace tailWord_932918 prefixEnd_932918 212904597880571638993153 := by
  unfold tailWord_932918
  simp only [CollatzResearch.WordTrace]
  refine ⟨2126644677137805659663963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22684209889469927036415605 2126644677137805659663963)
  ·
    refine ⟨3189967015706708489495945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2126644677137805659663963 3189967015706708489495945)
    ·
      refine ⟨2392475261780031367121959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3189967015706708489495945 2392475261780031367121959)
      ·
        refine ⟨3588712892670047050682939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2392475261780031367121959 3588712892670047050682939)
        ·
          refine ⟨5383069339005070576024409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3588712892670047050682939 5383069339005070576024409)
          ·
            refine ⟨4037302004253802932018307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5383069339005070576024409 4037302004253802932018307)
            ·
              refine ⟨6055953006380704398027461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4037302004253802932018307 6055953006380704398027461)
              ·
                refine ⟨1135491188696382074630149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6055953006380704398027461 1135491188696382074630149)
                ·
                  refine ⟨212904597880571638993153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1135491188696382074630149 212904597880571638993153)
                  ·
                    rfl

theorem cell21_932918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_932918 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_932918 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_932918 prefixEnd_932918 := by exact prefixLift 932918
  have htrace : WordTrace (prefixWord ++ tailWord_932918) baseStart_932918 baseEnd_932918 := by
    simpa [prefixWord, tailWord_932918, baseEnd_932918] using wordTrace_append hprefix tailTrace_932918
  have hstable : (prefixWord ++ tailWord_932918).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932918).length < 2 ^ (prefixWord ++ tailWord_932918).sum := by decide
  have hdescent : baseEnd_932918 < baseStart_932918 := by decide
  rcases family_descends (prefixWord ++ tailWord_932918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932921 : List Nat := [1, 2, 1, 5, 2, 3, 2, 2, 3]
def baseStart_932921 : Nat := 118140960795 + 932921 * 2 ^ 59
def prefixEnd_932921 : Nat := 4983230072969 + 3 ^ 40 * 932921 * 2
def baseEnd_932921 : Nat := 212905282521444300443147

theorem tailTrace_932921 : CollatzResearch.WordTrace tailWord_932921 prefixEnd_932921 212905282521444300443147 := by
  unfold tailWord_932921
  simp only [CollatzResearch.WordTrace]
  refine ⟨34026424253194022066982617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22684282835462681377988411 34026424253194022066982617)
  ·
    refine ⟨25519818189895516550236963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34026424253194022066982617 25519818189895516550236963)
    ·
      refine ⟨38279727284843274825355445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25519818189895516550236963 38279727284843274825355445)
      ·
        refine ⟨3588724432954057014877073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38279727284843274825355445 3588724432954057014877073)
        ·
          refine ⟨2691543324715542761157805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3588724432954057014877073 2691543324715542761157805)
          ·
            refine ⟨1009328746768328535434177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2691543324715542761157805 1009328746768328535434177)
            ·
              refine ⟨756996560076246401575633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1009328746768328535434177 756996560076246401575633)
              ·
                refine ⟨567747420057184801181725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 756996560076246401575633 567747420057184801181725)
                ·
                  refine ⟨212905282521444300443147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 567747420057184801181725 212905282521444300443147)
                  ·
                    rfl

theorem cell21_932921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 2, 2, 3].length) (baseStart_932921 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_932921 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_932921 prefixEnd_932921 := by exact prefixLift 932921
  have htrace : WordTrace (prefixWord ++ tailWord_932921) baseStart_932921 baseEnd_932921 := by
    simpa [prefixWord, tailWord_932921, baseEnd_932921] using wordTrace_append hprefix tailTrace_932921
  have hstable : (prefixWord ++ tailWord_932921).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932921).length < 2 ^ (prefixWord ++ tailWord_932921).sum := by decide
  have hdescent : baseEnd_932921 < baseStart_932921 := by decide
  rcases family_descends (prefixWord ++ tailWord_932921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932946 : List Nat := [3, 2, 2, 1, 3, 1, 1, 1, 7]
def baseStart_932946 : Nat := 118140960795 + 932946 * 2 ^ 59
def prefixEnd_932946 : Nat := 4983230072969 + 3 ^ 40 * 932946 * 2
def baseEnd_932946 : Nat := 212910987862049812526429

theorem tailTrace_932946 : CollatzResearch.WordTrace tailWord_932946 prefixEnd_932946 212910987862049812526429 := by
  unfold tailWord_932946
  simp only [CollatzResearch.WordTrace]
  refine ⟨8506834019525862834160673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22684890718735634224428461 8506834019525862834160673)
  ·
    refine ⟨6380125514644397125620505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8506834019525862834160673 6380125514644397125620505)
    ·
      refine ⟨4785094135983297844215379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6380125514644397125620505 4785094135983297844215379)
      ·
        refine ⟨7177641203974946766323069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4785094135983297844215379 7177641203974946766323069)
        ·
          refine ⟨2691615451490605037371151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7177641203974946766323069 2691615451490605037371151)
          ·
            refine ⟨4037423177235907556056727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2691615451490605037371151 4037423177235907556056727)
            ·
              refine ⟨6056134765853861334085091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4037423177235907556056727 6056134765853861334085091)
              ·
                refine ⟨9084202148780792001127637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6056134765853861334085091 9084202148780792001127637)
                ·
                  refine ⟨212910987862049812526429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9084202148780792001127637 212910987862049812526429)
                  ·
                    rfl

theorem cell21_932946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 7].length) (baseStart_932946 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_932946 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_932946 prefixEnd_932946 := by exact prefixLift 932946
  have htrace : WordTrace (prefixWord ++ tailWord_932946) baseStart_932946 baseEnd_932946 := by
    simpa [prefixWord, tailWord_932946, baseEnd_932946] using wordTrace_append hprefix tailTrace_932946
  have hstable : (prefixWord ++ tailWord_932946).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932946).length < 2 ^ (prefixWord ++ tailWord_932946).sum := by decide
  have hdescent : baseEnd_932946 < baseStart_932946 := by decide
  rcases family_descends (prefixWord ++ tailWord_932946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932960 : List Nat := [2, 1, 1, 3, 2, 2, 2, 2, 6]
def baseStart_932960 : Nat := 118140960795 + 932960 * 2 ^ 59
def prefixEnd_932960 : Nat := 4983230072969 + 3 ^ 40 * 932960 * 2
def baseEnd_932960 : Nat := 212914182852788899293067

theorem tailTrace_932960 : CollatzResearch.WordTrace tailWord_932960 prefixEnd_932960 212914182852788899293067 := by
  unfold tailWord_932960
  simp only [CollatzResearch.WordTrace]
  refine ⟨17013923350026365863826167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22685231133368487818434889 17013923350026365863826167)
  ·
    refine ⟨25520885025039548795739251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17013923350026365863826167 25520885025039548795739251)
    ·
      refine ⟨38281327537559323193608877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25520885025039548795739251 38281327537559323193608877)
      ·
        refine ⟨14355497826584746197603329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38281327537559323193608877 14355497826584746197603329)
        ·
          refine ⟨10766623369938559648202497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14355497826584746197603329 10766623369938559648202497)
          ·
            refine ⟨8074967527453919736151873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10766623369938559648202497 8074967527453919736151873)
            ·
              refine ⟨6056225645590439802113905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8074967527453919736151873 6056225645590439802113905)
              ·
                refine ⟨4542169234192829851585429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6056225645590439802113905 4542169234192829851585429)
                ·
                  refine ⟨212914182852788899293067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4542169234192829851585429 212914182852788899293067)
                  ·
                    rfl

theorem cell21_932960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 6].length) (baseStart_932960 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_932960 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_932960 prefixEnd_932960 := by exact prefixLift 932960
  have htrace : WordTrace (prefixWord ++ tailWord_932960) baseStart_932960 baseEnd_932960 := by
    simpa [prefixWord, tailWord_932960, baseEnd_932960] using wordTrace_append hprefix tailTrace_932960
  have hstable : (prefixWord ++ tailWord_932960).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932960).length < 2 ^ (prefixWord ++ tailWord_932960).sum := by decide
  have hdescent : baseEnd_932960 < baseStart_932960 := by decide
  rcases family_descends (prefixWord ++ tailWord_932960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933146 : List Nat := [3, 1, 1, 3, 3, 3, 1, 2, 4]
def baseStart_933146 : Nat := 118140960795 + 933146 * 2 ^ 59
def prefixEnd_933146 : Nat := 4983230072969 + 3 ^ 40 * 933146 * 2
def baseEnd_933146 : Nat := 212956630586893909192687

theorem tailTrace_933146 : CollatzResearch.WordTrace tailWord_933146 prefixEnd_933146 212956630586893909192687 := by
  unfold tailWord_933146
  simp only [CollatzResearch.WordTrace]
  refine ⟨8508657669344721373480823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22689753784919256995948861 8508657669344721373480823)
  ·
    refine ⟨12762986504017082060221235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8508657669344721373480823 12762986504017082060221235)
    ·
      refine ⟨19144479756025623090331853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12762986504017082060221235 19144479756025623090331853)
      ·
        refine ⟨7179179908509608658874445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19144479756025623090331853 7179179908509608658874445)
        ·
          refine ⟨2692192465691103247077917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7179179908509608658874445 2692192465691103247077917)
          ·
            refine ⟨1009572174634163717654219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2692192465691103247077917 1009572174634163717654219)
            ·
              refine ⟨1514358261951245576481329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1009572174634163717654219 1514358261951245576481329)
              ·
                refine ⟨1135768696463434182360997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1514358261951245576481329 1135768696463434182360997)
                ·
                  refine ⟨212956630586893909192687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1135768696463434182360997 212956630586893909192687)
                  ·
                    rfl

theorem cell21_933146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 2, 4].length) (baseStart_933146 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_933146 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_933146 prefixEnd_933146 := by exact prefixLift 933146
  have htrace : WordTrace (prefixWord ++ tailWord_933146) baseStart_933146 baseEnd_933146 := by
    simpa [prefixWord, tailWord_933146, baseEnd_933146] using wordTrace_append hprefix tailTrace_933146
  have hstable : (prefixWord ++ tailWord_933146).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933146).length < 2 ^ (prefixWord ++ tailWord_933146).sum := by decide
  have hdescent : baseEnd_933146 < baseStart_933146 := by decide
  rcases family_descends (prefixWord ++ tailWord_933146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933177 : List Nat := [1, 2, 1, 6, 2, 2, 2, 5]
def baseStart_933177 : Nat := 118140960795 + 933177 * 2 ^ 59
def prefixEnd_933177 : Nat := 4983230072969 + 3 ^ 40 * 933177 * 2
def baseEnd_933177 : Nat := 70987901736414914725319

theorem tailTrace_933177 : CollatzResearch.WordTrace tailWord_933177 prefixEnd_933177 70987901736414914725319 := by
  unfold tailWord_933177
  simp only [CollatzResearch.WordTrace]
  refine ⟨34035761340266577788301785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22690507560177718525534523 34035761340266577788301785)
  ·
    refine ⟨25526821005199933341226339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34035761340266577788301785 25526821005199933341226339)
    ·
      refine ⟨38290231507799900011839509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25526821005199933341226339 38290231507799900011839509)
      ·
        refine ⟨1794854601928120313054977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 38290231507799900011839509 1794854601928120313054977)
        ·
          refine ⟨1346140951446090234791233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1794854601928120313054977 1346140951446090234791233)
          ·
            refine ⟨1009605713584567676093425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1346140951446090234791233 1009605713584567676093425)
            ·
              refine ⟨757204285188425757070069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1009605713584567676093425 757204285188425757070069)
              ·
                refine ⟨70987901736414914725319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 757204285188425757070069 70987901736414914725319)
                ·
                  rfl

theorem cell21_933177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 2, 5].length) (baseStart_933177 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_933177 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_933177 prefixEnd_933177 := by exact prefixLift 933177
  have htrace : WordTrace (prefixWord ++ tailWord_933177) baseStart_933177 baseEnd_933177 := by
    simpa [prefixWord, tailWord_933177, baseEnd_933177] using wordTrace_append hprefix tailTrace_933177
  have hstable : (prefixWord ++ tailWord_933177).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933177).length < 2 ^ (prefixWord ++ tailWord_933177).sum := by decide
  have hdescent : baseEnd_933177 < baseStart_933177 := by decide
  rcases family_descends (prefixWord ++ tailWord_933177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933191 : List Nat := [1, 1, 4, 1, 2, 3, 3, 3, 3]
def baseStart_933191 : Nat := 118140960795 + 933191 * 2 ^ 59
def prefixEnd_933191 : Nat := 4983230072969 + 3 ^ 40 * 933191 * 2
def baseEnd_933191 : Nat := 212966900199983830942595

theorem tailTrace_933191 : CollatzResearch.WordTrace tailWord_933191 prefixEnd_933191 212966900199983830942595 := by
  unfold tailWord_933191
  simp only [CollatzResearch.WordTrace]
  refine ⟨34036271962215858179311427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22690847974810572119540951 34036271962215858179311427)
  ·
    refine ⟨51054407943323787268967141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34036271962215858179311427 51054407943323787268967141)
    ·
      refine ⟨9572701489373210112931339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51054407943323787268967141 9572701489373210112931339)
      ·
        refine ⟨14359052234059815169397009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9572701489373210112931339 14359052234059815169397009)
        ·
          refine ⟨10769289175544861377047757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14359052234059815169397009 10769289175544861377047757)
          ·
            refine ⟨4038483440829323016392909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10769289175544861377047757 4038483440829323016392909)
            ·
              refine ⟨1514431290310996131147341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4038483440829323016392909 1514431290310996131147341)
              ·
                refine ⟨567911733866623549180253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1514431290310996131147341 567911733866623549180253)
                ·
                  refine ⟨212966900199983830942595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 567911733866623549180253 212966900199983830942595)
                  ·
                    rfl

theorem cell21_933191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 3, 3].length) (baseStart_933191 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_933191 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_933191 prefixEnd_933191 := by exact prefixLift 933191
  have htrace : WordTrace (prefixWord ++ tailWord_933191) baseStart_933191 baseEnd_933191 := by
    simpa [prefixWord, tailWord_933191, baseEnd_933191] using wordTrace_append hprefix tailTrace_933191
  have hstable : (prefixWord ++ tailWord_933191).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933191).length < 2 ^ (prefixWord ++ tailWord_933191).sum := by decide
  have hdescent : baseEnd_933191 < baseStart_933191 := by decide
  rcases family_descends (prefixWord ++ tailWord_933191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933219 : List Nat := [1, 1, 1, 5, 2, 3, 2, 6]
def baseStart_933219 : Nat := 118140960795 + 933219 * 2 ^ 59
def prefixEnd_933219 : Nat := 4983230072969 + 3 ^ 40 * 933219 * 2
def baseEnd_933219 : Nat := 70991096727154001491957

theorem tailTrace_933219 : CollatzResearch.WordTrace tailWord_933219 prefixEnd_933219 70991096727154001491957 := by
  unfold tailWord_933219
  simp only [CollatzResearch.WordTrace]
  refine ⟨34037293206114418961330711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22691528804076279307553807 34037293206114418961330711)
  ·
    refine ⟨51055939809171628441996067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34037293206114418961330711 51055939809171628441996067)
    ·
      refine ⟨76583909713757442662994101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51055939809171628441996067 76583909713757442662994101)
      ·
        refine ⟨7179741535664760249655697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76583909713757442662994101 7179741535664760249655697)
        ·
          refine ⟨5384806151748570187241773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7179741535664760249655697 5384806151748570187241773)
          ·
            refine ⟨2019302306905713820215665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5384806151748570187241773 2019302306905713820215665)
            ·
              refine ⟨1514476730179285365161749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2019302306905713820215665 1514476730179285365161749)
              ·
                refine ⟨70991096727154001491957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1514476730179285365161749 70991096727154001491957)
                ·
                  rfl

theorem cell21_933219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 6].length) (baseStart_933219 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_933219 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_933219 prefixEnd_933219 := by exact prefixLift 933219
  have htrace : WordTrace (prefixWord ++ tailWord_933219) baseStart_933219 baseEnd_933219 := by
    simpa [prefixWord, tailWord_933219, baseEnd_933219] using wordTrace_append hprefix tailTrace_933219
  have hstable : (prefixWord ++ tailWord_933219).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933219).length < 2 ^ (prefixWord ++ tailWord_933219).sum := by decide
  have hdescent : baseEnd_933219 < baseStart_933219 := by decide
  rcases family_descends (prefixWord ++ tailWord_933219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933233 : List Nat := [1, 2, 2, 2, 1, 2, 2, 4, 5]
def baseStart_933233 : Nat := 118140960795 + 933233 * 2 ^ 59
def prefixEnd_933233 : Nat := 4983230072969 + 3 ^ 40 * 933233 * 2
def baseEnd_933233 : Nat := 212976485172201091242509

theorem tailTrace_933233 : CollatzResearch.WordTrace tailWord_933233 prefixEnd_933233 212976485172201091242509 := by
  unfold tailWord_933233
  simp only [CollatzResearch.WordTrace]
  refine ⟨34037803828063699352340353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22691869218709132901560235 34037803828063699352340353)
  ·
    refine ⟨25528352871047774514255265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34037803828063699352340353 25528352871047774514255265)
    ·
      refine ⟨19146264653285830885691449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25528352871047774514255265 19146264653285830885691449)
      ·
        refine ⟨14359698489964373164268587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19146264653285830885691449 14359698489964373164268587)
        ·
          refine ⟨21539547734946559746402881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14359698489964373164268587 21539547734946559746402881)
          ·
            refine ⟨16154660801209919809802161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21539547734946559746402881 16154660801209919809802161)
            ·
              refine ⟨12115995600907439857351621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16154660801209919809802161 12115995600907439857351621)
              ·
                refine ⟨2271749175170144973253429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12115995600907439857351621 2271749175170144973253429)
                ·
                  refine ⟨212976485172201091242509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2271749175170144973253429 212976485172201091242509)
                  ·
                    rfl

theorem cell21_933233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 4, 5].length) (baseStart_933233 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_933233 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_933233 prefixEnd_933233 := by exact prefixLift 933233
  have htrace : WordTrace (prefixWord ++ tailWord_933233) baseStart_933233 baseEnd_933233 := by
    simpa [prefixWord, tailWord_933233, baseEnd_933233] using wordTrace_append hprefix tailTrace_933233
  have hstable : (prefixWord ++ tailWord_933233).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933233).length < 2 ^ (prefixWord ++ tailWord_933233).sum := by decide
  have hdescent : baseEnd_933233 < baseStart_933233 := by decide
  rcases family_descends (prefixWord ++ tailWord_933233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933309 : List Nat := [1, 4, 1, 2, 2, 1, 1, 2, 7]
def baseStart_933309 : Nat := 118140960795 + 933309 * 2 ^ 59
def prefixEnd_933309 : Nat := 4983230072969 + 3 ^ 40 * 933309 * 2
def baseEnd_933309 : Nat := 212993829407641847975687

theorem tailTrace_933309 : CollatzResearch.WordTrace tailWord_933309 prefixEnd_933309 212993829407641847975687 := by
  unfold tailWord_933309
  simp only [CollatzResearch.WordTrace]
  refine ⟨34040575775788364332106981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22693717183858909554737987 34040575775788364332106981)
  ·
    refine ⟨6382607957960318312270059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34040575775788364332106981 6382607957960318312270059)
    ·
      refine ⟨9573911936940477468405089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6382607957960318312270059 9573911936940477468405089)
      ·
        refine ⟨7180433952705358101303817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9573911936940477468405089 7180433952705358101303817)
        ·
          refine ⟨5385325464529018575977863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7180433952705358101303817 5385325464529018575977863)
          ·
            refine ⟨8077988196793527863966795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5385325464529018575977863 8077988196793527863966795)
            ·
              refine ⟨12116982295190291795950193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8077988196793527863966795 12116982295190291795950193)
              ·
                refine ⟨9087736721392718846962645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12116982295190291795950193 9087736721392718846962645)
                ·
                  refine ⟨212993829407641847975687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9087736721392718846962645 212993829407641847975687)
                  ·
                    rfl

theorem cell21_933309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_933309 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_933309 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_933309 prefixEnd_933309 := by exact prefixLift 933309
  have htrace : WordTrace (prefixWord ++ tailWord_933309) baseStart_933309 baseEnd_933309 := by
    simpa [prefixWord, tailWord_933309, baseEnd_933309] using wordTrace_append hprefix tailTrace_933309
  have hstable : (prefixWord ++ tailWord_933309).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933309).length < 2 ^ (prefixWord ++ tailWord_933309).sum := by decide
  have hdescent : baseEnd_933309 < baseStart_933309 := by decide
  rcases family_descends (prefixWord ++ tailWord_933309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933433 : List Nat := [1, 2, 1, 5, 1, 3, 2, 2, 4]
def baseStart_933433 : Nat := 118140960795 + 933433 * 2 ^ 59
def prefixEnd_933433 : Nat := 4983230072969 + 3 ^ 40 * 933433 * 2
def baseEnd_933433 : Nat := 213022127897045187908767

theorem tailTrace_933433 : CollatzResearch.WordTrace tailWord_933433 prefixEnd_933433 213022127897045187908767 := by
  unfold tailWord_933433
  simp only [CollatzResearch.WordTrace]
  refine ⟨34045098427339133509620953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22696732284892755673080635 34045098427339133509620953)
  ·
    refine ⟨25533823820504350132215715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34045098427339133509620953 25533823820504350132215715)
    ·
      refine ⟨38300735730756525198323573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25533823820504350132215715 38300735730756525198323573)
      ·
        refine ⟨3590693974758424237342835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38300735730756525198323573 3590693974758424237342835)
        ·
          refine ⟨5386040962137636356014253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3590693974758424237342835 5386040962137636356014253)
          ·
            refine ⟨2019765360801613633505345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5386040962137636356014253 2019765360801613633505345)
            ·
              refine ⟨1514824020601210225129009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2019765360801613633505345 1514824020601210225129009)
              ·
                refine ⟨1136118015450907668846757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1514824020601210225129009 1136118015450907668846757)
                ·
                  refine ⟨213022127897045187908767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1136118015450907668846757 213022127897045187908767)
                  ·
                    rfl

theorem cell21_933433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 2, 4].length) (baseStart_933433 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_933433 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_933433 prefixEnd_933433 := by exact prefixLift 933433
  have htrace : WordTrace (prefixWord ++ tailWord_933433) baseStart_933433 baseEnd_933433 := by
    simpa [prefixWord, tailWord_933433, baseEnd_933433] using wordTrace_append hprefix tailTrace_933433
  have hstable : (prefixWord ++ tailWord_933433).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933433).length < 2 ^ (prefixWord ++ tailWord_933433).sum := by decide
  have hdescent : baseEnd_933433 < baseStart_933433 := by decide
  rcases family_descends (prefixWord ++ tailWord_933433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933509 : List Nat := [1, 3, 1, 1, 4, 1, 5, 1, 4]
def baseStart_933509 : Nat := 118140960795 + 933509 * 2 ^ 59
def prefixEnd_933509 : Nat := 4983230072969 + 3 ^ 40 * 933509 * 2
def baseEnd_933509 : Nat := 213039472132485944641945

theorem tailTrace_933509 : CollatzResearch.WordTrace tailWord_933509 prefixEnd_933509 213039472132485944641945 := by
  unfold tailWord_933509
  simp only [CollatzResearch.WordTrace]
  refine ⟨34047870375063798489387581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22698580250042532326258387 34047870375063798489387581)
  ·
    refine ⟨12767951390648924433520343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34047870375063798489387581 12767951390648924433520343)
    ·
      refine ⟨19151927085973386650280515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12767951390648924433520343 19151927085973386650280515)
      ·
        refine ⟨28727890628960079975420773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19151927085973386650280515 28727890628960079975420773)
        ·
          refine ⟨5386479492930014995391395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28727890628960079975420773 5386479492930014995391395)
          ·
            refine ⟨8079719239395022493087093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5386479492930014995391395 8079719239395022493087093)
            ·
              refine ⟨757473678693283358726915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8079719239395022493087093 757473678693283358726915)
              ·
                refine ⟨1136210518039925038090373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 757473678693283358726915 1136210518039925038090373)
                ·
                  refine ⟨213039472132485944641945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1136210518039925038090373 213039472132485944641945)
                  ·
                    rfl

theorem cell21_933509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 5, 1, 4].length) (baseStart_933509 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_933509 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_933509 prefixEnd_933509 := by exact prefixLift 933509
  have htrace : WordTrace (prefixWord ++ tailWord_933509) baseStart_933509 baseEnd_933509 := by
    simpa [prefixWord, tailWord_933509, baseEnd_933509] using wordTrace_append hprefix tailTrace_933509
  have hstable : (prefixWord ++ tailWord_933509).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933509).length < 2 ^ (prefixWord ++ tailWord_933509).sum := by decide
  have hdescent : baseEnd_933509 < baseStart_933509 := by decide
  rcases family_descends (prefixWord ++ tailWord_933509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933551 : List Nat := [1, 1, 2, 1, 2, 4, 1, 3, 6]
def baseStart_933551 : Nat := 118140960795 + 933551 * 2 ^ 59
def prefixEnd_933551 : Nat := 4983230072969 + 3 ^ 40 * 933551 * 2
def baseEnd_933551 : Nat := 213049057104703204941859

theorem tailTrace_933551 : CollatzResearch.WordTrace tailWord_933551 prefixEnd_933551 213049057104703204941859 := by
  unfold tailWord_933551
  simp only [CollatzResearch.WordTrace]
  refine ⟨34049402240911639662416507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22699601493941093108277671 34049402240911639662416507)
  ·
    refine ⟨51074103361367459493624761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34049402240911639662416507 51074103361367459493624761)
    ·
      refine ⟨38305577521025594620218571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51074103361367459493624761 38305577521025594620218571)
      ·
        refine ⟨57458366281538391930327857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38305577521025594620218571 57458366281538391930327857)
        ·
          refine ⟨43093774711153793947745893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57458366281538391930327857 43093774711153793947745893)
          ·
            refine ⟨8080082758341336365202355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43093774711153793947745893 8080082758341336365202355)
            ·
              refine ⟨12120124137512004547803533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8080082758341336365202355 12120124137512004547803533)
              ·
                refine ⟨4545046551567001705426325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12120124137512004547803533 4545046551567001705426325)
                ·
                  refine ⟨213049057104703204941859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4545046551567001705426325 213049057104703204941859)
                  ·
                    rfl

theorem cell21_933551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 6].length) (baseStart_933551 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_933551 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_933551 prefixEnd_933551 := by exact prefixLift 933551
  have htrace : WordTrace (prefixWord ++ tailWord_933551) baseStart_933551 baseEnd_933551 := by
    simpa [prefixWord, tailWord_933551, baseEnd_933551] using wordTrace_append hprefix tailTrace_933551
  have hstable : (prefixWord ++ tailWord_933551).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933551).length < 2 ^ (prefixWord ++ tailWord_933551).sum := by decide
  have hdescent : baseEnd_933551 < baseStart_933551 := by decide
  rcases family_descends (prefixWord ++ tailWord_933551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933554 : List Nat := [3, 2, 1, 1, 1, 2, 2, 6, 3]
def baseStart_933554 : Nat := 118140960795 + 933554 * 2 ^ 59
def prefixEnd_933554 : Nat := 4983230072969 + 3 ^ 40 * 933554 * 2
def baseEnd_933554 : Nat := 213049741745575866391853

theorem tailTrace_933554 : CollatzResearch.WordTrace tailWord_933554 prefixEnd_933554 213049741745575866391853 := by
  unfold tailWord_933554
  simp only [CollatzResearch.WordTrace]
  refine ⟨8512377914975192793693929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22699674439933847449850477 8512377914975192793693929)
  ·
    refine ⟨6384283436231394595270447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8512377914975192793693929 6384283436231394595270447)
    ·
      refine ⟨9576425154347091892905671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6384283436231394595270447 9576425154347091892905671)
      ·
        refine ⟨14364637731520637839358507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9576425154347091892905671 14364637731520637839358507)
        ·
          refine ⟨21546956597280956759037761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14364637731520637839358507 21546956597280956759037761)
          ·
            refine ⟨16160217447960717569278321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21546956597280956759037761 16160217447960717569278321)
            ·
              refine ⟨12120163085970538176958741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16160217447960717569278321 12120163085970538176958741)
              ·
                refine ⟨568132644654868977044941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12120163085970538176958741 568132644654868977044941)
                ·
                  refine ⟨213049741745575866391853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 568132644654868977044941 213049741745575866391853)
                  ·
                    rfl

theorem cell21_933554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 6, 3].length) (baseStart_933554 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_933554 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_933554 prefixEnd_933554 := by exact prefixLift 933554
  have htrace : WordTrace (prefixWord ++ tailWord_933554) baseStart_933554 baseEnd_933554 := by
    simpa [prefixWord, tailWord_933554, baseEnd_933554] using wordTrace_append hprefix tailTrace_933554
  have hstable : (prefixWord ++ tailWord_933554).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933554).length < 2 ^ (prefixWord ++ tailWord_933554).sum := by decide
  have hdescent : baseEnd_933554 < baseStart_933554 := by decide
  rcases family_descends (prefixWord ++ tailWord_933554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933568 : List Nat := [2, 1, 1, 2, 4, 1, 3, 3, 4]
def baseStart_933568 : Nat := 118140960795 + 933568 * 2 ^ 59
def prefixEnd_933568 : Nat := 4983230072969 + 3 ^ 40 * 933568 * 2
def baseEnd_933568 : Nat := 213052936736314953158491

theorem tailTrace_933568 : CollatzResearch.WordTrace tailWord_933568 prefixEnd_933568 213052936736314953158491 := by
  unfold tailWord_933568
  simp only [CollatzResearch.WordTrace]
  refine ⟨17025011140925025782892679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22700014854566701043856905 17025011140925025782892679)
  ·
    refine ⟨25537516711387538674339019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17025011140925025782892679 25537516711387538674339019)
    ·
      refine ⟨38306275067081308011508529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25537516711387538674339019 38306275067081308011508529)
      ·
        refine ⟨28729706300310981008631397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38306275067081308011508529 28729706300310981008631397)
        ·
          refine ⟨5386819931308308939118387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28729706300310981008631397 5386819931308308939118387)
          ·
            refine ⟨8080229896962463408677581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5386819931308308939118387 8080229896962463408677581)
            ·
              refine ⟨3030086211360923778254093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8080229896962463408677581 3030086211360923778254093)
              ·
                refine ⟨1136282329260346416845285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3030086211360923778254093 1136282329260346416845285)
                ·
                  refine ⟨213052936736314953158491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1136282329260346416845285 213052936736314953158491)
                  ·
                    rfl

theorem cell21_933568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 3, 4].length) (baseStart_933568 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_933568 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_933568 prefixEnd_933568 := by exact prefixLift 933568
  have htrace : WordTrace (prefixWord ++ tailWord_933568) baseStart_933568 baseEnd_933568 := by
    simpa [prefixWord, tailWord_933568, baseEnd_933568] using wordTrace_append hprefix tailTrace_933568
  have hstable : (prefixWord ++ tailWord_933568).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933568).length < 2 ^ (prefixWord ++ tailWord_933568).sum := by decide
  have hdescent : baseEnd_933568 < baseStart_933568 := by decide
  rcases family_descends (prefixWord ++ tailWord_933568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933582 : List Nat := [4, 1, 1, 1, 3, 1, 1, 9]
def baseStart_933582 : Nat := 118140960795 + 933582 * 2 ^ 59
def prefixEnd_933582 : Nat := 4983230072969 + 3 ^ 40 * 933582 * 2
def baseEnd_933582 : Nat := 71018710575684679975043

theorem tailTrace_933582 : CollatzResearch.WordTrace tailWord_933582 prefixEnd_933582 71018710575684679975043 := by
  unfold tailWord_933582
  simp only [CollatzResearch.WordTrace]
  refine ⟨4256316612974916494599375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22700355269199554637863333 4256316612974916494599375)
  ·
    refine ⟨6384474919462374741899063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4256316612974916494599375 6384474919462374741899063)
    ·
      refine ⟨9576712379193562112848595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6384474919462374741899063 9576712379193562112848595)
      ·
        refine ⟨14365068568790343169272893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9576712379193562112848595 14365068568790343169272893)
        ·
          refine ⟨5386900713296378688477335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14365068568790343169272893 5386900713296378688477335)
          ·
            refine ⟨8080351069944568032716003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5386900713296378688477335 8080351069944568032716003)
            ·
              refine ⟨12120526604916852049074005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8080351069944568032716003 12120526604916852049074005)
              ·
                refine ⟨71018710575684679975043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12120526604916852049074005 71018710575684679975043)
                ·
                  rfl

theorem cell21_933582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 9].length) (baseStart_933582 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_933582 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_933582 prefixEnd_933582 := by exact prefixLift 933582
  have htrace : WordTrace (prefixWord ++ tailWord_933582) baseStart_933582 baseEnd_933582 := by
    simpa [prefixWord, tailWord_933582, baseEnd_933582] using wordTrace_append hprefix tailTrace_933582
  have hstable : (prefixWord ++ tailWord_933582).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933582).length < 2 ^ (prefixWord ++ tailWord_933582).sum := by decide
  have hdescent : baseEnd_933582 < baseStart_933582 := by decide
  rcases family_descends (prefixWord ++ tailWord_933582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933658 : List Nat := [3, 1, 1, 3, 2, 3, 8]
def baseStart_933658 : Nat := 118140960795 + 933658 * 2 ^ 59
def prefixEnd_933658 : Nat := 4983230072969 + 3 ^ 40 * 933658 * 2
def baseEnd_933658 : Nat := 23674830662499421850923

theorem tailTrace_933658 : CollatzResearch.WordTrace tailWord_933658 prefixEnd_933658 23674830662499421850923 := by
  unfold tailWord_933658
  simp only [CollatzResearch.WordTrace]
  refine ⟨8513326212880999234140407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22702203234349331291041085 8513326212880999234140407)
  ·
    refine ⟨12769989319321498851210611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8513326212880999234140407 12769989319321498851210611)
    ·
      refine ⟨19154983978982248276815917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12769989319321498851210611 19154983978982248276815917)
      ·
        refine ⟨7183118992118343103805969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19154983978982248276815917 7183118992118343103805969)
        ·
          refine ⟨5387339244088757327854477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7183118992118343103805969 5387339244088757327854477)
          ·
            refine ⟨2020252216533283997945429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5387339244088757327854477 2020252216533283997945429)
            ·
              refine ⟨23674830662499421850923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2020252216533283997945429 23674830662499421850923)
              ·
                rfl

theorem cell21_933658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 8].length) (baseStart_933658 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_933658 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_933658 prefixEnd_933658 := by exact prefixLift 933658
  have htrace : WordTrace (prefixWord ++ tailWord_933658) baseStart_933658 baseEnd_933658 := by
    simpa [prefixWord, tailWord_933658, baseEnd_933658] using wordTrace_append hprefix tailTrace_933658
  have hstable : (prefixWord ++ tailWord_933658).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933658).length < 2 ^ (prefixWord ++ tailWord_933658).sum := by decide
  have hdescent : baseEnd_933658 < baseStart_933658 := by decide
  rcases family_descends (prefixWord ++ tailWord_933658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933703 : List Nat := [1, 1, 4, 1, 2, 1, 3, 2, 6]
def baseStart_933703 : Nat := 118140960795 + 933703 * 2 ^ 59
def prefixEnd_933703 : Nat := 4983230072969 + 3 ^ 40 * 933703 * 2
def baseEnd_933703 : Nat := 213083745575584718408215

theorem tailTrace_933703 : CollatzResearch.WordTrace tailWord_933703 prefixEnd_933703 213083745575584718408215 := by
  unfold tailWord_933703
  simp only [CollatzResearch.WordTrace]
  refine ⟨34054946136360969621949763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22703297424240646414633175 34054946136360969621949763)
  ·
    refine ⟨51082419204541454432924645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34054946136360969621949763 51082419204541454432924645)
    ·
      refine ⟨9577953600851522706173371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51082419204541454432924645 9577953600851522706173371)
      ·
        refine ⟨14366930401277284059260057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9577953600851522706173371 14366930401277284059260057)
        ·
          refine ⟨10775197800957963044445043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14366930401277284059260057 10775197800957963044445043)
          ·
            refine ⟨16162796701436944566667565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10775197800957963044445043 16162796701436944566667565)
            ·
              refine ⟨6061048763038854212500337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16162796701436944566667565 6061048763038854212500337)
              ·
                refine ⟨4545786572279140659375253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6061048763038854212500337 4545786572279140659375253)
                ·
                  refine ⟨213083745575584718408215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4545786572279140659375253 213083745575584718408215)
                  ·
                    rfl

theorem cell21_933703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 6].length) (baseStart_933703 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_933703 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_933703 prefixEnd_933703 := by exact prefixLift 933703
  have htrace : WordTrace (prefixWord ++ tailWord_933703) baseStart_933703 baseEnd_933703 := by
    simpa [prefixWord, tailWord_933703, baseEnd_933703] using wordTrace_append hprefix tailTrace_933703
  have hstable : (prefixWord ++ tailWord_933703).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933703).length < 2 ^ (prefixWord ++ tailWord_933703).sum := by decide
  have hdescent : baseEnd_933703 < baseStart_933703 := by decide
  rcases family_descends (prefixWord ++ tailWord_933703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933774 : List Nat := [4, 1, 1, 5, 2, 1, 2, 2, 3]
def baseStart_933774 : Nat := 118140960795 + 933774 * 2 ^ 59
def prefixEnd_933774 : Nat := 4983230072969 + 3 ^ 40 * 933774 * 2
def baseEnd_933774 : Nat := 213099948742904372724737

theorem tailTrace_933774 : CollatzResearch.WordTrace tailWord_933774 prefixEnd_933774 213099948742904372724737 := by
  unfold tailWord_933774
  simp only [CollatzResearch.WordTrace]
  refine ⟨4257191964887968593473047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22705023812735832498522917 4257191964887968593473047)
  ·
    refine ⟨6385787947331952890209571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4257191964887968593473047 6385787947331952890209571)
    ·
      refine ⟨9578681920997929335314357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6385787947331952890209571 9578681920997929335314357)
      ·
        refine ⟨898001430093555875185721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9578681920997929335314357 898001430093555875185721)
        ·
          refine ⟨673501072570166906389291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 898001430093555875185721 673501072570166906389291)
          ·
            refine ⟨1010251608855250359583937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 673501072570166906389291 1010251608855250359583937)
            ·
              refine ⟨757688706641437769687953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1010251608855250359583937 757688706641437769687953)
              ·
                refine ⟨568266529981078327265965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 757688706641437769687953 568266529981078327265965)
                ·
                  refine ⟨213099948742904372724737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 568266529981078327265965 213099948742904372724737)
                  ·
                    rfl

theorem cell21_933774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 2, 2, 3].length) (baseStart_933774 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_933774 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_933774 prefixEnd_933774 := by exact prefixLift 933774
  have htrace : WordTrace (prefixWord ++ tailWord_933774) baseStart_933774 baseEnd_933774 := by
    simpa [prefixWord, tailWord_933774, baseEnd_933774] using wordTrace_append hprefix tailTrace_933774
  have hstable : (prefixWord ++ tailWord_933774).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933774).length < 2 ^ (prefixWord ++ tailWord_933774).sum := by decide
  have hdescent : baseEnd_933774 < baseStart_933774 := by decide
  rcases family_descends (prefixWord ++ tailWord_933774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933796 : List Nat := [2, 3, 1, 2, 1, 3, 2, 3, 4]
def baseStart_933796 : Nat := 118140960795 + 933796 * 2 ^ 59
def prefixEnd_933796 : Nat := 4983230072969 + 3 ^ 40 * 933796 * 2
def baseEnd_933796 : Nat := 213104969442637223358025

theorem tailTrace_933796 : CollatzResearch.WordTrace tailWord_933796 prefixEnd_933796 213104969442637223358025 := by
  unfold tailWord_933796
  simp only [CollatzResearch.WordTrace]
  refine ⟨17029169062512023252542621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22705558750016031003390161 17029169062512023252542621)
  ·
    refine ⟨6385938398442008719703483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17029169062512023252542621 6385938398442008719703483)
    ·
      refine ⟨9578907597663013079555225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6385938398442008719703483 9578907597663013079555225)
      ·
        refine ⟨7184180698247259809666419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9578907597663013079555225 7184180698247259809666419)
        ·
          refine ⟨10776271047370889714499629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7184180698247259809666419 10776271047370889714499629)
          ·
            refine ⟨4041101642764083642937361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10776271047370889714499629 4041101642764083642937361)
            ·
              refine ⟨3030826232073062732203021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4041101642764083642937361 3030826232073062732203021)
              ·
                refine ⟨1136559837027398524576133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3030826232073062732203021 1136559837027398524576133)
                ·
                  refine ⟨213104969442637223358025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1136559837027398524576133 213104969442637223358025)
                  ·
                    rfl

theorem cell21_933796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 3, 4].length) (baseStart_933796 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_933796 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_933796 prefixEnd_933796 := by exact prefixLift 933796
  have htrace : WordTrace (prefixWord ++ tailWord_933796) baseStart_933796 baseEnd_933796 := by
    simpa [prefixWord, tailWord_933796, baseEnd_933796] using wordTrace_append hprefix tailTrace_933796
  have hstable : (prefixWord ++ tailWord_933796).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933796).length < 2 ^ (prefixWord ++ tailWord_933796).sum := by decide
  have hdescent : baseEnd_933796 < baseStart_933796 := by decide
  rcases family_descends (prefixWord ++ tailWord_933796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933824 : List Nat := [2, 1, 1, 2, 3, 2, 1, 2, 7]
def baseStart_933824 : Nat := 118140960795 + 933824 * 2 ^ 59
def prefixEnd_933824 : Nat := 4983230072969 + 3 ^ 40 * 933824 * 2
def baseEnd_933824 : Nat := 213111359424115396891301

theorem tailTrace_933824 : CollatzResearch.WordTrace tailWord_933824 prefixEnd_933824 213111359424115396891301 := by
  unfold tailWord_933824
  simp only [CollatzResearch.WordTrace]
  refine ⟨17029679684461303643552263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22706239579281738191403017 17029679684461303643552263)
  ·
    refine ⟨25544519526691955465328395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17029679684461303643552263 25544519526691955465328395)
    ·
      refine ⟨38316779290037933197992593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25544519526691955465328395 38316779290037933197992593)
      ·
        refine ⟨28737584467528449898494445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38316779290037933197992593 28737584467528449898494445)
        ·
          refine ⟨10776594175323168711935417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28737584467528449898494445 10776594175323168711935417)
          ·
            refine ⟨8082445631492376533951563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10776594175323168711935417 8082445631492376533951563)
            ·
              refine ⟨12123668447238564800927345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8082445631492376533951563 12123668447238564800927345)
              ·
                refine ⟨9092751335428923600695509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12123668447238564800927345 9092751335428923600695509)
                ·
                  refine ⟨213111359424115396891301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9092751335428923600695509 213111359424115396891301)
                  ·
                    rfl

theorem cell21_933824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 7].length) (baseStart_933824 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_933824 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_933824 prefixEnd_933824 := by exact prefixLift 933824
  have htrace : WordTrace (prefixWord ++ tailWord_933824) baseStart_933824 baseEnd_933824 := by
    simpa [prefixWord, tailWord_933824, baseEnd_933824] using wordTrace_append hprefix tailTrace_933824
  have hstable : (prefixWord ++ tailWord_933824).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933824).length < 2 ^ (prefixWord ++ tailWord_933824).sum := by decide
  have hdescent : baseEnd_933824 < baseStart_933824 := by decide
  rcases family_descends (prefixWord ++ tailWord_933824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933892 : List Nat := [2, 3, 2, 4, 2, 1, 1, 1, 5]
def baseStart_933892 : Nat := 118140960795 + 933892 * 2 ^ 59
def prefixEnd_933892 : Nat := 4983230072969 + 3 ^ 40 * 933892 * 2
def baseEnd_933892 : Nat := 213126877950562389757829

theorem tailTrace_933892 : CollatzResearch.WordTrace tailWord_933892 prefixEnd_933892 213126877950562389757829 := by
  unfold tailWord_933892
  simp only [CollatzResearch.WordTrace]
  refine ⟨17030919766338127450289965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22707893021784169933719953 17030919766338127450289965)
  ·
    refine ⟨6386594912376797793858737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17030919766338127450289965 6386594912376797793858737)
    ·
      refine ⟨4789946184282598345394053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6386594912376797793858737 4789946184282598345394053)
      ·
        refine ⟨898114909552987189761385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4789946184282598345394053 898114909552987189761385)
        ·
          refine ⟨673586182164740392321039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 898114909552987189761385 673586182164740392321039)
          ·
            refine ⟨1010379273247110588481559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 673586182164740392321039 1010379273247110588481559)
            ·
              refine ⟨1515568909870665882722339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1010379273247110588481559 1515568909870665882722339)
              ·
                refine ⟨2273353364805998824083509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1515568909870665882722339 2273353364805998824083509)
                ·
                  refine ⟨213126877950562389757829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2273353364805998824083509 213126877950562389757829)
                  ·
                    rfl

theorem cell21_933892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 1, 5].length) (baseStart_933892 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_933892 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_933892 prefixEnd_933892 := by exact prefixLift 933892
  have htrace : WordTrace (prefixWord ++ tailWord_933892) baseStart_933892 baseEnd_933892 := by
    simpa [prefixWord, tailWord_933892, baseEnd_933892] using wordTrace_append hprefix tailTrace_933892
  have hstable : (prefixWord ++ tailWord_933892).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933892).length < 2 ^ (prefixWord ++ tailWord_933892).sum := by decide
  have hdescent : baseEnd_933892 < baseStart_933892 := by decide
  rcases family_descends (prefixWord ++ tailWord_933892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933945 : List Nat := [1, 2, 1, 5, 12]
def baseStart_933945 : Nat := 118140960795 + 933945 * 2 ^ 59
def prefixEnd_933945 : Nat := 4983230072969 + 3 ^ 40 * 933945 * 2
def baseEnd_933945 : Nat := 2631345349045013276227

theorem tailTrace_933945 : CollatzResearch.WordTrace tailWord_933945 prefixEnd_933945 2631345349045013276227 := by
  unfold tailWord_933945
  simp only [CollatzResearch.WordTrace]
  refine ⟨34063772601484244952259289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22709181734322829968172859 34063772601484244952259289)
  ·
    refine ⟨25547829451113183714194467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34063772601484244952259289 25547829451113183714194467)
    ·
      refine ⟨38321744176669775571291701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25547829451113183714194467 38321744176669775571291701)
      ·
        refine ⟨3592663516562791459808597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38321744176669775571291701 3592663516562791459808597)
        ·
          refine ⟨2631345349045013276227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 3592663516562791459808597 2631345349045013276227)
          ·
            rfl

theorem cell21_933945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 12].length) (baseStart_933945 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_933945 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_933945 prefixEnd_933945 := by exact prefixLift 933945
  have htrace : WordTrace (prefixWord ++ tailWord_933945) baseStart_933945 baseEnd_933945 := by
    simpa [prefixWord, tailWord_933945, baseEnd_933945] using wordTrace_append hprefix tailTrace_933945
  have hstable : (prefixWord ++ tailWord_933945).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933945).length < 2 ^ (prefixWord ++ tailWord_933945).sum := by decide
  have hdescent : baseEnd_933945 < baseStart_933945 := by decide
  rcases family_descends (prefixWord ++ tailWord_933945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933948 : List Nat := [2, 2, 2, 2, 2, 1, 4, 2, 4]
def baseStart_933948 : Nat := 118140960795 + 933948 * 2 ^ 59
def prefixEnd_933948 : Nat := 4983230072969 + 3 ^ 40 * 933948 * 2
def baseEnd_933948 : Nat := 213139657913518736824381

theorem tailTrace_933948 : CollatzResearch.WordTrace tailWord_933948 prefixEnd_933948 213139657913518736824381 := by
  unfold tailWord_933948
  simp only [CollatzResearch.WordTrace]
  refine ⟨17031941010236688232309249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22709254680315584309745665 17031941010236688232309249)
  ·
    refine ⟨12773955757677516174231937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17031941010236688232309249 12773955757677516174231937)
    ·
      refine ⟨9580466818258137130673953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12773955757677516174231937 9580466818258137130673953)
      ·
        refine ⟨7185350113693602848005465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9580466818258137130673953 7185350113693602848005465)
        ·
          refine ⟨5389012585270202136004099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7185350113693602848005465 5389012585270202136004099)
          ·
            refine ⟨8083518877905303204006149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5389012585270202136004099 8083518877905303204006149)
            ·
              refine ⟨1515659789607244350751153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8083518877905303204006149 1515659789607244350751153)
              ·
                refine ⟨1136744842205433263063365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1515659789607244350751153 1136744842205433263063365)
                ·
                  refine ⟨213139657913518736824381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1136744842205433263063365 213139657913518736824381)
                  ·
                    rfl

theorem cell21_933948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 2, 4].length) (baseStart_933948 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_933948 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_933948 prefixEnd_933948 := by exact prefixLift 933948
  have htrace : WordTrace (prefixWord ++ tailWord_933948) baseStart_933948 baseEnd_933948 := by
    simpa [prefixWord, tailWord_933948, baseEnd_933948] using wordTrace_append hprefix tailTrace_933948
  have hstable : (prefixWord ++ tailWord_933948).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933948).length < 2 ^ (prefixWord ++ tailWord_933948).sum := by decide
  have hdescent : baseEnd_933948 < baseStart_933948 := by decide
  rcases family_descends (prefixWord ++ tailWord_933948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_933976 : List Nat := [2, 1, 2, 2, 1, 4, 1, 1, 7]
def baseStart_933976 : Nat := 118140960795 + 933976 * 2 ^ 59
def prefixEnd_933976 : Nat := 4983230072969 + 3 ^ 40 * 933976 * 2
def baseEnd_933976 : Nat := 213146047894996910357657

theorem tailTrace_933976 : CollatzResearch.WordTrace tailWord_933976 prefixEnd_933976 213146047894996910357657 := by
  unfold tailWord_933976
  simp only [CollatzResearch.WordTrace]
  refine ⟨17032451632185968623318891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22709935509581291497758521 17032451632185968623318891)
  ·
    refine ⟨25548677448278952934978337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17032451632185968623318891 25548677448278952934978337)
    ·
      refine ⟨19161508086209214701233753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25548677448278952934978337 19161508086209214701233753)
      ·
        refine ⟨14371131064656911025925315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19161508086209214701233753 14371131064656911025925315)
        ·
          refine ⟨21556696596985366538887973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14371131064656911025925315 21556696596985366538887973)
          ·
            refine ⟨4041880611934756226041495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21556696596985366538887973 4041880611934756226041495)
            ·
              refine ⟨6062820917902134339062243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4041880611934756226041495 6062820917902134339062243)
              ·
                refine ⟨9094231376853201508593365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6062820917902134339062243 9094231376853201508593365)
                ·
                  refine ⟨213146047894996910357657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9094231376853201508593365 213146047894996910357657)
                  ·
                    rfl

theorem cell21_933976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 7].length) (baseStart_933976 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_933976 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_933976 prefixEnd_933976 := by exact prefixLift 933976
  have htrace : WordTrace (prefixWord ++ tailWord_933976) baseStart_933976 baseEnd_933976 := by
    simpa [prefixWord, tailWord_933976, baseEnd_933976] using wordTrace_append hprefix tailTrace_933976
  have hstable : (prefixWord ++ tailWord_933976).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_933976).length < 2 ^ (prefixWord ++ tailWord_933976).sum := by decide
  have hdescent : baseEnd_933976 < baseStart_933976 := by decide
  rcases family_descends (prefixWord ++ tailWord_933976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934007 : List Nat := [1, 1, 3, 1, 1, 6, 1, 1, 6]
def baseStart_934007 : Nat := 118140960795 + 934007 * 2 ^ 59
def prefixEnd_934007 : Nat := 4983230072969 + 3 ^ 40 * 934007 * 2
def baseEnd_934007 : Nat := 213153122517347745340927

theorem tailTrace_934007 : CollatzResearch.WordTrace tailWord_934007 prefixEnd_934007 213153122517347745340927 := by
  unfold tailWord_934007
  simp only [CollatzResearch.WordTrace]
  refine ⟨34066033927259629541016275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22710689284839753027344183 34066033927259629541016275)
  ·
    refine ⟨51099050890889444311524413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34066033927259629541016275 51099050890889444311524413)
    ·
      refine ⟨19162144084083541616821655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51099050890889444311524413 19162144084083541616821655)
      ·
        refine ⟨28743216126125312425232483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19162144084083541616821655 28743216126125312425232483)
        ·
          refine ⟨43114824189187968637848725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28743216126125312425232483 43114824189187968637848725)
          ·
            refine ⟨2021007383868186029899159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 43114824189187968637848725 2021007383868186029899159)
            ·
              refine ⟨3031511075802279044848739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2021007383868186029899159 3031511075802279044848739)
              ·
                refine ⟨4547266613703418567273109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3031511075802279044848739 4547266613703418567273109)
                ·
                  refine ⟨213153122517347745340927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4547266613703418567273109 213153122517347745340927)
                  ·
                    rfl

theorem cell21_934007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 6].length) (baseStart_934007 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_934007 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_934007 prefixEnd_934007 := by exact prefixLift 934007
  have htrace : WordTrace (prefixWord ++ tailWord_934007) baseStart_934007 baseEnd_934007 := by
    simpa [prefixWord, tailWord_934007, baseEnd_934007] using wordTrace_append hprefix tailTrace_934007
  have hstable : (prefixWord ++ tailWord_934007).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934007).length < 2 ^ (prefixWord ++ tailWord_934007).sum := by decide
  have hdescent : baseEnd_934007 < baseStart_934007 := by decide
  rcases family_descends (prefixWord ++ tailWord_934007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934055 : List Nat := [1, 1, 6, 2, 2, 2, 7]
def baseStart_934055 : Nat := 118140960795 + 934055 * 2 ^ 59
def prefixEnd_934055 : Nat := 4983230072969 + 3 ^ 40 * 934055 * 2
def baseEnd_934055 : Nat := 23684897419034480948981

theorem tailTrace_934055 : CollatzResearch.WordTrace tailWord_934055 prefixEnd_934055 23684897419034480948981 := by
  unfold tailWord_934055
  simp only [CollatzResearch.WordTrace]
  refine ⟨34067784631085733738763619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22711856420723822492509079 34067784631085733738763619)
  ·
    refine ⟨51101676946628600608145429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34067784631085733738763619 51101676946628600608145429)
    ·
      refine ⟨2395391106873215653506817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 51101676946628600608145429 2395391106873215653506817)
      ·
        refine ⟨1796543330154911740130113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2395391106873215653506817 1796543330154911740130113)
        ·
          refine ⟨1347407497616183805097585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1796543330154911740130113 1347407497616183805097585)
          ·
            refine ⟨1010555623212137853823189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1347407497616183805097585 1010555623212137853823189)
            ·
              refine ⟨23684897419034480948981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1010555623212137853823189 23684897419034480948981)
              ·
                rfl

theorem cell21_934055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 7].length) (baseStart_934055 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_934055 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_934055 prefixEnd_934055 := by exact prefixLift 934055
  have htrace : WordTrace (prefixWord ++ tailWord_934055) baseStart_934055 baseEnd_934055 := by
    simpa [prefixWord, tailWord_934055, baseEnd_934055] using wordTrace_append hprefix tailTrace_934055
  have hstable : (prefixWord ++ tailWord_934055).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934055).length < 2 ^ (prefixWord ++ tailWord_934055).sum := by decide
  have hdescent : baseEnd_934055 < baseStart_934055 := by decide
  rcases family_descends (prefixWord ++ tailWord_934055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934097 : List Nat := [1, 2, 2, 1, 2, 2, 4, 7]
def baseStart_934097 : Nat := 118140960795 + 934097 * 2 ^ 59
def prefixEnd_934097 : Nat := 4983230072969 + 3 ^ 40 * 934097 * 2
def baseEnd_934097 : Nat := 71057887247842529613581

theorem tailTrace_934097 : CollatzResearch.WordTrace tailWord_934097 prefixEnd_934097 71057887247842529613581 := by
  unfold tailWord_934097
  simp only [CollatzResearch.WordTrace]
  refine ⟨34069316496933574911792545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22712877664622383274528363 34069316496933574911792545)
  ·
    refine ⟨25551987372700181183844409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34069316496933574911792545 25551987372700181183844409)
    ·
      refine ⟨19163990529525135887883307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25551987372700181183844409 19163990529525135887883307)
      ·
        refine ⟨28745985794287703831824961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19163990529525135887883307 28745985794287703831824961)
        ·
          refine ⟨21559489345715777873868721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28745985794287703831824961 21559489345715777873868721)
          ·
            refine ⟨16169617009286833405401541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21559489345715777873868721 16169617009286833405401541)
            ·
              refine ⟨3031803189241281263512789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16169617009286833405401541 3031803189241281263512789)
              ·
                refine ⟨71057887247842529613581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3031803189241281263512789 71057887247842529613581)
                ·
                  rfl

theorem cell21_934097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 7].length) (baseStart_934097 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_934097 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_934097 prefixEnd_934097 := by exact prefixLift 934097
  have htrace : WordTrace (prefixWord ++ tailWord_934097) baseStart_934097 baseEnd_934097 := by
    simpa [prefixWord, tailWord_934097, baseEnd_934097] using wordTrace_append hprefix tailTrace_934097
  have hstable : (prefixWord ++ tailWord_934097).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934097).length < 2 ^ (prefixWord ++ tailWord_934097).sum := by decide
  have hdescent : baseEnd_934097 < baseStart_934097 := by decide
  rcases family_descends (prefixWord ++ tailWord_934097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934176 : List Nat := [2, 1, 1, 5, 2, 1, 3, 2, 4]
def baseStart_934176 : Nat := 118140960795 + 934176 * 2 ^ 59
def prefixEnd_934176 : Nat := 4983230072969 + 3 ^ 40 * 934176 * 2
def baseEnd_934176 : Nat := 213191690619841007023915

theorem tailTrace_934176 : CollatzResearch.WordTrace tailWord_934176 prefixEnd_934176 213191690619841007023915 := by
  unfold tailWord_934176
  simp only [CollatzResearch.WordTrace]
  refine ⟨17036098931823685701959191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22714798575764914269278921 17036098931823685701959191)
  ·
    refine ⟨25554148397735528552938787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17036098931823685701959191 25554148397735528552938787)
    ·
      refine ⟨38331222596603292829408181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25554148397735528552938787 38331222596603292829408181)
      ·
        refine ⟨3593552118431558702757017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38331222596603292829408181 3593552118431558702757017)
        ·
          refine ⟨2695164088823669027067763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3593552118431558702757017 2695164088823669027067763)
          ·
            refine ⟨4042746133235503540601645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2695164088823669027067763 4042746133235503540601645)
            ·
              refine ⟨1516029799963313827725617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4042746133235503540601645 1516029799963313827725617)
              ·
                refine ⟨1137022349972485370794213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1516029799963313827725617 1137022349972485370794213)
                ·
                  refine ⟨213191690619841007023915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1137022349972485370794213 213191690619841007023915)
                  ·
                    rfl

theorem cell21_934176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 2, 4].length) (baseStart_934176 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_934176 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_934176 prefixEnd_934176 := by exact prefixLift 934176
  have htrace : WordTrace (prefixWord ++ tailWord_934176) baseStart_934176 baseEnd_934176 := by
    simpa [prefixWord, tailWord_934176, baseEnd_934176] using wordTrace_append hprefix tailTrace_934176
  have hstable : (prefixWord ++ tailWord_934176).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934176).length < 2 ^ (prefixWord ++ tailWord_934176).sum := by decide
  have hdescent : baseEnd_934176 < baseStart_934176 := by decide
  rcases family_descends (prefixWord ++ tailWord_934176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934193 : List Nat := [1, 2, 2, 3, 4, 1, 3, 1, 4]
def baseStart_934193 : Nat := 118140960795 + 934193 * 2 ^ 59
def prefixEnd_934193 : Nat := 4983230072969 + 3 ^ 40 * 934193 * 2
def baseEnd_934193 : Nat := 213195570251452755240547

theorem tailTrace_934193 : CollatzResearch.WordTrace tailWord_934193 prefixEnd_934193 213195570251452755240547 := by
  unfold tailWord_934193
  simp only [CollatzResearch.WordTrace]
  refine ⟨34072817904585783307287233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22715211936390522204858155 34072817904585783307287233)
  ·
    refine ⟨25554613428439337480465425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34072817904585783307287233 25554613428439337480465425)
    ·
      refine ⟨19165960071329503110349069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25554613428439337480465425 19165960071329503110349069)
      ·
        refine ⟨7187235026748563666380901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19165960071329503110349069 7187235026748563666380901)
        ·
          refine ⟨1347606567515355687446419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7187235026748563666380901 1347606567515355687446419)
          ·
            refine ⟨2021409851273033531169629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1347606567515355687446419 2021409851273033531169629)
            ·
              refine ⟨758028694227387574188611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2021409851273033531169629 758028694227387574188611)
              ·
                refine ⟨1137043041341081361282917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 758028694227387574188611 1137043041341081361282917)
                ·
                  refine ⟨213195570251452755240547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1137043041341081361282917 213195570251452755240547)
                  ·
                    rfl

theorem cell21_934193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 3, 1, 4].length) (baseStart_934193 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_934193 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_934193 prefixEnd_934193 := by exact prefixLift 934193
  have htrace : WordTrace (prefixWord ++ tailWord_934193) baseStart_934193 baseEnd_934193 := by
    simpa [prefixWord, tailWord_934193, baseEnd_934193] using wordTrace_append hprefix tailTrace_934193
  have hstable : (prefixWord ++ tailWord_934193).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934193).length < 2 ^ (prefixWord ++ tailWord_934193).sum := by decide
  have hdescent : baseEnd_934193 < baseStart_934193 := by decide
  rcases family_descends (prefixWord ++ tailWord_934193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934204 : List Nat := [2, 2, 2, 2, 1, 2, 1, 4, 5]
def baseStart_934204 : Nat := 118140960795 + 934204 * 2 ^ 59
def prefixEnd_934204 : Nat := 4983230072969 + 3 ^ 40 * 934204 * 2
def baseEnd_934204 : Nat := 213198080601319180557191

theorem tailTrace_934204 : CollatzResearch.WordTrace tailWord_934204 prefixEnd_934204 213198080601319180557191 := by
  unfold tailWord_934204
  simp only [CollatzResearch.WordTrace]
  refine ⟨17036609553772966092968833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22715479405030621457291777 17036609553772966092968833)
  ·
    refine ⟨12777457165329724569726625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17036609553772966092968833 12777457165329724569726625)
    ·
      refine ⟨9583092873997293427294969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12777457165329724569726625 9583092873997293427294969)
      ·
        refine ⟨7187319655497970070471227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9583092873997293427294969 7187319655497970070471227)
        ·
          refine ⟨10780979483246955105706841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7187319655497970070471227 10780979483246955105706841)
          ·
            refine ⟨8085734612435216329280131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10780979483246955105706841 8085734612435216329280131)
            ·
              refine ⟨12128601918652824493920197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8085734612435216329280131 12128601918652824493920197)
              ·
                refine ⟨2274112859747404592610037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12128601918652824493920197 2274112859747404592610037)
                ·
                  refine ⟨213198080601319180557191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2274112859747404592610037 213198080601319180557191)
                  ·
                    rfl

theorem cell21_934204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 4, 5].length) (baseStart_934204 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_934204 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_934204 prefixEnd_934204 := by exact prefixLift 934204
  have htrace : WordTrace (prefixWord ++ tailWord_934204) baseStart_934204 baseEnd_934204 := by
    simpa [prefixWord, tailWord_934204, baseEnd_934204] using wordTrace_append hprefix tailTrace_934204
  have hstable : (prefixWord ++ tailWord_934204).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934204).length < 2 ^ (prefixWord ++ tailWord_934204).sum := by decide
  have hdescent : baseEnd_934204 < baseStart_934204 := by decide
  rcases family_descends (prefixWord ++ tailWord_934204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934249 : List Nat := [1, 2, 1, 1, 1, 3, 6, 6]
def baseStart_934249 : Nat := 118140960795 + 934249 * 2 ^ 59
def prefixEnd_934249 : Nat := 4983230072969 + 3 ^ 40 * 934249 * 2
def baseEnd_934249 : Nat := 71069450071469700769033

theorem tailTrace_934249 : CollatzResearch.WordTrace tailWord_934249 prefixEnd_934249 71069450071469700769033 := by
  unfold tailWord_934249
  simp only [CollatzResearch.WordTrace]
  refine ⟨34074860392382904871325801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22716573594921936580883867 34074860392382904871325801)
  ·
    refine ⟨25556145294287178653494351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34074860392382904871325801 25556145294287178653494351)
    ·
      refine ⟨38334217941430767980241527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25556145294287178653494351 38334217941430767980241527)
      ·
        refine ⟨57501326912146151970362291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38334217941430767980241527 57501326912146151970362291)
        ·
          refine ⟨86251990368219227955543437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57501326912146151970362291 86251990368219227955543437)
          ·
            refine ⟨32344496388082210483328789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86251990368219227955543437 32344496388082210483328789)
            ·
              refine ⟨1516148268191353616406037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 32344496388082210483328789 1516148268191353616406037)
              ·
                refine ⟨71069450071469700769033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1516148268191353616406037 71069450071469700769033)
                ·
                  rfl

theorem cell21_934249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 6].length) (baseStart_934249 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_934249 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_934249 prefixEnd_934249 := by exact prefixLift 934249
  have htrace : WordTrace (prefixWord ++ tailWord_934249) baseStart_934249 baseEnd_934249 := by
    simpa [prefixWord, tailWord_934249, baseEnd_934249] using wordTrace_append hprefix tailTrace_934249
  have hstable : (prefixWord ++ tailWord_934249).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934249).length < 2 ^ (prefixWord ++ tailWord_934249).sum := by decide
  have hdescent : baseEnd_934249 < baseStart_934249 := by decide
  rcases family_descends (prefixWord ++ tailWord_934249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934252 : List Nat := [2, 2, 1, 1, 6, 1, 1, 3, 4]
def baseStart_934252 : Nat := 118140960795 + 934252 * 2 ^ 59
def prefixEnd_934252 : Nat := 4983230072969 + 3 ^ 40 * 934252 * 2
def baseEnd_934252 : Nat := 213209034855281763757093

theorem tailTrace_934252 : CollatzResearch.WordTrace tailWord_934252 prefixEnd_934252 213209034855281763757093 := by
  unfold tailWord_934252
  simp only [CollatzResearch.WordTrace]
  refine ⟨17037484905686018191842505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22716646540914690922456673 17037484905686018191842505)
  ·
    refine ⟨12778113679264513643881879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17037484905686018191842505 12778113679264513643881879)
    ·
      refine ⟨19167170518896770465822819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12778113679264513643881879 19167170518896770465822819)
      ·
        refine ⟨28750755778345155698734229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19167170518896770465822819 28750755778345155698734229)
        ·
          refine ⟨1347691677109929173378167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 28750755778345155698734229 1347691677109929173378167)
          ·
            refine ⟨2021537515664893760067251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1347691677109929173378167 2021537515664893760067251)
            ·
              refine ⟨3032306273497340640100877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2021537515664893760067251 3032306273497340640100877)
              ·
                refine ⟨1137114852561502740037829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3032306273497340640100877 1137114852561502740037829)
                ·
                  refine ⟨213209034855281763757093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1137114852561502740037829 213209034855281763757093)
                  ·
                    rfl

theorem cell21_934252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 4].length) (baseStart_934252 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_934252 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_934252 prefixEnd_934252 := by exact prefixLift 934252
  have htrace : WordTrace (prefixWord ++ tailWord_934252) baseStart_934252 baseEnd_934252 := by
    simpa [prefixWord, tailWord_934252, baseEnd_934252] using wordTrace_append hprefix tailTrace_934252
  have hstable : (prefixWord ++ tailWord_934252).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934252).length < 2 ^ (prefixWord ++ tailWord_934252).sum := by decide
  have hdescent : baseEnd_934252 < baseStart_934252 := by decide
  rcases family_descends (prefixWord ++ tailWord_934252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934297 : List Nat := [1, 2, 1, 2, 1, 4, 3, 4, 3]
def baseStart_934297 : Nat := 118140960795 + 934297 * 2 ^ 59
def prefixEnd_934297 : Nat := 4983230072969 + 3 ^ 40 * 934297 * 2
def baseEnd_934297 : Nat := 213219304468371685507001

theorem tailTrace_934297 : CollatzResearch.WordTrace tailWord_934297 prefixEnd_934297 213219304468371685507001 := by
  unfold tailWord_934297
  simp only [CollatzResearch.WordTrace]
  refine ⟨34076611096209009069073145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22717740730806006046048763 34076611096209009069073145)
  ·
    refine ⟨25557458322156756801804859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34076611096209009069073145 25557458322156756801804859)
    ·
      refine ⟨38336187483235135202707289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25557458322156756801804859 38336187483235135202707289)
      ·
        refine ⟨28752140612426351402030467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38336187483235135202707289 28752140612426351402030467)
        ·
          refine ⟨43128210918639527103045701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28752140612426351402030467 43128210918639527103045701)
          ·
            refine ⟨8086539547244911331821069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43128210918639527103045701 8086539547244911331821069)
            ·
              refine ⟨3032452330216841749432901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8086539547244911331821069 3032452330216841749432901)
              ·
                refine ⟨568584811915657828018669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3032452330216841749432901 568584811915657828018669)
                ·
                  refine ⟨213219304468371685507001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 568584811915657828018669 213219304468371685507001)
                  ·
                    rfl

theorem cell21_934297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 4, 3].length) (baseStart_934297 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_934297 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_934297 prefixEnd_934297 := by exact prefixLift 934297
  have htrace : WordTrace (prefixWord ++ tailWord_934297) baseStart_934297 baseEnd_934297 := by
    simpa [prefixWord, tailWord_934297, baseEnd_934297] using wordTrace_append hprefix tailTrace_934297
  have hstable : (prefixWord ++ tailWord_934297).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934297).length < 2 ^ (prefixWord ++ tailWord_934297).sum := by decide
  have hdescent : baseEnd_934297 < baseStart_934297 := by decide
  rcases family_descends (prefixWord ++ tailWord_934297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934339 : List Nat := [1, 1, 1, 3, 1, 1, 3, 1, 9]
def baseStart_934339 : Nat := 118140960795 + 934339 * 2 ^ 59
def prefixEnd_934339 : Nat := 4983230072969 + 3 ^ 40 * 934339 * 2
def baseEnd_934339 : Nat := 213228889440588945806915

theorem tailTrace_934339 : CollatzResearch.WordTrace tailWord_934339 prefixEnd_934339 213228889440588945806915 := by
  unfold tailWord_934339
  simp only [CollatzResearch.WordTrace]
  refine ⟨34078142962056850242102071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22718761974704566828068047 34078142962056850242102071)
  ·
    refine ⟨51117214443085275363153107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34078142962056850242102071 51117214443085275363153107)
    ·
      refine ⟨76675821664627913044729661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51117214443085275363153107 76675821664627913044729661)
      ·
        refine ⟨28753433124235467391773623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76675821664627913044729661 28753433124235467391773623)
        ·
          refine ⟨43130149686353201087660435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28753433124235467391773623 43130149686353201087660435)
          ·
            refine ⟨64695224529529801631490653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43130149686353201087660435 64695224529529801631490653)
            ·
              refine ⟨24260709198573675611808995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64695224529529801631490653 24260709198573675611808995)
              ·
                refine ⟨36391063797860513417713493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24260709198573675611808995 36391063797860513417713493)
                ·
                  refine ⟨213228889440588945806915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 36391063797860513417713493 213228889440588945806915)
                  ·
                    rfl

theorem cell21_934339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 9].length) (baseStart_934339 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_934339 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_934339 prefixEnd_934339 := by exact prefixLift 934339
  have htrace : WordTrace (prefixWord ++ tailWord_934339) baseStart_934339 baseEnd_934339 := by
    simpa [prefixWord, tailWord_934339, baseEnd_934339] using wordTrace_append hprefix tailTrace_934339
  have hstable : (prefixWord ++ tailWord_934339).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934339).length < 2 ^ (prefixWord ++ tailWord_934339).sum := by decide
  have hdescent : baseEnd_934339 < baseStart_934339 := by decide
  rcases family_descends (prefixWord ++ tailWord_934339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934401 : List Nat := [1, 2, 4, 1, 3, 1, 9]
def baseStart_934401 : Nat := 118140960795 + 934401 * 2 ^ 59
def prefixEnd_934401 : Nat := 4983230072969 + 3 ^ 40 * 934401 * 2
def baseEnd_934401 : Nat := 23693670965032290641495

theorem tailTrace_934401 : CollatzResearch.WordTrace tailWord_934401 prefixEnd_934401 23693670965032290641495 := by
  unfold tailWord_934401
  simp only [CollatzResearch.WordTrace]
  refine ⟨34080404287832234830859057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22720269525221489887239371 34080404287832234830859057)
  ·
    refine ⟨25560303215874176123144293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34080404287832234830859057 25560303215874176123144293)
    ·
      refine ⟨4792556852976408023089555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25560303215874176123144293 4792556852976408023089555)
      ·
        refine ⟨7188835279464612034634333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4792556852976408023089555 7188835279464612034634333)
        ·
          refine ⟨2695813229799229512987875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7188835279464612034634333 2695813229799229512987875)
          ·
            refine ⟨4043719844698844269481813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2695813229799229512987875 4043719844698844269481813)
            ·
              refine ⟨23693670965032290641495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4043719844698844269481813 23693670965032290641495)
              ·
                rfl

theorem cell21_934401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 9].length) (baseStart_934401 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_934401 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_934401 prefixEnd_934401 := by exact prefixLift 934401
  have htrace : WordTrace (prefixWord ++ tailWord_934401) baseStart_934401 baseEnd_934401 := by
    simpa [prefixWord, tailWord_934401, baseEnd_934401] using wordTrace_append hprefix tailTrace_934401
  have hstable : (prefixWord ++ tailWord_934401).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934401).length < 2 ^ (prefixWord ++ tailWord_934401).sum := by decide
  have hdescent : baseEnd_934401 < baseStart_934401 := by decide
  rcases family_descends (prefixWord ++ tailWord_934401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934407 : List Nat := [1, 1, 4, 3, 3, 1, 3, 2, 3]
def baseStart_934407 : Nat := 118140960795 + 934407 * 2 ^ 59
def prefixEnd_934407 : Nat := 4983230072969 + 3 ^ 40 * 934407 * 2
def baseEnd_934407 : Nat := 213244407967035938673443

theorem tailTrace_934407 : CollatzResearch.WordTrace tailWord_934407 prefixEnd_934407 213244407967035938673443 := by
  unfold tailWord_934407
  simp only [CollatzResearch.WordTrace]
  refine ⟨34080623125810497855577475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22720415417206998570384983 34080623125810497855577475)
  ·
    refine ⟨51120934688715746783366213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34080623125810497855577475 51120934688715746783366213)
    ·
      refine ⟨9585175254134202521881165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51120934688715746783366213 9585175254134202521881165)
      ·
        refine ⟨3594440720300325945705437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9585175254134202521881165 3594440720300325945705437)
        ·
          refine ⟨1347915270112622229639539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3594440720300325945705437 1347915270112622229639539)
          ·
            refine ⟨2021872905168933344459309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1347915270112622229639539 2021872905168933344459309)
            ·
              refine ⟨758202339438350004172241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2021872905168933344459309 758202339438350004172241)
              ·
                refine ⟨568651754578762503129181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 758202339438350004172241 568651754578762503129181)
                ·
                  refine ⟨213244407967035938673443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 568651754578762503129181 213244407967035938673443)
                  ·
                    rfl

theorem cell21_934407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 3, 2, 3].length) (baseStart_934407 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_934407 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_934407 prefixEnd_934407 := by exact prefixLift 934407
  have htrace : WordTrace (prefixWord ++ tailWord_934407) baseStart_934407 baseEnd_934407 := by
    simpa [prefixWord, tailWord_934407, baseEnd_934407] using wordTrace_append hprefix tailTrace_934407
  have hstable : (prefixWord ++ tailWord_934407).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934407).length < 2 ^ (prefixWord ++ tailWord_934407).sum := by decide
  have hdescent : baseEnd_934407 < baseStart_934407 := by decide
  rcases family_descends (prefixWord ++ tailWord_934407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934463 : List Nat := [1, 1, 2, 2, 3, 2, 4, 2, 4]
def baseStart_934463 : Nat := 118140960795 + 934463 * 2 ^ 59
def prefixEnd_934463 : Nat := 4983230072969 + 3 ^ 40 * 934463 * 2
def baseEnd_934463 : Nat := 213257187929992285739995

theorem tailTrace_934463 : CollatzResearch.WordTrace tailWord_934463 prefixEnd_934463 213257187929992285739995 := by
  unfold tailWord_934463
  simp only [CollatzResearch.WordTrace]
  refine ⟨34082665613607619419616043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22721777075738412946410695 34082665613607619419616043)
  ·
    refine ⟨51123998420411429129424065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34082665613607619419616043 51123998420411429129424065)
    ·
      refine ⟨38342998815308571847068049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51123998420411429129424065 38342998815308571847068049)
      ·
        refine ⟨28757249111481428885301037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38342998815308571847068049 28757249111481428885301037)
        ·
          refine ⟨10783968416805535831987889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28757249111481428885301037 10783968416805535831987889)
          ·
            refine ⟨8087976312604151873990917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10783968416805535831987889 8087976312604151873990917)
            ·
              refine ⟨1516495558613278476373297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8087976312604151873990917 1516495558613278476373297)
              ·
                refine ⟨1137371668959958857279973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1516495558613278476373297 1137371668959958857279973)
                ·
                  refine ⟨213257187929992285739995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1137371668959958857279973 213257187929992285739995)
                  ·
                    rfl

theorem cell21_934463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 2, 4].length) (baseStart_934463 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_934463 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_934463 prefixEnd_934463 := by exact prefixLift 934463
  have htrace : WordTrace (prefixWord ++ tailWord_934463) baseStart_934463 baseEnd_934463 := by
    simpa [prefixWord, tailWord_934463, baseEnd_934463] using wordTrace_append hprefix tailTrace_934463
  have hstable : (prefixWord ++ tailWord_934463).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934463).length < 2 ^ (prefixWord ++ tailWord_934463).sum := by decide
  have hdescent : baseEnd_934463 < baseStart_934463 := by decide
  rcases family_descends (prefixWord ++ tailWord_934463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934525 : List Nat := [1, 4, 1, 1, 5, 1, 2, 1, 5]
def baseStart_934525 : Nat := 118140960795 + 934525 * 2 ^ 59
def prefixEnd_934525 : Nat := 4983230072969 + 3 ^ 40 * 934525 * 2
def baseEnd_934525 : Nat := 213271337174693955706535

theorem tailTrace_934525 : CollatzResearch.WordTrace tailWord_934525 prefixEnd_934525 213271337174693955706535 := by
  unfold tailWord_934525
  simp only [CollatzResearch.WordTrace]
  refine ⟨34084926939383004008373029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22723284626255336005582019 34084926939383004008373029)
  ·
    refine ⟨6390923801134313251569943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34084926939383004008373029 6390923801134313251569943)
    ·
      refine ⟨9586385701701469877354915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6390923801134313251569943 9586385701701469877354915)
      ·
        refine ⟨14379578552552204816032373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9586385701701469877354915 14379578552552204816032373)
        ·
          refine ⟨1348085489301769201503035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14379578552552204816032373 1348085489301769201503035)
          ·
            refine ⟨2022128233952653802254553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1348085489301769201503035 2022128233952653802254553)
            ·
              refine ⟨1516596175464490351690915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2022128233952653802254553 1516596175464490351690915)
              ·
                refine ⟨2274894263196735527536373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1516596175464490351690915 2274894263196735527536373)
                ·
                  refine ⟨213271337174693955706535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2274894263196735527536373 213271337174693955706535)
                  ·
                    rfl

theorem cell21_934525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 1, 5].length) (baseStart_934525 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_934525 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_934525 prefixEnd_934525 := by exact prefixLift 934525
  have htrace : WordTrace (prefixWord ++ tailWord_934525) baseStart_934525 baseEnd_934525 := by
    simpa [prefixWord, tailWord_934525, baseEnd_934525] using wordTrace_append hprefix tailTrace_934525
  have hstable : (prefixWord ++ tailWord_934525).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934525).length < 2 ^ (prefixWord ++ tailWord_934525).sum := by decide
  have hdescent : baseEnd_934525 < baseStart_934525 := by decide
  rcases family_descends (prefixWord ++ tailWord_934525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934632 : List Nat := [2, 1, 4, 1, 4, 1, 2, 2, 4]
def baseStart_934632 : Nat := 118140960795 + 934632 * 2 ^ 59
def prefixEnd_934632 : Nat := 4983230072969 + 3 ^ 40 * 934632 * 2
def baseEnd_934632 : Nat := 213295756032485547422983

theorem tailTrace_934632 : CollatzResearch.WordTrace tailWord_934632 prefixEnd_934632 213295756032485547422983 := by
  unfold tailWord_934632
  simp only [CollatzResearch.WordTrace]
  refine ⟨17044414774997680641259075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22725886366663574188345433 17044414774997680641259075)
  ·
    refine ⟨25566622162496520961888613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17044414774997680641259075 25566622162496520961888613)
    ·
      refine ⟨4793741655468097680354115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25566622162496520961888613 4793741655468097680354115)
      ·
        refine ⟨7190612483202146520531173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4793741655468097680354115 7190612483202146520531173)
        ·
          refine ⟨1348239840600402472599595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7190612483202146520531173 1348239840600402472599595)
          ·
            refine ⟨2022359760900603708899393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1348239840600402472599595 2022359760900603708899393)
            ·
              refine ⟨1516769820675452781674545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2022359760900603708899393 1516769820675452781674545)
              ·
                refine ⟨1137577365506589586255909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1516769820675452781674545 1137577365506589586255909)
                ·
                  refine ⟨213295756032485547422983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1137577365506589586255909 213295756032485547422983)
                  ·
                    rfl

theorem cell21_934632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 2, 4].length) (baseStart_934632 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_934632 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_934632 prefixEnd_934632 := by exact prefixLift 934632
  have htrace : WordTrace (prefixWord ++ tailWord_934632) baseStart_934632 baseEnd_934632 := by
    simpa [prefixWord, tailWord_934632, baseEnd_934632] using wordTrace_append hprefix tailTrace_934632
  have hstable : (prefixWord ++ tailWord_934632).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934632).length < 2 ^ (prefixWord ++ tailWord_934632).sum := by decide
  have hdescent : baseEnd_934632 < baseStart_934632 := by decide
  rcases family_descends (prefixWord ++ tailWord_934632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934643 : List Nat := [1, 1, 1, 2, 2, 3, 1, 5, 5]
def baseStart_934643 : Nat := 118140960795 + 934643 * 2 ^ 59
def prefixEnd_934643 : Nat := 4983230072969 + 3 ^ 40 * 934643 * 2
def baseEnd_934643 : Nat := 213298266382351972739627

theorem tailTrace_934643 : CollatzResearch.WordTrace tailWord_934643 prefixEnd_934643 213298266382351972739627 := by
  unfold tailWord_934643
  simp only [CollatzResearch.WordTrace]
  refine ⟨34089230752955510161168583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22726153835303673440779055 34089230752955510161168583)
  ·
    refine ⟨51133846129433265241752875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34089230752955510161168583 51133846129433265241752875)
    ·
      refine ⟨76700769194149897862629313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51133846129433265241752875 76700769194149897862629313)
      ·
        refine ⟨57525576895612423396971985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76700769194149897862629313 57525576895612423396971985)
        ·
          refine ⟨43144182671709317547728989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57525576895612423396971985 43144182671709317547728989)
          ·
            refine ⟨16179068501890994080398371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43144182671709317547728989 16179068501890994080398371)
            ·
              refine ⟨24268602752836491120597557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16179068501890994080398371 24268602752836491120597557)
              ·
                refine ⟨2275181508078421042556021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24268602752836491120597557 2275181508078421042556021)
                ·
                  refine ⟨213298266382351972739627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2275181508078421042556021 213298266382351972739627)
                  ·
                    rfl

theorem cell21_934643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 5, 5].length) (baseStart_934643 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_934643 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_934643 prefixEnd_934643 := by exact prefixLift 934643
  have htrace : WordTrace (prefixWord ++ tailWord_934643) baseStart_934643 baseEnd_934643 := by
    simpa [prefixWord, tailWord_934643, baseEnd_934643] using wordTrace_append hprefix tailTrace_934643
  have hstable : (prefixWord ++ tailWord_934643).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934643).length < 2 ^ (prefixWord ++ tailWord_934643).sum := by decide
  have hdescent : baseEnd_934643 < baseStart_934643 := by decide
  rcases family_descends (prefixWord ++ tailWord_934643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934660 : List Nat := [2, 3, 2, 2, 1, 1, 3, 2, 5]
def baseStart_934660 : Nat := 118140960795 + 934660 * 2 ^ 59
def prefixEnd_934660 : Nat := 4983230072969 + 3 ^ 40 * 934660 * 2
def baseEnd_934660 : Nat := 213302146013963720956259

theorem tailTrace_934660 : CollatzResearch.WordTrace tailWord_934660 prefixEnd_934660 213302146013963720956259 := by
  unfold tailWord_934660
  simp only [CollatzResearch.WordTrace]
  refine ⟨17044925396946961032268717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22726567195929281376358289 17044925396946961032268717)
  ·
    refine ⟨6391847023855110387100769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17044925396946961032268717 6391847023855110387100769)
    ·
      refine ⟨4793885267891332790325577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6391847023855110387100769 4793885267891332790325577)
      ·
        refine ⟨3595413950918499592744183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4793885267891332790325577 3595413950918499592744183)
        ·
          refine ⟨5393120926377749389116275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3595413950918499592744183 5393120926377749389116275)
          ·
            refine ⟨8089681389566624083674413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5393120926377749389116275 8089681389566624083674413)
            ·
              refine ⟨3033630521087484031377905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8089681389566624083674413 3033630521087484031377905)
              ·
                refine ⟨2275222890815613023533429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3033630521087484031377905 2275222890815613023533429)
                ·
                  refine ⟨213302146013963720956259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2275222890815613023533429 213302146013963720956259)
                  ·
                    rfl

theorem cell21_934660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 2, 5].length) (baseStart_934660 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_934660 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_934660 prefixEnd_934660 := by exact prefixLift 934660
  have htrace : WordTrace (prefixWord ++ tailWord_934660) baseStart_934660 baseEnd_934660 := by
    simpa [prefixWord, tailWord_934660, baseEnd_934660] using wordTrace_append hprefix tailTrace_934660
  have hstable : (prefixWord ++ tailWord_934660).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934660).length < 2 ^ (prefixWord ++ tailWord_934660).sum := by decide
  have hdescent : baseEnd_934660 < baseStart_934660 := by decide
  rcases family_descends (prefixWord ++ tailWord_934660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934677 : List Nat := [1, 3, 2, 1, 2, 2, 4, 3, 3]
def baseStart_934677 : Nat := 118140960795 + 934677 * 2 ^ 59
def prefixEnd_934677 : Nat := 4983230072969 + 3 ^ 40 * 934677 * 2
def baseEnd_934677 : Nat := 213306025645575469172891

theorem tailTrace_934677 : CollatzResearch.WordTrace tailWord_934677 prefixEnd_934677 213306025645575469172891 := by
  unfold tailWord_934677
  simp only [CollatzResearch.WordTrace]
  refine ⟨34090470834832333967906285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22726980556554889311937523 34090470834832333967906285)
  ·
    refine ⟨12783926563062125237964857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34090470834832333967906285 12783926563062125237964857)
    ·
      refine ⟨9587944922296593928473643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12783926563062125237964857 9587944922296593928473643)
      ·
        refine ⟨14381917383444890892710465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9587944922296593928473643 14381917383444890892710465)
        ·
          refine ⟨10786438037583668169532849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14381917383444890892710465 10786438037583668169532849)
          ·
            refine ⟨8089828528187751127149637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10786438037583668169532849 8089828528187751127149637)
            ·
              refine ⟨1516842849035203336340557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8089828528187751127149637 1516842849035203336340557)
              ·
                refine ⟨568816068388201251127709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1516842849035203336340557 568816068388201251127709)
                ·
                  refine ⟨213306025645575469172891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 568816068388201251127709 213306025645575469172891)
                  ·
                    rfl

theorem cell21_934677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 3, 3].length) (baseStart_934677 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_934677 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_934677 prefixEnd_934677 := by exact prefixLift 934677
  have htrace : WordTrace (prefixWord ++ tailWord_934677) baseStart_934677 baseEnd_934677 := by
    simpa [prefixWord, tailWord_934677, baseEnd_934677] using wordTrace_append hprefix tailTrace_934677
  have hstable : (prefixWord ++ tailWord_934677).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934677).length < 2 ^ (prefixWord ++ tailWord_934677).sum := by decide
  have hdescent : baseEnd_934677 < baseStart_934677 := by decide
  rcases family_descends (prefixWord ++ tailWord_934677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934922 : List Nat := [3, 1, 2, 2, 3, 2, 3, 2, 3]
def baseStart_934922 : Nat := 118140960795 + 934922 * 2 ^ 59
def prefixEnd_934922 : Nat := 4983230072969 + 3 ^ 40 * 934922 * 2
def baseEnd_934922 : Nat := 213361937983509487589057

theorem tailTrace_934922 : CollatzResearch.WordTrace tailWord_934922 prefixEnd_934922 213361937983509487589057 := by
  unfold tailWord_934922
  simp only [CollatzResearch.WordTrace]
  refine ⟨8524851679736185202643755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22732937812629827207050013 8524851679736185202643755)
  ·
    refine ⟨12787277519604277803965633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8524851679736185202643755 12787277519604277803965633)
    ·
      refine ⟨9590458139703208352974225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12787277519604277803965633 9590458139703208352974225)
      ·
        refine ⟨7192843604777406264730669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9590458139703208352974225 7192843604777406264730669)
        ·
          refine ⟨2697316351791527349274001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7192843604777406264730669 2697316351791527349274001)
          ·
            refine ⟨2022987263843645511955501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2697316351791527349274001 2022987263843645511955501)
            ·
              refine ⟨758620223941367066983313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2022987263843645511955501 758620223941367066983313)
              ·
                refine ⟨568965167956025300237485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 758620223941367066983313 568965167956025300237485)
                ·
                  refine ⟨213361937983509487589057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 568965167956025300237485 213361937983509487589057)
                  ·
                    rfl

theorem cell21_934922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 3, 2, 3].length) (baseStart_934922 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_934922 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_934922 prefixEnd_934922 := by exact prefixLift 934922
  have htrace : WordTrace (prefixWord ++ tailWord_934922) baseStart_934922 baseEnd_934922 := by
    simpa [prefixWord, tailWord_934922, baseEnd_934922] using wordTrace_append hprefix tailTrace_934922
  have hstable : (prefixWord ++ tailWord_934922).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934922).length < 2 ^ (prefixWord ++ tailWord_934922).sum := by decide
  have hdescent : baseEnd_934922 < baseStart_934922 := by decide
  rcases family_descends (prefixWord ++ tailWord_934922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934933 : List Nat := [1, 3, 2, 1, 4, 2, 2, 6]
def baseStart_934933 : Nat := 118140960795 + 934933 * 2 ^ 59
def prefixEnd_934933 : Nat := 4983230072969 + 3 ^ 40 * 934933 * 2
def baseEnd_934933 : Nat := 71121482777791970968567

theorem tailTrace_934933 : CollatzResearch.WordTrace tailWord_934933 prefixEnd_934933 71121482777791970968567 := by
  unfold tailWord_934933
  simp only [CollatzResearch.WordTrace]
  refine ⟨34099807921904889689225453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22733205281269926459483635 34099807921904889689225453)
  ·
    refine ⟨12787427970714333633459545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34099807921904889689225453 12787427970714333633459545)
    ·
      refine ⟨9590570978035750225094659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12787427970714333633459545 9590570978035750225094659)
      ·
        refine ⟨14385856467053625337641989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9590570978035750225094659 14385856467053625337641989)
        ·
          refine ⟨2697348087572554750807873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14385856467053625337641989 2697348087572554750807873)
          ·
            refine ⟨2023011065679416063105905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2697348087572554750807873 2023011065679416063105905)
            ·
              refine ⟨1517258299259562047329429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2023011065679416063105905 1517258299259562047329429)
              ·
                refine ⟨71121482777791970968567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1517258299259562047329429 71121482777791970968567)
                ·
                  rfl

theorem cell21_934933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 6].length) (baseStart_934933 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_934933 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_934933 prefixEnd_934933 := by exact prefixLift 934933
  have htrace : WordTrace (prefixWord ++ tailWord_934933) baseStart_934933 baseEnd_934933 := by
    simpa [prefixWord, tailWord_934933, baseEnd_934933] using wordTrace_append hprefix tailTrace_934933
  have hstable : (prefixWord ++ tailWord_934933).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934933).length < 2 ^ (prefixWord ++ tailWord_934933).sum := by decide
  have hdescent : baseEnd_934933 < baseStart_934933 := by decide
  rcases family_descends (prefixWord ++ tailWord_934933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934936 : List Nat := [2, 1, 2, 3, 2, 4, 2, 1, 4]
def baseStart_934936 : Nat := 118140960795 + 934936 * 2 ^ 59
def prefixEnd_934936 : Nat := 4983230072969 + 3 ^ 40 * 934936 * 2
def baseEnd_934936 : Nat := 213365132974248574355695

theorem tailTrace_934936 : CollatzResearch.WordTrace tailWord_934936 prefixEnd_934936 213365132974248574355695 := by
  unfold tailWord_934936
  simp only [CollatzResearch.WordTrace]
  refine ⟨17049958670447010600792331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22733278227262680801056441 17049958670447010600792331)
  ·
    refine ⟨25574938005670515901188497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17049958670447010600792331 25574938005670515901188497)
    ·
      refine ⟨19181203504252886925891373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25574938005670515901188497 19181203504252886925891373)
      ·
        refine ⟨7192951314094832597209265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19181203504252886925891373 7192951314094832597209265)
        ·
          refine ⟨5394713485571124447906949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7192951314094832597209265 5394713485571124447906949)
          ·
            refine ⟨1011508778544585833982553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5394713485571124447906949 1011508778544585833982553)
            ·
              refine ⟨758631583908439375486915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1011508778544585833982553 758631583908439375486915)
              ·
                refine ⟨1137947375862659063230373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 758631583908439375486915 1137947375862659063230373)
                ·
                  refine ⟨213365132974248574355695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1137947375862659063230373 213365132974248574355695)
                  ·
                    rfl

theorem cell21_934936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 2, 1, 4].length) (baseStart_934936 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_934936 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_934936 prefixEnd_934936 := by exact prefixLift 934936
  have htrace : WordTrace (prefixWord ++ tailWord_934936) baseStart_934936 baseEnd_934936 := by
    simpa [prefixWord, tailWord_934936, baseEnd_934936] using wordTrace_append hprefix tailTrace_934936
  have hstable : (prefixWord ++ tailWord_934936).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934936).length < 2 ^ (prefixWord ++ tailWord_934936).sum := by decide
  have hdescent : baseEnd_934936 < baseStart_934936 := by decide
  rcases family_descends (prefixWord ++ tailWord_934936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934981 : List Nat := [1, 3, 1, 1, 1, 3, 6, 2, 3]
def baseStart_934981 : Nat := 118140960795 + 934981 * 2 ^ 59
def prefixEnd_934981 : Nat := 4983230072969 + 3 ^ 40 * 934981 * 2
def baseEnd_934981 : Nat := 213375402587338496105603

theorem tailTrace_934981 : CollatzResearch.WordTrace tailWord_934981 prefixEnd_934981 213375402587338496105603 := by
  unfold tailWord_934981
  simp only [CollatzResearch.WordTrace]
  refine ⟨34101558625730993886972797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22734372417153995924648531 34101558625730993886972797)
  ·
    refine ⟨12788084484649122707614799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34101558625730993886972797 12788084484649122707614799)
    ·
      refine ⟨19182126726973684061422199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12788084484649122707614799 19182126726973684061422199)
      ·
        refine ⟨28773190090460526092133299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19182126726973684061422199 28773190090460526092133299)
        ·
          refine ⟨43159785135690789138199949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28773190090460526092133299 43159785135690789138199949)
          ·
            refine ⟨16184919425884045926824981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43159785135690789138199949 16184919425884045926824981)
            ·
              refine ⟨758668098088314652819921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16184919425884045926824981 758668098088314652819921)
              ·
                refine ⟨569001073566235989614941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 758668098088314652819921 569001073566235989614941)
                ·
                  refine ⟨213375402587338496105603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 569001073566235989614941 213375402587338496105603)
                  ·
                    rfl

theorem cell21_934981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 6, 2, 3].length) (baseStart_934981 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_934981 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_934981 prefixEnd_934981 := by exact prefixLift 934981
  have htrace : WordTrace (prefixWord ++ tailWord_934981) baseStart_934981 baseEnd_934981 := by
    simpa [prefixWord, tailWord_934981, baseEnd_934981] using wordTrace_append hprefix tailTrace_934981
  have hstable : (prefixWord ++ tailWord_934981).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934981).length < 2 ^ (prefixWord ++ tailWord_934981).sum := by decide
  have hdescent : baseEnd_934981 < baseStart_934981 := by decide
  rcases family_descends (prefixWord ++ tailWord_934981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934998 : List Nat := [5, 2, 2, 1, 2, 1, 1, 2, 5]
def baseStart_934998 : Nat := 118140960795 + 934998 * 2 ^ 59
def prefixEnd_934998 : Nat := 4983230072969 + 3 ^ 40 * 934998 * 2
def baseEnd_934998 : Nat := 213379282218950244322235

theorem tailTrace_934998 : CollatzResearch.WordTrace tailWord_934998 prefixEnd_934998 213379282218950244322235 := by
  unfold tailWord_934998
  simp only [CollatzResearch.WordTrace]
  refine ⟨2131386166666837861896353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22734785777779603860227765 2131386166666837861896353)
  ·
    refine ⟨1598539625000128396422265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2131386166666837861896353 1598539625000128396422265)
    ·
      refine ⟨1198904718750096297316699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1598539625000128396422265 1198904718750096297316699)
      ·
        refine ⟨1798357078125144445975049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1198904718750096297316699 1798357078125144445975049)
        ·
          refine ⟨1348767808593858334481287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1798357078125144445975049 1348767808593858334481287)
          ·
            refine ⟨2023151712890787501721931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1348767808593858334481287 2023151712890787501721931)
            ·
              refine ⟨3034727569336181252582897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2023151712890787501721931 3034727569336181252582897)
              ·
                refine ⟨2276045677002135939437173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3034727569336181252582897 2276045677002135939437173)
                ·
                  refine ⟨213379282218950244322235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2276045677002135939437173 213379282218950244322235)
                  ·
                    rfl

theorem cell21_934998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_934998 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_934998 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_934998 prefixEnd_934998 := by exact prefixLift 934998
  have htrace : WordTrace (prefixWord ++ tailWord_934998) baseStart_934998 baseEnd_934998 := by
    simpa [prefixWord, tailWord_934998, baseEnd_934998] using wordTrace_append hprefix tailTrace_934998
  have hstable : (prefixWord ++ tailWord_934998).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934998).length < 2 ^ (prefixWord ++ tailWord_934998).sum := by decide
  have hdescent : baseEnd_934998 < baseStart_934998 := by decide
  rcases family_descends (prefixWord ++ tailWord_934998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935029 : List Nat := [1, 3, 4, 3, 1, 2, 1, 2, 4]
def baseStart_935029 : Nat := 118140960795 + 935029 * 2 ^ 59
def prefixEnd_935029 : Nat := 4983230072969 + 3 ^ 40 * 935029 * 2
def baseEnd_935029 : Nat := 213386356841301079305505

theorem tailTrace_935029 : CollatzResearch.WordTrace tailWord_935029 prefixEnd_935029 213386356841301079305505 := by
  unfold tailWord_935029
  simp only [CollatzResearch.WordTrace]
  refine ⟨34103309329557098084720141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22735539553038065389813427 34103309329557098084720141)
  ·
    refine ⟨12788740998583911781770053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34103309329557098084720141 12788740998583911781770053)
    ·
      refine ⟨2397888937234483459081885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12788740998583911781770053 2397888937234483459081885)
      ·
        refine ⟨899208351462931297155707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2397888937234483459081885 899208351462931297155707)
        ·
          refine ⟨1348812527194396945733561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 899208351462931297155707 1348812527194396945733561)
          ·
            refine ⟨1011609395395797709300171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1348812527194396945733561 1011609395395797709300171)
            ·
              refine ⟨1517414093093696563950257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1011609395395797709300171 1517414093093696563950257)
              ·
                refine ⟨1138060569820272422962693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1517414093093696563950257 1138060569820272422962693)
                ·
                  refine ⟨213386356841301079305505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1138060569820272422962693 213386356841301079305505)
                  ·
                    rfl

theorem cell21_935029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 2, 4].length) (baseStart_935029 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_935029 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_935029 prefixEnd_935029 := by exact prefixLift 935029
  have htrace : WordTrace (prefixWord ++ tailWord_935029) baseStart_935029 baseEnd_935029 := by
    simpa [prefixWord, tailWord_935029, baseEnd_935029] using wordTrace_append hprefix tailTrace_935029
  have hstable : (prefixWord ++ tailWord_935029).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935029).length < 2 ^ (prefixWord ++ tailWord_935029).sum := by decide
  have hdescent : baseEnd_935029 < baseStart_935029 := by decide
  rcases family_descends (prefixWord ++ tailWord_935029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935040 : List Nat := [2, 1, 1, 2, 1, 3, 4, 4, 3]
def baseStart_935040 : Nat := 118140960795 + 935040 * 2 ^ 59
def prefixEnd_935040 : Nat := 4983230072969 + 3 ^ 40 * 935040 * 2
def baseEnd_935040 : Nat := 213388867191167504622149

theorem tailTrace_935040 : CollatzResearch.WordTrace tailWord_935040 prefixEnd_935040 213388867191167504622149 := by
  unfold tailWord_935040
  simp only [CollatzResearch.WordTrace]
  refine ⟨17051855266258623481685287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22735807021678164642247049 17051855266258623481685287)
  ·
    refine ⟨25577782899387935222527931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17051855266258623481685287 25577782899387935222527931)
    ·
      refine ⟨38366674349081902833791897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25577782899387935222527931 38366674349081902833791897)
      ·
        refine ⟨28775005761811427125343923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38366674349081902833791897 28775005761811427125343923)
        ·
          refine ⟨43162508642717140688015885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28775005761811427125343923 43162508642717140688015885)
          ·
            refine ⟨16185940741018927758005957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43162508642717140688015885 16185940741018927758005957)
            ·
              refine ⟨3034863888941048954626117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16185940741018927758005957 3034863888941048954626117)
              ·
                refine ⟨569036979176446678992397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3034863888941048954626117 569036979176446678992397)
                ·
                  refine ⟨213388867191167504622149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 569036979176446678992397 213388867191167504622149)
                  ·
                    rfl

theorem cell21_935040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 4, 3].length) (baseStart_935040 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_935040 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_935040 prefixEnd_935040 := by exact prefixLift 935040
  have htrace : WordTrace (prefixWord ++ tailWord_935040) baseStart_935040 baseEnd_935040 := by
    simpa [prefixWord, tailWord_935040, baseEnd_935040] using wordTrace_append hprefix tailTrace_935040
  have hstable : (prefixWord ++ tailWord_935040).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935040).length < 2 ^ (prefixWord ++ tailWord_935040).sum := by decide
  have hdescent : baseEnd_935040 < baseStart_935040 := by decide
  rcases family_descends (prefixWord ++ tailWord_935040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935105 : List Nat := [1, 2, 6, 1, 1, 3, 2, 1, 4]
def baseStart_935105 : Nat := 118140960795 + 935105 * 2 ^ 59
def prefixEnd_935105 : Nat := 4983230072969 + 3 ^ 40 * 935105 * 2
def baseEnd_935105 : Nat := 213403701076741836038683

theorem tailTrace_935105 : CollatzResearch.WordTrace tailWord_935105 prefixEnd_935105 213403701076741836038683 := by
  unfold tailWord_935105
  simp only [CollatzResearch.WordTrace]
  refine ⟨34106081277281763064486769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22737387518187842042991179 34106081277281763064486769)
  ·
    refine ⟨25579560957961322298365077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34106081277281763064486769 25579560957961322298365077)
    ·
      refine ⟨1199041919904436982735863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 25579560957961322298365077 1199041919904436982735863)
      ·
        refine ⟨1798562879856655474103795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1199041919904436982735863 1798562879856655474103795)
        ·
          refine ⟨2697844319784983211155693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1798562879856655474103795 2697844319784983211155693)
          ·
            refine ⟨1011691619919368704183385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2697844319784983211155693 1011691619919368704183385)
            ·
              refine ⟨758768714939526528137539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1011691619919368704183385 758768714939526528137539)
              ·
                refine ⟨1138153072409289792206309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 758768714939526528137539 1138153072409289792206309)
                ·
                  refine ⟨213403701076741836038683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1138153072409289792206309 213403701076741836038683)
                  ·
                    rfl

theorem cell21_935105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 2, 1, 4].length) (baseStart_935105 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_935105 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_935105 prefixEnd_935105 := by exact prefixLift 935105
  have htrace : WordTrace (prefixWord ++ tailWord_935105) baseStart_935105 baseEnd_935105 := by
    simpa [prefixWord, tailWord_935105, baseEnd_935105] using wordTrace_append hprefix tailTrace_935105
  have hstable : (prefixWord ++ tailWord_935105).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935105).length < 2 ^ (prefixWord ++ tailWord_935105).sum := by decide
  have hdescent : baseEnd_935105 < baseStart_935105 := by decide
  rcases family_descends (prefixWord ++ tailWord_935105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935189 : List Nat := [1, 3, 2, 1, 2, 1, 1, 4, 6]
def baseStart_935189 : Nat := 118140960795 + 935189 * 2 ^ 59
def prefixEnd_935189 : Nat := 4983230072969 + 3 ^ 40 * 935189 * 2
def baseEnd_935189 : Nat := 213422871021176356638511

theorem tailTrace_935189 : CollatzResearch.WordTrace tailWord_935189 prefixEnd_935189 213422871021176356638511 := by
  unfold tailWord_935189
  simp only [CollatzResearch.WordTrace]
  refine ⟨34109145008977445410544621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22739430005984963607029747 34109145008977445410544621)
  ·
    refine ⟨12790929378366542028954233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34109145008977445410544621 12790929378366542028954233)
    ·
      refine ⟨9593197033774906521715675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12790929378366542028954233 9593197033774906521715675)
      ·
        refine ⟨14389795550662359782573513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9593197033774906521715675 14389795550662359782573513)
        ·
          refine ⟨10792346662996769836930135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14389795550662359782573513 10792346662996769836930135)
          ·
            refine ⟨16188519994495154755395203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10792346662996769836930135 16188519994495154755395203)
            ·
              refine ⟨24282779991742732133092805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16188519994495154755395203 24282779991742732133092805)
              ·
                refine ⟨4553021248451762274954901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24282779991742732133092805 4553021248451762274954901)
                ·
                  refine ⟨213422871021176356638511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4553021248451762274954901 213422871021176356638511)
                  ·
                    rfl

theorem cell21_935189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 6].length) (baseStart_935189 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_935189 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_935189 prefixEnd_935189 := by exact prefixLift 935189
  have htrace : WordTrace (prefixWord ++ tailWord_935189) baseStart_935189 baseEnd_935189 := by
    simpa [prefixWord, tailWord_935189, baseEnd_935189] using wordTrace_append hprefix tailTrace_935189
  have hstable : (prefixWord ++ tailWord_935189).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935189).length < 2 ^ (prefixWord ++ tailWord_935189).sum := by decide
  have hdescent : baseEnd_935189 < baseStart_935189 := by decide
  rcases family_descends (prefixWord ++ tailWord_935189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935192 : List Nat := [2, 1, 2, 3, 1, 3, 1, 5, 3]
def baseStart_935192 : Nat := 118140960795 + 935192 * 2 ^ 59
def prefixEnd_935192 : Nat := 4983230072969 + 3 ^ 40 * 935192 * 2
def baseEnd_935192 : Nat := 213423555662049018088505

theorem tailTrace_935192 : CollatzResearch.WordTrace tailWord_935192 prefixEnd_935192 213423555662049018088505 := by
  unfold tailWord_935192
  simp only [CollatzResearch.WordTrace]
  refine ⟨17054627213983288461451915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22739502951977717948602553 17054627213983288461451915)
  ·
    refine ⟨25581940820974932692177873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17054627213983288461451915 25581940820974932692177873)
    ·
      refine ⟨19186455615731199519133405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25581940820974932692177873 19186455615731199519133405)
      ·
        refine ⟨7194920855899199819675027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19186455615731199519133405 7194920855899199819675027)
        ·
          refine ⟨10792381283848799729512541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7194920855899199819675027 10792381283848799729512541)
          ·
            refine ⟨4047142981443299898567203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10792381283848799729512541 4047142981443299898567203)
            ·
              refine ⟨6070714472164949847850805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4047142981443299898567203 6070714472164949847850805)
              ·
                refine ⟨569129481765464048236013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6070714472164949847850805 569129481765464048236013)
                ·
                  refine ⟨213423555662049018088505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 569129481765464048236013 213423555662049018088505)
                  ·
                    rfl

theorem cell21_935192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 5, 3].length) (baseStart_935192 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_935192 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_935192 prefixEnd_935192 := by exact prefixLift 935192
  have htrace : WordTrace (prefixWord ++ tailWord_935192) baseStart_935192 baseEnd_935192 := by
    simpa [prefixWord, tailWord_935192, baseEnd_935192] using wordTrace_append hprefix tailTrace_935192
  have hstable : (prefixWord ++ tailWord_935192).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935192).length < 2 ^ (prefixWord ++ tailWord_935192).sum := by decide
  have hdescent : baseEnd_935192 < baseStart_935192 := by decide
  rcases family_descends (prefixWord ++ tailWord_935192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935198 : List Nat := [4, 3, 2, 1, 3, 1, 1, 2, 4]
def baseStart_935198 : Nat := 118140960795 + 935198 * 2 ^ 59
def prefixEnd_935198 : Nat := 4983230072969 + 3 ^ 40 * 935198 * 2
def baseEnd_935198 : Nat := 213424924943794340988493

theorem tailTrace_935198 : CollatzResearch.WordTrace tailWord_935198 prefixEnd_935198 213424924943794340988493 := by
  unfold tailWord_935198
  simp only [CollatzResearch.WordTrace]
  refine ⟨4263684158243104993452781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22739648843963226631748165 4263684158243104993452781)
  ·
    refine ⟨1598881559341164372544793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4263684158243104993452781 1598881559341164372544793)
    ·
      refine ⟨1199161169505873279408595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1598881559341164372544793 1199161169505873279408595)
      ·
        refine ⟨1798741754258809919112893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1199161169505873279408595 1798741754258809919112893)
        ·
          refine ⟨674528157847053719667335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1798741754258809919112893 674528157847053719667335)
          ·
            refine ⟨1011792236770580579501003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 674528157847053719667335 1011792236770580579501003)
            ·
              refine ⟨1517688355155870869251505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1011792236770580579501003 1517688355155870869251505)
              ·
                refine ⟨1138266266366903151938629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1517688355155870869251505 1138266266366903151938629)
                ·
                  refine ⟨213424924943794340988493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1138266266366903151938629 213424924943794340988493)
                  ·
                    rfl

theorem cell21_935198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_935198 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_935198 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_935198 prefixEnd_935198 := by exact prefixLift 935198
  have htrace : WordTrace (prefixWord ++ tailWord_935198) baseStart_935198 baseEnd_935198 := by
    simpa [prefixWord, tailWord_935198, baseEnd_935198] using wordTrace_append hprefix tailTrace_935198
  have hstable : (prefixWord ++ tailWord_935198).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935198).length < 2 ^ (prefixWord ++ tailWord_935198).sum := by decide
  have hdescent : baseEnd_935198 < baseStart_935198 := by decide
  rcases family_descends (prefixWord ++ tailWord_935198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935268 : List Nat := [2, 3, 1, 1, 3, 4, 1, 1, 5]
def baseStart_935268 : Nat := 118140960795 + 935268 * 2 ^ 59
def prefixEnd_935268 : Nat := 4983230072969 + 3 ^ 40 * 935268 * 2
def baseEnd_935268 : Nat := 213440899897489774821683

theorem tailTrace_935268 : CollatzResearch.WordTrace tailWord_935268 prefixEnd_935268 213440899897489774821683 := by
  unfold tailWord_935268
  simp only [CollatzResearch.WordTrace]
  refine ⟨17056013187845620951335229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22741350917127494601780305 17056013187845620951335229)
  ·
    refine ⟨6396004945442107856750711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17056013187845620951335229 6396004945442107856750711)
    ·
      refine ⟨9594007418163161785126067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6396004945442107856750711 9594007418163161785126067)
      ·
        refine ⟨14391011127244742677689101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9594007418163161785126067 14391011127244742677689101)
        ·
          refine ⟨5396629172716778504133413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14391011127244742677689101 5396629172716778504133413)
          ·
            refine ⟨1011867969884395969525015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5396629172716778504133413 1011867969884395969525015)
            ·
              refine ⟨1517801954826593954287523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1011867969884395969525015 1517801954826593954287523)
              ·
                refine ⟨2276702932239890931431285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1517801954826593954287523 2276702932239890931431285)
                ·
                  refine ⟨213440899897489774821683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2276702932239890931431285 213440899897489774821683)
                  ·
                    rfl

theorem cell21_935268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 1, 5].length) (baseStart_935268 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_935268 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_935268 prefixEnd_935268 := by exact prefixLift 935268
  have htrace : WordTrace (prefixWord ++ tailWord_935268) baseStart_935268 baseEnd_935268 := by
    simpa [prefixWord, tailWord_935268, baseEnd_935268] using wordTrace_append hprefix tailTrace_935268
  have hstable : (prefixWord ++ tailWord_935268).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935268).length < 2 ^ (prefixWord ++ tailWord_935268).sum := by decide
  have hdescent : baseEnd_935268 < baseStart_935268 := by decide
  rcases family_descends (prefixWord ++ tailWord_935268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935282 : List Nat := [3, 2, 1, 2, 1, 2, 3, 3, 4]
def baseStart_935282 : Nat := 118140960795 + 935282 * 2 ^ 59
def prefixEnd_935282 : Nat := 4983230072969 + 3 ^ 40 * 935282 * 2
def baseEnd_935282 : Nat := 213444094888228861588321

theorem tailTrace_935282 : CollatzResearch.WordTrace tailWord_935282 prefixEnd_935282 213444094888228861588321 := by
  unfold tailWord_935282
  simp only [CollatzResearch.WordTrace]
  refine ⟨8528134249410130573420025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22741691331760348195786733 8528134249410130573420025)
  ·
    refine ⟨6396100687057597930065019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8528134249410130573420025 6396100687057597930065019)
    ·
      refine ⟨9594151030586396895097529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6396100687057597930065019 9594151030586396895097529)
      ·
        refine ⟨7195613272939797671323147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9594151030586396895097529 7195613272939797671323147)
        ·
          refine ⟨10793419909409696506984721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7195613272939797671323147 10793419909409696506984721)
          ·
            refine ⟨8095064932057272380238541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10793419909409696506984721 8095064932057272380238541)
            ·
              refine ⟨3035649349521477142589453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8095064932057272380238541 3035649349521477142589453)
              ·
                refine ⟨1138368506070553928471045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3035649349521477142589453 1138368506070553928471045)
                ·
                  refine ⟨213444094888228861588321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1138368506070553928471045 213444094888228861588321)
                  ·
                    rfl

theorem cell21_935282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 3, 4].length) (baseStart_935282 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_935282 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_935282 prefixEnd_935282 := by exact prefixLift 935282
  have htrace : WordTrace (prefixWord ++ tailWord_935282) baseStart_935282 baseEnd_935282 := by
    simpa [prefixWord, tailWord_935282, baseEnd_935282] using wordTrace_append hprefix tailTrace_935282
  have hstable : (prefixWord ++ tailWord_935282).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935282).length < 2 ^ (prefixWord ++ tailWord_935282).sum := by decide
  have hdescent : baseEnd_935282 < baseStart_935282 := by decide
  rcases family_descends (prefixWord ++ tailWord_935282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935372 : List Nat := [2, 2, 1, 4, 2, 2, 8]
def baseStart_935372 : Nat := 118140960795 + 935372 * 2 ^ 59
def prefixEnd_935372 : Nat := 4983230072969 + 3 ^ 40 * 935372 * 2
def baseEnd_935372 : Nat := 23718292679378745009793

theorem tailTrace_935372 : CollatzResearch.WordTrace tailWord_935372 prefixEnd_935372 23718292679378745009793 := by
  unfold tailWord_935372
  simp only [CollatzResearch.WordTrace]
  refine ⟨17057909783657233832228185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22743879711542978442970913 17057909783657233832228185)
  ·
    refine ⟨12793432337742925374171139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17057909783657233832228185 12793432337742925374171139)
    ·
      refine ⟨19190148506614388061256709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12793432337742925374171139 19190148506614388061256709)
      ·
        refine ⟨3598152844990197761485633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19190148506614388061256709 3598152844990197761485633)
        ·
          refine ⟨2698614633742648321114225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3598152844990197761485633 2698614633742648321114225)
          ·
            refine ⟨2023960975306986240835669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2698614633742648321114225 2023960975306986240835669)
            ·
              refine ⟨23718292679378745009793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2023960975306986240835669 23718292679378745009793)
              ·
                rfl

theorem cell21_935372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 8].length) (baseStart_935372 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_935372 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_935372 prefixEnd_935372 := by exact prefixLift 935372
  have htrace : WordTrace (prefixWord ++ tailWord_935372) baseStart_935372 baseEnd_935372 := by
    simpa [prefixWord, tailWord_935372, baseEnd_935372] using wordTrace_append hprefix tailTrace_935372
  have hstable : (prefixWord ++ tailWord_935372).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935372).length < 2 ^ (prefixWord ++ tailWord_935372).sum := by decide
  have hdescent : baseEnd_935372 < baseStart_935372 := by decide
  rcases family_descends (prefixWord ++ tailWord_935372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935420 : List Nat := [2, 2, 2, 1, 2, 1, 5, 3, 3]
def baseStart_935420 : Nat := 118140960795 + 935420 * 2 ^ 59
def prefixEnd_935420 : Nat := 4983230072969 + 3 ^ 40 * 935420 * 2
def baseEnd_935420 : Nat := 213475588368371288288039

theorem tailTrace_935420 : CollatzResearch.WordTrace tailWord_935420 prefixEnd_935420 213475588368371288288039 := by
  unfold tailWord_935420
  simp only [CollatzResearch.WordTrace]
  refine ⟨17058785135570285931101857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22745046847427047908135809 17058785135570285931101857)
  ·
    refine ⟨12794088851677714448326393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17058785135570285931101857 12794088851677714448326393)
    ·
      refine ⟨9595566638758285836244795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12794088851677714448326393 9595566638758285836244795)
      ·
        refine ⟨14393349958137428754367193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9595566638758285836244795 14393349958137428754367193)
        ·
          refine ⟨10795012468603071565775395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14393349958137428754367193 10795012468603071565775395)
          ·
            refine ⟨16192518702904607348663093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10795012468603071565775395 16192518702904607348663093)
            ·
              refine ⟨1518048628397306938937165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16192518702904607348663093 1518048628397306938937165)
              ·
                refine ⟨569268235648990102101437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1518048628397306938937165 569268235648990102101437)
                ·
                  refine ⟨213475588368371288288039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 569268235648990102101437 213475588368371288288039)
                  ·
                    rfl

theorem cell21_935420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 3, 3].length) (baseStart_935420 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_935420 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_935420 prefixEnd_935420 := by exact prefixLift 935420
  have htrace : WordTrace (prefixWord ++ tailWord_935420) baseStart_935420 baseEnd_935420 := by
    simpa [prefixWord, tailWord_935420, baseEnd_935420] using wordTrace_append hprefix tailTrace_935420
  have hstable : (prefixWord ++ tailWord_935420).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935420).length < 2 ^ (prefixWord ++ tailWord_935420).sum := by decide
  have hdescent : baseEnd_935420 < baseStart_935420 := by decide
  rcases family_descends (prefixWord ++ tailWord_935420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935662 : List Nat := [4, 1, 2, 1, 1, 2, 4, 2, 4]
def baseStart_935662 : Nat := 118140960795 + 935662 * 2 ^ 59
def prefixEnd_935662 : Nat := 4983230072969 + 3 ^ 40 * 935662 * 2
def baseEnd_935662 : Nat := 213530816065432645254211

theorem tailTrace_935662 : CollatzResearch.WordTrace tailWord_935662 prefixEnd_935662 213530816065432645254211 := by
  unfold tailWord_935662
  simp only [CollatzResearch.WordTrace]
  refine ⟨4265799592032980899064155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22750931157509231461675493 4265799592032980899064155)
  ·
    refine ⟨6398699388049471348596233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4265799592032980899064155 6398699388049471348596233)
    ·
      refine ⟨4799024541037103511447175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6398699388049471348596233 4799024541037103511447175)
      ·
        refine ⟨7198536811555655267170763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4799024541037103511447175 7198536811555655267170763)
        ·
          refine ⟨10797805217333482900756145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7198536811555655267170763 10797805217333482900756145)
          ·
            refine ⟨8098353913000112175567109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10797805217333482900756145 8098353913000112175567109)
            ·
              refine ⟨1518441358687521032918833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8098353913000112175567109 1518441358687521032918833)
              ·
                refine ⟨1138831019015640774689125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1518441358687521032918833 1138831019015640774689125)
                ·
                  refine ⟨213530816065432645254211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1138831019015640774689125 213530816065432645254211)
                  ·
                    rfl

theorem cell21_935662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 2, 4].length) (baseStart_935662 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_935662 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_935662 prefixEnd_935662 := by exact prefixLift 935662
  have htrace : WordTrace (prefixWord ++ tailWord_935662) baseStart_935662 baseEnd_935662 := by
    simpa [prefixWord, tailWord_935662, baseEnd_935662] using wordTrace_append hprefix tailTrace_935662
  have hstable : (prefixWord ++ tailWord_935662).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935662).length < 2 ^ (prefixWord ++ tailWord_935662).sum := by decide
  have hdescent : baseEnd_935662 < baseStart_935662 := by decide
  rcases family_descends (prefixWord ++ tailWord_935662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935665 : List Nat := [1, 2, 2, 2, 2, 5, 2, 2, 3]
def baseStart_935665 : Nat := 118140960795 + 935665 * 2 ^ 59
def prefixEnd_935665 : Nat := 4983230072969 + 3 ^ 40 * 935665 * 2
def baseEnd_935665 : Nat := 213531500706305306704205

theorem tailTrace_935665 : CollatzResearch.WordTrace tailWord_935665 prefixEnd_935665 213531500706305306704205 := by
  unfold tailWord_935665
  simp only [CollatzResearch.WordTrace]
  refine ⟨34126506155252978704872449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22751004103501985803248299 34126506155252978704872449)
  ·
    refine ⟨25594879616439734028654337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34126506155252978704872449 25594879616439734028654337)
    ·
      refine ⟨19196159712329800521490753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25594879616439734028654337 19196159712329800521490753)
      ·
        refine ⟨14397119784247350391118065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19196159712329800521490753 14397119784247350391118065)
        ·
          refine ⟨10797839838185512793338549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14397119784247350391118065 10797839838185512793338549)
          ·
            refine ⟨1012297484829891824375489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10797839838185512793338549 1012297484829891824375489)
            ·
              refine ⟨759223113622418868281617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1012297484829891824375489 759223113622418868281617)
              ·
                refine ⟨569417335216814151211213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 759223113622418868281617 569417335216814151211213)
                ·
                  refine ⟨213531500706305306704205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 569417335216814151211213 213531500706305306704205)
                  ·
                    rfl

theorem cell21_935665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 2, 2, 3].length) (baseStart_935665 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_935665 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_935665 prefixEnd_935665 := by exact prefixLift 935665
  have htrace : WordTrace (prefixWord ++ tailWord_935665) baseStart_935665 baseEnd_935665 := by
    simpa [prefixWord, tailWord_935665, baseEnd_935665] using wordTrace_append hprefix tailTrace_935665
  have hstable : (prefixWord ++ tailWord_935665).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935665).length < 2 ^ (prefixWord ++ tailWord_935665).sum := by decide
  have hdescent : baseEnd_935665 < baseStart_935665 := by decide
  rcases family_descends (prefixWord ++ tailWord_935665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935690 : List Nat := [3, 1, 2, 2, 1, 3, 1, 1, 7]
def baseStart_935690 : Nat := 118140960795 + 935690 * 2 ^ 59
def prefixEnd_935690 : Nat := 4983230072969 + 3 ^ 40 * 935690 * 2
def baseEnd_935690 : Nat := 213537206046910818787487

theorem tailTrace_935690 : CollatzResearch.WordTrace tailWord_935690 prefixEnd_935690 213537206046910818787487 := by
  unfold tailWord_935690
  simp only [CollatzResearch.WordTrace]
  refine ⟨8531854495040601993633131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22751611986774938649688349 8531854495040601993633131)
  ·
    refine ⟨12797781742560902990449697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8531854495040601993633131 12797781742560902990449697)
    ·
      refine ⟨9598336306920677242837273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12797781742560902990449697 9598336306920677242837273)
      ·
        refine ⟨7198752230190507932127955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9598336306920677242837273 7198752230190507932127955)
        ·
          refine ⟨10798128345285761898191933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7198752230190507932127955 10798128345285761898191933)
          ·
            refine ⟨4049298129482160711821975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10798128345285761898191933 4049298129482160711821975)
            ·
              refine ⟨6073947194223241067732963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4049298129482160711821975 6073947194223241067732963)
              ·
                refine ⟨9110920791334861601599445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6073947194223241067732963 9110920791334861601599445)
                ·
                  refine ⟨213537206046910818787487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9110920791334861601599445 213537206046910818787487)
                  ·
                    rfl

theorem cell21_935690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 7].length) (baseStart_935690 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_935690 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_935690 prefixEnd_935690 := by exact prefixLift 935690
  have htrace : WordTrace (prefixWord ++ tailWord_935690) baseStart_935690 baseEnd_935690 := by
    simpa [prefixWord, tailWord_935690, baseEnd_935690] using wordTrace_append hprefix tailTrace_935690
  have hstable : (prefixWord ++ tailWord_935690).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935690).length < 2 ^ (prefixWord ++ tailWord_935690).sum := by decide
  have hdescent : baseEnd_935690 < baseStart_935690 := by decide
  rcases family_descends (prefixWord ++ tailWord_935690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935710 : List Nat := [4, 3, 2, 2, 1, 1, 8]
def baseStart_935710 : Nat := 118140960795 + 935710 * 2 ^ 59
def prefixEnd_935710 : Nat := 4983230072969 + 3 ^ 40 * 935710 * 2
def baseEnd_935710 : Nat := 23726863368821692050457

theorem tailTrace_935710 : CollatzResearch.WordTrace tailWord_935710 prefixEnd_935710 23726863368821692050457 := by
  unfold tailWord_935710
  simp only [CollatzResearch.WordTrace]
  refine ⟨4266018430011243923782573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22752098293393300926840389 4266018430011243923782573)
  ·
    refine ⟨1599756911254216471418465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4266018430011243923782573 1599756911254216471418465)
    ·
      refine ⟨1199817683440662353563849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1599756911254216471418465 1199817683440662353563849)
      ·
        refine ⟨899863262580496765172887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1199817683440662353563849 899863262580496765172887)
        ·
          refine ⟨1349794893870745147759331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 899863262580496765172887 1349794893870745147759331)
          ·
            refine ⟨2024692340806117721638997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1349794893870745147759331 2024692340806117721638997)
            ·
              refine ⟨23726863368821692050457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2024692340806117721638997 23726863368821692050457)
              ·
                rfl

theorem cell21_935710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 8].length) (baseStart_935710 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_935710 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_935710 prefixEnd_935710 := by exact prefixLift 935710
  have htrace : WordTrace (prefixWord ++ tailWord_935710) baseStart_935710 baseEnd_935710 := by
    simpa [prefixWord, tailWord_935710, baseEnd_935710] using wordTrace_append hprefix tailTrace_935710
  have hstable : (prefixWord ++ tailWord_935710).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935710).length < 2 ^ (prefixWord ++ tailWord_935710).sum := by decide
  have hdescent : baseEnd_935710 < baseStart_935710 := by decide
  rcases family_descends (prefixWord ++ tailWord_935710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935752 : List Nat := [2, 1, 3, 1, 1, 4, 4, 5]
def baseStart_935752 : Nat := 118140960795 + 935752 * 2 ^ 59
def prefixEnd_935752 : Nat := 4983230072969 + 3 ^ 40 * 935752 * 2
def baseEnd_935752 : Nat := 71183785097204162918009

theorem tailTrace_935752 : CollatzResearch.WordTrace tailWord_935752 prefixEnd_935752 71183785097204162918009 := by
  unfold tailWord_935752
  simp only [CollatzResearch.WordTrace]
  refine ⟨17064839652968896281644755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22753119537291861708859673 17064839652968896281644755)
  ·
    refine ⟨25597259479453344422467133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17064839652968896281644755 25597259479453344422467133)
    ·
      refine ⟨9598972304795004158425175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25597259479453344422467133 9598972304795004158425175)
      ·
        refine ⟨14398458457192506237637763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9598972304795004158425175 14398458457192506237637763)
        ·
          refine ⟨21597687685788759356456645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14398458457192506237637763 21597687685788759356456645)
          ·
            refine ⟨4049566441085392379335621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21597687685788759356456645 4049566441085392379335621)
            ·
              refine ⟨759293707703511071125429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4049566441085392379335621 759293707703511071125429)
              ·
                refine ⟨71183785097204162918009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 759293707703511071125429 71183785097204162918009)
                ·
                  rfl

theorem cell21_935752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 4, 5].length) (baseStart_935752 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_935752 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_935752 prefixEnd_935752 := by exact prefixLift 935752
  have htrace : WordTrace (prefixWord ++ tailWord_935752) baseStart_935752 baseEnd_935752 := by
    simpa [prefixWord, tailWord_935752, baseEnd_935752] using wordTrace_append hprefix tailTrace_935752
  have hstable : (prefixWord ++ tailWord_935752).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935752).length < 2 ^ (prefixWord ++ tailWord_935752).sum := by decide
  have hdescent : baseEnd_935752 < baseStart_935752 := by decide
  rcases family_descends (prefixWord ++ tailWord_935752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935811 : List Nat := [1, 1, 1, 3, 4, 2, 2, 7]
def baseStart_935811 : Nat := 118140960795 + 935811 * 2 ^ 59
def prefixEnd_935811 : Nat := 4983230072969 + 3 ^ 40 * 935811 * 2
def baseEnd_935811 : Nat := 71188273298480499090191

theorem tailTrace_935811 : CollatzResearch.WordTrace tailWord_935811 prefixEnd_935811 71188273298480499090191 := by
  unfold tailWord_935811
  simp only [CollatzResearch.WordTrace]
  refine ⟨34131831212724045639687287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22754554141816030426458191 34131831212724045639687287)
  ·
    refine ⟨51197746819086068459530931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34131831212724045639687287 51197746819086068459530931)
    ·
      refine ⟨76796620228629102689296397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51197746819086068459530931 76796620228629102689296397)
      ·
        refine ⟨28798732585735913508486149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76796620228629102689296397 28798732585735913508486149)
        ·
          refine ⟨5399762359825483782841153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28798732585735913508486149 5399762359825483782841153)
          ·
            refine ⟨4049821769869112837130865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5399762359825483782841153 4049821769869112837130865)
            ·
              refine ⟨3037366327401834627848149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4049821769869112837130865 3037366327401834627848149)
              ·
                refine ⟨71188273298480499090191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3037366327401834627848149 71188273298480499090191)
                ·
                  rfl

theorem cell21_935811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 7].length) (baseStart_935811 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_935811 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_935811 prefixEnd_935811 := by exact prefixLift 935811
  have htrace : WordTrace (prefixWord ++ tailWord_935811) baseStart_935811 baseEnd_935811 := by
    simpa [prefixWord, tailWord_935811, baseEnd_935811] using wordTrace_append hprefix tailTrace_935811
  have hstable : (prefixWord ++ tailWord_935811).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935811).length < 2 ^ (prefixWord ++ tailWord_935811).sum := by decide
  have hdescent : baseEnd_935811 < baseStart_935811 := by decide
  rcases family_descends (prefixWord ++ tailWord_935811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935890 : List Nat := [3, 2, 2, 3, 2, 1, 1, 1, 6]
def baseStart_935890 : Nat := 118140960795 + 935890 * 2 ^ 59
def prefixEnd_935890 : Nat := 4983230072969 + 3 ^ 40 * 935890 * 2
def baseEnd_935890 : Nat := 213582848771754915453745

theorem tailTrace_935890 : CollatzResearch.WordTrace tailWord_935890 prefixEnd_935890 213582848771754915453745 := by
  unfold tailWord_935890
  simp only [CollatzResearch.WordTrace]
  refine ⟨8533678144859460532953281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22756475052958561421208749 8533678144859460532953281)
  ·
    refine ⟨6400258608644595399714961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8533678144859460532953281 6400258608644595399714961)
    ·
      refine ⟨4800193956483446549786221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6400258608644595399714961 4800193956483446549786221)
      ·
        refine ⟨1800072733681292456169833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4800193956483446549786221 1800072733681292456169833)
        ·
          refine ⟨1350054550260969342127375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1800072733681292456169833 1350054550260969342127375)
          ·
            refine ⟨2025081825391454013191063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1350054550260969342127375 2025081825391454013191063)
            ·
              refine ⟨3037622738087181019786595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2025081825391454013191063 3037622738087181019786595)
              ·
                refine ⟨4556434107130771529679893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3037622738087181019786595 4556434107130771529679893)
                ·
                  refine ⟨213582848771754915453745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4556434107130771529679893 213582848771754915453745)
                  ·
                    rfl

theorem cell21_935890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 6].length) (baseStart_935890 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_935890 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_935890 prefixEnd_935890 := by exact prefixLift 935890
  have htrace : WordTrace (prefixWord ++ tailWord_935890) baseStart_935890 baseEnd_935890 := by
    simpa [prefixWord, tailWord_935890, baseEnd_935890] using wordTrace_append hprefix tailTrace_935890
  have hstable : (prefixWord ++ tailWord_935890).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935890).length < 2 ^ (prefixWord ++ tailWord_935890).sum := by decide
  have hdescent : baseEnd_935890 < baseStart_935890 := by decide
  rcases family_descends (prefixWord ++ tailWord_935890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935921 : List Nat := [1, 2, 2, 2, 5, 2, 2, 5]
def baseStart_935921 : Nat := 118140960795 + 935921 * 2 ^ 59
def prefixEnd_935921 : Nat := 4983230072969 + 3 ^ 40 * 935921 * 2
def baseEnd_935921 : Nat := 71196641131368583479005

theorem tailTrace_935921 : CollatzResearch.WordTrace tailWord_935921 prefixEnd_935921 71196641131368583479005 := by
  unfold tailWord_935921
  simp only [CollatzResearch.WordTrace]
  refine ⟨34135843242325534426191617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22757228828217022950794411 34135843242325534426191617)
  ·
    refine ⟨25601882431744150819643713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34135843242325534426191617 25601882431744150819643713)
    ·
      refine ⟨19201411823808113114732785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25601882431744150819643713 19201411823808113114732785)
      ·
        refine ⟨14401058867856084836049589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19201411823808113114732785 14401058867856084836049589)
        ·
          refine ⟨1350099268861507953379649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14401058867856084836049589 1350099268861507953379649)
          ·
            refine ⟨1012574451646130965034737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1350099268861507953379649 1012574451646130965034737)
            ·
              refine ⟨759430838734598223776053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1012574451646130965034737 759430838734598223776053)
              ·
                refine ⟨71196641131368583479005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 759430838734598223776053 71196641131368583479005)
                ·
                  rfl

theorem cell21_935921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 2, 5].length) (baseStart_935921 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_935921 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_935921 prefixEnd_935921 := by exact prefixLift 935921
  have htrace : WordTrace (prefixWord ++ tailWord_935921) baseStart_935921 baseEnd_935921 := by
    simpa [prefixWord, tailWord_935921, baseEnd_935921] using wordTrace_append hprefix tailTrace_935921
  have hstable : (prefixWord ++ tailWord_935921).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935921).length < 2 ^ (prefixWord ++ tailWord_935921).sum := by decide
  have hdescent : baseEnd_935921 < baseStart_935921 := by decide
  rcases family_descends (prefixWord ++ tailWord_935921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935932 : List Nat := [2, 2, 2, 1, 2, 2, 1, 1, 8]
def baseStart_935932 : Nat := 118140960795 + 935932 * 2 ^ 59
def prefixEnd_935932 : Nat := 4983230072969 + 3 ^ 40 * 935932 * 2
def baseEnd_935932 : Nat := 213592433743972175753659

theorem tailTrace_935932 : CollatzResearch.WordTrace tailWord_935932 prefixEnd_935932 213592433743972175753659 := by
  unfold tailWord_935932
  simp only [CollatzResearch.WordTrace]
  refine ⟨17068122222642841652421025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22757496296857122203228033 17068122222642841652421025)
  ·
    refine ⟨12801091666982131239315769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17068122222642841652421025 12801091666982131239315769)
    ·
      refine ⟨9600818750236598429486827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12801091666982131239315769 9600818750236598429486827)
      ·
        refine ⟨14401228125354897644230241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9600818750236598429486827 14401228125354897644230241)
        ·
          refine ⟨10800921094016173233172681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14401228125354897644230241 10800921094016173233172681)
          ·
            refine ⟨8100690820512129924879511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10800921094016173233172681 8100690820512129924879511)
            ·
              refine ⟨12151036230768194887319267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8100690820512129924879511 12151036230768194887319267)
              ·
                refine ⟨18226554346152292330978901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12151036230768194887319267 18226554346152292330978901)
                ·
                  refine ⟨213592433743972175753659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18226554346152292330978901 213592433743972175753659)
                  ·
                    rfl

theorem cell21_935932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 8].length) (baseStart_935932 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_935932 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_935932 prefixEnd_935932 := by exact prefixLift 935932
  have htrace : WordTrace (prefixWord ++ tailWord_935932) baseStart_935932 baseEnd_935932 := by
    simpa [prefixWord, tailWord_935932, baseEnd_935932] using wordTrace_append hprefix tailTrace_935932
  have hstable : (prefixWord ++ tailWord_935932).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935932).length < 2 ^ (prefixWord ++ tailWord_935932).sum := by decide
  have hdescent : baseEnd_935932 < baseStart_935932 := by decide
  rcases family_descends (prefixWord ++ tailWord_935932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936090 : List Nat := [3, 1, 1, 5, 3, 1, 2, 5]
def baseStart_936090 : Nat := 118140960795 + 936090 * 2 ^ 59
def prefixEnd_936090 : Nat := 4983230072969 + 3 ^ 40 * 936090 * 2
def baseEnd_936090 : Nat := 71209497165533004040001

theorem tailTrace_936090 : CollatzResearch.WordTrace tailWord_936090 prefixEnd_936090 71209497165533004040001 := by
  unfold tailWord_936090
  simp only [CollatzResearch.WordTrace]
  refine ⟨8535501794678319072273431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22761338119142184192729149 8535501794678319072273431)
  ·
    refine ⟨12803252692017478608410147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8535501794678319072273431 12803252692017478608410147)
    ·
      refine ⟨19204879038026217912615221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12803252692017478608410147 19204879038026217912615221)
      ·
        refine ⟨1800457409814957929307677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19204879038026217912615221 1800457409814957929307677)
        ·
          refine ⟨675171528680609223490379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1800457409814957929307677 675171528680609223490379)
          ·
            refine ⟨1012757293020913835235569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 675171528680609223490379 1012757293020913835235569)
            ·
              refine ⟨759567969765685376426677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1012757293020913835235569 759567969765685376426677)
              ·
                refine ⟨71209497165533004040001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 759567969765685376426677 71209497165533004040001)
                ·
                  rfl

theorem cell21_936090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 2, 5].length) (baseStart_936090 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_936090 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_936090 prefixEnd_936090 := by exact prefixLift 936090
  have htrace : WordTrace (prefixWord ++ tailWord_936090) baseStart_936090 baseEnd_936090 := by
    simpa [prefixWord, tailWord_936090, baseEnd_936090] using wordTrace_append hprefix tailTrace_936090
  have hstable : (prefixWord ++ tailWord_936090).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936090).length < 2 ^ (prefixWord ++ tailWord_936090).sum := by decide
  have hdescent : baseEnd_936090 < baseStart_936090 := by decide
  rcases family_descends (prefixWord ++ tailWord_936090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936132 : List Nat := [2, 3, 3, 1, 2, 2, 2, 6]
def baseStart_936132 : Nat := 118140960795 + 936132 * 2 ^ 59
def prefixEnd_936132 : Nat := 4983230072969 + 3 ^ 40 * 936132 * 2
def baseEnd_936132 : Nat := 71212692156272090806639

theorem tailTrace_936132 : CollatzResearch.WordTrace tailWord_936132 prefixEnd_936132 71212692156272090806639 := by
  unfold tailWord_936132
  simp only [CollatzResearch.WordTrace]
  refine ⟨17071769522280558731061325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22762359363040744974748433 17071769522280558731061325)
  ·
    refine ⟨6401913570855209524147997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17071769522280558731061325 6401913570855209524147997)
    ·
      refine ⟨2400717589070703571555499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6401913570855209524147997 2400717589070703571555499)
      ·
        refine ⟨3601076383606055357333249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2400717589070703571555499 3601076383606055357333249)
        ·
          refine ⟨2700807287704541517999937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3601076383606055357333249 2700807287704541517999937)
          ·
            refine ⟨2025605465778406138499953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2700807287704541517999937 2025605465778406138499953)
            ·
              refine ⟨1519204099333804603874965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2025605465778406138499953 1519204099333804603874965)
              ·
                refine ⟨71212692156272090806639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1519204099333804603874965 71212692156272090806639)
                ·
                  rfl

theorem cell21_936132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 6].length) (baseStart_936132 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_936132 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_936132 prefixEnd_936132 := by exact prefixLift 936132
  have htrace : WordTrace (prefixWord ++ tailWord_936132) baseStart_936132 baseEnd_936132 := by
    simpa [prefixWord, tailWord_936132, baseEnd_936132] using wordTrace_append hprefix tailTrace_936132
  have hstable : (prefixWord ++ tailWord_936132).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936132).length < 2 ^ (prefixWord ++ tailWord_936132).sum := by decide
  have hdescent : baseEnd_936132 < baseStart_936132 := by decide
  rcases family_descends (prefixWord ++ tailWord_936132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936194 : List Nat := [3, 4, 1, 1, 2, 1, 2, 3, 4]
def baseStart_936194 : Nat := 118140960795 + 936194 * 2 ^ 59
def prefixEnd_936194 : Nat := 4983230072969 + 3 ^ 40 * 936194 * 2
def baseEnd_936194 : Nat := 213652225713517942386457

theorem tailTrace_936194 : CollatzResearch.WordTrace tailWord_936194 prefixEnd_936194 213652225713517942386457 := by
  unfold tailWord_936194
  simp only [CollatzResearch.WordTrace]
  refine ⟨8536450092584125512719909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22763866913557668033919757 8536450092584125512719909)
  ·
    refine ⟨1600584392359523533634983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8536450092584125512719909 1600584392359523533634983)
    ·
      refine ⟨2400876588539285300452475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1600584392359523533634983 2400876588539285300452475)
      ·
        refine ⟨3601314882808927950678713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2400876588539285300452475 3601314882808927950678713)
        ·
          refine ⟨2700986162106695963009035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3601314882808927950678713 2700986162106695963009035)
          ·
            refine ⟨4051479243160043944513553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2700986162106695963009035 4051479243160043944513553)
            ·
              refine ⟨3038609432370032958385165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4051479243160043944513553 3038609432370032958385165)
              ·
                refine ⟨1139478537138762359394437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3038609432370032958385165 1139478537138762359394437)
                ·
                  refine ⟨213652225713517942386457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1139478537138762359394437 213652225713517942386457)
                  ·
                    rfl

theorem cell21_936194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_936194 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_936194 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_936194 prefixEnd_936194 := by exact prefixLift 936194
  have htrace : WordTrace (prefixWord ++ tailWord_936194) baseStart_936194 baseEnd_936194 := by
    simpa [prefixWord, tailWord_936194, baseEnd_936194] using wordTrace_append hprefix tailTrace_936194
  have hstable : (prefixWord ++ tailWord_936194).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936194).length < 2 ^ (prefixWord ++ tailWord_936194).sum := by decide
  have hdescent : baseEnd_936194 < baseStart_936194 := by decide
  rcases family_descends (prefixWord ++ tailWord_936194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936349 : List Nat := [1, 4, 2, 1, 4, 2, 2, 2, 3]
def baseStart_936349 : Nat := 118140960795 + 936349 * 2 ^ 59
def prefixEnd_936349 : Nat := 4983230072969 + 3 ^ 40 * 936349 * 2
def baseEnd_936349 : Nat := 213687598825272117302807

theorem tailTrace_936349 : CollatzResearch.WordTrace tailWord_936349 prefixEnd_936349 213687598825272117302807 := by
  unfold tailWord_936349
  simp only [CollatzResearch.WordTrace]
  refine ⟨34151453684774963522772101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22767635789849975681848067 34151453684774963522772101)
  ·
    refine ⟨6403397565895305660519769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34151453684774963522772101 6403397565895305660519769)
    ·
      refine ⟨4802548174421479245389827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6403397565895305660519769 4802548174421479245389827)
      ·
        refine ⟨7203822261632218868084741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4802548174421479245389827 7203822261632218868084741)
        ·
          refine ⟨1350716674056041037765889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7203822261632218868084741 1350716674056041037765889)
          ·
            refine ⟨1013037505542030778324417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1350716674056041037765889 1013037505542030778324417)
            ·
              refine ⟨759778129156523083743313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1013037505542030778324417 759778129156523083743313)
              ·
                refine ⟨569833596867392312807485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 759778129156523083743313 569833596867392312807485)
                ·
                  refine ⟨213687598825272117302807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 569833596867392312807485 213687598825272117302807)
                  ·
                    rfl

theorem cell21_936349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 2, 2, 3].length) (baseStart_936349 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_936349 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_936349 prefixEnd_936349 := by exact prefixLift 936349
  have htrace : WordTrace (prefixWord ++ tailWord_936349) baseStart_936349 baseEnd_936349 := by
    simpa [prefixWord, tailWord_936349, baseEnd_936349] using wordTrace_append hprefix tailTrace_936349
  have hstable : (prefixWord ++ tailWord_936349).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936349).length < 2 ^ (prefixWord ++ tailWord_936349).sum := by decide
  have hdescent : baseEnd_936349 < baseStart_936349 := by decide
  rcases family_descends (prefixWord ++ tailWord_936349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936357 : List Nat := [1, 3, 1, 2, 1, 1, 4, 3, 5]
def baseStart_936357 : Nat := 118140960795 + 936357 * 2 ^ 59
def prefixEnd_936357 : Nat := 4983230072969 + 3 ^ 40 * 936357 * 2
def baseEnd_936357 : Nat := 213689424534265881169457

theorem tailTrace_936357 : CollatzResearch.WordTrace tailWord_936357 prefixEnd_936357 213689424534265881169457 := by
  unfold tailWord_936357
  simp only [CollatzResearch.WordTrace]
  refine ⟨34151745468745980889063325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22767830312497320592708883 34151745468745980889063325)
  ·
    refine ⟨12806904550779742833398747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34151745468745980889063325 12806904550779742833398747)
    ·
      refine ⟨19210356826169614250098121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12806904550779742833398747 19210356826169614250098121)
      ·
        refine ⟨14407767619627210687573591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19210356826169614250098121 14407767619627210687573591)
        ·
          refine ⟨21611651429440816031360387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14407767619627210687573591 21611651429440816031360387)
          ·
            refine ⟨32417477144161224047040581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21611651429440816031360387 32417477144161224047040581)
            ·
              refine ⟨6078276964530229508820109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32417477144161224047040581 6078276964530229508820109)
              ·
                refine ⟨2279353861698836065807541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6078276964530229508820109 2279353861698836065807541)
                ·
                  refine ⟨213689424534265881169457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2279353861698836065807541 213689424534265881169457)
                  ·
                    rfl

theorem cell21_936357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 3, 5].length) (baseStart_936357 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_936357 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_936357 prefixEnd_936357 := by exact prefixLift 936357
  have htrace : WordTrace (prefixWord ++ tailWord_936357) baseStart_936357 baseEnd_936357 := by
    simpa [prefixWord, tailWord_936357, baseEnd_936357] using wordTrace_append hprefix tailTrace_936357
  have hstable : (prefixWord ++ tailWord_936357).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936357).length < 2 ^ (prefixWord ++ tailWord_936357).sum := by decide
  have hdescent : baseEnd_936357 < baseStart_936357 := by decide
  rcases family_descends (prefixWord ++ tailWord_936357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936360 : List Nat := [2, 1, 6, 1, 1, 1, 3, 6]
def baseStart_936360 : Nat := 118140960795 + 936360 * 2 ^ 59
def prefixEnd_936360 : Nat := 4983230072969 + 3 ^ 40 * 936360 * 2
def baseEnd_936360 : Nat := 71230036391712847539817

theorem tailTrace_936360 : CollatzResearch.WordTrace tailWord_936360 prefixEnd_936360 71230036391712847539817 := by
  unfold tailWord_936360
  simp only [CollatzResearch.WordTrace]
  refine ⟨17075927443867556200711267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22767903258490074934281689 17075927443867556200711267)
  ·
    refine ⟨25613891165801334301066901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17075927443867556200711267 25613891165801334301066901)
    ·
      refine ⟨1200651148396937545362511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 25613891165801334301066901 1200651148396937545362511)
      ·
        refine ⟨1800976722595406318043767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1200651148396937545362511 1800976722595406318043767)
        ·
          refine ⟨2701465083893109477065651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1800976722595406318043767 2701465083893109477065651)
          ·
            refine ⟨4052197625839664215598477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2701465083893109477065651 4052197625839664215598477)
            ·
              refine ⟨1519574109689874080849429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4052197625839664215598477 1519574109689874080849429)
              ·
                refine ⟨71230036391712847539817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1519574109689874080849429 71230036391712847539817)
                ·
                  rfl

theorem cell21_936360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 6].length) (baseStart_936360 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_936360 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_936360 prefixEnd_936360 := by exact prefixLift 936360
  have htrace : WordTrace (prefixWord ++ tailWord_936360) baseStart_936360 baseEnd_936360 := by
    simpa [prefixWord, tailWord_936360, baseEnd_936360] using wordTrace_append hprefix tailTrace_936360
  have hstable : (prefixWord ++ tailWord_936360).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936360).length < 2 ^ (prefixWord ++ tailWord_936360).sum := by decide
  have hdescent : baseEnd_936360 < baseStart_936360 := by decide
  rcases family_descends (prefixWord ++ tailWord_936360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936371 : List Nat := [1, 1, 1, 2, 3, 1, 1, 1, 10]
def baseStart_936371 : Nat := 118140960795 + 936371 * 2 ^ 59
def prefixEnd_936371 : Nat := 4983230072969 + 3 ^ 40 * 936371 * 2
def baseEnd_936371 : Nat := 213692619525004967936095

theorem tailTrace_936371 : CollatzResearch.WordTrace tailWord_936371 prefixEnd_936371 213692619525004967936095 := by
  unfold tailWord_936371
  simp only [CollatzResearch.WordTrace]
  refine ⟨34152256090695261280072967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22768170727130174186715311 34152256090695261280072967)
  ·
    refine ⟨51228384136042891920109451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34152256090695261280072967 51228384136042891920109451)
    ·
      refine ⟨76842576204064337880164177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51228384136042891920109451 76842576204064337880164177)
      ·
        refine ⟨57631932153048253410123133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76842576204064337880164177 57631932153048253410123133)
        ·
          refine ⟨21611974557393095028796175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57631932153048253410123133 21611974557393095028796175)
          ·
            refine ⟨32417961836089642543194263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21611974557393095028796175 32417961836089642543194263)
            ·
              refine ⟨48626942754134463814791395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32417961836089642543194263 48626942754134463814791395)
              ·
                refine ⟨72940414131201695722187093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48626942754134463814791395 72940414131201695722187093)
                ·
                  refine ⟨213692619525004967936095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 72940414131201695722187093 213692619525004967936095)
                  ·
                    rfl

theorem cell21_936371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 10].length) (baseStart_936371 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_936371 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_936371 prefixEnd_936371 := by exact prefixLift 936371
  have htrace : WordTrace (prefixWord ++ tailWord_936371) baseStart_936371 baseEnd_936371 := by
    simpa [prefixWord, tailWord_936371, baseEnd_936371] using wordTrace_append hprefix tailTrace_936371
  have hstable : (prefixWord ++ tailWord_936371).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936371).length < 2 ^ (prefixWord ++ tailWord_936371).sum := by decide
  have hdescent : baseEnd_936371 < baseStart_936371 := by decide
  rcases family_descends (prefixWord ++ tailWord_936371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936391 : List Nat := [1, 1, 4, 1, 1, 5, 2, 3, 3]
def baseStart_936391 : Nat := 118140960795 + 936391 * 2 ^ 59
def prefixEnd_936391 : Nat := 4983230072969 + 3 ^ 40 * 936391 * 2
def baseEnd_936391 : Nat := 213697183797489377602721

theorem tailTrace_936391 : CollatzResearch.WordTrace tailWord_936391 prefixEnd_936391 213697183797489377602721 := by
  unfold tailWord_936391
  simp only [CollatzResearch.WordTrace]
  refine ⟨34152985550622804695801027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22768657033748536463867351 34152985550622804695801027)
  ·
    refine ⟨51229478325934207043701541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34152985550622804695801027 51229478325934207043701541)
    ·
      refine ⟨9605527186112663820694039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51229478325934207043701541 9605527186112663820694039)
      ·
        refine ⟨14408290779168995731041059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9605527186112663820694039 14408290779168995731041059)
        ·
          refine ⟨21612436168753493596561589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14408290779168995731041059 21612436168753493596561589)
          ·
            refine ⟨2026165890820640024677649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21612436168753493596561589 2026165890820640024677649)
            ·
              refine ⟨1519624418115480018508237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2026165890820640024677649 1519624418115480018508237)
              ·
                refine ⟨569859156793305006940589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1519624418115480018508237 569859156793305006940589)
                ·
                  refine ⟨213697183797489377602721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 569859156793305006940589 213697183797489377602721)
                  ·
                    rfl

theorem cell21_936391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 3, 3].length) (baseStart_936391 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_936391 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_936391 prefixEnd_936391 := by exact prefixLift 936391
  have htrace : WordTrace (prefixWord ++ tailWord_936391) baseStart_936391 baseEnd_936391 := by
    simpa [prefixWord, tailWord_936391, baseEnd_936391] using wordTrace_append hprefix tailTrace_936391
  have hstable : (prefixWord ++ tailWord_936391).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936391).length < 2 ^ (prefixWord ++ tailWord_936391).sum := by decide
  have hdescent : baseEnd_936391 < baseStart_936391 := by decide
  rcases family_descends (prefixWord ++ tailWord_936391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936405 : List Nat := [1, 3, 2, 3, 1, 2, 3, 2, 4]
def baseStart_936405 : Nat := 118140960795 + 936405 * 2 ^ 59
def prefixEnd_936405 : Nat := 4983230072969 + 3 ^ 40 * 936405 * 2
def baseEnd_936405 : Nat := 213700378788228464369359

theorem tailTrace_936405 : CollatzResearch.WordTrace tailWord_936405 prefixEnd_936405 213700378788228464369359 := by
  unfold tailWord_936405
  simp only [CollatzResearch.WordTrace]
  refine ⟨34153496172572085086810669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22768997448381390057873779 34153496172572085086810669)
  ·
    refine ⟨12807561064714531907554001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34153496172572085086810669 12807561064714531907554001)
    ·
      refine ⟨9605670798535898930665501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12807561064714531907554001 9605670798535898930665501)
      ·
        refine ⟨3602126549450962098999563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9605670798535898930665501 3602126549450962098999563)
        ·
          refine ⟨5403189824176443148499345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3602126549450962098999563 5403189824176443148499345)
          ·
            refine ⟨4052392368132332361374509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5403189824176443148499345 4052392368132332361374509)
            ·
              refine ⟨1519647138049624635515441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4052392368132332361374509 1519647138049624635515441)
              ·
                refine ⟨1139735353537218476636581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1519647138049624635515441 1139735353537218476636581)
                ·
                  refine ⟨213700378788228464369359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1139735353537218476636581 213700378788228464369359)
                  ·
                    rfl

theorem cell21_936405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 2, 4].length) (baseStart_936405 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_936405 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_936405 prefixEnd_936405 := by exact prefixLift 936405
  have htrace : WordTrace (prefixWord ++ tailWord_936405) baseStart_936405 baseEnd_936405 := by
    simpa [prefixWord, tailWord_936405, baseEnd_936405] using wordTrace_append hprefix tailTrace_936405
  have hstable : (prefixWord ++ tailWord_936405).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936405).length < 2 ^ (prefixWord ++ tailWord_936405).sum := by decide
  have hdescent : baseEnd_936405 < baseStart_936405 := by decide
  rcases family_descends (prefixWord ++ tailWord_936405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936433 : List Nat := [1, 2, 2, 2, 3, 1, 1, 4, 5]
def baseStart_936433 : Nat := 118140960795 + 936433 * 2 ^ 59
def prefixEnd_936433 : Nat := 4983230072969 + 3 ^ 40 * 936433 * 2
def baseEnd_936433 : Nat := 213706768769706637902635

theorem tailTrace_936433 : CollatzResearch.WordTrace tailWord_936433 prefixEnd_936433 213706768769706637902635 := by
  unfold tailWord_936433
  simp only [CollatzResearch.WordTrace]
  refine ⟨34154517416470645868829953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22769678277647097245886635 34154517416470645868829953)
  ·
    refine ⟨25615888062352984401622465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34154517416470645868829953 25615888062352984401622465)
    ·
      refine ⟨19211916046764738301216849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25615888062352984401622465 19211916046764738301216849)
      ·
        refine ⟨14408937035073553725912637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19211916046764738301216849 14408937035073553725912637)
        ·
          refine ⟨5403351388152582647217239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14408937035073553725912637 5403351388152582647217239)
          ·
            refine ⟨8105027082228873970825859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5403351388152582647217239 8105027082228873970825859)
            ·
              refine ⟨12157540623343310956238789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8105027082228873970825859 12157540623343310956238789)
              ·
                refine ⟨2279538866876870804294773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12157540623343310956238789 2279538866876870804294773)
                ·
                  refine ⟨213706768769706637902635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2279538866876870804294773 213706768769706637902635)
                  ·
                    rfl

theorem cell21_936433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 4, 5].length) (baseStart_936433 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_936433 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_936433 prefixEnd_936433 := by exact prefixLift 936433
  have htrace : WordTrace (prefixWord ++ tailWord_936433) baseStart_936433 baseEnd_936433 := by
    simpa [prefixWord, tailWord_936433, baseEnd_936433] using wordTrace_append hprefix tailTrace_936433
  have hstable : (prefixWord ++ tailWord_936433).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936433).length < 2 ^ (prefixWord ++ tailWord_936433).sum := by decide
  have hdescent : baseEnd_936433 < baseStart_936433 := by decide
  rcases family_descends (prefixWord ++ tailWord_936433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936447 : List Nat := [1, 1, 2, 2, 1, 2, 3, 1, 8]
def baseStart_936447 : Nat := 118140960795 + 936447 * 2 ^ 59
def prefixEnd_936447 : Nat := 4983230072969 + 3 ^ 40 * 936447 * 2
def baseEnd_936447 : Nat := 213709963760445724669273

theorem tailTrace_936447 : CollatzResearch.WordTrace tailWord_936447 prefixEnd_936447 213709963760445724669273 := by
  unfold tailWord_936447
  simp only [CollatzResearch.WordTrace]
  refine ⟨34155028038419926259839595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22770018692279950839893063 34155028038419926259839595)
  ·
    refine ⟨51232542057629889389759393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34155028038419926259839595 51232542057629889389759393)
    ·
      refine ⟨38424406543222417042319545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51232542057629889389759393 38424406543222417042319545)
      ·
        refine ⟨28818304907416812781739659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38424406543222417042319545 28818304907416812781739659)
        ·
          refine ⟨43227457361125219172609489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28818304907416812781739659 43227457361125219172609489)
          ·
            refine ⟨32420593020843914379457117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43227457361125219172609489 32420593020843914379457117)
            ·
              refine ⟨12157722382816467892296419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32420593020843914379457117 12157722382816467892296419)
              ·
                refine ⟨18236583574224701838444629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12157722382816467892296419 18236583574224701838444629)
                ·
                  refine ⟨213709963760445724669273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18236583574224701838444629 213709963760445724669273)
                  ·
                    rfl

theorem cell21_936447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 8].length) (baseStart_936447 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_936447 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_936447 prefixEnd_936447 := by exact prefixLift 936447
  have htrace : WordTrace (prefixWord ++ tailWord_936447) baseStart_936447 baseEnd_936447 := by
    simpa [prefixWord, tailWord_936447, baseEnd_936447] using wordTrace_append hprefix tailTrace_936447
  have hstable : (prefixWord ++ tailWord_936447).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936447).length < 2 ^ (prefixWord ++ tailWord_936447).sum := by decide
  have hdescent : baseEnd_936447 < baseStart_936447 := by decide
  rcases family_descends (prefixWord ++ tailWord_936447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936467 : List Nat := [1, 1, 1, 2, 1, 5, 5, 2, 3]
def baseStart_936467 : Nat := 118140960795 + 936467 * 2 ^ 59
def prefixEnd_936467 : Nat := 4983230072969 + 3 ^ 40 * 936467 * 2
def baseEnd_936467 : Nat := 213714528032930134335899

theorem tailTrace_936467 : CollatzResearch.WordTrace tailWord_936467 prefixEnd_936467 213714528032930134335899 := by
  unfold tailWord_936467
  simp only [CollatzResearch.WordTrace]
  refine ⟨34155757498347469675567655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22770504998898313117045103 34155757498347469675567655)
  ·
    refine ⟨51233636247521204513351483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34155757498347469675567655 51233636247521204513351483)
    ·
      refine ⟨76850454371281806770027225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51233636247521204513351483 76850454371281806770027225)
      ·
        refine ⟨57637840778461355077520419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76850454371281806770027225 57637840778461355077520419)
        ·
          refine ⟨86456761167692032616280629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57637840778461355077520419 86456761167692032616280629)
          ·
            refine ⟨8105321359471128057776309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86456761167692032616280629 8105321359471128057776309)
            ·
              refine ⟨759873877450418255416529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8105321359471128057776309 759873877450418255416529)
              ·
                refine ⟨569905408087813691562397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 759873877450418255416529 569905408087813691562397)
                ·
                  refine ⟨213714528032930134335899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 569905408087813691562397 213714528032930134335899)
                  ·
                    rfl

theorem cell21_936467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 5, 2, 3].length) (baseStart_936467 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_936467 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_936467 prefixEnd_936467 := by exact prefixLift 936467
  have htrace : WordTrace (prefixWord ++ tailWord_936467) baseStart_936467 baseEnd_936467 := by
    simpa [prefixWord, tailWord_936467, baseEnd_936467] using wordTrace_append hprefix tailTrace_936467
  have hstable : (prefixWord ++ tailWord_936467).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936467).length < 2 ^ (prefixWord ++ tailWord_936467).sum := by decide
  have hdescent : baseEnd_936467 < baseStart_936467 := by decide
  rcases family_descends (prefixWord ++ tailWord_936467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936518 : List Nat := [6, 1, 1, 1, 2, 3, 2, 2, 3]
def baseStart_936518 : Nat := 118140960795 + 936518 * 2 ^ 59
def prefixEnd_936518 : Nat := 4983230072969 + 3 ^ 40 * 936518 * 2
def baseEnd_936518 : Nat := 213726166927765378985795

theorem tailTrace_936518 : CollatzResearch.WordTrace tailWord_936518 prefixEnd_936518 213726166927765378985795 := by
  unfold tailWord_936518
  simp only [CollatzResearch.WordTrace]
  refine ⟨1067425550661334543302319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 22771745080775136923782805 1067425550661334543302319)
  ·
    refine ⟨1601138325992001814953479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1067425550661334543302319 1601138325992001814953479)
    ·
      refine ⟨2401707488988002722430219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1601138325992001814953479 2401707488988002722430219)
      ·
        refine ⟨3602561233482004083645329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2401707488988002722430219 3602561233482004083645329)
        ·
          refine ⟨2701920925111503062733997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3602561233482004083645329 2701920925111503062733997)
          ·
            refine ⟨1013220346916813648525249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2701920925111503062733997 1013220346916813648525249)
            ·
              refine ⟨759915260187610236393937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1013220346916813648525249 759915260187610236393937)
              ·
                refine ⟨569936445140707677295453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 759915260187610236393937 569936445140707677295453)
                ·
                  refine ⟨213726166927765378985795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 569936445140707677295453 213726166927765378985795)
                  ·
                    rfl

theorem cell21_936518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_936518 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_936518 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_936518 prefixEnd_936518 := by exact prefixLift 936518
  have htrace : WordTrace (prefixWord ++ tailWord_936518) baseStart_936518 baseEnd_936518 := by
    simpa [prefixWord, tailWord_936518, baseEnd_936518] using wordTrace_append hprefix tailTrace_936518
  have hstable : (prefixWord ++ tailWord_936518).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936518).length < 2 ^ (prefixWord ++ tailWord_936518).sum := by decide
  have hdescent : baseEnd_936518 < baseStart_936518 := by decide
  rcases family_descends (prefixWord ++ tailWord_936518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936523 : List Nat := [1, 1, 1, 1, 3, 1, 4, 3, 6]
def baseStart_936523 : Nat := 118140960795 + 936523 * 2 ^ 59
def prefixEnd_936523 : Nat := 4983230072969 + 3 ^ 40 * 936523 * 2
def baseEnd_936523 : Nat := 213727307995886481402451

theorem tailTrace_936523 : CollatzResearch.WordTrace tailWord_936523 prefixEnd_936523 213727307995886481402451 := by
  unfold tailWord_936523
  simp only [CollatzResearch.WordTrace]
  refine ⟨34157799986144591239606223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22771866657429727493070815 34157799986144591239606223)
  ·
    refine ⟨51236699979216886859409335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34157799986144591239606223 51236699979216886859409335)
    ·
      refine ⟨76855049968825330289114003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51236699979216886859409335 76855049968825330289114003)
      ·
        refine ⟨115282574953237995433671005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76855049968825330289114003 115282574953237995433671005)
        ·
          refine ⟨43230965607464248287626627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115282574953237995433671005 43230965607464248287626627)
          ·
            refine ⟨64846448411196372431439941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43230965607464248287626627 64846448411196372431439941)
            ·
              refine ⟨12158709077099319830894989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64846448411196372431439941 12158709077099319830894989)
              ·
                refine ⟨4559515903912244936585621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12158709077099319830894989 4559515903912244936585621)
                ·
                  refine ⟨213727307995886481402451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4559515903912244936585621 213727307995886481402451)
                  ·
                    rfl

theorem cell21_936523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 6].length) (baseStart_936523 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_936523 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_936523 prefixEnd_936523 := by exact prefixLift 936523
  have htrace : WordTrace (prefixWord ++ tailWord_936523) baseStart_936523 baseEnd_936523 := by
    simpa [prefixWord, tailWord_936523, baseEnd_936523] using wordTrace_append hprefix tailTrace_936523
  have hstable : (prefixWord ++ tailWord_936523).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936523).length < 2 ^ (prefixWord ++ tailWord_936523).sum := by decide
  have hdescent : baseEnd_936523 < baseStart_936523 := by decide
  rcases family_descends (prefixWord ++ tailWord_936523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936650 : List Nat := [3, 1, 2, 1, 4, 3, 2, 1, 4]
def baseStart_936650 : Nat := 118140960795 + 936650 * 2 ^ 59
def prefixEnd_936650 : Nat := 4983230072969 + 3 ^ 40 * 936650 * 2
def baseEnd_936650 : Nat := 213756291126162482785525

theorem tailTrace_936650 : CollatzResearch.WordTrace tailWord_936650 prefixEnd_936650 213756291126162482785525 := by
  unfold tailWord_936650
  simp only [CollatzResearch.WordTrace]
  refine ⟨8540608014171122982369851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22774954704456327952986269 8540608014171122982369851)
  ·
    refine ⟨12810912021256684473554777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8540608014171122982369851 12810912021256684473554777)
    ·
      refine ⟨9608184015942513355166083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12810912021256684473554777 9608184015942513355166083)
      ·
        refine ⟨14412276023913770032749125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9608184015942513355166083 14412276023913770032749125)
        ·
          refine ⟨2702301754483831881140461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14412276023913770032749125 2702301754483831881140461)
          ·
            refine ⟨1013363157931436955427673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2702301754483831881140461 1013363157931436955427673)
            ·
              refine ⟨760022368448577716570755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1013363157931436955427673 760022368448577716570755)
              ·
                refine ⟨1140033552672866574856133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 760022368448577716570755 1140033552672866574856133)
                ·
                  refine ⟨213756291126162482785525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1140033552672866574856133 213756291126162482785525)
                  ·
                    rfl

theorem cell21_936650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 2, 1, 4].length) (baseStart_936650 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_936650 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_936650 prefixEnd_936650 := by exact prefixLift 936650
  have htrace : WordTrace (prefixWord ++ tailWord_936650) baseStart_936650 baseEnd_936650 := by
    simpa [prefixWord, tailWord_936650, baseEnd_936650] using wordTrace_append hprefix tailTrace_936650
  have hstable : (prefixWord ++ tailWord_936650).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936650).length < 2 ^ (prefixWord ++ tailWord_936650).sum := by decide
  have hdescent : baseEnd_936650 < baseStart_936650 := by decide
  rcases family_descends (prefixWord ++ tailWord_936650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936754 : List Nat := [3, 2, 1, 1, 3, 1, 1, 6, 3]
def baseStart_936754 : Nat := 118140960795 + 936754 * 2 ^ 59
def prefixEnd_936754 : Nat := 4983230072969 + 3 ^ 40 * 936754 * 2
def baseEnd_936754 : Nat := 213780025343081413051979

theorem tailTrace_936754 : CollatzResearch.WordTrace tailWord_936754 prefixEnd_936754 213780025343081413051979 := by
  unfold tailWord_936754
  simp only [CollatzResearch.WordTrace]
  refine ⟨8541556312076929422816329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22777483498871811794176877 8541556312076929422816329)
  ·
    refine ⟨6406167234057697067112247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8541556312076929422816329 6406167234057697067112247)
    ·
      refine ⟨9609250851086545600668371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6406167234057697067112247 9609250851086545600668371)
      ·
        refine ⟨14413876276629818401002557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9609250851086545600668371 14413876276629818401002557)
        ·
          refine ⟨5405203603736181900375959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14413876276629818401002557 5405203603736181900375959)
          ·
            refine ⟨8107805405604272850563939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5405203603736181900375959 8107805405604272850563939)
            ·
              refine ⟨12161708108406409275845909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8107805405604272850563939 12161708108406409275845909)
              ·
                refine ⟨570080067581550434805277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12161708108406409275845909 570080067581550434805277)
                ·
                  refine ⟨213780025343081413051979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 570080067581550434805277 213780025343081413051979)
                  ·
                    rfl

theorem cell21_936754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 6, 3].length) (baseStart_936754 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_936754 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_936754 prefixEnd_936754 := by exact prefixLift 936754
  have htrace : WordTrace (prefixWord ++ tailWord_936754) baseStart_936754 baseEnd_936754 := by
    simpa [prefixWord, tailWord_936754, baseEnd_936754] using wordTrace_append hprefix tailTrace_936754
  have hstable : (prefixWord ++ tailWord_936754).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936754).length < 2 ^ (prefixWord ++ tailWord_936754).sum := by decide
  have hdescent : baseEnd_936754 < baseStart_936754 := by decide
  rcases family_descends (prefixWord ++ tailWord_936754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936774 : List Nat := [6, 1, 1, 2, 2, 2, 2, 5]
def baseStart_936774 : Nat := 118140960795 + 936774 * 2 ^ 59
def prefixEnd_936774 : Nat := 4983230072969 + 3 ^ 40 * 936774 * 2
def baseEnd_936774 : Nat := 71261529871855274239535

theorem tailTrace_936774 : CollatzResearch.WordTrace tailWord_936774 prefixEnd_936774 71261529871855274239535 := by
  unfold tailWord_936774
  simp only [CollatzResearch.WordTrace]
  refine ⟨1067717334632351909593543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 22777969805490174071328917 1067717334632351909593543)
  ·
    refine ⟨1601576001948527864390315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1067717334632351909593543 1601576001948527864390315)
    ·
      refine ⟨2402364002922791796585473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1601576001948527864390315 2402364002922791796585473)
      ·
        refine ⟨1801773002192093847439105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2402364002922791796585473 1801773002192093847439105)
        ·
          refine ⟨1351329751644070385579329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1801773002192093847439105 1351329751644070385579329)
          ·
            refine ⟨1013497313733052789184497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1351329751644070385579329 1013497313733052789184497)
            ·
              refine ⟨760122985299789591888373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1013497313733052789184497 760122985299789591888373)
              ·
                refine ⟨71261529871855274239535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 760122985299789591888373 71261529871855274239535)
                ·
                  rfl

theorem cell21_936774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_936774 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_936774 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_936774 prefixEnd_936774 := by exact prefixLift 936774
  have htrace : WordTrace (prefixWord ++ tailWord_936774) baseStart_936774 baseEnd_936774 := by
    simpa [prefixWord, tailWord_936774, baseEnd_936774] using wordTrace_append hprefix tailTrace_936774
  have hstable : (prefixWord ++ tailWord_936774).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936774).length < 2 ^ (prefixWord ++ tailWord_936774).sum := by decide
  have hdescent : baseEnd_936774 < baseStart_936774 := by decide
  rcases family_descends (prefixWord ++ tailWord_936774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936788 : List Nat := [2, 4, 1, 1, 4, 2, 1, 3, 3]
def baseStart_936788 : Nat := 118140960795 + 936788 * 2 ^ 59
def prefixEnd_936788 : Nat := 4983230072969 + 3 ^ 40 * 936788 * 2
def baseEnd_936788 : Nat := 213787784606304909485243

theorem tailTrace_936788 : CollatzResearch.WordTrace tailWord_936788 prefixEnd_936788 213787784606304909485243 := by
  unfold tailWord_936788
  simp only [CollatzResearch.WordTrace]
  refine ⟨17083732665092270749001509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22778310220123027665335345 17083732665092270749001509)
  ·
    refine ⟨3203199874704800765437783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17083732665092270749001509 3203199874704800765437783)
    ·
      refine ⟨4804799812057201148156675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3203199874704800765437783 4804799812057201148156675)
      ·
        refine ⟨7207199718085801722235013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4804799812057201148156675 7207199718085801722235013)
        ·
          refine ⟨1351349947141087822919065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7207199718085801722235013 1351349947141087822919065)
          ·
            refine ⟨1013512460355815867189299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1351349947141087822919065 1013512460355815867189299)
            ·
              refine ⟨1520268690533723800783949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1013512460355815867189299 1520268690533723800783949)
              ·
                refine ⟨570100758950146425293981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1520268690533723800783949 570100758950146425293981)
                ·
                  refine ⟨213787784606304909485243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 570100758950146425293981 213787784606304909485243)
                  ·
                    rfl

theorem cell21_936788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 3, 3].length) (baseStart_936788 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_936788 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_936788 prefixEnd_936788 := by exact prefixLift 936788
  have htrace : WordTrace (prefixWord ++ tailWord_936788) baseStart_936788 baseEnd_936788 := by
    simpa [prefixWord, tailWord_936788, baseEnd_936788] using wordTrace_append hprefix tailTrace_936788
  have hstable : (prefixWord ++ tailWord_936788).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936788).length < 2 ^ (prefixWord ++ tailWord_936788).sum := by decide
  have hdescent : baseEnd_936788 < baseStart_936788 := by decide
  rcases family_descends (prefixWord ++ tailWord_936788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936858 : List Nat := [3, 1, 1, 4, 3, 9]
def baseStart_936858 : Nat := 118140960795 + 936858 * 2 ^ 59
def prefixEnd_936858 : Nat := 4983230072969 + 3 ^ 40 * 936858 * 2
def baseEnd_936858 : Nat := 7918657761481494196979

theorem tailTrace_936858 : CollatzResearch.WordTrace tailWord_936858 prefixEnd_936858 7918657761481494196979 := by
  unfold tailWord_936858
  simp only [CollatzResearch.WordTrace]
  refine ⟨8542504609982735863262807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22780012293287295635367485 8542504609982735863262807)
  ·
    refine ⟨12813756914974103794894211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8542504609982735863262807 12813756914974103794894211)
    ·
      refine ⟨19220635372461155692341317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12813756914974103794894211 19220635372461155692341317)
      ·
        refine ⟨3603869132336466692313997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19220635372461155692341317 3603869132336466692313997)
        ·
          refine ⟨1351450924626175009617749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3603869132336466692313997 1351450924626175009617749)
          ·
            refine ⟨7918657761481494196979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1351450924626175009617749 7918657761481494196979)
            ·
              rfl

theorem cell21_936858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 9].length) (baseStart_936858 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_936858 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_936858 prefixEnd_936858 := by exact prefixLift 936858
  have htrace : WordTrace (prefixWord ++ tailWord_936858) baseStart_936858 baseEnd_936858 := by
    simpa [prefixWord, tailWord_936858, baseEnd_936858] using wordTrace_append hprefix tailTrace_936858
  have hstable : (prefixWord ++ tailWord_936858).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936858).length < 2 ^ (prefixWord ++ tailWord_936858).sum := by decide
  have hdescent : baseEnd_936858 < baseStart_936858 := by decide
  rcases family_descends (prefixWord ++ tailWord_936858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936889 : List Nat := [1, 2, 1, 4, 2, 3, 1, 2, 5]
def baseStart_936889 : Nat := 118140960795 + 936889 * 2 ^ 59
def prefixEnd_936889 : Nat := 4983230072969 + 3 ^ 40 * 936889 * 2
def baseEnd_936889 : Nat := 213810834182351178301703

theorem tailTrace_936889 : CollatzResearch.WordTrace tailWord_936889 prefixEnd_936889 213810834182351178301703 := by
  unfold tailWord_936889
  simp only [CollatzResearch.WordTrace]
  refine ⟨34171149102818635747429721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22780766068545757164953147 34171149102818635747429721)
  ·
    refine ⟨25628361827113976810572291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34171149102818635747429721 25628361827113976810572291)
    ·
      refine ⟨38442542740670965215858437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25628361827113976810572291 38442542740670965215858437)
      ·
        refine ⟨7207976763875805977973457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38442542740670965215858437 7207976763875805977973457)
        ·
          refine ⟨5405982572906854483480093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7207976763875805977973457 5405982572906854483480093)
          ·
            refine ⟨2027243464840070431305035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5405982572906854483480093 2027243464840070431305035)
            ·
              refine ⟨3040865197260105646957553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2027243464840070431305035 3040865197260105646957553)
              ·
                refine ⟨2280648897945079235218165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3040865197260105646957553 2280648897945079235218165)
                ·
                  refine ⟨213810834182351178301703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2280648897945079235218165 213810834182351178301703)
                  ·
                    rfl

theorem cell21_936889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 2, 5].length) (baseStart_936889 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_936889 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_936889 prefixEnd_936889 := by exact prefixLift 936889
  have htrace : WordTrace (prefixWord ++ tailWord_936889) baseStart_936889 baseEnd_936889 := by
    simpa [prefixWord, tailWord_936889, baseEnd_936889] using wordTrace_append hprefix tailTrace_936889
  have hstable : (prefixWord ++ tailWord_936889).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936889).length < 2 ^ (prefixWord ++ tailWord_936889).sum := by decide
  have hdescent : baseEnd_936889 < baseStart_936889 := by decide
  rcases family_descends (prefixWord ++ tailWord_936889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936909 : List Nat := [1, 6, 3, 1, 1, 1, 8]
def baseStart_936909 : Nat := 118140960795 + 936909 * 2 ^ 59
def prefixEnd_936909 : Nat := 4983230072969 + 3 ^ 40 * 936909 * 2
def baseEnd_936909 : Nat := 23757266494981731996481

theorem tailTrace_936909 : CollatzResearch.WordTrace tailWord_936909 prefixEnd_936909 23757266494981731996481 := by
  unfold tailWord_936909
  simp only [CollatzResearch.WordTrace]
  refine ⟨34171878562746179163157781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22781252375164119442105187 34171878562746179163157781)
  ·
    refine ⟨1601806807628727148273021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 34171878562746179163157781 1601806807628727148273021)
    ·
      refine ⟨600677552860772680602383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1601806807628727148273021 600677552860772680602383)
      ·
        refine ⟨901016329291159020903575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 600677552860772680602383 901016329291159020903575)
        ·
          refine ⟨1351524493936738531355363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 901016329291159020903575 1351524493936738531355363)
          ·
            refine ⟨2027286740905107797033045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1351524493936738531355363 2027286740905107797033045)
            ·
              refine ⟨23757266494981731996481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2027286740905107797033045 23757266494981731996481)
              ·
                rfl

theorem cell21_936909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 8].length) (baseStart_936909 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_936909 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_936909 prefixEnd_936909 := by exact prefixLift 936909
  have htrace : WordTrace (prefixWord ++ tailWord_936909) baseStart_936909 baseEnd_936909 := by
    simpa [prefixWord, tailWord_936909, baseEnd_936909] using wordTrace_append hprefix tailTrace_936909
  have hstable : (prefixWord ++ tailWord_936909).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936909).length < 2 ^ (prefixWord ++ tailWord_936909).sum := by decide
  have hdescent : baseEnd_936909 < baseStart_936909 := by decide
  rcases family_descends (prefixWord ++ tailWord_936909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936920 : List Nat := [2, 1, 2, 2, 2, 3, 3, 2, 4]
def baseStart_936920 : Nat := 118140960795 + 936920 * 2 ^ 59
def prefixEnd_936920 : Nat := 4983230072969 + 3 ^ 40 * 936920 * 2
def baseEnd_936920 : Nat := 213817908804702013284973

theorem tailTrace_936920 : CollatzResearch.WordTrace tailWord_936920 prefixEnd_936920 213817908804702013284973 := by
  unfold tailWord_936920
  simp only [CollatzResearch.WordTrace]
  refine ⟨17086139882853164020904107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22781519843804218694538809 17086139882853164020904107)
  ·
    refine ⟨25629209824279746031356161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17086139882853164020904107 25629209824279746031356161)
    ·
      refine ⟨19221907368209809523517121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25629209824279746031356161 19221907368209809523517121)
      ·
        refine ⟨14416430526157357142637841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19221907368209809523517121 14416430526157357142637841)
        ·
          refine ⟨10812322894618017856978381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14416430526157357142637841 10812322894618017856978381)
          ·
            refine ⟨4054621085481756696366893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10812322894618017856978381 4054621085481756696366893)
            ·
              refine ⟨1520482907055658761137585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4054621085481756696366893 1520482907055658761137585)
              ·
                refine ⟨1140362180291744070853189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1520482907055658761137585 1140362180291744070853189)
                ·
                  refine ⟨213817908804702013284973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1140362180291744070853189 213817908804702013284973)
                  ·
                    rfl

theorem cell21_936920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 2, 4].length) (baseStart_936920 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_936920 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_936920 prefixEnd_936920 := by exact prefixLift 936920
  have htrace : WordTrace (prefixWord ++ tailWord_936920) baseStart_936920 baseEnd_936920 := by
    simpa [prefixWord, tailWord_936920, baseEnd_936920] using wordTrace_append hprefix tailTrace_936920
  have hstable : (prefixWord ++ tailWord_936920).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936920).length < 2 ^ (prefixWord ++ tailWord_936920).sum := by decide
  have hdescent : baseEnd_936920 < baseStart_936920 := by decide
  rcases family_descends (prefixWord ++ tailWord_936920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936979 : List Nat := [1, 1, 1, 2, 1, 4, 1, 6, 4]
def baseStart_936979 : Nat := 118140960795 + 936979 * 2 ^ 59
def prefixEnd_936979 : Nat := 4983230072969 + 3 ^ 40 * 936979 * 2
def baseEnd_936979 : Nat := 213831373408531021801519

theorem tailTrace_936979 : CollatzResearch.WordTrace tailWord_936979 prefixEnd_936979 213831373408531021801519 := by
  unfold tailWord_936979
  simp only [CollatzResearch.WordTrace]
  refine ⟨34174431672492581118205991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22782954448328387412137327 34174431672492581118205991)
  ·
    refine ⟨51261647508738871677308987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34174431672492581118205991 51261647508738871677308987)
    ·
      refine ⟨76892471263108307515963481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51261647508738871677308987 76892471263108307515963481)
      ·
        refine ⟨57669353447331230636972611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76892471263108307515963481 57669353447331230636972611)
        ·
          refine ⟨86504030170996845955458917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57669353447331230636972611 86504030170996845955458917)
          ·
            refine ⟨16219505657061908616648547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86504030170996845955458917 16219505657061908616648547)
            ·
              refine ⟨24329258485592862924972821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16219505657061908616648547 24329258485592862924972821)
              ·
                refine ⟨1140433991512165449608101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24329258485592862924972821 1140433991512165449608101)
                ·
                  refine ⟨213831373408531021801519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1140433991512165449608101 213831373408531021801519)
                  ·
                    rfl

theorem cell21_936979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 6, 4].length) (baseStart_936979 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_936979 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_936979 prefixEnd_936979 := by exact prefixLift 936979
  have htrace : WordTrace (prefixWord ++ tailWord_936979) baseStart_936979 baseEnd_936979 := by
    simpa [prefixWord, tailWord_936979, baseEnd_936979] using wordTrace_append hprefix tailTrace_936979
  have hstable : (prefixWord ++ tailWord_936979).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936979).length < 2 ^ (prefixWord ++ tailWord_936979).sum := by decide
  have hdescent : baseEnd_936979 < baseStart_936979 := by decide
  rcases family_descends (prefixWord ++ tailWord_936979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937030 : List Nat := [6, 1, 1, 1, 1, 3, 2, 2, 4]
def baseStart_937030 : Nat := 118140960795 + 937030 * 2 ^ 59
def prefixEnd_937030 : Nat := 4983230072969 + 3 ^ 40 * 937030 * 2
def baseEnd_937030 : Nat := 213843012303366266451415

theorem tailTrace_937030 : CollatzResearch.WordTrace tailWord_937030 prefixEnd_937030 213843012303366266451415 := by
  unfold tailWord_937030
  simp only [CollatzResearch.WordTrace]
  refine ⟨1068009118603369275884767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 22784194530205211218875029 1068009118603369275884767)
  ·
    refine ⟨1602013677905053913827151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1068009118603369275884767 1602013677905053913827151)
    ·
      refine ⟨2403020516857580870740727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1602013677905053913827151 2403020516857580870740727)
      ·
        refine ⟨3604530775286371306111091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2403020516857580870740727 3604530775286371306111091)
        ·
          refine ⟨5406796162929556959166637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3604530775286371306111091 5406796162929556959166637)
          ·
            refine ⟨2027548561098583859687489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5406796162929556959166637 2027548561098583859687489)
            ·
              refine ⟨1520661420823937894765617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2027548561098583859687489 1520661420823937894765617)
              ·
                refine ⟨1140496065617953421074213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1520661420823937894765617 1140496065617953421074213)
                ·
                  refine ⟨213843012303366266451415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1140496065617953421074213 213843012303366266451415)
                  ·
                    rfl

theorem cell21_937030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_937030 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_937030 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_937030 prefixEnd_937030 := by exact prefixLift 937030
  have htrace : WordTrace (prefixWord ++ tailWord_937030) baseStart_937030 baseEnd_937030 := by
    simpa [prefixWord, tailWord_937030, baseEnd_937030] using wordTrace_append hprefix tailTrace_937030
  have hstable : (prefixWord ++ tailWord_937030).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937030).length < 2 ^ (prefixWord ++ tailWord_937030).sum := by decide
  have hdescent : baseEnd_937030 < baseStart_937030 := by decide
  rcases family_descends (prefixWord ++ tailWord_937030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937055 : List Nat := [1, 1, 2, 3, 1, 1, 3, 5, 4]
def baseStart_937055 : Nat := 118140960795 + 937055 * 2 ^ 59
def prefixEnd_937055 : Nat := 4983230072969 + 3 ^ 40 * 937055 * 2
def baseEnd_937055 : Nat := 213848717643971778534697

theorem tailTrace_937055 : CollatzResearch.WordTrace tailWord_937055 prefixEnd_937055 213848717643971778534697 := by
  unfold tailWord_937055
  simp only [CollatzResearch.WordTrace]
  refine ⟨34177203620217246097972619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22784802413478164065315079 34177203620217246097972619)
  ·
    refine ⟨51265805430325869146958929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34177203620217246097972619 51265805430325869146958929)
    ·
      refine ⟨38449354072744401860219197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51265805430325869146958929 38449354072744401860219197)
      ·
        refine ⟨14418507777279150697582199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38449354072744401860219197 14418507777279150697582199)
        ·
          refine ⟨21627761665918726046373299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14418507777279150697582199 21627761665918726046373299)
          ·
            refine ⟨32441642498878089069559949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21627761665918726046373299 32441642498878089069559949)
            ·
              refine ⟨12165615937079283401084981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32441642498878089069559949 12165615937079283401084981)
              ·
                refine ⟨1140526494101182818851717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12165615937079283401084981 1140526494101182818851717)
                ·
                  refine ⟨213848717643971778534697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1140526494101182818851717 213848717643971778534697)
                  ·
                    rfl

theorem cell21_937055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 5, 4].length) (baseStart_937055 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_937055 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_937055 prefixEnd_937055 := by exact prefixLift 937055
  have htrace : WordTrace (prefixWord ++ tailWord_937055) baseStart_937055 baseEnd_937055 := by
    simpa [prefixWord, tailWord_937055, baseEnd_937055] using wordTrace_append hprefix tailTrace_937055
  have hstable : (prefixWord ++ tailWord_937055).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937055).length < 2 ^ (prefixWord ++ tailWord_937055).sum := by decide
  have hdescent : baseEnd_937055 < baseStart_937055 := by decide
  rcases family_descends (prefixWord ++ tailWord_937055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937058 : List Nat := [3, 3, 2, 2, 1, 2, 1, 2, 5]
def baseStart_937058 : Nat := 118140960795 + 937058 * 2 ^ 59
def prefixEnd_937058 : Nat := 4983230072969 + 3 ^ 40 * 937058 * 2
def baseEnd_937058 : Nat := 213849402284844439984691

theorem tailTrace_937058 : CollatzResearch.WordTrace tailWord_937058 prefixEnd_937058 213849402284844439984691 := by
  unfold tailWord_937058
  simp only [CollatzResearch.WordTrace]
  refine ⟨8544328259801594402582957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22784875359470918406887885 8544328259801594402582957)
  ·
    refine ⟨3204123097425597900968609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8544328259801594402582957 3204123097425597900968609)
    ·
      refine ⟨2403092323069198425726457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3204123097425597900968609 2403092323069198425726457)
      ·
        refine ⟨1802319242301898819294843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2403092323069198425726457 1802319242301898819294843)
        ·
          refine ⟨2703478863452848228942265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1802319242301898819294843 2703478863452848228942265)
          ·
            refine ⟨2027609147589636171706699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2703478863452848228942265 2027609147589636171706699)
            ·
              refine ⟨3041413721384454257560049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2027609147589636171706699 3041413721384454257560049)
              ·
                refine ⟨2281060291038340693170037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3041413721384454257560049 2281060291038340693170037)
                ·
                  refine ⟨213849402284844439984691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2281060291038340693170037 213849402284844439984691)
                  ·
                    rfl

theorem cell21_937058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_937058 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_937058 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_937058 prefixEnd_937058 := by exact prefixLift 937058
  have htrace : WordTrace (prefixWord ++ tailWord_937058) baseStart_937058 baseEnd_937058 := by
    simpa [prefixWord, tailWord_937058, baseEnd_937058] using wordTrace_append hprefix tailTrace_937058
  have hstable : (prefixWord ++ tailWord_937058).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937058).length < 2 ^ (prefixWord ++ tailWord_937058).sum := by decide
  have hdescent : baseEnd_937058 < baseStart_937058 := by decide
  rcases family_descends (prefixWord ++ tailWord_937058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937089 : List Nat := [1, 2, 4, 2, 2, 3, 1, 2, 4]
def baseStart_937089 : Nat := 118140960795 + 937089 * 2 ^ 59
def prefixEnd_937089 : Nat := 4983230072969 + 3 ^ 40 * 937089 * 2
def baseEnd_937089 : Nat := 213856476907195274967961

theorem tailTrace_937089 : CollatzResearch.WordTrace tailWord_937089 prefixEnd_937089 213856476907195274967961 := by
  unfold tailWord_937089
  simp only [CollatzResearch.WordTrace]
  refine ⟨34178443702094069904710321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22785629134729379936473547 34178443702094069904710321)
  ·
    refine ⟨25633832776570552428532741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34178443702094069904710321 25633832776570552428532741)
    ·
      refine ⟨4806343645606978580349889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25633832776570552428532741 4806343645606978580349889)
      ·
        refine ⟨3604757734205233935262417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4806343645606978580349889 3604757734205233935262417)
        ·
          refine ⟨2703568300653925451446813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3604757734205233935262417 2703568300653925451446813)
          ·
            refine ⟨1013838112745222044292555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2703568300653925451446813 1013838112745222044292555)
            ·
              refine ⟨1520757169117833066438833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1013838112745222044292555 1520757169117833066438833)
              ·
                refine ⟨1140567876838374799829125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1520757169117833066438833 1140567876838374799829125)
                ·
                  refine ⟨213856476907195274967961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1140567876838374799829125 213856476907195274967961)
                  ·
                    rfl

theorem cell21_937089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 2, 4].length) (baseStart_937089 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_937089 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_937089 prefixEnd_937089 := by exact prefixLift 937089
  have htrace : WordTrace (prefixWord ++ tailWord_937089) baseStart_937089 baseEnd_937089 := by
    simpa [prefixWord, tailWord_937089, baseEnd_937089] using wordTrace_append hprefix tailTrace_937089
  have hstable : (prefixWord ++ tailWord_937089).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937089).length < 2 ^ (prefixWord ++ tailWord_937089).sum := by decide
  have hdescent : baseEnd_937089 < baseStart_937089 := by decide
  rcases family_descends (prefixWord ++ tailWord_937089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937145 : List Nat := [1, 2, 1, 4, 1, 3, 9]
def baseStart_937145 : Nat := 118140960795 + 937145 * 2 ^ 59
def prefixEnd_937145 : Nat := 4983230072969 + 3 ^ 40 * 937145 * 2
def baseEnd_937145 : Nat := 23763250763350180226057

theorem tailTrace_937145 : CollatzResearch.WordTrace tailWord_937145 prefixEnd_937145 23763250763350180226057 := by
  unfold tailWord_937145
  simp only [CollatzResearch.WordTrace]
  refine ⟨34180486189891191468748889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22786990793260794312499259 34180486189891191468748889)
  ·
    refine ⟨25635364642418393601561667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34180486189891191468748889 25635364642418393601561667)
    ·
      refine ⟨38453046963627590402342501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25635364642418393601561667 38453046963627590402342501)
      ·
        refine ⟨7209946305680173200439219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38453046963627590402342501 7209946305680173200439219)
        ·
          refine ⟨10814919458520259800658829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7209946305680173200439219 10814919458520259800658829)
          ·
            refine ⟨4055594796945097425247061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10814919458520259800658829 4055594796945097425247061)
            ·
              refine ⟨23763250763350180226057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4055594796945097425247061 23763250763350180226057)
              ·
                rfl

theorem cell21_937145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 9].length) (baseStart_937145 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_937145 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_937145 prefixEnd_937145 := by exact prefixLift 937145
  have htrace : WordTrace (prefixWord ++ tailWord_937145) baseStart_937145 baseEnd_937145 := by
    simpa [prefixWord, tailWord_937145, baseEnd_937145] using wordTrace_append hprefix tailTrace_937145
  have hstable : (prefixWord ++ tailWord_937145).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937145).length < 2 ^ (prefixWord ++ tailWord_937145).sum := by decide
  have hdescent : baseEnd_937145 < baseStart_937145 := by decide
  rcases family_descends (prefixWord ++ tailWord_937145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937162 : List Nat := [3, 1, 2, 1, 3, 3, 2, 6]
def baseStart_937162 : Nat := 118140960795 + 937162 * 2 ^ 59
def prefixEnd_937162 : Nat := 4983230072969 + 3 ^ 40 * 937162 * 2
def baseEnd_937162 : Nat := 71291045500587790083715

theorem tailTrace_937162 : CollatzResearch.WordTrace tailWord_937162 prefixEnd_937162 71291045500587790083715 := by
  unfold tailWord_937162
  simp only [CollatzResearch.WordTrace]
  refine ⟨8545276557707400843029435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22787404153886402248078493 8545276557707400843029435)
  ·
    refine ⟨12817914836561101264544153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8545276557707400843029435 12817914836561101264544153)
    ·
      refine ⟨9613436127420825948408115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12817914836561101264544153 9613436127420825948408115)
      ·
        refine ⟨14420154191131238922612173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9613436127420825948408115 14420154191131238922612173)
        ·
          refine ⟨5407557821674214595979565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14420154191131238922612173 5407557821674214595979565)
          ·
            refine ⟨2027834183127830473492337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5407557821674214595979565 2027834183127830473492337)
            ·
              refine ⟨1520875637345872855119253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2027834183127830473492337 1520875637345872855119253)
              ·
                refine ⟨71291045500587790083715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1520875637345872855119253 71291045500587790083715)
                ·
                  rfl

theorem cell21_937162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 6].length) (baseStart_937162 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_937162 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_937162 prefixEnd_937162 := by exact prefixLift 937162
  have htrace : WordTrace (prefixWord ++ tailWord_937162) baseStart_937162 baseEnd_937162 := by
    simpa [prefixWord, tailWord_937162, baseEnd_937162] using wordTrace_append hprefix tailTrace_937162
  have hstable : (prefixWord ++ tailWord_937162).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937162).length < 2 ^ (prefixWord ++ tailWord_937162).sum := by decide
  have hdescent : baseEnd_937162 < baseStart_937162 := by decide
  rcases family_descends (prefixWord ++ tailWord_937162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937252 : List Nat := [2, 3, 1, 3, 1, 1, 1, 2, 7]
def baseStart_937252 : Nat := 118140960795 + 937252 * 2 ^ 59
def prefixEnd_937252 : Nat := 4983230072969 + 3 ^ 40 * 937252 * 2
def baseEnd_937252 : Nat := 213893675727943213750961

theorem tailTrace_937252 : CollatzResearch.WordTrace tailWord_937252 prefixEnd_937252 213893675727943213750961 := by
  unfold tailWord_937252
  simp only [CollatzResearch.WordTrace]
  refine ⟨17092194400251774371447005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22789592533669032495262673 17092194400251774371447005)
  ·
    refine ⟨6409572900094415389292627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17092194400251774371447005 6409572900094415389292627)
    ·
      refine ⟨9614359350141623083938941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6409572900094415389292627 9614359350141623083938941)
      ·
        refine ⟨3605384756303108656477103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9614359350141623083938941 3605384756303108656477103)
        ·
          refine ⟨5408077134454662984715655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3605384756303108656477103 5408077134454662984715655)
          ·
            refine ⟨8112115701681994477073483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5408077134454662984715655 8112115701681994477073483)
            ·
              refine ⟨12168173552522991715610225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8112115701681994477073483 12168173552522991715610225)
              ·
                refine ⟨9126130164392243786707669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12168173552522991715610225 9126130164392243786707669)
                ·
                  refine ⟨213893675727943213750961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9126130164392243786707669 213893675727943213750961)
                  ·
                    rfl

theorem cell21_937252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_937252 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_937252 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_937252 prefixEnd_937252 := by exact prefixLift 937252
  have htrace : WordTrace (prefixWord ++ tailWord_937252) baseStart_937252 baseEnd_937252 := by
    simpa [prefixWord, tailWord_937252, baseEnd_937252] using wordTrace_append hprefix tailTrace_937252
  have hstable : (prefixWord ++ tailWord_937252).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937252).length < 2 ^ (prefixWord ++ tailWord_937252).sum := by decide
  have hdescent : baseEnd_937252 < baseStart_937252 := by decide
  rcases family_descends (prefixWord ++ tailWord_937252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937269 : List Nat := [1, 3, 3, 1, 2, 3, 2, 1, 5]
def baseStart_937269 : Nat := 118140960795 + 937269 * 2 ^ 59
def prefixEnd_937269 : Nat := 4983230072969 + 3 ^ 40 * 937269 * 2
def baseEnd_937269 : Nat := 213897555359554961967593

theorem tailTrace_937269 : CollatzResearch.WordTrace tailWord_937269 prefixEnd_937269 213897555359554961967593 := by
  unfold tailWord_937269
  simp only [CollatzResearch.WordTrace]
  refine ⟨34185008841441960646262861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22790005894294640430841907 34185008841441960646262861)
  ·
    refine ⟨12819378315540735242348573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34185008841441960646262861 12819378315540735242348573)
    ·
      refine ⟨4807266868327775715880715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12819378315540735242348573 4807266868327775715880715)
      ·
        refine ⟨7210900302491663573821073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4807266868327775715880715 7210900302491663573821073)
        ·
          refine ⟨5408175226868747680365805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7210900302491663573821073 5408175226868747680365805)
          ·
            refine ⟨2028065710075780380137177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5408175226868747680365805 2028065710075780380137177)
            ·
              refine ⟨1521049282556835285102883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2028065710075780380137177 1521049282556835285102883)
              ·
                refine ⟨2281573923835252927654325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1521049282556835285102883 2281573923835252927654325)
                ·
                  refine ⟨213897555359554961967593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2281573923835252927654325 213897555359554961967593)
                  ·
                    rfl

theorem cell21_937269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 1, 5].length) (baseStart_937269 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_937269 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_937269 prefixEnd_937269 := by exact prefixLift 937269
  have htrace : WordTrace (prefixWord ++ tailWord_937269) baseStart_937269 baseEnd_937269 := by
    simpa [prefixWord, tailWord_937269, baseEnd_937269] using wordTrace_append hprefix tailTrace_937269
  have hstable : (prefixWord ++ tailWord_937269).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937269).length < 2 ^ (prefixWord ++ tailWord_937269).sum := by decide
  have hdescent : baseEnd_937269 < baseStart_937269 := by decide
  rcases family_descends (prefixWord ++ tailWord_937269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937297 : List Nat := [1, 2, 2, 1, 4, 1, 3, 7]
def baseStart_937297 : Nat := 118140960795 + 937297 * 2 ^ 59
def prefixEnd_937297 : Nat := 4983230072969 + 3 ^ 40 * 937297 * 2
def baseEnd_937297 : Nat := 71301315113677711833623

theorem tailTrace_937297 : CollatzResearch.WordTrace tailWord_937297 prefixEnd_937297 71301315113677711833623 := by
  unfold tailWord_937297
  simp only [CollatzResearch.WordTrace]
  refine ⟨34186030085340521428282145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22790686723560347618854763 34186030085340521428282145)
  ·
    refine ⟨25639522564005391071211609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34186030085340521428282145 25639522564005391071211609)
    ·
      refine ⟨19229641923004043303408707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25639522564005391071211609 19229641923004043303408707)
      ·
        refine ⟨28844462884506064955113061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19229641923004043303408707 28844462884506064955113061)
        ·
          refine ⟨5408336790844887179083699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28844462884506064955113061 5408336790844887179083699)
          ·
            refine ⟨8112505186267330768625549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5408336790844887179083699 8112505186267330768625549)
            ·
              refine ⟨3042189444850249038234581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8112505186267330768625549 3042189444850249038234581)
              ·
                refine ⟨71301315113677711833623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3042189444850249038234581 71301315113677711833623)
                ·
                  rfl

theorem cell21_937297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 7].length) (baseStart_937297 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_937297 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_937297 prefixEnd_937297 := by exact prefixLift 937297
  have htrace : WordTrace (prefixWord ++ tailWord_937297) baseStart_937297 baseEnd_937297 := by
    simpa [prefixWord, tailWord_937297, baseEnd_937297] using wordTrace_append hprefix tailTrace_937297
  have hstable : (prefixWord ++ tailWord_937297).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937297).length < 2 ^ (prefixWord ++ tailWord_937297).sum := by decide
  have hdescent : baseEnd_937297 < baseStart_937297 := by decide
  rcases family_descends (prefixWord ++ tailWord_937297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937373 : List Nat := [1, 4, 2, 1, 3, 10]
def baseStart_937373 : Nat := 118140960795 + 937373 * 2 ^ 59
def prefixEnd_937373 : Nat := 4983230072969 + 3 ^ 40 * 937373 * 2
def baseEnd_937373 : Nat := 7923010725054588601261

theorem tailTrace_937373 : CollatzResearch.WordTrace tailWord_937373 prefixEnd_937373 7923010725054588601261 := by
  unfold tailWord_937373
  simp only [CollatzResearch.WordTrace]
  refine ⟨34188802033065186408048773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22792534688710124272032515 34188802033065186408048773)
  ·
    refine ⟨6410400381199722451509145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34188802033065186408048773 6410400381199722451509145)
    ·
      refine ⟨4807800285899791838631859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6410400381199722451509145 4807800285899791838631859)
      ·
        refine ⟨7211700428849687757947789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4807800285899791838631859 7211700428849687757947789)
        ·
          refine ⟨2704387660818632909230421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7211700428849687757947789 2704387660818632909230421)
          ·
            refine ⟨7923010725054588601261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2704387660818632909230421 7923010725054588601261)
            ·
              rfl

theorem cell21_937373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 10].length) (baseStart_937373 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_937373 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_937373 prefixEnd_937373 := by exact prefixLift 937373
  have htrace : WordTrace (prefixWord ++ tailWord_937373) baseStart_937373 baseEnd_937373 := by
    simpa [prefixWord, tailWord_937373, baseEnd_937373] using wordTrace_append hprefix tailTrace_937373
  have hstable : (prefixWord ++ tailWord_937373).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937373).length < 2 ^ (prefixWord ++ tailWord_937373).sum := by decide
  have hdescent : baseEnd_937373 < baseStart_937373 := by decide
  rcases family_descends (prefixWord ++ tailWord_937373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937463 : List Nat := [1, 1, 3, 1, 1, 1, 1, 5, 7]
def baseStart_937463 : Nat := 118140960795 + 937463 * 2 ^ 59
def prefixEnd_937463 : Nat := 4983230072969 + 3 ^ 40 * 937463 * 2
def baseEnd_937463 : Nat := 213941828802653735733863

theorem tailTrace_937463 : CollatzResearch.WordTrace tailWord_937463 prefixEnd_937463 213941828802653735733863 := by
  unfold tailWord_937463
  simp only [CollatzResearch.WordTrace]
  refine ⟨34192084602739131778825043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22794723068492754519216695 34192084602739131778825043)
  ·
    refine ⟨51288126904108697668237565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34192084602739131778825043 51288126904108697668237565)
    ·
      refine ⟨19233047589040761625589087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51288126904108697668237565 19233047589040761625589087)
      ·
        refine ⟨28849571383561142438383631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19233047589040761625589087 28849571383561142438383631)
        ·
          refine ⟨43274357075341713657575447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28849571383561142438383631 43274357075341713657575447)
          ·
            refine ⟨64911535613012570486363171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43274357075341713657575447 64911535613012570486363171)
            ·
              refine ⟨97367303419518855729544757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64911535613012570486363171 97367303419518855729544757)
              ·
                refine ⟨9128184695579892724644821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97367303419518855729544757 9128184695579892724644821)
                ·
                  refine ⟨213941828802653735733863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9128184695579892724644821 213941828802653735733863)
                  ·
                    rfl

theorem cell21_937463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 7].length) (baseStart_937463 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_937463 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_937463 prefixEnd_937463 := by exact prefixLift 937463
  have htrace : WordTrace (prefixWord ++ tailWord_937463) baseStart_937463 baseEnd_937463 := by
    simpa [prefixWord, tailWord_937463, baseEnd_937463] using wordTrace_append hprefix tailTrace_937463
  have hstable : (prefixWord ++ tailWord_937463).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937463).length < 2 ^ (prefixWord ++ tailWord_937463).sum := by decide
  have hdescent : baseEnd_937463 < baseStart_937463 := by decide
  rcases family_descends (prefixWord ++ tailWord_937463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937525 : List Nat := [1, 3, 3, 1, 1, 3, 2, 7]
def baseStart_937525 : Nat := 118140960795 + 937525 * 2 ^ 59
def prefixEnd_937525 : Nat := 4983230072969 + 3 ^ 40 * 937525 * 2
def baseEnd_937525 : Nat := 71318659349118468566801

theorem tailTrace_937525 : CollatzResearch.WordTrace tailWord_937525 prefixEnd_937525 71318659349118468566801 := by
  unfold tailWord_937525
  simp only [CollatzResearch.WordTrace]
  refine ⟨34194345928514516367582029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22796230619009677578388019 34194345928514516367582029)
  ·
    refine ⟨12822879723192943637843261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34194345928514516367582029 12822879723192943637843261)
    ·
      refine ⟨4808579896197353864191223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12822879723192943637843261 4808579896197353864191223)
      ·
        refine ⟨7212869844296030796286835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4808579896197353864191223 7212869844296030796286835)
        ·
          refine ⟨10819304766444046194430253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7212869844296030796286835 10819304766444046194430253)
          ·
            refine ⟨4057239287416517322911345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10819304766444046194430253 4057239287416517322911345)
            ·
              refine ⟨3042929465562387992183509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4057239287416517322911345 3042929465562387992183509)
              ·
                refine ⟨71318659349118468566801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3042929465562387992183509 71318659349118468566801)
                ·
                  rfl

theorem cell21_937525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 7].length) (baseStart_937525 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_937525 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_937525 prefixEnd_937525 := by exact prefixLift 937525
  have htrace : WordTrace (prefixWord ++ tailWord_937525) baseStart_937525 baseEnd_937525 := by
    simpa [prefixWord, tailWord_937525, baseEnd_937525] using wordTrace_append hprefix tailTrace_937525
  have hstable : (prefixWord ++ tailWord_937525).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937525).length < 2 ^ (prefixWord ++ tailWord_937525).sum := by decide
  have hdescent : baseEnd_937525 < baseStart_937525 := by decide
  rcases family_descends (prefixWord ++ tailWord_937525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937542 : List Nat := [6, 1, 1, 1, 12]
def baseStart_937542 : Nat := 118140960795 + 937542 * 2 ^ 59
def prefixEnd_937542 : Nat := 4983230072969 + 3 ^ 40 * 937542 * 2
def baseEnd_937542 : Nat := 2641479724431693258235

theorem tailTrace_937542 : CollatzResearch.WordTrace tailWord_937542 prefixEnd_937542 2641479724431693258235 := by
  unfold tailWord_937542
  simp only [CollatzResearch.WordTrace]
  refine ⟨1068592686545404008467215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 22796643979635285513967253 1068592686545404008467215)
  ·
    refine ⟨1602889029818106012700823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1068592686545404008467215 1602889029818106012700823)
    ·
      refine ⟨2404333544727159019051235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1602889029818106012700823 2404333544727159019051235)
      ·
        refine ⟨3606500317090738528576853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2404333544727159019051235 3606500317090738528576853)
        ·
          refine ⟨2641479724431693258235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 3606500317090738528576853 2641479724431693258235)
          ·
            rfl

theorem cell21_937542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 12].length) (baseStart_937542 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_937542 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_937542 prefixEnd_937542 := by exact prefixLift 937542
  have htrace : WordTrace (prefixWord ++ tailWord_937542) baseStart_937542 baseEnd_937542 := by
    simpa [prefixWord, tailWord_937542, baseEnd_937542] using wordTrace_append hprefix tailTrace_937542
  have hstable : (prefixWord ++ tailWord_937542).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937542).length < 2 ^ (prefixWord ++ tailWord_937542).sum := by decide
  have hdescent : baseEnd_937542 < baseStart_937542 := by decide
  rcases family_descends (prefixWord ++ tailWord_937542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937556 : List Nat := [2, 4, 1, 1, 1, 2, 2, 3, 5]
def baseStart_937556 : Nat := 118140960795 + 937556 * 2 ^ 59
def prefixEnd_937556 : Nat := 4983230072969 + 3 ^ 40 * 937556 * 2
def baseEnd_937556 : Nat := 213963052669706240683673

theorem tailTrace_937556 : CollatzResearch.WordTrace tailWord_937556 prefixEnd_937556 213963052669706240683673 := by
  unfold tailWord_937556
  simp only [CollatzResearch.WordTrace]
  refine ⟨17097738295701104330980261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22796984394268139107973681 17097738295701104330980261)
  ·
    refine ⟨3205825930443957062058799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17097738295701104330980261 3205825930443957062058799)
    ·
      refine ⟨4808738895665935593088199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3205825930443957062058799 4808738895665935593088199)
      ·
        refine ⟨7213108343498903389632299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4808738895665935593088199 7213108343498903389632299)
        ·
          refine ⟨10819662515248355084448449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7213108343498903389632299 10819662515248355084448449)
          ·
            refine ⟨8114746886436266313336337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10819662515248355084448449 8114746886436266313336337)
            ·
              refine ⟨6086060164827199735002253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8114746886436266313336337 6086060164827199735002253)
              ·
                refine ⟨2282272561810199900625845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6086060164827199735002253 2282272561810199900625845)
                ·
                  refine ⟨213963052669706240683673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2282272561810199900625845 213963052669706240683673)
                  ·
                    rfl

theorem cell21_937556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_937556 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_937556 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_937556 prefixEnd_937556 := by exact prefixLift 937556
  have htrace : WordTrace (prefixWord ++ tailWord_937556) baseStart_937556 baseEnd_937556 := by
    simpa [prefixWord, tailWord_937556, baseEnd_937556] using wordTrace_append hprefix tailTrace_937556
  have hstable : (prefixWord ++ tailWord_937556).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937556).length < 2 ^ (prefixWord ++ tailWord_937556).sum := by decide
  have hdescent : baseEnd_937556 < baseStart_937556 := by decide
  rcases family_descends (prefixWord ++ tailWord_937556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937590 : List Nat := [5, 1, 1, 2, 2, 1, 1, 5, 3]
def baseStart_937590 : Nat := 118140960795 + 937590 * 2 ^ 59
def prefixEnd_937590 : Nat := 4983230072969 + 3 ^ 40 * 937590 * 2
def baseEnd_937590 : Nat := 213970811932929737116937

theorem tailTrace_937590 : CollatzResearch.WordTrace tailWord_937590 prefixEnd_937590 213970811932929737116937 := by
  unfold tailWord_937590
  simp only [CollatzResearch.WordTrace]
  refine ⟨2137294792079939529293639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22797811115519354979132149 2137294792079939529293639)
  ·
    refine ⟨3205942188119909293940459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2137294792079939529293639 3205942188119909293940459)
    ·
      refine ⟨4808913282179863940910689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3205942188119909293940459 4808913282179863940910689)
      ·
        refine ⟨3606684961634897955683017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4808913282179863940910689 3606684961634897955683017)
        ·
          refine ⟨2705013721226173466762263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3606684961634897955683017 2705013721226173466762263)
          ·
            refine ⟨4057520581839260200143395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2705013721226173466762263 4057520581839260200143395)
            ·
              refine ⟨6086280872758890300215093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4057520581839260200143395 6086280872758890300215093)
              ·
                refine ⟨570588831821145965645165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6086280872758890300215093 570588831821145965645165)
                ·
                  refine ⟨213970811932929737116937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 570588831821145965645165 213970811932929737116937)
                  ·
                    rfl

theorem cell21_937590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 5, 3].length) (baseStart_937590 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_937590 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_937590 prefixEnd_937590 := by exact prefixLift 937590
  have htrace : WordTrace (prefixWord ++ tailWord_937590) baseStart_937590 baseEnd_937590 := by
    simpa [prefixWord, tailWord_937590, baseEnd_937590] using wordTrace_append hprefix tailTrace_937590
  have hstable : (prefixWord ++ tailWord_937590).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937590).length < 2 ^ (prefixWord ++ tailWord_937590).sum := by decide
  have hdescent : baseEnd_937590 < baseStart_937590 := by decide
  rcases family_descends (prefixWord ++ tailWord_937590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937601 : List Nat := [1, 2, 4, 2, 1, 3, 8]
def baseStart_937601 : Nat := 118140960795 + 937601 * 2 ^ 59
def prefixEnd_937601 : Nat := 4983230072969 + 3 ^ 40 * 937601 * 2
def baseEnd_937601 : Nat := 23774813586977351381509

theorem tailTrace_937601 : CollatzResearch.WordTrace tailWord_937601 prefixEnd_937601 23774813586977351381509 := by
  unfold tailWord_937601
  simp only [CollatzResearch.WordTrace]
  refine ⟨34197117876239181347348657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22798078584159454231565771 34197117876239181347348657)
  ·
    refine ⟨25647838407179386010511493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34197117876239181347348657 25647838407179386010511493)
    ·
      refine ⟨4808969701346134876970905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25647838407179386010511493 4808969701346134876970905)
      ·
        refine ⟨3606727276009601157728179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4808969701346134876970905 3606727276009601157728179)
        ·
          refine ⟨5410090914014401736592269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3606727276009601157728179 5410090914014401736592269)
          ·
            refine ⟨2028784092755400651222101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5410090914014401736592269 2028784092755400651222101)
            ·
              refine ⟨23774813586977351381509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2028784092755400651222101 23774813586977351381509)
              ·
                rfl

theorem cell21_937601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 8].length) (baseStart_937601 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_937601 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_937601 prefixEnd_937601 := by exact prefixLift 937601
  have htrace : WordTrace (prefixWord ++ tailWord_937601) baseStart_937601 baseEnd_937601 := by
    simpa [prefixWord, tailWord_937601, baseEnd_937601] using wordTrace_append hprefix tailTrace_937601
  have hstable : (prefixWord ++ tailWord_937601).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937601).length < 2 ^ (prefixWord ++ tailWord_937601).sum := by decide
  have hdescent : baseEnd_937601 < baseStart_937601 := by decide
  rcases family_descends (prefixWord ++ tailWord_937601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937632 : List Nat := [2, 1, 1, 4, 3, 1, 2, 2, 5]
def baseStart_937632 : Nat := 118140960795 + 937632 * 2 ^ 59
def prefixEnd_937632 : Nat := 4983230072969 + 3 ^ 40 * 937632 * 2
def baseEnd_937632 : Nat := 213980396905146997416851

theorem tailTrace_937632 : CollatzResearch.WordTrace tailWord_937632 prefixEnd_937632 213980396905146997416851 := by
  unfold tailWord_937632
  simp only [CollatzResearch.WordTrace]
  refine ⟨17099124269563436820863575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22798832359417915761151433 17099124269563436820863575)
  ·
    refine ⟨25648686404345155231295363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17099124269563436820863575 25648686404345155231295363)
    ·
      refine ⟨38473029606517732846943045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25648686404345155231295363 38473029606517732846943045)
      ·
        refine ⟨7213693051222074908801821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38473029606517732846943045 7213693051222074908801821)
        ·
          refine ⟨2705134894208278090800683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7213693051222074908801821 2705134894208278090800683)
          ·
            refine ⟨4057702341312417136201025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2705134894208278090800683 4057702341312417136201025)
            ·
              refine ⟨3043276755984312852150769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4057702341312417136201025 3043276755984312852150769)
              ·
                refine ⟨2282457566988234639113077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3043276755984312852150769 2282457566988234639113077)
                ·
                  refine ⟨213980396905146997416851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2282457566988234639113077 213980396905146997416851)
                  ·
                    rfl

theorem cell21_937632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 2, 5].length) (baseStart_937632 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_937632 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_937632 prefixEnd_937632 := by exact prefixLift 937632
  have htrace : WordTrace (prefixWord ++ tailWord_937632) baseStart_937632 baseEnd_937632 := by
    simpa [prefixWord, tailWord_937632, baseEnd_937632] using wordTrace_append hprefix tailTrace_937632
  have hstable : (prefixWord ++ tailWord_937632).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937632).length < 2 ^ (prefixWord ++ tailWord_937632).sum := by decide
  have hdescent : baseEnd_937632 < baseStart_937632 := by decide
  rcases family_descends (prefixWord ++ tailWord_937632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937784 : List Nat := [2, 1, 2, 1, 3, 4, 2, 1, 5]
def baseStart_937784 : Nat := 118140960795 + 937784 * 2 ^ 59
def prefixEnd_937784 : Nat := 4983230072969 + 3 ^ 40 * 937784 * 2
def baseEnd_937784 : Nat := 214015085376028510883207

theorem tailTrace_937784 : CollatzResearch.WordTrace tailWord_937784 prefixEnd_937784 214015085376028510883207 := by
  unfold tailWord_937784
  simp only [CollatzResearch.WordTrace]
  refine ⟨17101896217288101800630203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22802528289717469067506937 17101896217288101800630203)
  ·
    refine ⟨25652844325932152700945305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17101896217288101800630203 25652844325932152700945305)
    ·
      refine ⟨19239633244449114525708979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25652844325932152700945305 19239633244449114525708979)
      ·
        refine ⟨28859449866673671788563469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19239633244449114525708979 28859449866673671788563469)
        ·
          refine ⟨10822293700002626920711301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28859449866673671788563469 10822293700002626920711301)
          ·
            refine ⟨2029180068750492547633369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10822293700002626920711301 2029180068750492547633369)
            ·
              refine ⟨1521885051562869410725027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2029180068750492547633369 1521885051562869410725027)
              ·
                refine ⟨2282827577344304116087541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1521885051562869410725027 2282827577344304116087541)
                ·
                  refine ⟨214015085376028510883207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2282827577344304116087541 214015085376028510883207)
                  ·
                    rfl

theorem cell21_937784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 1, 5].length) (baseStart_937784 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_937784 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_937784 prefixEnd_937784 := by exact prefixLift 937784
  have htrace : WordTrace (prefixWord ++ tailWord_937784) baseStart_937784 baseEnd_937784 := by
    simpa [prefixWord, tailWord_937784, baseEnd_937784] using wordTrace_append hprefix tailTrace_937784
  have hstable : (prefixWord ++ tailWord_937784).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937784).length < 2 ^ (prefixWord ++ tailWord_937784).sum := by decide
  have hdescent : baseEnd_937784 < baseStart_937784 := by decide
  rcases family_descends (prefixWord ++ tailWord_937784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937905 : List Nat := [1, 2, 2, 4, 2, 1, 3, 6]
def baseStart_937905 : Nat := 118140960795 + 937905 * 2 ^ 59
def prefixEnd_937905 : Nat := 4983230072969 + 3 ^ 40 * 937905 * 2
def baseEnd_937905 : Nat := 71347566408186396455431

theorem tailTrace_937905 : CollatzResearch.WordTrace tailWord_937905 prefixEnd_937905 71347566408186396455431 := by
  unfold tailWord_937905
  simp only [CollatzResearch.WordTrace]
  refine ⟨34208205667137841266415169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22805470444758560844276779 34208205667137841266415169)
  ·
    refine ⟨25656154250353380949811377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34208205667137841266415169 25656154250353380949811377)
    ·
      refine ⟨19242115687765035712358533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25656154250353380949811377 19242115687765035712358533)
      ·
        refine ⟨3607896691455944196067225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19242115687765035712358533 3607896691455944196067225)
        ·
          refine ⟨2705922518591958147050419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3607896691455944196067225 2705922518591958147050419)
          ·
            refine ⟨4058883777887937220575629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2705922518591958147050419 4058883777887937220575629)
            ·
              refine ⟨1522081416707976457715861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4058883777887937220575629 1522081416707976457715861)
              ·
                refine ⟨71347566408186396455431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1522081416707976457715861 71347566408186396455431)
                ·
                  rfl

theorem cell21_937905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 6].length) (baseStart_937905 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_937905 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_937905 prefixEnd_937905 := by exact prefixLift 937905
  have htrace : WordTrace (prefixWord ++ tailWord_937905) baseStart_937905 baseEnd_937905 := by
    simpa [prefixWord, tailWord_937905, baseEnd_937905] using wordTrace_append hprefix tailTrace_937905
  have hstable : (prefixWord ++ tailWord_937905).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937905).length < 2 ^ (prefixWord ++ tailWord_937905).sum := by decide
  have hdescent : baseEnd_937905 < baseStart_937905 := by decide
  rcases family_descends (prefixWord ++ tailWord_937905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937919 : List Nat := [1, 1, 2, 2, 2, 1, 5, 2, 5]
def baseStart_937919 : Nat := 118140960795 + 937919 * 2 ^ 59
def prefixEnd_937919 : Nat := 4983230072969 + 3 ^ 40 * 937919 * 2
def baseEnd_937919 : Nat := 214045894215298276132931

theorem tailTrace_937919 : CollatzResearch.WordTrace tailWord_937919 prefixEnd_937919 214045894215298276132931 := by
  unfold tailWord_937919
  simp only [CollatzResearch.WordTrace]
  refine ⟨34208716289087121657424811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22805810859391414438283207 34208716289087121657424811)
  ·
    refine ⟨51313074433630682486137217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34208716289087121657424811 51313074433630682486137217)
    ·
      refine ⟨38484805825223011864602913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51313074433630682486137217 38484805825223011864602913)
      ·
        refine ⟨28863604368917258898452185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38484805825223011864602913 28863604368917258898452185)
        ·
          refine ⟨21647703276687944173839139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28863604368917258898452185 21647703276687944173839139)
          ·
            refine ⟨32471554915031916260758709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21647703276687944173839139 32471554915031916260758709)
            ·
              refine ⟨3044208273284242149446129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32471554915031916260758709 3044208273284242149446129)
              ·
                refine ⟨2283156204963181612084597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3044208273284242149446129 2283156204963181612084597)
                ·
                  refine ⟨214045894215298276132931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2283156204963181612084597 214045894215298276132931)
                  ·
                    rfl

theorem cell21_937919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 2, 5].length) (baseStart_937919 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_937919 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_937919 prefixEnd_937919 := by exact prefixLift 937919
  have htrace : WordTrace (prefixWord ++ tailWord_937919) baseStart_937919 baseEnd_937919 := by
    simpa [prefixWord, tailWord_937919, baseEnd_937919] using wordTrace_append hprefix tailTrace_937919
  have hstable : (prefixWord ++ tailWord_937919).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937919).length < 2 ^ (prefixWord ++ tailWord_937919).sum := by decide
  have hdescent : baseEnd_937919 < baseStart_937919 := by decide
  rcases family_descends (prefixWord ++ tailWord_937919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937936 : List Nat := [2, 1, 1, 1, 1, 2, 5, 5, 3]
def baseStart_937936 : Nat := 118140960795 + 937936 * 2 ^ 59
def prefixEnd_937936 : Nat := 4983230072969 + 3 ^ 40 * 937936 * 2
def baseEnd_937936 : Nat := 214049773846910024349563

theorem tailTrace_937936 : CollatzResearch.WordTrace tailWord_937936 prefixEnd_937936 214049773846910024349563 := by
  unfold tailWord_937936
  simp only [CollatzResearch.WordTrace]
  refine ⟨17104668165012766780396831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22806224220017022373862441 17104668165012766780396831)
  ·
    refine ⟨25657002247519150170595247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17104668165012766780396831 25657002247519150170595247)
    ·
      refine ⟨38485503371278725255892871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25657002247519150170595247 38485503371278725255892871)
      ·
        refine ⟨57728255056918087883839307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38485503371278725255892871 57728255056918087883839307)
        ·
          refine ⟨86592382585377131825758961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57728255056918087883839307 86592382585377131825758961)
          ·
            refine ⟨64944286939032848869319221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86592382585377131825758961 64944286939032848869319221)
            ·
              refine ⟨6088526900534329581498677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64944286939032848869319221 6088526900534329581498677)
              ·
                refine ⟨570799396925093398265501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6088526900534329581498677 570799396925093398265501)
                ·
                  refine ⟨214049773846910024349563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 570799396925093398265501 214049773846910024349563)
                  ·
                    rfl

theorem cell21_937936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 5, 3].length) (baseStart_937936 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_937936 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_937936 prefixEnd_937936 := by exact prefixLift 937936
  have htrace : WordTrace (prefixWord ++ tailWord_937936) baseStart_937936 baseEnd_937936 := by
    simpa [prefixWord, tailWord_937936, baseEnd_937936] using wordTrace_append hprefix tailTrace_937936
  have hstable : (prefixWord ++ tailWord_937936).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937936).length < 2 ^ (prefixWord ++ tailWord_937936).sum := by decide
  have hdescent : baseEnd_937936 < baseStart_937936 := by decide
  rcases family_descends (prefixWord ++ tailWord_937936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937942 : List Nat := [5, 2, 1, 1, 4, 1, 1, 2, 4]
def baseStart_937942 : Nat := 118140960795 + 937942 * 2 ^ 59
def prefixEnd_937942 : Nat := 4983230072969 + 3 ^ 40 * 937942 * 2
def baseEnd_937942 : Nat := 214051143128655347249551

theorem tailTrace_937942 : CollatzResearch.WordTrace tailWord_937942 prefixEnd_937942 214051143128655347249551 := by
  unfold tailWord_937942
  simp only [CollatzResearch.WordTrace]
  refine ⟨2138097198000237286594505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22806370112002531057008053 2138097198000237286594505)
  ·
    refine ⟨1603572898500177964945879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2138097198000237286594505 1603572898500177964945879)
    ·
      refine ⟨2405359347750266947418819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1603572898500177964945879 2405359347750266947418819)
      ·
        refine ⟨3608039021625400421128229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2405359347750266947418819 3608039021625400421128229)
        ·
          refine ⟨676507316554762578961543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3608039021625400421128229 676507316554762578961543)
          ·
            refine ⟨1014760974832143868442315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 676507316554762578961543 1014760974832143868442315)
            ·
              refine ⟨1522141462248215802663473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1014760974832143868442315 1522141462248215802663473)
              ·
                refine ⟨1141606096686161851997605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1522141462248215802663473 1141606096686161851997605)
                ·
                  refine ⟨214051143128655347249551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1141606096686161851997605 214051143128655347249551)
                  ·
                    rfl

theorem cell21_937942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_937942 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_937942 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_937942 prefixEnd_937942 := by exact prefixLift 937942
  have htrace : WordTrace (prefixWord ++ tailWord_937942) baseStart_937942 baseEnd_937942 := by
    simpa [prefixWord, tailWord_937942, baseEnd_937942] using wordTrace_append hprefix tailTrace_937942
  have hstable : (prefixWord ++ tailWord_937942).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937942).length < 2 ^ (prefixWord ++ tailWord_937942).sum := by decide
  have hdescent : baseEnd_937942 < baseStart_937942 := by decide
  rcases family_descends (prefixWord ++ tailWord_937942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937967 : List Nat := [1, 1, 2, 1, 4, 2, 5, 1, 4]
def baseStart_937967 : Nat := 118140960795 + 937967 * 2 ^ 59
def prefixEnd_937967 : Nat := 4983230072969 + 3 ^ 40 * 937967 * 2
def baseEnd_937967 : Nat := 214056848469260859332833

theorem tailTrace_937967 : CollatzResearch.WordTrace tailWord_937967 prefixEnd_937967 214056848469260859332833 := by
  unfold tailWord_937967
  simp only [CollatzResearch.WordTrace]
  refine ⟨34210466992913225855172155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22806977995275483903448103 34210466992913225855172155)
  ·
    refine ⟨51315700489369838782758233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34210466992913225855172155 51315700489369838782758233)
    ·
      refine ⟨38486775367027379087068675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51315700489369838782758233 38486775367027379087068675)
      ·
        refine ⟨57730163050541068630603013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38486775367027379087068675 57730163050541068630603013)
        ·
          refine ⟨10824405571976450368238065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57730163050541068630603013 10824405571976450368238065)
          ·
            refine ⟨8118304178982337776178549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10824405571976450368238065 8118304178982337776178549)
            ·
              refine ⟨761091016779594166516739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8118304178982337776178549 761091016779594166516739)
              ·
                refine ⟨1141636525169391249775109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 761091016779594166516739 1141636525169391249775109)
                ·
                  refine ⟨214056848469260859332833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1141636525169391249775109 214056848469260859332833)
                  ·
                    rfl

theorem cell21_937967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 5, 1, 4].length) (baseStart_937967 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_937967 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_937967 prefixEnd_937967 := by exact prefixLift 937967
  have htrace : WordTrace (prefixWord ++ tailWord_937967) baseStart_937967 baseEnd_937967 := by
    simpa [prefixWord, tailWord_937967, baseEnd_937967] using wordTrace_append hprefix tailTrace_937967
  have hstable : (prefixWord ++ tailWord_937967).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937967).length < 2 ^ (prefixWord ++ tailWord_937967).sum := by decide
  have hdescent : baseEnd_937967 < baseStart_937967 := by decide
  rcases family_descends (prefixWord ++ tailWord_937967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937981 : List Nat := [1, 4, 1, 1, 1, 2, 6, 5]
def baseStart_937981 : Nat := 118140960795 + 937981 * 2 ^ 59
def prefixEnd_937981 : Nat := 4983230072969 + 3 ^ 40 * 937981 * 2
def baseEnd_937981 : Nat := 71353347819999982033157

theorem tailTrace_937981 : CollatzResearch.WordTrace tailWord_937981 prefixEnd_937981 71353347819999982033157 := by
  unfold tailWord_937981
  simp only [CollatzResearch.WordTrace]
  refine ⟨34210977614862506246181797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22807318409908337497454531 34210977614862506246181797)
  ·
    refine ⟨6414558302786719921159087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34210977614862506246181797 6414558302786719921159087)
    ·
      refine ⟨9621837454180079881738631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6414558302786719921159087 9621837454180079881738631)
      ·
        refine ⟨14432756181270119822607947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9621837454180079881738631 14432756181270119822607947)
        ·
          refine ⟨21649134271905179733911921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14432756181270119822607947 21649134271905179733911921)
          ·
            refine ⟨16236850703928884800433941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21649134271905179733911921 16236850703928884800433941)
            ·
              refine ⟨761102376746666475020341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16236850703928884800433941 761102376746666475020341)
              ·
                refine ⟨71353347819999982033157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 761102376746666475020341 71353347819999982033157)
                ·
                  rfl

theorem cell21_937981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 6, 5].length) (baseStart_937981 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_937981 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_937981 prefixEnd_937981 := by exact prefixLift 937981
  have htrace : WordTrace (prefixWord ++ tailWord_937981) baseStart_937981 baseEnd_937981 := by
    simpa [prefixWord, tailWord_937981, baseEnd_937981] using wordTrace_append hprefix tailTrace_937981
  have hstable : (prefixWord ++ tailWord_937981).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937981).length < 2 ^ (prefixWord ++ tailWord_937981).sum := by decide
  have hdescent : baseEnd_937981 < baseStart_937981 := by decide
  rcases family_descends (prefixWord ++ tailWord_937981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938004 : List Nat := [2, 4, 3, 2, 1, 1, 3, 2, 3]
def baseStart_938004 : Nat := 118140960795 + 938004 * 2 ^ 59
def prefixEnd_938004 : Nat := 4983230072969 + 3 ^ 40 * 938004 * 2
def baseEnd_938004 : Nat := 214065292373357017216091

theorem tailTrace_938004 : CollatzResearch.WordTrace tailWord_938004 prefixEnd_938004 214065292373357017216091 := by
  unfold tailWord_938004
  simp only [CollatzResearch.WordTrace]
  refine ⟨17105908246889590587134533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22807877662519454116179377 17105908246889590587134533)
  ·
    refine ⟨3207357796291798235087725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17105908246889590587134533 3207357796291798235087725)
    ·
      refine ⟨1202759173609424338157897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3207357796291798235087725 1202759173609424338157897)
      ·
        refine ⟨902069380207068253618423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1202759173609424338157897 902069380207068253618423)
        ·
          refine ⟨1353104070310602380427635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 902069380207068253618423 1353104070310602380427635)
          ·
            refine ⟨2029656105465903570641453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1353104070310602380427635 2029656105465903570641453)
            ·
              refine ⟨761121039549713838990545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2029656105465903570641453 761121039549713838990545)
              ·
                refine ⟨570840779662285379242909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 761121039549713838990545 570840779662285379242909)
                ·
                  refine ⟨214065292373357017216091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 570840779662285379242909 214065292373357017216091)
                  ·
                    rfl

theorem cell21_938004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 3, 2, 3].length) (baseStart_938004 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_938004 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_938004 prefixEnd_938004 := by exact prefixLift 938004
  have htrace : WordTrace (prefixWord ++ tailWord_938004) baseStart_938004 baseEnd_938004 := by
    simpa [prefixWord, tailWord_938004, baseEnd_938004] using wordTrace_append hprefix tailTrace_938004
  have hstable : (prefixWord ++ tailWord_938004).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938004).length < 2 ^ (prefixWord ++ tailWord_938004).sum := by decide
  have hdescent : baseEnd_938004 < baseStart_938004 := by decide
  rcases family_descends (prefixWord ++ tailWord_938004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938012 : List Nat := [2, 2, 3, 1, 3, 1, 3, 1, 5]
def baseStart_938012 : Nat := 118140960795 + 938012 * 2 ^ 59
def prefixEnd_938012 : Nat := 4983230072969 + 3 ^ 40 * 938012 * 2
def baseEnd_938012 : Nat := 214067118082350781082741

theorem tailTrace_938012 : CollatzResearch.WordTrace tailWord_938012 prefixEnd_938012 214067118082350781082741 := by
  unfold tailWord_938012
  simp only [CollatzResearch.WordTrace]
  refine ⟨17106054138875099270280145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22808072185166799027040193 17106054138875099270280145)
  ·
    refine ⟨12829540604156324452710109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17106054138875099270280145 12829540604156324452710109)
    ·
      refine ⟨4811077726558621669766291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12829540604156324452710109 4811077726558621669766291)
      ·
        refine ⟨7216616589837932504649437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4811077726558621669766291 7216616589837932504649437)
        ·
          refine ⟨2706231221189224689243539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7216616589837932504649437 2706231221189224689243539)
          ·
            refine ⟨4059346831783837033865309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2706231221189224689243539 4059346831783837033865309)
            ·
              refine ⟨1522255061918938887699491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4059346831783837033865309 1522255061918938887699491)
              ·
                refine ⟨2283382592878408331549237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1522255061918938887699491 2283382592878408331549237)
                ·
                  refine ⟨214067118082350781082741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2283382592878408331549237 214067118082350781082741)
                  ·
                    rfl

theorem cell21_938012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 1, 5].length) (baseStart_938012 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_938012 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_938012 prefixEnd_938012 := by exact prefixLift 938012
  have htrace : WordTrace (prefixWord ++ tailWord_938012) baseStart_938012 baseEnd_938012 := by
    simpa [prefixWord, tailWord_938012, baseEnd_938012] using wordTrace_append hprefix tailTrace_938012
  have hstable : (prefixWord ++ tailWord_938012).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938012).length < 2 ^ (prefixWord ++ tailWord_938012).sum := by decide
  have hdescent : baseEnd_938012 < baseStart_938012 := by decide
  rcases family_descends (prefixWord ++ tailWord_938012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938105 : List Nat := [1, 2, 1, 3, 4, 2, 2, 3, 3]
def baseStart_938105 : Nat := 118140960795 + 938105 * 2 ^ 59
def prefixEnd_938105 : Nat := 4983230072969 + 3 ^ 40 * 938105 * 2
def baseEnd_938105 : Nat := 214088341949403286032551

theorem tailTrace_938105 : CollatzResearch.WordTrace tailWord_938105 prefixEnd_938105 214088341949403286032551 := by
  unfold tailWord_938105
  simp only [CollatzResearch.WordTrace]
  refine ⟨34215500266413275423695769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22810333510942183615797179 34215500266413275423695769)
  ·
    refine ⟨25661625199809956567771827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34215500266413275423695769 25661625199809956567771827)
    ·
      refine ⟨38492437799714934851657741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25661625199809956567771827 38492437799714934851657741)
      ·
        refine ⟨14434664174893100569371653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38492437799714934851657741 14434664174893100569371653)
        ·
          refine ⟨2706499532792456356757185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14434664174893100569371653 2706499532792456356757185)
          ·
            refine ⟨2029874649594342267567889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2706499532792456356757185 2029874649594342267567889)
            ·
              refine ⟨1522405987195756700675917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2029874649594342267567889 1522405987195756700675917)
              ·
                refine ⟨570902245198408762753469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1522405987195756700675917 570902245198408762753469)
                ·
                  refine ⟨214088341949403286032551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 570902245198408762753469 214088341949403286032551)
                  ·
                    rfl

theorem cell21_938105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 3, 3].length) (baseStart_938105 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_938105 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_938105 prefixEnd_938105 := by exact prefixLift 938105
  have htrace : WordTrace (prefixWord ++ tailWord_938105) baseStart_938105 baseEnd_938105 := by
    simpa [prefixWord, tailWord_938105, baseEnd_938105] using wordTrace_append hprefix tailTrace_938105
  have hstable : (prefixWord ++ tailWord_938105).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938105).length < 2 ^ (prefixWord ++ tailWord_938105).sum := by decide
  have hdescent : baseEnd_938105 < baseStart_938105 := by decide
  rcases family_descends (prefixWord ++ tailWord_938105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938116 : List Nat := [2, 3, 2, 1, 2, 1, 10]
def baseStart_938116 : Nat := 118140960795 + 938116 * 2 ^ 59
def prefixEnd_938116 : Nat := 4983230072969 + 3 ^ 40 * 938116 * 2
def baseEnd_938116 : Nat := 23787872477696634594355

theorem tailTrace_938116 : CollatzResearch.WordTrace tailWord_938116 prefixEnd_938116 23787872477696634594355 := by
  unfold tailWord_938116
  simp only [CollatzResearch.WordTrace]
  refine ⟨17107950734686712151173101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22810600979582282868230801 17107950734686712151173101)
  ·
    refine ⟨6415481525507517056689913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17107950734686712151173101 6415481525507517056689913)
    ·
      refine ⟨4811611144130637792517435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6415481525507517056689913 4811611144130637792517435)
      ·
        refine ⟨7217416716195956688776153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4811611144130637792517435 7217416716195956688776153)
        ·
          refine ⟨5413062537146967516582115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7217416716195956688776153 5413062537146967516582115)
          ·
            refine ⟨8119593805720451274873173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5413062537146967516582115 8119593805720451274873173)
            ·
              refine ⟨23787872477696634594355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8119593805720451274873173 23787872477696634594355)
              ·
                rfl

theorem cell21_938116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 10].length) (baseStart_938116 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_938116 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_938116 prefixEnd_938116 := by exact prefixLift 938116
  have htrace : WordTrace (prefixWord ++ tailWord_938116) baseStart_938116 baseEnd_938116 := by
    simpa [prefixWord, tailWord_938116, baseEnd_938116] using wordTrace_append hprefix tailTrace_938116
  have hstable : (prefixWord ++ tailWord_938116).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938116).length < 2 ^ (prefixWord ++ tailWord_938116).sum := by decide
  have hdescent : baseEnd_938116 < baseStart_938116 := by decide
  rcases family_descends (prefixWord ++ tailWord_938116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938136 : List Nat := [2, 1, 2, 4, 3, 1, 3, 1, 4]
def baseStart_938136 : Nat := 118140960795 + 938136 * 2 ^ 59
def prefixEnd_938136 : Nat := 4983230072969 + 3 ^ 40 * 938136 * 2
def baseEnd_938136 : Nat := 214095416571754121015821

theorem tailTrace_938136 : CollatzResearch.WordTrace tailWord_938136 prefixEnd_938136 214095416571754121015821 := by
  unfold tailWord_938136
  simp only [CollatzResearch.WordTrace]
  refine ⟨17108315464650483859037131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22811087286200645145382841 17108315464650483859037131)
  ·
    refine ⟨25662473196975725788555697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17108315464650483859037131 25662473196975725788555697)
    ·
      refine ⟨19246854897731794341416773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25662473196975725788555697 19246854897731794341416773)
      ·
        refine ⟨3608785293324711439015645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19246854897731794341416773 3608785293324711439015645)
        ·
          refine ⟨1353294484996766789630867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3608785293324711439015645 1353294484996766789630867)
          ·
            refine ⟨2029941727495150184446301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1353294484996766789630867 2029941727495150184446301)
            ·
              refine ⟨761228147810681319167363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2029941727495150184446301 761228147810681319167363)
              ·
                refine ⟨1141842221716021978751045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 761228147810681319167363 1141842221716021978751045)
                ·
                  refine ⟨214095416571754121015821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1141842221716021978751045 214095416571754121015821)
                  ·
                    rfl

theorem cell21_938136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 3, 1, 4].length) (baseStart_938136 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_938136 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_938136 prefixEnd_938136 := by exact prefixLift 938136
  have htrace : WordTrace (prefixWord ++ tailWord_938136) baseStart_938136 baseEnd_938136 := by
    simpa [prefixWord, tailWord_938136, baseEnd_938136] using wordTrace_append hprefix tailTrace_938136
  have hstable : (prefixWord ++ tailWord_938136).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938136).length < 2 ^ (prefixWord ++ tailWord_938136).sum := by decide
  have hdescent : baseEnd_938136 < baseStart_938136 := by decide
  rcases family_descends (prefixWord ++ tailWord_938136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938237 : List Nat := [1, 4, 1, 1, 1, 1, 1, 5, 6]
def baseStart_938237 : Nat := 118140960795 + 938237 * 2 ^ 59
def prefixEnd_938237 : Nat := 4983230072969 + 3 ^ 40 * 938237 * 2
def baseEnd_938237 : Nat := 214118466147800389832281

theorem tailTrace_938237 : CollatzResearch.WordTrace tailWord_938237 prefixEnd_938237 214118466147800389832281 := by
  unfold tailWord_938237
  simp only [CollatzResearch.WordTrace]
  refine ⟨34220314701935061967500965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22813543134623374645000643 34220314701935061967500965)
  ·
    refine ⟨6416309006612824118906431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34220314701935061967500965 6416309006612824118906431)
    ·
      refine ⟨9624463509919236178359647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6416309006612824118906431 9624463509919236178359647)
      ·
        refine ⟨14436695264878854267539471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9624463509919236178359647 14436695264878854267539471)
        ·
          refine ⟨21655042897318281401309207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14436695264878854267539471 21655042897318281401309207)
          ·
            refine ⟨32482564345977422101963811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21655042897318281401309207 32482564345977422101963811)
            ·
              refine ⟨48723846518966133152945717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32482564345977422101963811 48723846518966133152945717)
              ·
                refine ⟨4567860611153074983088661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48723846518966133152945717 4567860611153074983088661)
                ·
                  refine ⟨214118466147800389832281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4567860611153074983088661 214118466147800389832281)
                  ·
                    rfl

theorem cell21_938237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_938237 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_938237 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_938237 prefixEnd_938237 := by exact prefixLift 938237
  have htrace : WordTrace (prefixWord ++ tailWord_938237) baseStart_938237 baseEnd_938237 := by
    simpa [prefixWord, tailWord_938237, baseEnd_938237] using wordTrace_append hprefix tailTrace_938237
  have hstable : (prefixWord ++ tailWord_938237).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938237).length < 2 ^ (prefixWord ++ tailWord_938237).sum := by decide
  have hdescent : baseEnd_938237 < baseStart_938237 := by decide
  rcases family_descends (prefixWord ++ tailWord_938237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938254 : List Nat := [4, 1, 1, 2, 1, 2, 1, 5, 4]
def baseStart_938254 : Nat := 118140960795 + 938254 * 2 ^ 59
def prefixEnd_938254 : Nat := 4983230072969 + 3 ^ 40 * 938254 * 2
def baseEnd_938254 : Nat := 214122345779412138048913

theorem tailTrace_938254 : CollatzResearch.WordTrace tailWord_938254 prefixEnd_938254 214122345779412138048913 := by
  unfold tailWord_938254
  simp only [CollatzResearch.WordTrace]
  refine ⟨4277616842859184233858727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22813956495248982580579877 4277616842859184233858727)
  ·
    refine ⟨6416425264288776350788091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4277616842859184233858727 6416425264288776350788091)
    ·
      refine ⟨9624637896433164526182137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6416425264288776350788091 9624637896433164526182137)
      ·
        refine ⟨7218478422324873394636603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9624637896433164526182137 7218478422324873394636603)
        ·
          refine ⟨10827717633487310091954905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7218478422324873394636603 10827717633487310091954905)
          ·
            refine ⟨8120788225115482568966179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10827717633487310091954905 8120788225115482568966179)
            ·
              refine ⟨12181182337673223853449269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8120788225115482568966179 12181182337673223853449269)
              ·
                refine ⟨1141985844156864736260869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12181182337673223853449269 1141985844156864736260869)
                ·
                  refine ⟨214122345779412138048913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1141985844156864736260869 214122345779412138048913)
                  ·
                    rfl

theorem cell21_938254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 5, 4].length) (baseStart_938254 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_938254 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_938254 prefixEnd_938254 := by exact prefixLift 938254
  have htrace : WordTrace (prefixWord ++ tailWord_938254) baseStart_938254 baseEnd_938254 := by
    simpa [prefixWord, tailWord_938254, baseEnd_938254] using wordTrace_append hprefix tailTrace_938254
  have hstable : (prefixWord ++ tailWord_938254).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938254).length < 2 ^ (prefixWord ++ tailWord_938254).sum := by decide
  have hdescent : baseEnd_938254 < baseStart_938254 := by decide
  rcases family_descends (prefixWord ++ tailWord_938254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938344 : List Nat := [2, 1, 4, 2, 2, 1, 9]
def baseStart_938344 : Nat := 118140960795 + 938344 * 2 ^ 59
def prefixEnd_938344 : Nat := 4983230072969 + 3 ^ 40 * 938344 * 2
def baseEnd_938344 : Nat := 23793653889510220172081

theorem tailTrace_938344 : CollatzResearch.WordTrace tailWord_938344 prefixEnd_938344 23793653889510220172081 := by
  unfold tailWord_938344
  simp only [CollatzResearch.WordTrace]
  refine ⟨17112108656273709620823043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22816144875031612827764057 17112108656273709620823043)
  ·
    refine ⟨25668162984410564431234565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17112108656273709620823043 25668162984410564431234565)
    ·
      refine ⟨4812780559576980830856481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25668162984410564431234565 4812780559576980830856481)
      ·
        refine ⟨3609585419682735623142361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4812780559576980830856481 3609585419682735623142361)
        ·
          refine ⟨2707189064762051717356771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3609585419682735623142361 2707189064762051717356771)
          ·
            refine ⟨4060783597143077576035157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2707189064762051717356771 4060783597143077576035157)
            ·
              refine ⟨23793653889510220172081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4060783597143077576035157 23793653889510220172081)
              ·
                rfl

theorem cell21_938344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 9].length) (baseStart_938344 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_938344 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_938344 prefixEnd_938344 := by exact prefixLift 938344
  have htrace : WordTrace (prefixWord ++ tailWord_938344) baseStart_938344 baseEnd_938344 := by
    simpa [prefixWord, tailWord_938344, baseEnd_938344] using wordTrace_append hprefix tailTrace_938344
  have hstable : (prefixWord ++ tailWord_938344).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938344).length < 2 ^ (prefixWord ++ tailWord_938344).sum := by decide
  have hdescent : baseEnd_938344 < baseStart_938344 := by decide
  rcases family_descends (prefixWord ++ tailWord_938344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938403 : List Nat := [1, 1, 1, 4, 1, 13]
def baseStart_938403 : Nat := 118140960795 + 938403 * 2 ^ 59
def prefixEnd_938403 : Nat := 4983230072969 + 3 ^ 40 * 938403 * 2
def baseEnd_938403 : Nat := 7931716652200777409825

theorem tailTrace_938403 : CollatzResearch.WordTrace tailWord_938403 prefixEnd_938403 7931716652200777409825 := by
  unfold tailWord_938403
  simp only [CollatzResearch.WordTrace]
  refine ⟨34226369219333672318043863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22817579479555781545362575 34226369219333672318043863)
  ·
    refine ⟨51339553829000508477065795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34226369219333672318043863 51339553829000508477065795)
    ·
      refine ⟨77009330743500762715598693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51339553829000508477065795 77009330743500762715598693)
      ·
        refine ⟨14439249514406393009174755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77009330743500762715598693 14439249514406393009174755)
        ·
          refine ⟨21658874271609589513762133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14439249514406393009174755 21658874271609589513762133)
          ·
            refine ⟨7931716652200777409825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 21658874271609589513762133 7931716652200777409825)
            ·
              rfl

theorem cell21_938403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 13].length) (baseStart_938403 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_938403 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_938403 prefixEnd_938403 := by exact prefixLift 938403
  have htrace : WordTrace (prefixWord ++ tailWord_938403) baseStart_938403 baseEnd_938403 := by
    simpa [prefixWord, tailWord_938403, baseEnd_938403] using wordTrace_append hprefix tailTrace_938403
  have hstable : (prefixWord ++ tailWord_938403).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938403).length < 2 ^ (prefixWord ++ tailWord_938403).sum := by decide
  have hdescent : baseEnd_938403 < baseStart_938403 := by decide
  rcases family_descends (prefixWord ++ tailWord_938403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938465 : List Nat := [1, 2, 3, 1, 2, 2, 3, 1, 6]
def baseStart_938465 : Nat := 118140960795 + 938465 * 2 ^ 59
def prefixEnd_938465 : Nat := 4983230072969 + 3 ^ 40 * 938465 * 2
def baseEnd_938465 : Nat := 214170498854122660031815

theorem tailTrace_938465 : CollatzResearch.WordTrace tailWord_938465 prefixEnd_938465 214170498854122660031815 := by
  unfold tailWord_938465
  simp only [CollatzResearch.WordTrace]
  refine ⟨34228630545109056906800849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22819087030072704604533899 34228630545109056906800849)
  ·
    refine ⟨25671472908831792680100637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34228630545109056906800849 25671472908831792680100637)
    ·
      refine ⟨9626802340811922255037739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25671472908831792680100637 9626802340811922255037739)
      ·
        refine ⟨14440203511217883382556609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9626802340811922255037739 14440203511217883382556609)
        ·
          refine ⟨10830152633413412536917457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14440203511217883382556609 10830152633413412536917457)
          ·
            refine ⟨8122614475060059402688093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10830152633413412536917457 8122614475060059402688093)
            ·
              refine ⟨3045980428147522276008035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8122614475060059402688093 3045980428147522276008035)
              ·
                refine ⟨4568970642221283414012053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3045980428147522276008035 4568970642221283414012053)
                ·
                  refine ⟨214170498854122660031815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4568970642221283414012053 214170498854122660031815)
                  ·
                    rfl

theorem cell21_938465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 6].length) (baseStart_938465 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_938465 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_938465 prefixEnd_938465 := by exact prefixLift 938465
  have htrace : WordTrace (prefixWord ++ tailWord_938465) baseStart_938465 baseEnd_938465 := by
    simpa [prefixWord, tailWord_938465, baseEnd_938465] using wordTrace_append hprefix tailTrace_938465
  have hstable : (prefixWord ++ tailWord_938465).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938465).length < 2 ^ (prefixWord ++ tailWord_938465).sum := by decide
  have hdescent : baseEnd_938465 < baseStart_938465 := by decide
  rcases family_descends (prefixWord ++ tailWord_938465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938479 : List Nat := [1, 1, 2, 1, 4, 1, 1, 10]
def baseStart_938479 : Nat := 118140960795 + 938479 * 2 ^ 59
def prefixEnd_938479 : Nat := 4983230072969 + 3 ^ 40 * 938479 * 2
def baseEnd_938479 : Nat := 71391231281620582266151

theorem tailTrace_938479 : CollatzResearch.WordTrace tailWord_938479 prefixEnd_938479 71391231281620582266151 := by
  unfold tailWord_938479
  simp only [CollatzResearch.WordTrace]
  refine ⟨34229141167058337297810491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22819427444705558198540327 34229141167058337297810491)
  ·
    refine ⟨51343711750587505946715737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34229141167058337297810491 51343711750587505946715737)
    ·
      refine ⟨38507783812940629460036803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51343711750587505946715737 38507783812940629460036803)
      ·
        refine ⟨57761675719410944190055205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38507783812940629460036803 57761675719410944190055205)
        ·
          refine ⟨10830314197389552035635351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57761675719410944190055205 10830314197389552035635351)
          ·
            refine ⟨16245471296084328053453027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10830314197389552035635351 16245471296084328053453027)
            ·
              refine ⟨24368206944126492080179541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16245471296084328053453027 24368206944126492080179541)
              ·
                refine ⟨71391231281620582266151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 24368206944126492080179541 71391231281620582266151)
                ·
                  rfl

theorem cell21_938479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 10].length) (baseStart_938479 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_938479 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_938479 prefixEnd_938479 := by exact prefixLift 938479
  have htrace : WordTrace (prefixWord ++ tailWord_938479) baseStart_938479 baseEnd_938479 := by
    simpa [prefixWord, tailWord_938479, baseEnd_938479] using wordTrace_append hprefix tailTrace_938479
  have hstable : (prefixWord ++ tailWord_938479).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938479).length < 2 ^ (prefixWord ++ tailWord_938479).sum := by decide
  have hdescent : baseEnd_938479 < baseStart_938479 := by decide
  rcases family_descends (prefixWord ++ tailWord_938479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938626 : List Nat := [3, 4, 3, 1, 1, 2, 1, 2, 4]
def baseStart_938626 : Nat := 118140960795 + 938626 * 2 ^ 59
def prefixEnd_938626 : Nat := 4983230072969 + 3 ^ 40 * 938626 * 2
def baseEnd_938626 : Nat := 214207241247622157848153

theorem tailTrace_938626 : CollatzResearch.WordTrace tailWord_938626 prefixEnd_938626 214207241247622157848153 := by
  unfold tailWord_938626
  simp only [CollatzResearch.WordTrace]
  refine ⟨8558625674381445350852933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22823001798350520935607821 8558625674381445350852933)
  ·
    refine ⟨1604742313946521003284925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8558625674381445350852933 1604742313946521003284925)
    ·
      refine ⟨601778367729945376231847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1604742313946521003284925 601778367729945376231847)
      ·
        refine ⟨902667551594918064347771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 601778367729945376231847 902667551594918064347771)
        ·
          refine ⟨1354001327392377096521657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 902667551594918064347771 1354001327392377096521657)
          ·
            refine ⟨1015500995544282822391243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1354001327392377096521657 1015500995544282822391243)
            ·
              refine ⟨1523251493316424233586865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1015500995544282822391243 1523251493316424233586865)
              ·
                refine ⟨1142438619987318175190149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1523251493316424233586865 1142438619987318175190149)
                ·
                  refine ⟨214207241247622157848153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1142438619987318175190149 214207241247622157848153)
                  ·
                    rfl

theorem cell21_938626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_938626 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_938626 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_938626 prefixEnd_938626 := by exact prefixLift 938626
  have htrace : WordTrace (prefixWord ++ tailWord_938626) baseStart_938626 baseEnd_938626 := by
    simpa [prefixWord, tailWord_938626, baseEnd_938626] using wordTrace_append hprefix tailTrace_938626
  have hstable : (prefixWord ++ tailWord_938626).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938626).length < 2 ^ (prefixWord ++ tailWord_938626).sum := by decide
  have hdescent : baseEnd_938626 < baseStart_938626 := by decide
  rcases family_descends (prefixWord ++ tailWord_938626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938631 : List Nat := [1, 1, 4, 2, 1, 2, 10]
def baseStart_938631 : Nat := 118140960795 + 938631 * 2 ^ 59
def prefixEnd_938631 : Nat := 4983230072969 + 3 ^ 40 * 938631 * 2
def baseEnd_938631 : Nat := 23800931368415917807201

theorem tailTrace_938631 : CollatzResearch.WordTrace tailWord_938631 prefixEnd_938631 23800931368415917807201 := by
  unfold tailWord_938631
  simp only [CollatzResearch.WordTrace]
  refine ⟨34234685062507667257343747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22823123375005111504895831 34234685062507667257343747)
  ·
    refine ⟨51352027593761500886015621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34234685062507667257343747 51352027593761500886015621)
    ·
      refine ⟨9628505173830281416127929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51352027593761500886015621 9628505173830281416127929)
      ·
        refine ⟨7221378880372711062095947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9628505173830281416127929 7221378880372711062095947)
        ·
          refine ⟨10832068320559066593143921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7221378880372711062095947 10832068320559066593143921)
          ·
            refine ⟨8124051240419299944857941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10832068320559066593143921 8124051240419299944857941)
            ·
              refine ⟨23800931368415917807201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8124051240419299944857941 23800931368415917807201)
              ·
                rfl

theorem cell21_938631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 10].length) (baseStart_938631 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_938631 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_938631 prefixEnd_938631 := by exact prefixLift 938631
  have htrace : WordTrace (prefixWord ++ tailWord_938631) baseStart_938631 baseEnd_938631 := by
    simpa [prefixWord, tailWord_938631, baseEnd_938631] using wordTrace_append hprefix tailTrace_938631
  have hstable : (prefixWord ++ tailWord_938631).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938631).length < 2 ^ (prefixWord ++ tailWord_938631).sum := by decide
  have hdescent : baseEnd_938631 < baseStart_938631 := by decide
  rcases family_descends (prefixWord ++ tailWord_938631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938634 : List Nat := [3, 1, 2, 3, 3, 1, 1, 1, 6]
def baseStart_938634 : Nat := 118140960795 + 938634 * 2 ^ 59
def prefixEnd_938634 : Nat := 4983230072969 + 3 ^ 40 * 938634 * 2
def baseEnd_938634 : Nat := 214209066956615921714803

theorem tailTrace_938634 : CollatzResearch.WordTrace tailWord_938634 prefixEnd_938634 214209066956615921714803 := by
  unfold tailWord_938634
  simp only [CollatzResearch.WordTrace]
  refine ⟨8558698620374199692425739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22823196320997865846468637 8558698620374199692425739)
  ·
    refine ⟨12838047930561299538638609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8558698620374199692425739 12838047930561299538638609)
    ·
      refine ⟨9628535947920974653978957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12838047930561299538638609 9628535947920974653978957)
      ·
        refine ⟨3610700980470365495242109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9628535947920974653978957 3610700980470365495242109)
        ·
          refine ⟨1354012867676387060715791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3610700980470365495242109 1354012867676387060715791)
          ·
            refine ⟨2031019301514580591073687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1354012867676387060715791 2031019301514580591073687)
            ·
              refine ⟨3046528952271870886610531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2031019301514580591073687 3046528952271870886610531)
              ·
                refine ⟨4569793428407806329915797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3046528952271870886610531 4569793428407806329915797)
                ·
                  refine ⟨214209066956615921714803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4569793428407806329915797 214209066956615921714803)
                  ·
                    rfl

theorem cell21_938634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 6].length) (baseStart_938634 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_938634 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_938634 prefixEnd_938634 := by exact prefixLift 938634
  have htrace : WordTrace (prefixWord ++ tailWord_938634) baseStart_938634 baseEnd_938634 := by
    simpa [prefixWord, tailWord_938634, baseEnd_938634] using wordTrace_append hprefix tailTrace_938634
  have hstable : (prefixWord ++ tailWord_938634).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938634).length < 2 ^ (prefixWord ++ tailWord_938634).sum := by decide
  have hdescent : baseEnd_938634 < baseStart_938634 := by decide
  rcases family_descends (prefixWord ++ tailWord_938634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938741 : List Nat := [1, 3, 6, 1, 10]
def baseStart_938741 : Nat := 118140960795 + 938741 * 2 ^ 59
def prefixEnd_938741 : Nat := 4983230072969 + 3 ^ 40 * 938741 * 2
def baseEnd_938741 : Nat := 2644857849560586585571

theorem tailTrace_938741 : CollatzResearch.WordTrace tailWord_938741 prefixEnd_938741 2644857849560586585571 := by
  unfold tailWord_938741
  simp only [CollatzResearch.WordTrace]
  refine ⟨34238697092109156043848077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22825798061406104029232051 34238697092109156043848077)
  ·
    refine ⟨12839511409540933516443029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34238697092109156043848077 12839511409540933516443029)
    ·
      refine ⟨601852097322231258583267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 12839511409540933516443029 601852097322231258583267)
      ·
        refine ⟨902778145983346887874901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 601852097322231258583267 902778145983346887874901)
        ·
          refine ⟨2644857849560586585571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 902778145983346887874901 2644857849560586585571)
          ·
            rfl

theorem cell21_938741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 10].length) (baseStart_938741 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_938741 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_938741 prefixEnd_938741 := by exact prefixLift 938741
  have htrace : WordTrace (prefixWord ++ tailWord_938741) baseStart_938741 baseEnd_938741 := by
    simpa [prefixWord, tailWord_938741, baseEnd_938741] using wordTrace_append hprefix tailTrace_938741
  have hstable : (prefixWord ++ tailWord_938741).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938741).length < 2 ^ (prefixWord ++ tailWord_938741).sum := by decide
  have hdescent : baseEnd_938741 < baseStart_938741 := by decide
  rcases family_descends (prefixWord ++ tailWord_938741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938769 : List Nat := [1, 2, 2, 1, 1, 3, 4, 3, 4]
def baseStart_938769 : Nat := 118140960795 + 938769 * 2 ^ 59
def prefixEnd_938769 : Nat := 4983230072969 + 3 ^ 40 * 938769 * 2
def baseEnd_938769 : Nat := 214239875795885686964527

theorem tailTrace_938769 : CollatzResearch.WordTrace tailWord_938769 prefixEnd_938769 214239875795885686964527 := by
  unfold tailWord_938769
  simp only [CollatzResearch.WordTrace]
  refine ⟨34239718336007716825867361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22826478890671811217244907 34239718336007716825867361)
  ·
    refine ⟨25679788752005787619400521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34239718336007716825867361 25679788752005787619400521)
    ·
      refine ⟨19259841564004340714550391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25679788752005787619400521 19259841564004340714550391)
      ·
        refine ⟨28889762346006511071825587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19259841564004340714550391 28889762346006511071825587)
        ·
          refine ⟨43334643519009766607738381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28889762346006511071825587 43334643519009766607738381)
          ·
            refine ⟨16250491319628662477901893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43334643519009766607738381 16250491319628662477901893)
            ·
              refine ⟨3046967122430374214606605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16250491319628662477901893 3046967122430374214606605)
              ·
                refine ⟨1142612670911390330477477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3046967122430374214606605 1142612670911390330477477)
                ·
                  refine ⟨214239875795885686964527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1142612670911390330477477 214239875795885686964527)
                  ·
                    rfl

theorem cell21_938769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 3, 4].length) (baseStart_938769 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_938769 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_938769 prefixEnd_938769 := by exact prefixLift 938769
  have htrace : WordTrace (prefixWord ++ tailWord_938769) baseStart_938769 baseEnd_938769 := by
    simpa [prefixWord, tailWord_938769, baseEnd_938769] using wordTrace_append hprefix tailTrace_938769
  have hstable : (prefixWord ++ tailWord_938769).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938769).length < 2 ^ (prefixWord ++ tailWord_938769).sum := by decide
  have hdescent : baseEnd_938769 < baseStart_938769 := by decide
  rcases family_descends (prefixWord ++ tailWord_938769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938921 : List Nat := [1, 2, 1, 1, 1, 1, 8, 2, 4]
def baseStart_938921 : Nat := 118140960795 + 938921 * 2 ^ 59
def prefixEnd_938921 : Nat := 4983230072969 + 3 ^ 40 * 938921 * 2
def baseEnd_938921 : Nat := 214274564266767200430883

theorem tailTrace_938921 : CollatzResearch.WordTrace tailWord_938921 prefixEnd_938921 214274564266767200430883 := by
  unfold tailWord_938921
  simp only [CollatzResearch.WordTrace]
  refine ⟨34245262231457046785400617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22830174820971364523600411 34245262231457046785400617)
  ·
    refine ⟨25683946673592785089050463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34245262231457046785400617 25683946673592785089050463)
    ·
      refine ⟨38525920010389177633575695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25683946673592785089050463 38525920010389177633575695)
      ·
        refine ⟨57788880015583766450363543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38525920010389177633575695 57788880015583766450363543)
        ·
          refine ⟨86683320023375649675545315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57788880015583766450363543 86683320023375649675545315)
          ·
            refine ⟨130024980035063474513317973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86683320023375649675545315 130024980035063474513317973)
            ·
              refine ⟨1523730234785900091952945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 130024980035063474513317973 1523730234785900091952945)
              ·
                refine ⟨1142797676089425068964709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1523730234785900091952945 1142797676089425068964709)
                ·
                  refine ⟨214274564266767200430883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1142797676089425068964709 214274564266767200430883)
                  ·
                    rfl

theorem cell21_938921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 2, 4].length) (baseStart_938921 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_938921 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_938921 prefixEnd_938921 := by exact prefixLift 938921
  have htrace : WordTrace (prefixWord ++ tailWord_938921) baseStart_938921 baseEnd_938921 := by
    simpa [prefixWord, tailWord_938921, baseEnd_938921] using wordTrace_append hprefix tailTrace_938921
  have hstable : (prefixWord ++ tailWord_938921).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938921).length < 2 ^ (prefixWord ++ tailWord_938921).sum := by decide
  have hdescent : baseEnd_938921 < baseStart_938921 := by decide
  rcases family_descends (prefixWord ++ tailWord_938921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938935 : List Nat := [1, 1, 3, 1, 3, 1, 5, 6]
def baseStart_938935 : Nat := 118140960795 + 938935 * 2 ^ 59
def prefixEnd_938935 : Nat := 4983230072969 + 3 ^ 40 * 938935 * 2
def baseEnd_938935 : Nat := 71425919752502095732507

theorem tailTrace_938935 : CollatzResearch.WordTrace tailWord_938935 prefixEnd_938935 71425919752502095732507 := by
  unfold tailWord_938935
  simp only [CollatzResearch.WordTrace]
  refine ⟨34245772853406327176410259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22830515235604218117606839 34245772853406327176410259)
  ·
    refine ⟨51368659280109490764615389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34245772853406327176410259 51368659280109490764615389)
    ·
      refine ⟨19263247230041059036730771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51368659280109490764615389 19263247230041059036730771)
      ·
        refine ⟨28894870845061588555096157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19263247230041059036730771 28894870845061588555096157)
        ·
          refine ⟨10835576566898095708161059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28894870845061588555096157 10835576566898095708161059)
          ·
            refine ⟨16253364850347143562241589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10835576566898095708161059 16253364850347143562241589)
            ·
              refine ⟨1523752954720044708960149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16253364850347143562241589 1523752954720044708960149)
              ·
                refine ⟨71425919752502095732507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1523752954720044708960149 71425919752502095732507)
                ·
                  rfl

theorem cell21_938935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 6].length) (baseStart_938935 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_938935 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_938935 prefixEnd_938935 := by exact prefixLift 938935
  have htrace : WordTrace (prefixWord ++ tailWord_938935) baseStart_938935 baseEnd_938935 := by
    simpa [prefixWord, tailWord_938935, baseEnd_938935] using wordTrace_append hprefix tailTrace_938935
  have hstable : (prefixWord ++ tailWord_938935).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938935).length < 2 ^ (prefixWord ++ tailWord_938935).sum := by decide
  have hdescent : baseEnd_938935 < baseStart_938935 := by decide
  rcases family_descends (prefixWord ++ tailWord_938935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938983 : List Nat := [1, 1, 5, 2, 2, 2, 2, 1, 5]
def baseStart_938983 : Nat := 118140960795 + 938983 * 2 ^ 59
def prefixEnd_938983 : Nat := 4983230072969 + 3 ^ 40 * 938983 * 2
def baseEnd_938983 : Nat := 214288713511468870397423

theorem tailTrace_938983 : CollatzResearch.WordTrace tailWord_938983 prefixEnd_938983 214288713511468870397423 := by
  unfold tailWord_938983
  simp only [CollatzResearch.WordTrace]
  refine ⟨34247523557232431374157603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22831682371488287582771735 34247523557232431374157603)
  ·
    refine ⟨51371285335848647061236405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34247523557232431374157603 51371285335848647061236405)
    ·
      refine ⟨4816058000235810661990913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51371285335848647061236405 4816058000235810661990913)
      ·
        refine ⟨3612043500176857996493185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4816058000235810661990913 3612043500176857996493185)
        ·
          refine ⟨2709032625132643497369889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3612043500176857996493185 2709032625132643497369889)
          ·
            refine ⟨2031774468849482623027417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2709032625132643497369889 2031774468849482623027417)
            ·
              refine ⟨1523830851637111967270563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2031774468849482623027417 1523830851637111967270563)
              ·
                refine ⟨2285746277455667950905845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1523830851637111967270563 2285746277455667950905845)
                ·
                  refine ⟨214288713511468870397423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2285746277455667950905845 214288713511468870397423)
                  ·
                    rfl

theorem cell21_938983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 1, 5].length) (baseStart_938983 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_938983 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_938983 prefixEnd_938983 := by exact prefixLift 938983
  have htrace : WordTrace (prefixWord ++ tailWord_938983) baseStart_938983 baseEnd_938983 := by
    simpa [prefixWord, tailWord_938983, baseEnd_938983] using wordTrace_append hprefix tailTrace_938983
  have hstable : (prefixWord ++ tailWord_938983).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938983).length < 2 ^ (prefixWord ++ tailWord_938983).sum := by decide
  have hdescent : baseEnd_938983 < baseStart_938983 := by decide
  rcases family_descends (prefixWord ++ tailWord_938983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939025 : List Nat := [1, 2, 2, 1, 1, 2, 1, 4, 7]
def baseStart_939025 : Nat := 118140960795 + 939025 * 2 ^ 59
def prefixEnd_939025 : Nat := 4983230072969 + 3 ^ 40 * 939025 * 2
def baseEnd_939025 : Nat := 214298298483686130697337

theorem tailTrace_939025 : CollatzResearch.WordTrace tailWord_939025 prefixEnd_939025 214298298483686130697337 := by
  unfold tailWord_939025
  simp only [CollatzResearch.WordTrace]
  refine ⟨34249055423080272547186529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22832703615386848364791019 34249055423080272547186529)
  ·
    refine ⟨25686791567310204410389897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34249055423080272547186529 25686791567310204410389897)
    ·
      refine ⟨19265093675482653307792423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25686791567310204410389897 19265093675482653307792423)
      ·
        refine ⟨28897640513223979961688635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19265093675482653307792423 28897640513223979961688635)
        ·
          refine ⟨43346460769835969942532953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28897640513223979961688635 43346460769835969942532953)
          ·
            refine ⟨32509845577376977456899715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43346460769835969942532953 32509845577376977456899715)
            ·
              refine ⟨48764768366065466185349573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32509845577376977456899715 48764768366065466185349573)
              ·
                refine ⟨9143394068637274909753045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48764768366065466185349573 9143394068637274909753045)
                ·
                  refine ⟨214298298483686130697337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9143394068637274909753045 214298298483686130697337)
                  ·
                    rfl

theorem cell21_939025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 7].length) (baseStart_939025 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_939025 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_939025 prefixEnd_939025 := by exact prefixLift 939025
  have htrace : WordTrace (prefixWord ++ tailWord_939025) baseStart_939025 baseEnd_939025 := by
    simpa [prefixWord, tailWord_939025, baseEnd_939025] using wordTrace_append hprefix tailTrace_939025
  have hstable : (prefixWord ++ tailWord_939025).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939025).length < 2 ^ (prefixWord ++ tailWord_939025).sum := by decide
  have hdescent : baseEnd_939025 < baseStart_939025 := by decide
  rcases family_descends (prefixWord ++ tailWord_939025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939090 : List Nat := [3, 2, 2, 1, 3, 2, 2, 2, 4]
def baseStart_939090 : Nat := 118140960795 + 939090 * 2 ^ 59
def prefixEnd_939090 : Nat := 4983230072969 + 3 ^ 40 * 939090 * 2
def baseEnd_939090 : Nat := 214313132369260462113871

theorem tailTrace_939090 : CollatzResearch.WordTrace tailWord_939090 prefixEnd_939090 214313132369260462113871 := by
  unfold tailWord_939090
  simp only [CollatzResearch.WordTrace]
  refine ⟨8562856541961197162075681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22834284111896525765535149 8562856541961197162075681)
  ·
    refine ⟨6422142406470897871556761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8562856541961197162075681 6422142406470897871556761)
    ·
      refine ⟨4816606804853173403667571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6422142406470897871556761 4816606804853173403667571)
      ·
        refine ⟨7224910207279760105501357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4816606804853173403667571 7224910207279760105501357)
        ·
          refine ⟨2709341327729910039563009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7224910207279760105501357 2709341327729910039563009)
          ·
            refine ⟨2032005995797432529672257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2709341327729910039563009 2032005995797432529672257)
            ·
              refine ⟨1524004496848074397254193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2032005995797432529672257 1524004496848074397254193)
              ·
                refine ⟨1143003372636055797940645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1524004496848074397254193 1143003372636055797940645)
                ·
                  refine ⟨214313132369260462113871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1143003372636055797940645 214313132369260462113871)
                  ·
                    rfl

theorem cell21_939090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 2, 4].length) (baseStart_939090 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_939090 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_939090 prefixEnd_939090 := by exact prefixLift 939090
  have htrace : WordTrace (prefixWord ++ tailWord_939090) baseStart_939090 baseEnd_939090 := by
    simpa [prefixWord, tailWord_939090, baseEnd_939090] using wordTrace_append hprefix tailTrace_939090
  have hstable : (prefixWord ++ tailWord_939090).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939090).length < 2 ^ (prefixWord ++ tailWord_939090).sum := by decide
  have hdescent : baseEnd_939090 < baseStart_939090 := by decide
  rcases family_descends (prefixWord ++ tailWord_939090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939118 : List Nat := [4, 1, 2, 2, 1, 2, 1, 1, 7]
def baseStart_939118 : Nat := 118140960795 + 939118 * 2 ^ 59
def prefixEnd_939118 : Nat := 4983230072969 + 3 ^ 40 * 939118 * 2
def baseEnd_939118 : Nat := 214319522350738635647147

theorem tailTrace_939118 : CollatzResearch.WordTrace tailWord_939118 prefixEnd_939118 214319522350738635647147 := by
  unfold tailWord_939118
  simp only [CollatzResearch.WordTrace]
  refine ⟨4281555926467918678790251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22834964941162232953548005 4281555926467918678790251)
  ·
    refine ⟨6422333889701878018185377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4281555926467918678790251 6422333889701878018185377)
    ·
      refine ⟨4816750417276408513639033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6422333889701878018185377 4816750417276408513639033)
      ·
        refine ⟨3612562812957306385229275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4816750417276408513639033 3612562812957306385229275)
        ·
          refine ⟨5418844219435959577843913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3612562812957306385229275 5418844219435959577843913)
          ·
            refine ⟨4064133164576969683382935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5418844219435959577843913 4064133164576969683382935)
            ·
              refine ⟨6096199746865454525074403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4064133164576969683382935 6096199746865454525074403)
              ·
                refine ⟨9144299620298181787611605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6096199746865454525074403 9144299620298181787611605)
                ·
                  refine ⟨214319522350738635647147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9144299620298181787611605 214319522350738635647147)
                  ·
                    rfl

theorem cell21_939118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_939118 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_939118 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_939118 prefixEnd_939118 := by exact prefixLift 939118
  have htrace : WordTrace (prefixWord ++ tailWord_939118) baseStart_939118 baseEnd_939118 := by
    simpa [prefixWord, tailWord_939118, baseEnd_939118] using wordTrace_append hprefix tailTrace_939118
  have hstable : (prefixWord ++ tailWord_939118).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939118).length < 2 ^ (prefixWord ++ tailWord_939118).sum := by decide
  have hdescent : baseEnd_939118 < baseStart_939118 := by decide
  rcases family_descends (prefixWord ++ tailWord_939118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939132 : List Nat := [2, 2, 2, 1, 1, 3, 2, 2, 6]
def baseStart_939132 : Nat := 118140960795 + 939132 * 2 ^ 59
def prefixEnd_939132 : Nat := 4983230072969 + 3 ^ 40 * 939132 * 2
def baseEnd_939132 : Nat := 214322717341477722413785

theorem tailTrace_939132 : CollatzResearch.WordTrace tailWord_939132 prefixEnd_939132 214322717341477722413785 := by
  unfold tailWord_939132
  simp only [CollatzResearch.WordTrace]
  refine ⟨17126479016846314910665825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22835305355795086547554433 17126479016846314910665825)
  ·
    refine ⟨12844859262634736182999369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17126479016846314910665825 12844859262634736182999369)
    ·
      refine ⟨9633644446976052137249527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12844859262634736182999369 9633644446976052137249527)
      ·
        refine ⟨14450466670464078205874291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9633644446976052137249527 14450466670464078205874291)
        ·
          refine ⟨21675700005696117308811437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14450466670464078205874291 21675700005696117308811437)
          ·
            refine ⟨8128387502136043990804289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21675700005696117308811437 8128387502136043990804289)
            ·
              refine ⟨6096290626602032993103217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8128387502136043990804289 6096290626602032993103217)
              ·
                refine ⟨4572217969951524744827413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6096290626602032993103217 4572217969951524744827413)
                ·
                  refine ⟨214322717341477722413785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4572217969951524744827413 214322717341477722413785)
                  ·
                    rfl

theorem cell21_939132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 6].length) (baseStart_939132 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_939132 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_939132 prefixEnd_939132 := by exact prefixLift 939132
  have htrace : WordTrace (prefixWord ++ tailWord_939132) baseStart_939132 baseEnd_939132 := by
    simpa [prefixWord, tailWord_939132, baseEnd_939132] using wordTrace_append hprefix tailTrace_939132
  have hstable : (prefixWord ++ tailWord_939132).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939132).length < 2 ^ (prefixWord ++ tailWord_939132).sum := by decide
  have hdescent : baseEnd_939132 < baseStart_939132 := by decide
  rcases family_descends (prefixWord ++ tailWord_939132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939208 : List Nat := [2, 1, 3, 1, 2, 1, 4, 1, 6]
def baseStart_939208 : Nat := 118140960795 + 939208 * 2 ^ 59
def prefixEnd_939208 : Nat := 4983230072969 + 3 ^ 40 * 939208 * 2
def baseEnd_939208 : Nat := 214340061576918479146963

theorem tailTrace_939208 : CollatzResearch.WordTrace tailWord_939208 prefixEnd_939208 214340061576918479146963 := by
  unfold tailWord_939208
  simp only [CollatzResearch.WordTrace]
  refine ⟨17127864990708647400549139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22837153320944863200732185 17127864990708647400549139)
  ·
    refine ⟨25691797486062971100823709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17127864990708647400549139 25691797486062971100823709)
    ·
      refine ⟨9634424057273614162808891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25691797486062971100823709 9634424057273614162808891)
      ·
        refine ⟨14451636085910421244213337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9634424057273614162808891 14451636085910421244213337)
        ·
          refine ⟨10838727064432815933160003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14451636085910421244213337 10838727064432815933160003)
          ·
            refine ⟨16258090596649223899740005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10838727064432815933160003 16258090596649223899740005)
            ·
              refine ⟨3048391986871729481201251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16258090596649223899740005 3048391986871729481201251)
              ·
                refine ⟨4572587980307594221801877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3048391986871729481201251 4572587980307594221801877)
                ·
                  refine ⟨214340061576918479146963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4572587980307594221801877 214340061576918479146963)
                  ·
                    rfl

theorem cell21_939208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 6].length) (baseStart_939208 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_939208 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_939208 prefixEnd_939208 := by exact prefixLift 939208
  have htrace : WordTrace (prefixWord ++ tailWord_939208) baseStart_939208 baseEnd_939208 := by
    simpa [prefixWord, tailWord_939208, baseEnd_939208] using wordTrace_append hprefix tailTrace_939208
  have hstable : (prefixWord ++ tailWord_939208).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939208).length < 2 ^ (prefixWord ++ tailWord_939208).sum := by decide
  have hdescent : baseEnd_939208 < baseStart_939208 := by decide
  rcases family_descends (prefixWord ++ tailWord_939208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939304 : List Nat := [2, 1, 5, 1, 2, 2, 2, 3, 3]
def baseStart_939304 : Nat := 118140960795 + 939304 * 2 ^ 59
def prefixEnd_939304 : Nat := 4983230072969 + 3 ^ 40 * 939304 * 2
def baseEnd_939304 : Nat := 214361970084843645546767

theorem tailTrace_939304 : CollatzResearch.WordTrace tailWord_939304 prefixEnd_939304 214361970084843645546767 := by
  unfold tailWord_939304
  simp only [CollatzResearch.WordTrace]
  refine ⟨17129615694534751598296483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22839487592713002131061977 17129615694534751598296483)
  ·
    refine ⟨25694423541802127397444725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17129615694534751598296483 25694423541802127397444725)
    ·
      refine ⟨2408852207043949443510443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25694423541802127397444725 2408852207043949443510443)
      ·
        refine ⟨3613278310565924165265665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2408852207043949443510443 3613278310565924165265665)
        ·
          refine ⟨2709958732924443123949249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3613278310565924165265665 2709958732924443123949249)
          ·
            refine ⟨2032469049693332342961937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2709958732924443123949249 2032469049693332342961937)
            ·
              refine ⟨1524351787269999257221453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2032469049693332342961937 1524351787269999257221453)
              ·
                refine ⟨571631920226249721458045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1524351787269999257221453 571631920226249721458045)
                ·
                  refine ⟨214361970084843645546767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 571631920226249721458045 214361970084843645546767)
                  ·
                    rfl

theorem cell21_939304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 3, 3].length) (baseStart_939304 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_939304 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_939304 prefixEnd_939304 := by exact prefixLift 939304
  have htrace : WordTrace (prefixWord ++ tailWord_939304) baseStart_939304 baseEnd_939304 := by
    simpa [prefixWord, tailWord_939304, baseEnd_939304] using wordTrace_append hprefix tailTrace_939304
  have hstable : (prefixWord ++ tailWord_939304).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939304).length < 2 ^ (prefixWord ++ tailWord_939304).sum := by decide
  have hdescent : baseEnd_939304 < baseStart_939304 := by decide
  rcases family_descends (prefixWord ++ tailWord_939304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939360 : List Nat := [2, 1, 1, 3, 4, 1, 1, 2, 6]
def baseStart_939360 : Nat := 118140960795 + 939360 * 2 ^ 59
def prefixEnd_939360 : Nat := 4983230072969 + 3 ^ 40 * 939360 * 2
def baseEnd_939360 : Nat := 214374750047799992613319

theorem tailTrace_939360 : CollatzResearch.WordTrace tailWord_939360 prefixEnd_939360 214374750047799992613319 := by
  unfold tailWord_939360
  simp only [CollatzResearch.WordTrace]
  refine ⟨17130636938433312380315767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22840849251244416507087689 17130636938433312380315767)
  ·
    refine ⟨25695955407649968570473651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17130636938433312380315767 25695955407649968570473651)
    ·
      refine ⟨38543933111474952855710477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25695955407649968570473651 38543933111474952855710477)
      ·
        refine ⟨14453974916803107320891429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38543933111474952855710477 14453974916803107320891429)
        ·
          refine ⟨2710120296900582622667143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14453974916803107320891429 2710120296900582622667143)
          ·
            refine ⟨4065180445350873934000715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2710120296900582622667143 4065180445350873934000715)
            ·
              refine ⟨6097770668026310901001073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4065180445350873934000715 6097770668026310901001073)
              ·
                refine ⟨4573328001019733175750805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6097770668026310901001073 4573328001019733175750805)
                ·
                  refine ⟨214374750047799992613319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4573328001019733175750805 214374750047799992613319)
                  ·
                    rfl

theorem cell21_939360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 6].length) (baseStart_939360 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_939360 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_939360 prefixEnd_939360 := by exact prefixLift 939360
  have htrace : WordTrace (prefixWord ++ tailWord_939360) baseStart_939360 baseEnd_939360 := by
    simpa [prefixWord, tailWord_939360, baseEnd_939360] using wordTrace_append hprefix tailTrace_939360
  have hstable : (prefixWord ++ tailWord_939360).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939360).length < 2 ^ (prefixWord ++ tailWord_939360).sum := by decide
  have hdescent : baseEnd_939360 < baseStart_939360 := by decide
  rcases family_descends (prefixWord ++ tailWord_939360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939363 : List Nat := [1, 1, 1, 5, 2, 2, 3, 3, 3]
def baseStart_939363 : Nat := 118140960795 + 939363 * 2 ^ 59
def prefixEnd_939363 : Nat := 4983230072969 + 3 ^ 40 * 939363 * 2
def baseEnd_939363 : Nat := 214375434688672654063313

theorem tailTrace_939363 : CollatzResearch.WordTrace tailWord_939363 prefixEnd_939363 214375434688672654063313 := by
  unfold tailWord_939363
  simp only [CollatzResearch.WordTrace]
  refine ⟨34261383295855756272990743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22840922197237170848660495 34261383295855756272990743)
  ·
    refine ⟨51392074943783634409486115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34261383295855756272990743 51392074943783634409486115)
    ·
      refine ⟨77088112415675451614229173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51392074943783634409486115 77088112415675451614229173)
      ·
        refine ⟨7227010538969573588833985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77088112415675451614229173 7227010538969573588833985)
        ·
          refine ⟨5420257904227180191625489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7227010538969573588833985 5420257904227180191625489)
          ·
            refine ⟨4065193428170385143719117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5420257904227180191625489 4065193428170385143719117)
            ·
              refine ⟨1524447535563894428894669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4065193428170385143719117 1524447535563894428894669)
              ·
                refine ⟨571667825836460410835501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1524447535563894428894669 571667825836460410835501)
                ·
                  refine ⟨214375434688672654063313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 571667825836460410835501 214375434688672654063313)
                  ·
                    rfl

theorem cell21_939363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 3, 3].length) (baseStart_939363 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_939363 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_939363 prefixEnd_939363 := by exact prefixLift 939363
  have htrace : WordTrace (prefixWord ++ tailWord_939363) baseStart_939363 baseEnd_939363 := by
    simpa [prefixWord, tailWord_939363, baseEnd_939363] using wordTrace_append hprefix tailTrace_939363
  have hstable : (prefixWord ++ tailWord_939363).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939363).length < 2 ^ (prefixWord ++ tailWord_939363).sum := by decide
  have hdescent : baseEnd_939363 < baseStart_939363 := by decide
  rcases family_descends (prefixWord ++ tailWord_939363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939436 : List Nat := [2, 2, 1, 1, 1, 1, 5, 4, 4]
def baseStart_939436 : Nat := 118140960795 + 939436 * 2 ^ 59
def prefixEnd_939436 : Nat := 4983230072969 + 3 ^ 40 * 939436 * 2
def baseEnd_939436 : Nat := 214392094283240749346497

theorem tailTrace_939436 : CollatzResearch.WordTrace tailWord_939436 prefixEnd_939436 214392094283240749346497 := by
  unfold tailWord_939436
  simp only [CollatzResearch.WordTrace]
  refine ⟨17132022912295644870199081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22842697216394193160265441 17132022912295644870199081)
  ·
    refine ⟨12849017184221733652649311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17132022912295644870199081 12849017184221733652649311)
    ·
      refine ⟨19273525776332600478973967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12849017184221733652649311 19273525776332600478973967)
      ·
        refine ⟨28910288664498900718460951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19273525776332600478973967 28910288664498900718460951)
        ·
          refine ⟨43365432996748351077691427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28910288664498900718460951 43365432996748351077691427)
          ·
            refine ⟨65048149495122526616537141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43365432996748351077691427 65048149495122526616537141)
            ·
              refine ⟨6098264015167736870300357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65048149495122526616537141 6098264015167736870300357)
              ·
                refine ⟨1143424502843950663181317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6098264015167736870300357 1143424502843950663181317)
                ·
                  refine ⟨214392094283240749346497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1143424502843950663181317 214392094283240749346497)
                  ·
                    rfl

theorem cell21_939436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 4].length) (baseStart_939436 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_939436 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_939436 prefixEnd_939436 := by exact prefixLift 939436
  have htrace : WordTrace (prefixWord ++ tailWord_939436) baseStart_939436 baseEnd_939436 := by
    simpa [prefixWord, tailWord_939436, baseEnd_939436] using wordTrace_append hprefix tailTrace_939436
  have hstable : (prefixWord ++ tailWord_939436).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939436).length < 2 ^ (prefixWord ++ tailWord_939436).sum := by decide
  have hdescent : baseEnd_939436 < baseStart_939436 := by decide
  rcases family_descends (prefixWord ++ tailWord_939436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939518 : List Nat := [4, 2, 2, 3, 1, 2, 2, 5]
def baseStart_939518 : Nat := 118140960795 + 939518 * 2 ^ 59
def prefixEnd_939518 : Nat := 4983230072969 + 3 ^ 40 * 939518 * 2
def baseEnd_939518 : Nat := 71470269266808942993221

theorem tailTrace_939518 : CollatzResearch.WordTrace tailWord_939518 prefixEnd_939518 71470269266808942993221 := by
  unfold tailWord_939518
  simp only [CollatzResearch.WordTrace]
  refine ⟨4283379576286777218110401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22844691073529478496588805 4283379576286777218110401)
  ·
    refine ⟨3212534682215082913582801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4283379576286777218110401 3212534682215082913582801)
    ·
      refine ⟨2409401011661312185187101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3212534682215082913582801 2409401011661312185187101)
      ·
        refine ⟨903525379372992069445163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2409401011661312185187101 903525379372992069445163)
        ·
          refine ⟨1355288069059488104167745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 903525379372992069445163 1355288069059488104167745)
          ·
            refine ⟨1016466051794616078125809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1355288069059488104167745 1016466051794616078125809)
            ·
              refine ⟨762349538845962058594357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1016466051794616078125809 762349538845962058594357)
              ·
                refine ⟨71470269266808942993221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 762349538845962058594357 71470269266808942993221)
                ·
                  rfl

theorem cell21_939518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 2, 5].length) (baseStart_939518 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_939518 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_939518 prefixEnd_939518 := by exact prefixLift 939518
  have htrace : WordTrace (prefixWord ++ tailWord_939518) baseStart_939518 baseEnd_939518 := by
    simpa [prefixWord, tailWord_939518, baseEnd_939518] using wordTrace_append hprefix tailTrace_939518
  have hstable : (prefixWord ++ tailWord_939518).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939518).length < 2 ^ (prefixWord ++ tailWord_939518).sum := by decide
  have hdescent : baseEnd_939518 < baseStart_939518 := by decide
  rcases family_descends (prefixWord ++ tailWord_939518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939532 : List Nat := [2, 2, 1, 2, 5, 2, 1, 3, 3]
def baseStart_939532 : Nat := 118140960795 + 939532 * 2 ^ 59
def prefixEnd_939532 : Nat := 4983230072969 + 3 ^ 40 * 939532 * 2
def baseEnd_939532 : Nat := 214414002791165915746301

theorem tailTrace_939532 : CollatzResearch.WordTrace tailWord_939532 prefixEnd_939532 214414002791165915746301 := by
  unfold tailWord_939532
  simp only [CollatzResearch.WordTrace]
  refine ⟨17133773616121749067946425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22845031488162332090595233 17133773616121749067946425)
  ·
    refine ⟨12850330212091311800959819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17133773616121749067946425 12850330212091311800959819)
    ·
      refine ⟨19275495318136967701439729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12850330212091311800959819 19275495318136967701439729)
      ·
        refine ⟨14456621488602725776079797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19275495318136967701439729 14456621488602725776079797)
        ·
          refine ⟨1355308264556505541507481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14456621488602725776079797 1355308264556505541507481)
          ·
            refine ⟨1016481198417379156130611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1355308264556505541507481 1016481198417379156130611)
            ·
              refine ⟨1524721797626068734195917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1016481198417379156130611 1524721797626068734195917)
              ·
                refine ⟨571770674109775775323469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1524721797626068734195917 571770674109775775323469)
                ·
                  refine ⟨214414002791165915746301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 571770674109775775323469 214414002791165915746301)
                  ·
                    rfl

theorem cell21_939532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 3, 3].length) (baseStart_939532 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_939532 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_939532 prefixEnd_939532 := by exact prefixLift 939532
  have htrace : WordTrace (prefixWord ++ tailWord_939532) baseStart_939532 baseEnd_939532 := by
    simpa [prefixWord, tailWord_939532, baseEnd_939532] using wordTrace_append hprefix tailTrace_939532
  have hstable : (prefixWord ++ tailWord_939532).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939532).length < 2 ^ (prefixWord ++ tailWord_939532).sum := by decide
  have hdescent : baseEnd_939532 < baseStart_939532 := by decide
  rcases family_descends (prefixWord ++ tailWord_939532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939560 : List Nat := [2, 1, 5, 2, 2, 1, 2, 6]
def baseStart_939560 : Nat := 118140960795 + 939560 * 2 ^ 59
def prefixEnd_939560 : Nat := 4983230072969 + 3 ^ 40 * 939560 * 2
def baseEnd_939560 : Nat := 71473464257548029759859

theorem tailTrace_939560 : CollatzResearch.WordTrace tailWord_939560 prefixEnd_939560 71473464257548029759859 := by
  unfold tailWord_939560
  simp only [CollatzResearch.WordTrace]
  refine ⟨17134284238071029458956067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22845712317428039278608089 17134284238071029458956067)
  ·
    refine ⟨25701426357106544188434101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17134284238071029458956067 25701426357106544188434101)
    ·
      refine ⟨2409508720978738517665697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25701426357106544188434101 2409508720978738517665697)
      ·
        refine ⟨1807131540734053888249273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2409508720978738517665697 1807131540734053888249273)
        ·
          refine ⟨1355348655550540416186955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1807131540734053888249273 1355348655550540416186955)
          ·
            refine ⟨2033022983325810624280433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1355348655550540416186955 2033022983325810624280433)
            ·
              refine ⟨1524767237494357968210325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2033022983325810624280433 1524767237494357968210325)
              ·
                refine ⟨71473464257548029759859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1524767237494357968210325 71473464257548029759859)
                ·
                  rfl

theorem cell21_939560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 6].length) (baseStart_939560 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_939560 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_939560 prefixEnd_939560 := by exact prefixLift 939560
  have htrace : WordTrace (prefixWord ++ tailWord_939560) baseStart_939560 baseEnd_939560 := by
    simpa [prefixWord, tailWord_939560, baseEnd_939560] using wordTrace_append hprefix tailTrace_939560
  have hstable : (prefixWord ++ tailWord_939560).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939560).length < 2 ^ (prefixWord ++ tailWord_939560).sum := by decide
  have hdescent : baseEnd_939560 < baseStart_939560 := by decide
  rcases family_descends (prefixWord ++ tailWord_939560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939602 : List Nat := [3, 2, 2, 1, 2, 11]
def baseStart_939602 : Nat := 118140960795 + 939602 * 2 ^ 59
def prefixEnd_939602 : Nat := 4983230072969 + 3 ^ 40 * 939602 * 2
def baseEnd_939602 : Nat := 7941851027587457391833

theorem tailTrace_939602 : CollatzResearch.WordTrace tailWord_939602 prefixEnd_939602 7941851027587457391833 := by
  unfold tailWord_939602
  simp only [CollatzResearch.WordTrace]
  refine ⟨8567525085497475022735265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22846733561326600060627373 8567525085497475022735265)
  ·
    refine ⟨6425643814123106267051449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8567525085497475022735265 6425643814123106267051449)
    ·
      refine ⟨4819232860592329700288587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6425643814123106267051449 4819232860592329700288587)
      ·
        refine ⟨7228849290888494550432881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4819232860592329700288587 7228849290888494550432881)
        ·
          refine ⟨5421636968166370912824661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7228849290888494550432881 5421636968166370912824661)
          ·
            refine ⟨7941851027587457391833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 5421636968166370912824661 7941851027587457391833)
            ·
              rfl

theorem cell21_939602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 11].length) (baseStart_939602 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_939602 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_939602 prefixEnd_939602 := by exact prefixLift 939602
  have htrace : WordTrace (prefixWord ++ tailWord_939602) baseStart_939602 baseEnd_939602 := by
    simpa [prefixWord, tailWord_939602, baseEnd_939602] using wordTrace_append hprefix tailTrace_939602
  have hstable : (prefixWord ++ tailWord_939602).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939602).length < 2 ^ (prefixWord ++ tailWord_939602).sum := by decide
  have hdescent : baseEnd_939602 < baseStart_939602 := by decide
  rcases family_descends (prefixWord ++ tailWord_939602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939619 : List Nat := [1, 1, 1, 5, 1, 5, 1, 6]
def baseStart_939619 : Nat := 118140960795 + 939619 * 2 ^ 59
def prefixEnd_939619 : Nat := 4983230072969 + 3 ^ 40 * 939619 * 2
def baseEnd_939619 : Nat := 71477952458824365932041

theorem tailTrace_939619 : CollatzResearch.WordTrace tailWord_939619 prefixEnd_939619 71477952458824365932041 := by
  unfold tailWord_939619
  simp only [CollatzResearch.WordTrace]
  refine ⟨34270720382928311994309911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22847146921952207996206607 34270720382928311994309911)
  ·
    refine ⟨51406080574392467991464867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34270720382928311994309911 51406080574392467991464867)
    ·
      refine ⟨77109120861588701987197301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51406080574392467991464867 77109120861588701987197301)
      ·
        refine ⟨7228980080773940811299747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77109120861588701987197301 7228980080773940811299747)
        ·
          refine ⟨10843470121160911216949621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7228980080773940811299747 10843470121160911216949621)
          ·
            refine ⟨1016575323858835426589027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10843470121160911216949621 1016575323858835426589027)
            ·
              refine ⟨1524862985788253139883541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1016575323858835426589027 1524862985788253139883541)
              ·
                refine ⟨71477952458824365932041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1524862985788253139883541 71477952458824365932041)
                ·
                  rfl

theorem cell21_939619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 6].length) (baseStart_939619 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_939619 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_939619 prefixEnd_939619 := by exact prefixLift 939619
  have htrace : WordTrace (prefixWord ++ tailWord_939619) baseStart_939619 baseEnd_939619 := by
    simpa [prefixWord, tailWord_939619, baseEnd_939619] using wordTrace_append hprefix tailTrace_939619
  have hstable : (prefixWord ++ tailWord_939619).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939619).length < 2 ^ (prefixWord ++ tailWord_939619).sum := by decide
  have hdescent : baseEnd_939619 < baseStart_939619 := by decide
  rcases family_descends (prefixWord ++ tailWord_939619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939701 : List Nat := [1, 3, 3, 3, 3, 1, 1, 3, 3]
def baseStart_939701 : Nat := 118140960795 + 939701 * 2 ^ 59
def prefixEnd_939701 : Nat := 4983230072969 + 3 ^ 40 * 939701 * 2
def baseEnd_939701 : Nat := 214452570893659177429289

theorem tailTrace_939701 : CollatzResearch.WordTrace tailWord_939701 prefixEnd_939701 214452570893659177429289 := by
  unfold tailWord_939701
  simp only [CollatzResearch.WordTrace]
  refine ⟨34273711168631239998794957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22849140779087493332529971 34273711168631239998794957)
  ·
    refine ⟨12852641688236714999548109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34273711168631239998794957 12852641688236714999548109)
    ·
      refine ⟨4819740633088768124830541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12852641688236714999548109 4819740633088768124830541)
      ·
        refine ⟨1807402737408288046811453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4819740633088768124830541 1807402737408288046811453)
        ·
          refine ⟨677776026528108017554295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1807402737408288046811453 677776026528108017554295)
          ·
            refine ⟨1016664039792162026331443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 677776026528108017554295 1016664039792162026331443)
            ·
              refine ⟨1524996059688243039497165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1016664039792162026331443 1524996059688243039497165)
              ·
                refine ⟨571873522383091139811437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1524996059688243039497165 571873522383091139811437)
                ·
                  refine ⟨214452570893659177429289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 571873522383091139811437 214452570893659177429289)
                  ·
                    rfl

theorem cell21_939701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 3, 3].length) (baseStart_939701 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_939701 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_939701 prefixEnd_939701 := by exact prefixLift 939701
  have htrace : WordTrace (prefixWord ++ tailWord_939701) baseStart_939701 baseEnd_939701 := by
    simpa [prefixWord, tailWord_939701, baseEnd_939701] using wordTrace_append hprefix tailTrace_939701
  have hstable : (prefixWord ++ tailWord_939701).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939701).length < 2 ^ (prefixWord ++ tailWord_939701).sum := by decide
  have hdescent : baseEnd_939701 < baseStart_939701 := by decide
  rcases family_descends (prefixWord ++ tailWord_939701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939718 : List Nat := [6, 1, 2, 1, 1, 2, 3, 2, 3]
def baseStart_939718 : Nat := 118140960795 + 939718 * 2 ^ 59
def prefixEnd_939718 : Nat := 4983230072969 + 3 ^ 40 * 939718 * 2
def baseEnd_939718 : Nat := 214456450525270925645921

theorem tailTrace_939718 : CollatzResearch.WordTrace tailWord_939718 prefixEnd_939718 214456450525270925645921 := by
  unfold tailWord_939718
  simp only [CollatzResearch.WordTrace]
  refine ⟨1071072850299051621942619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 22849554139713101268109205 1071072850299051621942619)
  ·
    refine ⟨1606609275448577432913929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1071072850299051621942619 1606609275448577432913929)
    ·
      refine ⟨1204956956586433074685447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1606609275448577432913929 1204956956586433074685447)
      ·
        refine ⟨1807435434879649612028171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1204956956586433074685447 1807435434879649612028171)
        ·
          refine ⟨2711153152319474418042257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1807435434879649612028171 2711153152319474418042257)
          ·
            refine ⟨2033364864239605813531693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2711153152319474418042257 2033364864239605813531693)
            ·
              refine ⟨762511824089852180074385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2033364864239605813531693 762511824089852180074385)
              ·
                refine ⟨571883868067389135055789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 762511824089852180074385 571883868067389135055789)
                ·
                  refine ⟨214456450525270925645921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 571883868067389135055789 214456450525270925645921)
                  ·
                    rfl

theorem cell21_939718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_939718 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_939718 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_939718 prefixEnd_939718 := by exact prefixLift 939718
  have htrace : WordTrace (prefixWord ++ tailWord_939718) baseStart_939718 baseEnd_939718 := by
    simpa [prefixWord, tailWord_939718, baseEnd_939718] using wordTrace_append hprefix tailTrace_939718
  have hstable : (prefixWord ++ tailWord_939718).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939718).length < 2 ^ (prefixWord ++ tailWord_939718).sum := by decide
  have hdescent : baseEnd_939718 < baseStart_939718 := by decide
  rcases family_descends (prefixWord ++ tailWord_939718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939754 : List Nat := [3, 1, 3, 1, 1, 1, 4, 7]
def baseStart_939754 : Nat := 118140960795 + 939754 * 2 ^ 59
def prefixEnd_939754 : Nat := 4983230072969 + 3 ^ 40 * 939754 * 2
def baseEnd_939754 : Nat := 71488222071914287681949

theorem tailTrace_939754 : CollatzResearch.WordTrace tailWord_939754 prefixEnd_939754 71488222071914287681949 := by
  unfold tailWord_939754
  simp only [CollatzResearch.WordTrace]
  refine ⟨8568911059359807512618579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22850429491626153366982877 8568911059359807512618579)
  ·
    refine ⟨12853366589039711268927869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8568911059359807512618579 12853366589039711268927869)
    ·
      refine ⟨4820012470889891725847951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12853366589039711268927869 4820012470889891725847951)
      ·
        refine ⟨7230018706334837588771927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4820012470889891725847951 7230018706334837588771927)
        ·
          refine ⟨10845028059502256383157891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7230018706334837588771927 10845028059502256383157891)
          ·
            refine ⟨16267542089253384574736837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10845028059502256383157891 16267542089253384574736837)
            ·
              refine ⟨3050164141735009607763157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16267542089253384574736837 3050164141735009607763157)
              ·
                refine ⟨71488222071914287681949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3050164141735009607763157 71488222071914287681949)
                ·
                  rfl

theorem cell21_939754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 7].length) (baseStart_939754 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_939754 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_939754 prefixEnd_939754 := by exact prefixLift 939754
  have htrace : WordTrace (prefixWord ++ tailWord_939754) baseStart_939754 baseEnd_939754 := by
    simpa [prefixWord, tailWord_939754, baseEnd_939754] using wordTrace_append hprefix tailTrace_939754
  have hstable : (prefixWord ++ tailWord_939754).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939754).length < 2 ^ (prefixWord ++ tailWord_939754).sum := by decide
  have hdescent : baseEnd_939754 < baseStart_939754 := by decide
  rcases family_descends (prefixWord ++ tailWord_939754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939768 : List Nat := [2, 1, 2, 1, 1, 2, 2, 1, 9]
def baseStart_939768 : Nat := 118140960795 + 939768 * 2 ^ 59
def prefixEnd_939768 : Nat := 4983230072969 + 3 ^ 40 * 939768 * 2
def baseEnd_939768 : Nat := 214467861206481949812485

theorem tailTrace_939768 : CollatzResearch.WordTrace tailWord_939768 prefixEnd_939768 214467861206481949812485 := by
  unfold tailWord_939768
  simp only [CollatzResearch.WordTrace]
  refine ⟨17138077429694255220741979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22850769906259006960989305 17138077429694255220741979)
  ·
    refine ⟨25707116144541382831112969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17138077429694255220741979 25707116144541382831112969)
    ·
      refine ⟨19280337108406037123334727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25707116144541382831112969 19280337108406037123334727)
      ·
        refine ⟨28920505662609055685002091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19280337108406037123334727 28920505662609055685002091)
        ·
          refine ⟨43380758493913583527503137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28920505662609055685002091 43380758493913583527503137)
          ·
            refine ⟨32535568870435187645627353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43380758493913583527503137 32535568870435187645627353)
            ·
              refine ⟨24401676652826390734220515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32535568870435187645627353 24401676652826390734220515)
              ·
                refine ⟨36602514979239586101330773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24401676652826390734220515 36602514979239586101330773)
                ·
                  refine ⟨214467861206481949812485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 36602514979239586101330773 214467861206481949812485)
                  ·
                    rfl

theorem cell21_939768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 9].length) (baseStart_939768 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_939768 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_939768 prefixEnd_939768 := by exact prefixLift 939768
  have htrace : WordTrace (prefixWord ++ tailWord_939768) baseStart_939768 baseEnd_939768 := by
    simpa [prefixWord, tailWord_939768, baseEnd_939768] using wordTrace_append hprefix tailTrace_939768
  have hstable : (prefixWord ++ tailWord_939768).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939768).length < 2 ^ (prefixWord ++ tailWord_939768).sum := by decide
  have hdescent : baseEnd_939768 < baseStart_939768 := by decide
  rcases family_descends (prefixWord ++ tailWord_939768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939774 : List Nat := [4, 2, 2, 1, 3, 1, 2, 2, 4]
def baseStart_939774 : Nat := 118140960795 + 939774 * 2 ^ 59
def prefixEnd_939774 : Nat := 4983230072969 + 3 ^ 40 * 939774 * 2
def baseEnd_939774 : Nat := 214469230488227272712473

theorem tailTrace_939774 : CollatzResearch.WordTrace tailWord_939774 prefixEnd_939774 214469230488227272712473 := by
  unfold tailWord_939774
  simp only [CollatzResearch.WordTrace]
  refine ⟨4284546712170846683275297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22850915798244515644134917 4284546712170846683275297)
  ·
    refine ⟨3213410034128135012456473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4284546712170846683275297 3213410034128135012456473)
    ·
      refine ⟨2410057525596101259342355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3213410034128135012456473 2410057525596101259342355)
      ·
        refine ⟨3615086288394151889013533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2410057525596101259342355 3615086288394151889013533)
        ·
          refine ⟨1355657358147806958380075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3615086288394151889013533 1355657358147806958380075)
          ·
            refine ⟨2033486037221710437570113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1355657358147806958380075 2033486037221710437570113)
            ·
              refine ⟨1525114527916282828177585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2033486037221710437570113 1525114527916282828177585)
              ·
                refine ⟨1143835895937212121133189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1525114527916282828177585 1143835895937212121133189)
                ·
                  refine ⟨214469230488227272712473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1143835895937212121133189 214469230488227272712473)
                  ·
                    rfl

theorem cell21_939774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_939774 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_939774 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_939774 prefixEnd_939774 := by exact prefixLift 939774
  have htrace : WordTrace (prefixWord ++ tailWord_939774) baseStart_939774 baseEnd_939774 := by
    simpa [prefixWord, tailWord_939774, baseEnd_939774] using wordTrace_append hprefix tailTrace_939774
  have hstable : (prefixWord ++ tailWord_939774).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939774).length < 2 ^ (prefixWord ++ tailWord_939774).sum := by decide
  have hdescent : baseEnd_939774 < baseStart_939774 := by decide
  rcases family_descends (prefixWord ++ tailWord_939774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939833 : List Nat := [1, 2, 1, 7, 1, 1, 1, 1, 6]
def baseStart_939833 : Nat := 118140960795 + 939833 * 2 ^ 59
def prefixEnd_939833 : Nat := 4983230072969 + 3 ^ 40 * 939833 * 2
def baseEnd_939833 : Nat := 214482695092056281229019

theorem tailTrace_939833 : CollatzResearch.WordTrace tailWord_939833 prefixEnd_939833 214482695092056281229019 := by
  unfold tailWord_939833
  simp only [CollatzResearch.WordTrace]
  refine ⟨34278525604153026542600153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22852350402768684361733435 34278525604153026542600153)
  ·
    refine ⟨25708894203114769906950115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34278525604153026542600153 25708894203114769906950115)
    ·
      refine ⟨38563341304672154860425173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25708894203114769906950115 38563341304672154860425173)
      ·
        refine ⟨903828311828253629541215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 38563341304672154860425173 903828311828253629541215)
        ·
          refine ⟨1355742467742380444311823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 903828311828253629541215 1355742467742380444311823)
          ·
            refine ⟨2033613701613570666467735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1355742467742380444311823 2033613701613570666467735)
            ·
              refine ⟨3050420552420355999701603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2033613701613570666467735 3050420552420355999701603)
              ·
                refine ⟨4575630828630533999552405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3050420552420355999701603 4575630828630533999552405)
                ·
                  refine ⟨214482695092056281229019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4575630828630533999552405 214482695092056281229019)
                  ·
                    rfl

theorem cell21_939833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 6].length) (baseStart_939833 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_939833 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_939833 prefixEnd_939833 := by exact prefixLift 939833
  have htrace : WordTrace (prefixWord ++ tailWord_939833) baseStart_939833 baseEnd_939833 := by
    simpa [prefixWord, tailWord_939833, baseEnd_939833] using wordTrace_append hprefix tailTrace_939833
  have hstable : (prefixWord ++ tailWord_939833).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939833).length < 2 ^ (prefixWord ++ tailWord_939833).sum := by decide
  have hdescent : baseEnd_939833 < baseStart_939833 := by decide
  rcases family_descends (prefixWord ++ tailWord_939833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939861 : List Nat := [1, 3, 2, 2, 2, 2, 2, 2, 5]
def baseStart_939861 : Nat := 118140960795 + 939861 * 2 ^ 59
def prefixEnd_939861 : Nat := 4983230072969 + 3 ^ 40 * 939861 * 2
def baseEnd_939861 : Nat := 214489085073534454762295

theorem tailTrace_939861 : CollatzResearch.WordTrace tailWord_939861 prefixEnd_939861 214489085073534454762295 := by
  unfold tailWord_939861
  simp only [CollatzResearch.WordTrace]
  refine ⟨34279546848051587324619437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22853031232034391549746291 34279546848051587324619437)
  ·
    refine ⟨12854830068019345246732289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34279546848051587324619437 12854830068019345246732289)
    ·
      refine ⟨9641122551014508935049217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12854830068019345246732289 9641122551014508935049217)
      ·
        refine ⟨7230841913260881701286913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9641122551014508935049217 7230841913260881701286913)
        ·
          refine ⟨5423131434945661275965185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7230841913260881701286913 5423131434945661275965185)
          ·
            refine ⟨4067348576209245956973889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5423131434945661275965185 4067348576209245956973889)
            ·
              refine ⟨3050511432156934467730417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4067348576209245956973889 3050511432156934467730417)
              ·
                refine ⟨2287883574117700850797813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3050511432156934467730417 2287883574117700850797813)
                ·
                  refine ⟨214489085073534454762295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2287883574117700850797813 214489085073534454762295)
                  ·
                    rfl

theorem cell21_939861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 2, 5].length) (baseStart_939861 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_939861 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_939861 prefixEnd_939861 := by exact prefixLift 939861
  have htrace : WordTrace (prefixWord ++ tailWord_939861) baseStart_939861 baseEnd_939861 := by
    simpa [prefixWord, tailWord_939861, baseEnd_939861] using wordTrace_append hprefix tailTrace_939861
  have hstable : (prefixWord ++ tailWord_939861).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939861).length < 2 ^ (prefixWord ++ tailWord_939861).sum := by decide
  have hdescent : baseEnd_939861 < baseStart_939861 := by decide
  rcases family_descends (prefixWord ++ tailWord_939861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940027 : List Nat := [1, 1, 1, 1, 1, 3, 4, 5, 4]
def baseStart_940027 : Nat := 118140960795 + 940027 * 2 ^ 59
def prefixEnd_940027 : Nat := 4983230072969 + 3 ^ 40 * 940027 * 2
def baseEnd_940027 : Nat := 214526968535155054995289

theorem tailTrace_940027 : CollatzResearch.WordTrace tailWord_940027 prefixEnd_940027 214526968535155054995289 := by
  unfold tailWord_940027
  simp only [CollatzResearch.WordTrace]
  refine ⟨34285601365450197675162335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22857067576966798450108223 34285601365450197675162335)
  ·
    refine ⟨51428402048175296512743503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34285601365450197675162335 51428402048175296512743503)
    ·
      refine ⟨77142603072262944769115255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51428402048175296512743503 77142603072262944769115255)
      ·
        refine ⟨115713904608394417153672883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77142603072262944769115255 115713904608394417153672883)
        ·
          refine ⟨173570856912591625730509325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115713904608394417153672883 173570856912591625730509325)
          ·
            refine ⟨65089071342221859648940997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173570856912591625730509325 65089071342221859648940997)
            ·
              refine ⟨12204200876666598684176437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65089071342221859648940997 12204200876666598684176437)
              ·
                refine ⟨1144143832187493626641541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12204200876666598684176437 1144143832187493626641541)
                ·
                  refine ⟨214526968535155054995289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1144143832187493626641541 214526968535155054995289)
                  ·
                    rfl

theorem cell21_940027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 5, 4].length) (baseStart_940027 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_940027 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_940027 prefixEnd_940027 := by exact prefixLift 940027
  have htrace : WordTrace (prefixWord ++ tailWord_940027) baseStart_940027 baseEnd_940027 := by
    simpa [prefixWord, tailWord_940027, baseEnd_940027] using wordTrace_append hprefix tailTrace_940027
  have hstable : (prefixWord ++ tailWord_940027).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940027).length < 2 ^ (prefixWord ++ tailWord_940027).sum := by decide
  have hdescent : baseEnd_940027 < baseStart_940027 := by decide
  rcases family_descends (prefixWord ++ tailWord_940027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940030 : List Nat := [4, 2, 2, 2, 1, 1, 2, 2, 5]
def baseStart_940030 : Nat := 118140960795 + 940030 * 2 ^ 59
def prefixEnd_940030 : Nat := 4983230072969 + 3 ^ 40 * 940030 * 2
def baseEnd_940030 : Nat := 214527653176027716445283

theorem tailTrace_940030 : CollatzResearch.WordTrace tailWord_940030 prefixEnd_940030 214527653176027716445283 := by
  unfold tailWord_940030
  simp only [CollatzResearch.WordTrace]
  refine ⟨4285713848054916148440193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22857140522959552791681029 4285713848054916148440193)
  ·
    refine ⟨3214285386041187111330145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4285713848054916148440193 3214285386041187111330145)
    ·
      refine ⟨2410714039530890333497609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3214285386041187111330145 2410714039530890333497609)
      ·
        refine ⟨1808035529648167750123207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2410714039530890333497609 1808035529648167750123207)
        ·
          refine ⟨2712053294472251625184811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1808035529648167750123207 2712053294472251625184811)
          ·
            refine ⟨4068079941708377437777217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2712053294472251625184811 4068079941708377437777217)
            ·
              refine ⟨3051059956281283078332913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4068079941708377437777217 3051059956281283078332913)
              ·
                refine ⟨2288294967210962308749685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3051059956281283078332913 2288294967210962308749685)
                ·
                  refine ⟨214527653176027716445283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2288294967210962308749685 214527653176027716445283)
                  ·
                    rfl

theorem cell21_940030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_940030 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_940030 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_940030 prefixEnd_940030 := by exact prefixLift 940030
  have htrace : WordTrace (prefixWord ++ tailWord_940030) baseStart_940030 baseEnd_940030 := by
    simpa [prefixWord, tailWord_940030, baseEnd_940030] using wordTrace_append hprefix tailTrace_940030
  have hstable : (prefixWord ++ tailWord_940030).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940030).length < 2 ^ (prefixWord ++ tailWord_940030).sum := by decide
  have hdescent : baseEnd_940030 < baseStart_940030 := by decide
  rcases family_descends (prefixWord ++ tailWord_940030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940058 : List Nat := [3, 1, 1, 3, 1, 5, 7]
def baseStart_940058 : Nat := 118140960795 + 940058 * 2 ^ 59
def prefixEnd_940058 : Nat := 4983230072969 + 3 ^ 40 * 940058 * 2
def baseEnd_940058 : Nat := 23837115906389543330951

theorem tailTrace_940058 : CollatzResearch.WordTrace tailWord_940058 prefixEnd_940058 23837115906389543330951 := by
  unfold tailWord_940058
  simp only [CollatzResearch.WordTrace]
  refine ⟨8571683007084472492385207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22857821352225259979693885 8571683007084472492385207)
  ·
    refine ⟨12857524510626708738577811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8571683007084472492385207 12857524510626708738577811)
    ·
      refine ⟨19286286765940063107866717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12857524510626708738577811 19286286765940063107866717)
      ·
        refine ⟨7232357537227523665450019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19286286765940063107866717 7232357537227523665450019)
        ·
          refine ⟨10848536305841285498175029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7232357537227523665450019 10848536305841285498175029)
          ·
            refine ⟨1017050278672620515453909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10848536305841285498175029 1017050278672620515453909)
            ·
              refine ⟨23837115906389543330951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1017050278672620515453909 23837115906389543330951)
              ·
                rfl

theorem cell21_940058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 7].length) (baseStart_940058 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_940058 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_940058 prefixEnd_940058 := by exact prefixLift 940058
  have htrace : WordTrace (prefixWord ++ tailWord_940058) baseStart_940058 baseEnd_940058 := by
    simpa [prefixWord, tailWord_940058, baseEnd_940058] using wordTrace_append hprefix tailTrace_940058
  have hstable : (prefixWord ++ tailWord_940058).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940058).length < 2 ^ (prefixWord ++ tailWord_940058).sum := by decide
  have hdescent : baseEnd_940058 < baseStart_940058 := by decide
  rcases family_descends (prefixWord ++ tailWord_940058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940078 : List Nat := [4, 1, 3, 1, 1, 4, 2, 1, 4]
def baseStart_940078 : Nat := 118140960795 + 940078 * 2 ^ 59
def prefixEnd_940078 : Nat := 4983230072969 + 3 ^ 40 * 940078 * 2
def baseEnd_940078 : Nat := 214538607429990299645185

theorem tailTrace_940078 : CollatzResearch.WordTrace tailWord_940078 prefixEnd_940078 214538607429990299645185 := by
  unfold tailWord_940078
  simp only [CollatzResearch.WordTrace]
  refine ⟨4285932686033179173158611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22858307658843622256845925 4285932686033179173158611)
  ·
    refine ⟨6428899029049768759737917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4285932686033179173158611 6428899029049768759737917)
    ·
      refine ⟨2410837135893663284901719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6428899029049768759737917 2410837135893663284901719)
      ·
        refine ⟨3616255703840494927352579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2410837135893663284901719 3616255703840494927352579)
        ·
          refine ⟨5424383555760742391028869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3616255703840494927352579 5424383555760742391028869)
          ·
            refine ⟨1017071916705139198317913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5424383555760742391028869 1017071916705139198317913)
            ·
              refine ⟨762803937528854398738435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1017071916705139198317913 762803937528854398738435)
              ·
                refine ⟨1144205906293281598107653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 762803937528854398738435 1144205906293281598107653)
                ·
                  refine ⟨214538607429990299645185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1144205906293281598107653 214538607429990299645185)
                  ·
                    rfl

theorem cell21_940078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 2, 1, 4].length) (baseStart_940078 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_940078 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_940078 prefixEnd_940078 := by exact prefixLift 940078
  have htrace : WordTrace (prefixWord ++ tailWord_940078) baseStart_940078 baseEnd_940078 := by
    simpa [prefixWord, tailWord_940078, baseEnd_940078] using wordTrace_append hprefix tailTrace_940078
  have hstable : (prefixWord ++ tailWord_940078).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940078).length < 2 ^ (prefixWord ++ tailWord_940078).sum := by decide
  have hdescent : baseEnd_940078 < baseStart_940078 := by decide
  rcases family_descends (prefixWord ++ tailWord_940078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940117 : List Nat := [1, 3, 2, 2, 1, 12]
def baseStart_940117 : Nat := 118140960795 + 940117 * 2 ^ 59
def prefixEnd_940117 : Nat := 4983230072969 + 3 ^ 40 * 940117 * 2
def baseEnd_940117 : Nat := 7946203991160551796115

theorem tailTrace_940117 : CollatzResearch.WordTrace tailWord_940117 prefixEnd_940117 7946203991160551796115 := by
  unfold tailWord_940117
  simp only [CollatzResearch.WordTrace]
  refine ⟨34288883935124143045938605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22859255956749428697292403 34288883935124143045938605)
  ·
    refine ⟨12858331475671553642226977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34288883935124143045938605 12858331475671553642226977)
    ·
      refine ⟨9643748606753665231670233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12858331475671553642226977 9643748606753665231670233)
      ·
        refine ⟨7232811455065248923752675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9643748606753665231670233 7232811455065248923752675)
        ·
          refine ⟨10849217182597873385629013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7232811455065248923752675 10849217182597873385629013)
          ·
            refine ⟨7946203991160551796115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 10849217182597873385629013 7946203991160551796115)
            ·
              rfl

theorem cell21_940117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 12].length) (baseStart_940117 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_940117 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_940117 prefixEnd_940117 := by exact prefixLift 940117
  have htrace : WordTrace (prefixWord ++ tailWord_940117) baseStart_940117 baseEnd_940117 := by
    simpa [prefixWord, tailWord_940117, baseEnd_940117] using wordTrace_append hprefix tailTrace_940117
  have hstable : (prefixWord ++ tailWord_940117).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940117).length < 2 ^ (prefixWord ++ tailWord_940117).sum := by decide
  have hdescent : baseEnd_940117 < baseStart_940117 := by decide
  rcases family_descends (prefixWord ++ tailWord_940117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940120 : List Nat := [2, 1, 2, 2, 1, 5, 2, 2, 4]
def baseStart_940120 : Nat := 118140960795 + 940120 * 2 ^ 59
def prefixEnd_940120 : Nat := 4983230072969 + 3 ^ 40 * 940120 * 2
def baseEnd_940120 : Nat := 214548192402207559945099

theorem tailTrace_940120 : CollatzResearch.WordTrace tailWord_940120 prefixEnd_940120 214548192402207559945099 := by
  unfold tailWord_940120
  simp only [CollatzResearch.WordTrace]
  refine ⟨17144496677056637279148907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22859328902742183038865209 17144496677056637279148907)
  ·
    refine ⟨25716745015584955918723361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17144496677056637279148907 25716745015584955918723361)
    ·
      refine ⟨19287558761688716939042521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25716745015584955918723361 19287558761688716939042521)
      ·
        refine ⟨14465669071266537704281891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19287558761688716939042521 14465669071266537704281891)
        ·
          refine ⟨21698503606899806556422837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14465669071266537704281891 21698503606899806556422837)
          ·
            refine ⟨2034234713146856864664641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21698503606899806556422837 2034234713146856864664641)
            ·
              refine ⟨1525676034860142648498481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2034234713146856864664641 1525676034860142648498481)
              ·
                refine ⟨1144257026145106986373861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1525676034860142648498481 1144257026145106986373861)
                ·
                  refine ⟨214548192402207559945099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1144257026145106986373861 214548192402207559945099)
                  ·
                    rfl

theorem cell21_940120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 2, 4].length) (baseStart_940120 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_940120 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_940120 prefixEnd_940120 := by exact prefixLift 940120
  have htrace : WordTrace (prefixWord ++ tailWord_940120) baseStart_940120 baseEnd_940120 := by
    simpa [prefixWord, tailWord_940120, baseEnd_940120] using wordTrace_append hprefix tailTrace_940120
  have hstable : (prefixWord ++ tailWord_940120).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940120).length < 2 ^ (prefixWord ++ tailWord_940120).sum := by decide
  have hdescent : baseEnd_940120 < baseStart_940120 := by decide
  rcases family_descends (prefixWord ++ tailWord_940120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940126 : List Nat := [4, 4, 1, 1, 3, 1, 1, 6]
def baseStart_940126 : Nat := 118140960795 + 940126 * 2 ^ 59
def prefixEnd_940126 : Nat := 4983230072969 + 3 ^ 40 * 940126 * 2
def baseEnd_940126 : Nat := 71516520561317627615029

theorem tailTrace_940126 : CollatzResearch.WordTrace tailWord_940126 prefixEnd_940126 71516520561317627615029 := by
  unfold tailWord_940126
  simp only [CollatzResearch.WordTrace]
  refine ⟨4286151524011442197877029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22859474794727691722010821 4286151524011442197877029)
  ·
    refine ⟨803653410752145412101943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4286151524011442197877029 803653410752145412101943)
    ·
      refine ⟨1205480116128218118152915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 803653410752145412101943 1205480116128218118152915)
      ·
        refine ⟨1808220174192327177229373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1205480116128218118152915 1808220174192327177229373)
        ·
          refine ⟨678082565322122691461015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1808220174192327177229373 678082565322122691461015)
          ·
            refine ⟨1017123847983184037191523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 678082565322122691461015 1017123847983184037191523)
            ·
              refine ⟨1525685771974776055787285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1017123847983184037191523 1525685771974776055787285)
              ·
                refine ⟨71516520561317627615029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1525685771974776055787285 71516520561317627615029)
                ·
                  rfl

theorem cell21_940126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 6].length) (baseStart_940126 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_940126 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_940126 prefixEnd_940126 := by exact prefixLift 940126
  have htrace : WordTrace (prefixWord ++ tailWord_940126) baseStart_940126 baseEnd_940126 := by
    simpa [prefixWord, tailWord_940126, baseEnd_940126] using wordTrace_append hprefix tailTrace_940126
  have hstable : (prefixWord ++ tailWord_940126).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940126).length < 2 ^ (prefixWord ++ tailWord_940126).sum := by decide
  have hdescent : baseEnd_940126 < baseStart_940126 := by decide
  rcases family_descends (prefixWord ++ tailWord_940126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940241 : List Nat := [1, 2, 2, 1, 2, 2, 2, 6, 3]
def baseStart_940241 : Nat := 118140960795 + 940241 * 2 ^ 59
def prefixEnd_940241 : Nat := 4983230072969 + 3 ^ 40 * 940241 * 2
def baseEnd_940241 : Nat := 214575806250738238428185

theorem tailTrace_940241 : CollatzResearch.WordTrace tailWord_940241 prefixEnd_940241 214575806250738238428185 := by
  unfold tailWord_940241
  simp only [CollatzResearch.WordTrace]
  refine ⟨34293406586674912223452577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22862271057783274815635051 34293406586674912223452577)
  ·
    refine ⟨25720054940006184167589433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34293406586674912223452577 25720054940006184167589433)
    ·
      refine ⟨19290041205004638125692075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25720054940006184167589433 19290041205004638125692075)
      ·
        refine ⟨28935061807506957188538113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19290041205004638125692075 28935061807506957188538113)
        ·
          refine ⟨21701296355630217891403585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28935061807506957188538113 21701296355630217891403585)
          ·
            refine ⟨16275972266722663418552689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21701296355630217891403585 16275972266722663418552689)
            ·
              refine ⟨12206979200041997563914517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16275972266722663418552689 12206979200041997563914517)
              ·
                refine ⟨572202150001968635808493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12206979200041997563914517 572202150001968635808493)
                ·
                  refine ⟨214575806250738238428185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 572202150001968635808493 214575806250738238428185)
                  ·
                    rfl

theorem cell21_940241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 6, 3].length) (baseStart_940241 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_940241 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_940241 prefixEnd_940241 := by exact prefixLift 940241
  have htrace : WordTrace (prefixWord ++ tailWord_940241) baseStart_940241 baseEnd_940241 := by
    simpa [prefixWord, tailWord_940241, baseEnd_940241] using wordTrace_append hprefix tailTrace_940241
  have hstable : (prefixWord ++ tailWord_940241).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940241).length < 2 ^ (prefixWord ++ tailWord_940241).sum := by decide
  have hdescent : baseEnd_940241 < baseStart_940241 := by decide
  rcases family_descends (prefixWord ++ tailWord_940241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940292 : List Nat := [2, 3, 2, 2, 3, 2, 2, 2, 3]
def baseStart_940292 : Nat := 118140960795 + 940292 * 2 ^ 59
def prefixEnd_940292 : Nat := 4983230072969 + 3 ^ 40 * 940292 * 2
def baseEnd_940292 : Nat := 214587445145573483078081

theorem tailTrace_940292 : CollatzResearch.WordTrace tailWord_940292 prefixEnd_940292 214587445145573483078081 := by
  unfold tailWord_940292
  simp only [CollatzResearch.WordTrace]
  refine ⟨17147633354745073966779565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22863511139660098622372753 17147633354745073966779565)
  ·
    refine ⟨6430362508029402737542337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17147633354745073966779565 6430362508029402737542337)
    ·
      refine ⟨4822771881022052053156753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6430362508029402737542337 4822771881022052053156753)
      ·
        refine ⟨3617078910766539039867565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4822771881022052053156753 3617078910766539039867565)
        ·
          refine ⟨1356404591537452139950337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3617078910766539039867565 1356404591537452139950337)
          ·
            refine ⟨1017303443653089104962753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1356404591537452139950337 1017303443653089104962753)
            ·
              refine ⟨762977582739816828722065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1017303443653089104962753 762977582739816828722065)
              ·
                refine ⟨572233187054862621541549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 762977582739816828722065 572233187054862621541549)
                ·
                  refine ⟨214587445145573483078081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 572233187054862621541549 214587445145573483078081)
                  ·
                    rfl

theorem cell21_940292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 2, 2, 3].length) (baseStart_940292 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_940292 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_940292 prefixEnd_940292 := by exact prefixLift 940292
  have htrace : WordTrace (prefixWord ++ tailWord_940292) baseStart_940292 baseEnd_940292 := by
    simpa [prefixWord, tailWord_940292, baseEnd_940292] using wordTrace_append hprefix tailTrace_940292
  have hstable : (prefixWord ++ tailWord_940292).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940292).length < 2 ^ (prefixWord ++ tailWord_940292).sum := by decide
  have hdescent : baseEnd_940292 < baseStart_940292 := by decide
  rcases family_descends (prefixWord ++ tailWord_940292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940300 : List Nat := [2, 2, 1, 2, 2, 2, 2, 3, 5]
def baseStart_940300 : Nat := 118140960795 + 940300 * 2 ^ 59
def prefixEnd_940300 : Nat := 4983230072969 + 3 ^ 40 * 940300 * 2
def baseEnd_940300 : Nat := 214589270854567246944731

theorem tailTrace_940300 : CollatzResearch.WordTrace tailWord_940300 prefixEnd_940300 214589270854567246944731 := by
  unfold tailWord_940300
  simp only [CollatzResearch.WordTrace]
  refine ⟨17147779246730582649925177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22863705662307443533233569 17147779246730582649925177)
  ·
    refine ⟨12860834435047936987443883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17147779246730582649925177 12860834435047936987443883)
    ·
      refine ⟨19291251652571905481165825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12860834435047936987443883 19291251652571905481165825)
      ·
        refine ⟨14468438739428929110874369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19291251652571905481165825 14468438739428929110874369)
        ·
          refine ⟨10851329054571696833155777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14468438739428929110874369 10851329054571696833155777)
          ·
            refine ⟨8138496790928772624866833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10851329054571696833155777 8138496790928772624866833)
            ·
              refine ⟨6103872593196579468650125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8138496790928772624866833 6103872593196579468650125)
              ·
                refine ⟨2288952222448717300743797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6103872593196579468650125 2288952222448717300743797)
                ·
                  refine ⟨214589270854567246944731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2288952222448717300743797 214589270854567246944731)
                  ·
                    rfl

theorem cell21_940300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 3, 5].length) (baseStart_940300 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_940300 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_940300 prefixEnd_940300 := by exact prefixLift 940300
  have htrace : WordTrace (prefixWord ++ tailWord_940300) baseStart_940300 baseEnd_940300 := by
    simpa [prefixWord, tailWord_940300, baseEnd_940300] using wordTrace_append hprefix tailTrace_940300
  have hstable : (prefixWord ++ tailWord_940300).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940300).length < 2 ^ (prefixWord ++ tailWord_940300).sum := by decide
  have hdescent : baseEnd_940300 < baseStart_940300 := by decide
  rcases family_descends (prefixWord ++ tailWord_940300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940461 : List Nat := [1, 5, 2, 2, 3, 1, 2, 2, 3]
def baseStart_940461 : Nat := 118140960795 + 940461 * 2 ^ 59
def prefixEnd_940461 : Nat := 4983230072969 + 3 ^ 40 * 940461 * 2
def baseEnd_940461 : Nat := 214626013248066744761069

theorem tailTrace_940461 : CollatzResearch.WordTrace tailWord_940461 prefixEnd_940461 214626013248066744761069 := by
  unfold tailWord_940461
  simp only [CollatzResearch.WordTrace]
  refine ⟨34301430645877889796461237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22867620430585259864307491 34301430645877889796461237)
  ·
    refine ⟨3215759123051052168418241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34301430645877889796461237 3215759123051052168418241)
    ·
      refine ⟨2411819342288289126313681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3215759123051052168418241 2411819342288289126313681)
      ·
        refine ⟨1808864506716216844735261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2411819342288289126313681 1808864506716216844735261)
        ·
          refine ⟨678324190018581316775723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1808864506716216844735261 678324190018581316775723)
          ·
            refine ⟨1017486285027871975163585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 678324190018581316775723 1017486285027871975163585)
            ·
              refine ⟨763114713770903981372689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1017486285027871975163585 763114713770903981372689)
              ·
                refine ⟨572336035328177986029517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 763114713770903981372689 572336035328177986029517)
                ·
                  refine ⟨214626013248066744761069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 572336035328177986029517 214626013248066744761069)
                  ·
                    rfl

theorem cell21_940461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 2, 2, 3].length) (baseStart_940461 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_940461 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_940461 prefixEnd_940461 := by exact prefixLift 940461
  have htrace : WordTrace (prefixWord ++ tailWord_940461) baseStart_940461 baseEnd_940461 := by
    simpa [prefixWord, tailWord_940461, baseEnd_940461] using wordTrace_append hprefix tailTrace_940461
  have hstable : (prefixWord ++ tailWord_940461).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940461).length < 2 ^ (prefixWord ++ tailWord_940461).sum := by decide
  have hdescent : baseEnd_940461 < baseStart_940461 := by decide
  rcases family_descends (prefixWord ++ tailWord_940461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940517 : List Nat := [1, 3, 1, 5, 2, 2, 1, 2, 4]
def baseStart_940517 : Nat := 118140960795 + 940517 * 2 ^ 59
def prefixEnd_940517 : Nat := 4983230072969 + 3 ^ 40 * 940517 * 2
def baseEnd_940517 : Nat := 214638793211023091827621

theorem tailTrace_940517 : CollatzResearch.WordTrace tailWord_940517 prefixEnd_940517 214638793211023091827621 := by
  unfold tailWord_940517
  simp only [CollatzResearch.WordTrace]
  refine ⟨34303473133675011360499805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22868982089116674240333203 34303473133675011360499805)
  ·
    refine ⟨12863802425128129260187427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34303473133675011360499805 12863802425128129260187427)
    ·
      refine ⟨19295703637692193890281141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12863802425128129260187427 19295703637692193890281141)
      ·
        refine ⟨1808972216033643177213857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19295703637692193890281141 1808972216033643177213857)
        ·
          refine ⟨1356729162025232382910393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1808972216033643177213857 1356729162025232382910393)
          ·
            refine ⟨1017546871518924287182795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1356729162025232382910393 1017546871518924287182795)
            ·
              refine ⟨1526320307278386430774193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1017546871518924287182795 1526320307278386430774193)
              ·
                refine ⟨1144740230458789823080645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1526320307278386430774193 1144740230458789823080645)
                ·
                  refine ⟨214638793211023091827621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1144740230458789823080645 214638793211023091827621)
                  ·
                    rfl

theorem cell21_940517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 2, 4].length) (baseStart_940517 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_940517 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_940517 prefixEnd_940517 := by exact prefixLift 940517
  have htrace : WordTrace (prefixWord ++ tailWord_940517) baseStart_940517 baseEnd_940517 := by
    simpa [prefixWord, tailWord_940517, baseEnd_940517] using wordTrace_append hprefix tailTrace_940517
  have hstable : (prefixWord ++ tailWord_940517).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940517).length < 2 ^ (prefixWord ++ tailWord_940517).sum := by decide
  have hdescent : baseEnd_940517 < baseStart_940517 := by decide
  rcases family_descends (prefixWord ++ tailWord_940517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940528 : List Nat := [2, 1, 1, 1, 3, 3, 4, 1, 5]
def baseStart_940528 : Nat := 118140960795 + 940528 * 2 ^ 59
def prefixEnd_940528 : Nat := 4983230072969 + 3 ^ 40 * 940528 * 2
def baseEnd_940528 : Nat := 214641303560889517144265

theorem tailTrace_940528 : CollatzResearch.WordTrace tailWord_940528 prefixEnd_940528 214641303560889517144265 := by
  unfold tailWord_940528
  simp only [CollatzResearch.WordTrace]
  refine ⟨17151937168317580119575119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22869249557756773492766825 17151937168317580119575119)
  ·
    refine ⟨25727905752476370179362679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17151937168317580119575119 25727905752476370179362679)
    ·
      refine ⟨38591858628714555269044019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25727905752476370179362679 38591858628714555269044019)
      ·
        refine ⟨57887787943071832903566029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38591858628714555269044019 57887787943071832903566029)
        ·
          refine ⟨21707920478651937338837261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57887787943071832903566029 21707920478651937338837261)
          ·
            refine ⟨8140470179494476502063973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21707920478651937338837261 8140470179494476502063973)
            ·
              refine ⟨1526338158655214344136995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8140470179494476502063973 1526338158655214344136995)
              ·
                refine ⟨2289507237982821516205493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1526338158655214344136995 2289507237982821516205493)
                ·
                  refine ⟨214641303560889517144265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2289507237982821516205493 214641303560889517144265)
                  ·
                    rfl

theorem cell21_940528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 1, 5].length) (baseStart_940528 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_940528 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_940528 prefixEnd_940528 := by exact prefixLift 940528
  have htrace : WordTrace (prefixWord ++ tailWord_940528) baseStart_940528 baseEnd_940528 := by
    simpa [prefixWord, tailWord_940528, baseEnd_940528] using wordTrace_append hprefix tailTrace_940528
  have hstable : (prefixWord ++ tailWord_940528).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940528).length < 2 ^ (prefixWord ++ tailWord_940528).sum := by decide
  have hdescent : baseEnd_940528 < baseStart_940528 := by decide
  rcases family_descends (prefixWord ++ tailWord_940528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940573 : List Nat := [1, 4, 2, 2, 1, 2, 9]
def baseStart_940573 : Nat := 118140960795 + 940573 * 2 ^ 59
def prefixEnd_940573 : Nat := 4983230072969 + 3 ^ 40 * 940573 * 2
def baseEnd_940573 : Nat := 23850174797108826543797

theorem tailTrace_940573 : CollatzResearch.WordTrace tailWord_940573 prefixEnd_940573 23850174797108826543797 := by
  unfold tailWord_940573
  simp only [CollatzResearch.WordTrace]
  refine ⟨34305515621472132924538373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22870343747648088616358915 34305515621472132924538373)
  ·
    refine ⟨6432284179026024923350945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34305515621472132924538373 6432284179026024923350945)
    ·
      refine ⟨4824213134269518692513209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6432284179026024923350945 4824213134269518692513209)
      ·
        refine ⟨3618159850702139019384907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4824213134269518692513209 3618159850702139019384907)
        ·
          refine ⟨5427239776053208529077361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3618159850702139019384907 5427239776053208529077361)
          ·
            refine ⟨4070429832039906396808021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5427239776053208529077361 4070429832039906396808021)
            ·
              refine ⟨23850174797108826543797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4070429832039906396808021 23850174797108826543797)
              ·
                rfl

theorem cell21_940573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 9].length) (baseStart_940573 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_940573 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_940573 prefixEnd_940573 := by exact prefixLift 940573
  have htrace : WordTrace (prefixWord ++ tailWord_940573) baseStart_940573 baseEnd_940573 := by
    simpa [prefixWord, tailWord_940573, baseEnd_940573] using wordTrace_append hprefix tailTrace_940573
  have hstable : (prefixWord ++ tailWord_940573).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940573).length < 2 ^ (prefixWord ++ tailWord_940573).sum := by decide
  have hdescent : baseEnd_940573 < baseStart_940573 := by decide
  rcases family_descends (prefixWord ++ tailWord_940573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940663 : List Nat := [1, 1, 3, 1, 1, 3, 3, 1, 7]
def baseStart_940663 : Nat := 118140960795 + 940663 * 2 ^ 59
def prefixEnd_940663 : Nat := 4983230072969 + 3 ^ 40 * 940663 * 2
def baseEnd_940663 : Nat := 214672112400159282393989

theorem tailTrace_940663 : CollatzResearch.WordTrace tailWord_940663 prefixEnd_940663 214672112400159282393989 := by
  unfold tailWord_940663
  simp only [CollatzResearch.WordTrace]
  refine ⟨34308798191146078295314643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22872532127430718863543095 34308798191146078295314643)
  ·
    refine ⟨51463197286719117442971965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34308798191146078295314643 51463197286719117442971965)
    ·
      refine ⟨19298698982519669041114487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51463197286719117442971965 19298698982519669041114487)
      ·
        refine ⟨28948048473779503561671731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19298698982519669041114487 28948048473779503561671731)
        ·
          refine ⟨43422072710669255342507597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28948048473779503561671731 43422072710669255342507597)
          ·
            refine ⟨16283277266500970753440349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43422072710669255342507597 16283277266500970753440349)
            ·
              refine ⟨6106228974937864032540131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16283277266500970753440349 6106228974937864032540131)
              ·
                refine ⟨9159343462406796048810197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6106228974937864032540131 9159343462406796048810197)
                ·
                  refine ⟨214672112400159282393989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9159343462406796048810197 214672112400159282393989)
                  ·
                    rfl

theorem cell21_940663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 7].length) (baseStart_940663 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_940663 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_940663 prefixEnd_940663 := by exact prefixLift 940663
  have htrace : WordTrace (prefixWord ++ tailWord_940663) baseStart_940663 baseEnd_940663 := by
    simpa [prefixWord, tailWord_940663, baseEnd_940663] using wordTrace_append hprefix tailTrace_940663
  have hstable : (prefixWord ++ tailWord_940663).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940663).length < 2 ^ (prefixWord ++ tailWord_940663).sum := by decide
  have hdescent : baseEnd_940663 < baseStart_940663 := by decide
  rcases family_descends (prefixWord ++ tailWord_940663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940784 : List Nat := [2, 1, 1, 1, 3, 1, 3, 9]
def baseStart_940784 : Nat := 118140960795 + 940784 * 2 ^ 59
def prefixEnd_940784 : Nat := 4983230072969 + 3 ^ 40 * 940784 * 2
def baseEnd_940784 : Nat := 71566575416229986959025

theorem tailTrace_940784 : CollatzResearch.WordTrace tailWord_940784 prefixEnd_940784 71566575416229986959025 := by
  unfold tailWord_940784
  simp only [CollatzResearch.WordTrace]
  refine ⟨17156605711853857980234703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22875474282471810640312937 17156605711853857980234703)
  ·
    refine ⟨25734908567780786970352055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17156605711853857980234703 25734908567780786970352055)
    ·
      refine ⟨38602362851671180455528083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25734908567780786970352055 38602362851671180455528083)
      ·
        refine ⟨57903544277506770683292125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38602362851671180455528083 57903544277506770683292125)
        ·
          refine ⟨21713829104065039006234547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57903544277506770683292125 21713829104065039006234547)
          ·
            refine ⟨32570743656097558509351821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21713829104065039006234547 32570743656097558509351821)
            ·
              refine ⟨12214028871036584441006933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32570743656097558509351821 12214028871036584441006933)
              ·
                refine ⟨71566575416229986959025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12214028871036584441006933 71566575416229986959025)
                ·
                  rfl

theorem cell21_940784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 9].length) (baseStart_940784 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_940784 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_940784 prefixEnd_940784 := by exact prefixLift 940784
  have htrace : WordTrace (prefixWord ++ tailWord_940784) baseStart_940784 baseEnd_940784 := by
    simpa [prefixWord, tailWord_940784, baseEnd_940784] using wordTrace_append hprefix tailTrace_940784
  have hstable : (prefixWord ++ tailWord_940784).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940784).length < 2 ^ (prefixWord ++ tailWord_940784).sum := by decide
  have hdescent : baseEnd_940784 < baseStart_940784 := by decide
  rcases family_descends (prefixWord ++ tailWord_940784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940807 : List Nat := [1, 1, 4, 4, 1, 3, 2, 2, 3]
def baseStart_940807 : Nat := 118140960795 + 940807 * 2 ^ 59
def prefixEnd_940807 : Nat := 4983230072969 + 3 ^ 40 * 940807 * 2
def baseEnd_940807 : Nat := 214704975162047031993695

theorem tailTrace_940807 : CollatzResearch.WordTrace tailWord_940807 prefixEnd_940807 214704975162047031993695 := by
  unfold tailWord_940807
  simp only [CollatzResearch.WordTrace]
  refine ⟨34314050302624390888556675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22876033535082927259037783 34314050302624390888556675)
  ·
    refine ⟨51471075453936586332835013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34314050302624390888556675 51471075453936586332835013)
    ·
      refine ⟨9650826647613109937406565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51471075453936586332835013 9650826647613109937406565)
      ·
        refine ⟨1809529996427458113263731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9650826647613109937406565 1809529996427458113263731)
        ·
          refine ⟨2714294994641187169895597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1809529996427458113263731 2714294994641187169895597)
          ·
            refine ⟨1017860622990445188710849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2714294994641187169895597 1017860622990445188710849)
            ·
              refine ⟨763395467242833891533137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1017860622990445188710849 763395467242833891533137)
              ·
                refine ⟨572546600432125418649853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 763395467242833891533137 572546600432125418649853)
                ·
                  refine ⟨214704975162047031993695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 572546600432125418649853 214704975162047031993695)
                  ·
                    rfl

theorem cell21_940807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 2, 2, 3].length) (baseStart_940807 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_940807 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_940807 prefixEnd_940807 := by exact prefixLift 940807
  have htrace : WordTrace (prefixWord ++ tailWord_940807) baseStart_940807 baseEnd_940807 := by
    simpa [prefixWord, tailWord_940807, baseEnd_940807] using wordTrace_append hprefix tailTrace_940807
  have hstable : (prefixWord ++ tailWord_940807).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940807).length < 2 ^ (prefixWord ++ tailWord_940807).sum := by decide
  have hdescent : baseEnd_940807 < baseStart_940807 := by decide
  rcases family_descends (prefixWord ++ tailWord_940807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940815 : List Nat := [1, 1, 2, 1, 1, 1, 6, 3, 5]
def baseStart_940815 : Nat := 118140960795 + 940815 * 2 ^ 59
def prefixEnd_940815 : Nat := 4983230072969 + 3 ^ 40 * 940815 * 2
def baseEnd_940815 : Nat := 214706800871040795860345

theorem tailTrace_940815 : CollatzResearch.WordTrace tailWord_940815 prefixEnd_940815 214706800871040795860345 := by
  unfold tailWord_940815
  simp only [CollatzResearch.WordTrace]
  refine ⟨34314342086595408254847899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22876228057730272169898599 34314342086595408254847899)
  ·
    refine ⟨51471513129893112382271849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34314342086595408254847899 51471513129893112382271849)
    ·
      refine ⟨38603634847419834286703887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51471513129893112382271849 38603634847419834286703887)
      ·
        refine ⟨57905452271129751430055831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38603634847419834286703887 57905452271129751430055831)
        ·
          refine ⟨86858178406694627145083747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57905452271129751430055831 86858178406694627145083747)
          ·
            refine ⟨130287267610041940717625621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86858178406694627145083747 130287267610041940717625621)
            ·
              refine ⟨6107215669220715971138701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 130287267610041940717625621 6107215669220715971138701)
              ·
                refine ⟨2290205875957768489177013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6107215669220715971138701 2290205875957768489177013)
                ·
                  refine ⟨214706800871040795860345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2290205875957768489177013 214706800871040795860345)
                  ·
                    rfl

theorem cell21_940815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 3, 5].length) (baseStart_940815 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_940815 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_940815 prefixEnd_940815 := by exact prefixLift 940815
  have htrace : WordTrace (prefixWord ++ tailWord_940815) baseStart_940815 baseEnd_940815 := by
    simpa [prefixWord, tailWord_940815, baseEnd_940815] using wordTrace_append hprefix tailTrace_940815
  have hstable : (prefixWord ++ tailWord_940815).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940815).length < 2 ^ (prefixWord ++ tailWord_940815).sum := by decide
  have hdescent : baseEnd_940815 < baseStart_940815 := by decide
  rcases family_descends (prefixWord ++ tailWord_940815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940832 : List Nat := [2, 1, 1, 5, 1, 3, 1, 2, 5]
def baseStart_940832 : Nat := 118140960795 + 940832 * 2 ^ 59
def prefixEnd_940832 : Nat := 4983230072969 + 3 ^ 40 * 940832 * 2
def baseEnd_940832 : Nat := 214710680502652544076977

theorem tailTrace_940832 : CollatzResearch.WordTrace tailWord_940832 prefixEnd_940832 214710680502652544076977 := by
  unfold tailWord_940832
  simp only [CollatzResearch.WordTrace]
  refine ⟨17157481063766910079108375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22876641418355880105477833 17157481063766910079108375)
  ·
    refine ⟨25736221595650365118662563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17157481063766910079108375 25736221595650365118662563)
    ·
      refine ⟨38604332393475547677993845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25736221595650365118662563 38604332393475547677993845)
      ·
        refine ⟨3619156161888332594811923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38604332393475547677993845 3619156161888332594811923)
        ·
          refine ⟨5428734242832498892217885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3619156161888332594811923 5428734242832498892217885)
          ·
            refine ⟨2035775341062187084581707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5428734242832498892217885 2035775341062187084581707)
            ·
              refine ⟨3053663011593280626872561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2035775341062187084581707 3053663011593280626872561)
              ·
                refine ⟨2290247258694960470154421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3053663011593280626872561 2290247258694960470154421)
                ·
                  refine ⟨214710680502652544076977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2290247258694960470154421 214710680502652544076977)
                  ·
                    rfl

theorem cell21_940832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 2, 5].length) (baseStart_940832 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_940832 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_940832 prefixEnd_940832 := by exact prefixLift 940832
  have htrace : WordTrace (prefixWord ++ tailWord_940832) baseStart_940832 baseEnd_940832 := by
    simpa [prefixWord, tailWord_940832, baseEnd_940832] using wordTrace_append hprefix tailTrace_940832
  have hstable : (prefixWord ++ tailWord_940832).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940832).length < 2 ^ (prefixWord ++ tailWord_940832).sum := by decide
  have hdescent : baseEnd_940832 < baseStart_940832 := by decide
  rcases family_descends (prefixWord ++ tailWord_940832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940849 : List Nat := [1, 2, 2, 3, 2, 1, 4, 3, 3]
def baseStart_940849 : Nat := 118140960795 + 940849 * 2 ^ 59
def prefixEnd_940849 : Nat := 4983230072969 + 3 ^ 40 * 940849 * 2
def baseEnd_940849 : Nat := 214714560134264292293609

theorem tailTrace_940849 : CollatzResearch.WordTrace tailWord_940849 prefixEnd_940849 214714560134264292293609 := by
  unfold tailWord_940849
  simp only [CollatzResearch.WordTrace]
  refine ⟨34315582168472232061585601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22877054778981488041057067 34315582168472232061585601)
  ·
    refine ⟨25736686626354174046189201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34315582168472232061585601 25736686626354174046189201)
    ·
      refine ⟨19302514969765630534641901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25736686626354174046189201 19302514969765630534641901)
      ·
        refine ⟨7238443113662111450490713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19302514969765630534641901 7238443113662111450490713)
        ·
          refine ⟨5428832335246583587868035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7238443113662111450490713 5428832335246583587868035)
          ·
            refine ⟨8143248502869875381802053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5428832335246583587868035 8143248502869875381802053)
            ·
              refine ⟨1526859094288101634087885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8143248502869875381802053 1526859094288101634087885)
              ·
                refine ⟨572572160358038112782957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1526859094288101634087885 572572160358038112782957)
                ·
                  refine ⟨214714560134264292293609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 572572160358038112782957 214714560134264292293609)
                  ·
                    rfl

theorem cell21_940849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 3, 3].length) (baseStart_940849 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_940849 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_940849 prefixEnd_940849 := by exact prefixLift 940849
  have htrace : WordTrace (prefixWord ++ tailWord_940849) baseStart_940849 baseEnd_940849 := by
    simpa [prefixWord, tailWord_940849, baseEnd_940849] using wordTrace_append hprefix tailTrace_940849
  have hstable : (prefixWord ++ tailWord_940849).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940849).length < 2 ^ (prefixWord ++ tailWord_940849).sum := by decide
  have hdescent : baseEnd_940849 < baseStart_940849 := by decide
  rcases family_descends (prefixWord ++ tailWord_940849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940863 : List Nat := [1, 1, 2, 2, 5, 1, 3, 2, 4]
def baseStart_940863 : Nat := 118140960795 + 940863 * 2 ^ 59
def prefixEnd_940863 : Nat := 4983230072969 + 3 ^ 40 * 940863 * 2
def baseEnd_940863 : Nat := 214717755125003379060247

theorem tailTrace_940863 : CollatzResearch.WordTrace tailWord_940863 prefixEnd_940863 214717755125003379060247 := by
  unfold tailWord_940863
  simp only [CollatzResearch.WordTrace]
  refine ⟨34316092790421512452595243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22877395193614341635063495 34316092790421512452595243)
  ·
    refine ⟨51474139185632268678892865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34316092790421512452595243 51474139185632268678892865)
    ·
      refine ⟨38605604389224201509169649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51474139185632268678892865 38605604389224201509169649)
      ·
        refine ⟨28954203291918151131877237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38605604389224201509169649 28954203291918151131877237)
        ·
          refine ⟨2714456558617326668613491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28954203291918151131877237 2714456558617326668613491)
          ·
            refine ⟨4071684837925990002920237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2714456558617326668613491 4071684837925990002920237)
            ·
              refine ⟨1526881814222246251095089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4071684837925990002920237 1526881814222246251095089)
              ·
                refine ⟨1145161360666684688321317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1526881814222246251095089 1145161360666684688321317)
                ·
                  refine ⟨214717755125003379060247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1145161360666684688321317 214717755125003379060247)
                  ·
                    rfl

theorem cell21_940863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 2, 4].length) (baseStart_940863 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_940863 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_940863 prefixEnd_940863 := by exact prefixLift 940863
  have htrace : WordTrace (prefixWord ++ tailWord_940863) baseStart_940863 baseEnd_940863 := by
    simpa [prefixWord, tailWord_940863, baseEnd_940863] using wordTrace_append hprefix tailTrace_940863
  have hstable : (prefixWord ++ tailWord_940863).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940863).length < 2 ^ (prefixWord ++ tailWord_940863).sum := by decide
  have hdescent : baseEnd_940863 < baseStart_940863 := by decide
  rcases family_descends (prefixWord ++ tailWord_940863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940922 : List Nat := [3, 1, 1, 1, 1, 1, 3, 6, 4]
def baseStart_940922 : Nat := 118140960795 + 940922 * 2 ^ 59
def prefixEnd_940922 : Nat := 4983230072969 + 3 ^ 40 * 940922 * 2
def baseEnd_940922 : Nat := 214731219728832387576793

theorem tailTrace_940922 : CollatzResearch.WordTrace tailWord_940922 prefixEnd_940922 214731219728832387576793 := by
  unfold tailWord_940922
  simp only [CollatzResearch.WordTrace]
  refine ⟨8579561174301941382248255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22878829798138510352662013 8579561174301941382248255)
  ·
    refine ⟨12869341761452912073372383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8579561174301941382248255 12869341761452912073372383)
    ·
      refine ⟨19304012642179368110058575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12869341761452912073372383 19304012642179368110058575)
      ·
        refine ⟨28956018963269052165087863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19304012642179368110058575 28956018963269052165087863)
        ·
          refine ⟨43434028444903578247631795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28956018963269052165087863 43434028444903578247631795)
          ·
            refine ⟨65151042667355367371447693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43434028444903578247631795 65151042667355367371447693)
            ·
              refine ⟨24431641000258262764292885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65151042667355367371447693 24431641000258262764292885)
              ·
                refine ⟨1145233171887106067076229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24431641000258262764292885 1145233171887106067076229)
                ·
                  refine ⟨214731219728832387576793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1145233171887106067076229 214731219728832387576793)
                  ·
                    rfl

theorem cell21_940922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 6, 4].length) (baseStart_940922 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_940922 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_940922 prefixEnd_940922 := by exact prefixLift 940922
  have htrace : WordTrace (prefixWord ++ tailWord_940922) baseStart_940922 baseEnd_940922 := by
    simpa [prefixWord, tailWord_940922, baseEnd_940922] using wordTrace_append hprefix tailTrace_940922
  have hstable : (prefixWord ++ tailWord_940922).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940922).length < 2 ^ (prefixWord ++ tailWord_940922).sum := by decide
  have hdescent : baseEnd_940922 < baseStart_940922 := by decide
  rcases family_descends (prefixWord ++ tailWord_940922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940939 : List Nat := [1, 1, 1, 1, 4, 2, 6, 1, 4]
def baseStart_940939 : Nat := 118140960795 + 940939 * 2 ^ 59
def prefixEnd_940939 : Nat := 4983230072969 + 3 ^ 40 * 940939 * 2
def baseEnd_940939 : Nat := 214735099360444135793425

theorem tailTrace_940939 : CollatzResearch.WordTrace tailWord_940939 prefixEnd_940939 214735099360444135793425 := by
  unfold tailWord_940939
  simp only [CollatzResearch.WordTrace]
  refine ⟨34318864738146177432361871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22879243158764118288241247 34318864738146177432361871)
  ·
    refine ⟨51478297107219266148542807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34318864738146177432361871 51478297107219266148542807)
    ·
      refine ⟨77217445660828899222814211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51478297107219266148542807 77217445660828899222814211)
      ·
        refine ⟨115826168491243348834221317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77217445660828899222814211 115826168491243348834221317)
        ·
          refine ⟨21717406592108127906416497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115826168491243348834221317 21717406592108127906416497)
          ·
            refine ⟨16288054944081095929812373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21717406592108127906416497 16288054944081095929812373)
            ·
              refine ⟨763502575503801371709955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16288054944081095929812373 763502575503801371709955)
              ·
                refine ⟨1145253863255702057564933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 763502575503801371709955 1145253863255702057564933)
                ·
                  refine ⟨214735099360444135793425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1145253863255702057564933 214735099360444135793425)
                  ·
                    rfl

theorem cell21_940939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 6, 1, 4].length) (baseStart_940939 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_940939 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_940939 prefixEnd_940939 := by exact prefixLift 940939
  have htrace : WordTrace (prefixWord ++ tailWord_940939) baseStart_940939 baseEnd_940939 := by
    simpa [prefixWord, tailWord_940939, baseEnd_940939] using wordTrace_append hprefix tailTrace_940939
  have hstable : (prefixWord ++ tailWord_940939).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940939).length < 2 ^ (prefixWord ++ tailWord_940939).sum := by decide
  have hdescent : baseEnd_940939 < baseStart_940939 := by decide
  rcases family_descends (prefixWord ++ tailWord_940939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940973 : List Nat := [1, 5, 2, 3, 1, 1, 2, 2, 4]
def baseStart_940973 : Nat := 118140960795 + 940973 * 2 ^ 59
def prefixEnd_940973 : Nat := 4983230072969 + 3 ^ 40 * 940973 * 2
def baseEnd_940973 : Nat := 214742858623667632226689

theorem tailTrace_940973 : CollatzResearch.WordTrace tailWord_940973 prefixEnd_940973 214742858623667632226689 := by
  unfold tailWord_940973
  simp only [CollatzResearch.WordTrace]
  refine ⟨34320104820023001239099573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22880069880015334159399715 34320104820023001239099573)
  ·
    refine ⟨3217509826877156366165585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34320104820023001239099573 3217509826877156366165585)
    ·
      refine ⟨2413132370157867274624189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3217509826877156366165585 2413132370157867274624189)
      ·
        refine ⟨904924638809200227984071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2413132370157867274624189 904924638809200227984071)
        ·
          refine ⟨1357386958213800341976107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 904924638809200227984071 1357386958213800341976107)
          ·
            refine ⟨2036080437320700512964161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1357386958213800341976107 2036080437320700512964161)
            ·
              refine ⟨1527060327990525384723121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2036080437320700512964161 1527060327990525384723121)
              ·
                refine ⟨1145295245992894038542341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1527060327990525384723121 1145295245992894038542341)
                ·
                  refine ⟨214742858623667632226689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1145295245992894038542341 214742858623667632226689)
                  ·
                    rfl

theorem cell21_940973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_940973 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_940973 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_940973 prefixEnd_940973 := by exact prefixLift 940973
  have htrace : WordTrace (prefixWord ++ tailWord_940973) baseStart_940973 baseEnd_940973 := by
    simpa [prefixWord, tailWord_940973, baseEnd_940973] using wordTrace_append hprefix tailTrace_940973
  have hstable : (prefixWord ++ tailWord_940973).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940973).length < 2 ^ (prefixWord ++ tailWord_940973).sum := by decide
  have hdescent : baseEnd_940973 < baseStart_940973 := by decide
  rcases family_descends (prefixWord ++ tailWord_940973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941077 : List Nat := [1, 3, 2, 1, 4, 1, 3, 3, 3]
def baseStart_941077 : Nat := 118140960795 + 941077 * 2 ^ 59
def prefixEnd_941077 : Nat := 4983230072969 + 3 ^ 40 * 941077 * 2
def baseEnd_941077 : Nat := 214766592840586562493143

theorem tailTrace_941077 : CollatzResearch.WordTrace tailWord_941077 prefixEnd_941077 214766592840586562493143 := by
  unfold tailWord_941077
  simp only [CollatzResearch.WordTrace]
  refine ⟨34323898011646227000885485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22882598674430818000590323 34323898011646227000885485)
  ·
    refine ⟨12871461754367335125332057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34323898011646227000885485 12871461754367335125332057)
    ·
      refine ⟨9653596315775501343999043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12871461754367335125332057 9653596315775501343999043)
      ·
        refine ⟨14480394473663252015998565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9653596315775501343999043 14480394473663252015998565)
        ·
          refine ⟨2715073963811859752999731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14480394473663252015998565 2715073963811859752999731)
          ·
            refine ⟨4072610945717789629499597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2715073963811859752999731 4072610945717789629499597)
            ·
              refine ⟨1527229104644171111062349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4072610945717789629499597 1527229104644171111062349)
              ·
                refine ⟨572710914241564166648381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1527229104644171111062349 572710914241564166648381)
                ·
                  refine ⟨214766592840586562493143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 572710914241564166648381 214766592840586562493143)
                  ·
                    rfl

theorem cell21_941077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 3, 3].length) (baseStart_941077 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_941077 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_941077 prefixEnd_941077 := by exact prefixLift 941077
  have htrace : WordTrace (prefixWord ++ tailWord_941077) baseStart_941077 baseEnd_941077 := by
    simpa [prefixWord, tailWord_941077, baseEnd_941077] using wordTrace_append hprefix tailTrace_941077
  have hstable : (prefixWord ++ tailWord_941077).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941077).length < 2 ^ (prefixWord ++ tailWord_941077).sum := by decide
  have hdescent : baseEnd_941077 < baseStart_941077 := by decide
  rcases family_descends (prefixWord ++ tailWord_941077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941108 : List Nat := [2, 5, 1, 2, 1, 2, 1, 3, 4]
def baseStart_941108 : Nat := 118140960795 + 941108 * 2 ^ 59
def prefixEnd_941108 : Nat := 4983230072969 + 3 ^ 40 * 941108 * 2
def baseEnd_941108 : Nat := 214773667462937397476413

theorem tailTrace_941108 : CollatzResearch.WordTrace tailWord_941108 prefixEnd_941108 214773667462937397476413 := by
  unfold tailWord_941108
  simp only [CollatzResearch.WordTrace]
  refine ⟨17162514337266959647631989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22883352449689279530175985 17162514337266959647631989)
  ·
    refine ⟨1608985719118777466965499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17162514337266959647631989 1608985719118777466965499)
    ·
      refine ⟨2413478578678166200448249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1608985719118777466965499 2413478578678166200448249)
      ·
        refine ⟨1810108934008624650336187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2413478578678166200448249 1810108934008624650336187)
        ·
          refine ⟨2715163401012936975504281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1810108934008624650336187 2715163401012936975504281)
          ·
            refine ⟨2036372550759702731628211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2715163401012936975504281 2036372550759702731628211)
            ·
              refine ⟨3054558826139554097442317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2036372550759702731628211 3054558826139554097442317)
              ·
                refine ⟨1145459559802332786540869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3054558826139554097442317 1145459559802332786540869)
                ·
                  refine ⟨214773667462937397476413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1145459559802332786540869 214773667462937397476413)
                  ·
                    rfl

theorem cell21_941108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_941108 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_941108 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_941108 prefixEnd_941108 := by exact prefixLift 941108
  have htrace : WordTrace (prefixWord ++ tailWord_941108) baseStart_941108 baseEnd_941108 := by
    simpa [prefixWord, tailWord_941108, baseEnd_941108] using wordTrace_append hprefix tailTrace_941108
  have hstable : (prefixWord ++ tailWord_941108).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941108).length < 2 ^ (prefixWord ++ tailWord_941108).sum := by decide
  have hdescent : baseEnd_941108 < baseStart_941108 := by decide
  rcases family_descends (prefixWord ++ tailWord_941108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941153 : List Nat := [1, 2, 3, 1, 1, 2, 6, 2, 3]
def baseStart_941153 : Nat := 118140960795 + 941153 * 2 ^ 59
def prefixEnd_941153 : Nat := 4983230072969 + 3 ^ 40 * 941153 * 2
def baseEnd_941153 : Nat := 214783937076027319226321

theorem tailTrace_941153 : CollatzResearch.WordTrace tailWord_941153 prefixEnd_941153 214783937076027319226321 := by
  unfold tailWord_941153
  simp only [CollatzResearch.WordTrace]
  refine ⟨34326669959370891980652113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22884446639580594653768075 34326669959370891980652113)
  ·
    refine ⟨25745002469528168985489085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34326669959370891980652113 25745002469528168985489085)
    ·
      refine ⟨9654375926073063369558407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25745002469528168985489085 9654375926073063369558407)
      ·
        refine ⟨14481563889109595054337611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9654375926073063369558407 14481563889109595054337611)
        ·
          refine ⟨21722345833664392581506417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14481563889109595054337611 21722345833664392581506417)
          ·
            refine ⟨16291759375248294436129813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21722345833664392581506417 16291759375248294436129813)
            ·
              refine ⟨763676220714763801693585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16291759375248294436129813 763676220714763801693585)
              ·
                refine ⟨572757165536072851270189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 763676220714763801693585 572757165536072851270189)
                ·
                  refine ⟨214783937076027319226321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 572757165536072851270189 214783937076027319226321)
                  ·
                    rfl

theorem cell21_941153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 6, 2, 3].length) (baseStart_941153 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_941153 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_941153 prefixEnd_941153 := by exact prefixLift 941153
  have htrace : WordTrace (prefixWord ++ tailWord_941153) baseStart_941153 baseEnd_941153 := by
    simpa [prefixWord, tailWord_941153, baseEnd_941153] using wordTrace_append hprefix tailTrace_941153
  have hstable : (prefixWord ++ tailWord_941153).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941153).length < 2 ^ (prefixWord ++ tailWord_941153).sum := by decide
  have hdescent : baseEnd_941153 < baseStart_941153 := by decide
  rcases family_descends (prefixWord ++ tailWord_941153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941181 : List Nat := [1, 4, 1, 1, 3, 1, 5, 5]
def baseStart_941181 : Nat := 118140960795 + 941181 * 2 ^ 59
def prefixEnd_941181 : Nat := 4983230072969 + 3 ^ 40 * 941181 * 2
def baseEnd_941181 : Nat := 71596775685835164253199

theorem tailTrace_941181 : CollatzResearch.WordTrace tailWord_941181 prefixEnd_941181 71596775685835164253199 := by
  unfold tailWord_941181
  simp only [CollatzResearch.WordTrace]
  refine ⟨34327691203269452762671397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22885127468846301841780931 34327691203269452762671397)
  ·
    refine ⟨6436442100613022393000887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34327691203269452762671397 6436442100613022393000887)
    ·
      refine ⟨9654663150919533589501331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6436442100613022393000887 9654663150919533589501331)
      ·
        refine ⟨14481994726379300384251997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9654663150919533589501331 14481994726379300384251997)
        ·
          refine ⟨5430748022392237644094499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14481994726379300384251997 5430748022392237644094499)
          ·
            refine ⟨8146122033588356466141749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5430748022392237644094499 8146122033588356466141749)
            ·
              refine ⟨763698940648908418700789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8146122033588356466141749 763698940648908418700789)
              ·
                refine ⟨71596775685835164253199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 763698940648908418700789 71596775685835164253199)
                ·
                  rfl

theorem cell21_941181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 5, 5].length) (baseStart_941181 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_941181 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_941181 prefixEnd_941181 := by exact prefixLift 941181
  have htrace : WordTrace (prefixWord ++ tailWord_941181) baseStart_941181 baseEnd_941181 := by
    simpa [prefixWord, tailWord_941181, baseEnd_941181] using wordTrace_append hprefix tailTrace_941181
  have hstable : (prefixWord ++ tailWord_941181).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941181).length < 2 ^ (prefixWord ++ tailWord_941181).sum := by decide
  have hdescent : baseEnd_941181 < baseStart_941181 := by decide
  rcases family_descends (prefixWord ++ tailWord_941181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941212 : List Nat := [2, 2, 3, 2, 1, 3, 2, 1, 5]
def baseStart_941212 : Nat := 118140960795 + 941212 * 2 ^ 59
def prefixEnd_941212 : Nat := 4983230072969 + 3 ^ 40 * 941212 * 2
def baseEnd_941212 : Nat := 214797401679856327742867

theorem tailTrace_941212 : CollatzResearch.WordTrace tailWord_941212 prefixEnd_941212 214797401679856327742867 := by
  unfold tailWord_941212
  simp only [CollatzResearch.WordTrace]
  refine ⟨17164410933078572528524945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22885881244104763371366593 17164410933078572528524945)
  ·
    refine ⟨12873308199808929396393709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17164410933078572528524945 12873308199808929396393709)
    ·
      refine ⟨4827490574928348523647641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12873308199808929396393709 4827490574928348523647641)
      ·
        refine ⟨3620617931196261392735731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4827490574928348523647641 3620617931196261392735731)
        ·
          refine ⟨5430926896794392089103597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3620617931196261392735731 5430926896794392089103597)
          ·
            refine ⟨2036597586297897033413849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5430926896794392089103597 2036597586297897033413849)
            ·
              refine ⟨1527448189723422775060387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2036597586297897033413849 1527448189723422775060387)
              ·
                refine ⟨2291172284585134162590581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1527448189723422775060387 2291172284585134162590581)
                ·
                  refine ⟨214797401679856327742867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2291172284585134162590581 214797401679856327742867)
                  ·
                    rfl

theorem cell21_941212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 1, 5].length) (baseStart_941212 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_941212 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_941212 prefixEnd_941212 := by exact prefixLift 941212
  have htrace : WordTrace (prefixWord ++ tailWord_941212) baseStart_941212 baseEnd_941212 := by
    simpa [prefixWord, tailWord_941212, baseEnd_941212] using wordTrace_append hprefix tailTrace_941212
  have hstable : (prefixWord ++ tailWord_941212).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941212).length < 2 ^ (prefixWord ++ tailWord_941212).sum := by decide
  have hdescent : baseEnd_941212 < baseStart_941212 := by decide
  rcases family_descends (prefixWord ++ tailWord_941212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941246 : List Nat := [4, 2, 1, 1, 3, 3, 1, 3, 3]
def baseStart_941246 : Nat := 118140960795 + 941246 * 2 ^ 59
def prefixEnd_941246 : Nat := 4983230072969 + 3 ^ 40 * 941246 * 2
def baseEnd_941246 : Nat := 214805160943079824176131

theorem tailTrace_941246 : CollatzResearch.WordTrace tailWord_941246 prefixEnd_941246 214805160943079824176131 := by
  unfold tailWord_941246
  simp only [CollatzResearch.WordTrace]
  refine ⟨4291257743504246107973449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22886707965355979242525061 4291257743504246107973449)
  ·
    refine ⟨3218443307628184580980087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4291257743504246107973449 3218443307628184580980087)
    ·
      refine ⟨4827664961442276871470131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3218443307628184580980087 4827664961442276871470131)
      ·
        refine ⟨7241497442163415307205197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4827664961442276871470131 7241497442163415307205197)
        ·
          refine ⟨2715561540811280740201949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7241497442163415307205197 2715561540811280740201949)
          ·
            refine ⟨1018335577804230277575731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2715561540811280740201949 1018335577804230277575731)
            ·
              refine ⟨1527503366706345416363597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1018335577804230277575731 1527503366706345416363597)
              ·
                refine ⟨572813762514879531136349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1527503366706345416363597 572813762514879531136349)
                ·
                  refine ⟨214805160943079824176131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 572813762514879531136349 214805160943079824176131)
                  ·
                    rfl

theorem cell21_941246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 3, 3].length) (baseStart_941246 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_941246 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_941246 prefixEnd_941246 := by exact prefixLift 941246
  have htrace : WordTrace (prefixWord ++ tailWord_941246) baseStart_941246 baseEnd_941246 := by
    simpa [prefixWord, tailWord_941246, baseEnd_941246] using wordTrace_append hprefix tailTrace_941246
  have hstable : (prefixWord ++ tailWord_941246).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941246).length < 2 ^ (prefixWord ++ tailWord_941246).sum := by decide
  have hdescent : baseEnd_941246 < baseStart_941246 := by decide
  rcases family_descends (prefixWord ++ tailWord_941246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941271 : List Nat := [1, 1, 3, 2, 1, 2, 5, 1, 5]
def baseStart_941271 : Nat := 118140960795 + 941271 * 2 ^ 59
def prefixEnd_941271 : Nat := 4983230072969 + 3 ^ 40 * 941271 * 2
def baseEnd_941271 : Nat := 214810866283685336259413

theorem tailTrace_941271 : CollatzResearch.WordTrace tailWord_941271 prefixEnd_941271 214810866283685336259413 := by
  unfold tailWord_941271
  simp only [CollatzResearch.WordTrace]
  refine ⟨34330973772943398133447667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22887315848628932088965111 34330973772943398133447667)
  ·
    refine ⟨51496460659415097200171501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34330973772943398133447667 51496460659415097200171501)
    ·
      refine ⟨19311172747280661450064313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51496460659415097200171501 19311172747280661450064313)
      ·
        refine ⟨14483379560460496087548235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19311172747280661450064313 14483379560460496087548235)
        ·
          refine ⟨21725069340690744131322353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14483379560460496087548235 21725069340690744131322353)
          ·
            refine ⟨16293802005518058098491765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21725069340690744131322353 16293802005518058098491765)
            ·
              refine ⟨1527543938017317946733603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16293802005518058098491765 1527543938017317946733603)
              ·
                refine ⟨2291315907025976920100405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1527543938017317946733603 2291315907025976920100405)
                ·
                  refine ⟨214810866283685336259413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2291315907025976920100405 214810866283685336259413)
                  ·
                    rfl

theorem cell21_941271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 1, 5].length) (baseStart_941271 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_941271 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_941271 prefixEnd_941271 := by exact prefixLift 941271
  have htrace : WordTrace (prefixWord ++ tailWord_941271) baseStart_941271 baseEnd_941271 := by
    simpa [prefixWord, tailWord_941271, baseEnd_941271] using wordTrace_append hprefix tailTrace_941271
  have hstable : (prefixWord ++ tailWord_941271).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941271).length < 2 ^ (prefixWord ++ tailWord_941271).sum := by decide
  have hdescent : baseEnd_941271 < baseStart_941271 := by decide
  rcases family_descends (prefixWord ++ tailWord_941271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941277 : List Nat := [1, 4, 3, 2, 2, 2, 2, 1, 4]
def baseStart_941277 : Nat := 118140960795 + 941277 * 2 ^ 59
def prefixEnd_941277 : Nat := 4983230072969 + 3 ^ 40 * 941277 * 2
def baseEnd_941277 : Nat := 214812235565430659159401

theorem tailTrace_941277 : CollatzResearch.WordTrace tailWord_941277 prefixEnd_941277 214812235565430659159401 := by
  unfold tailWord_941277
  simp only [CollatzResearch.WordTrace]
  refine ⟨34331192610921661158166085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22887461740614440772110723 34331192610921661158166085)
  ·
    refine ⟨6437098614547811467156141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34331192610921661158166085 6437098614547811467156141)
    ·
      refine ⟨2413911980455429300183553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6437098614547811467156141 2413911980455429300183553)
      ·
        refine ⟨1810433985341571975137665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2413911980455429300183553 1810433985341571975137665)
        ·
          refine ⟨1357825489006178981353249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1810433985341571975137665 1357825489006178981353249)
          ·
            refine ⟨1018369116754634236014937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1357825489006178981353249 1018369116754634236014937)
            ·
              refine ⟨763776837565975677011203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1018369116754634236014937 763776837565975677011203)
              ·
                refine ⟨1145665256348963515516805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 763776837565975677011203 1145665256348963515516805)
                ·
                  refine ⟨214812235565430659159401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1145665256348963515516805 214812235565430659159401)
                  ·
                    rfl

theorem cell21_941277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 2, 1, 4].length) (baseStart_941277 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_941277 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_941277 prefixEnd_941277 := by exact prefixLift 941277
  have htrace : WordTrace (prefixWord ++ tailWord_941277) baseStart_941277 baseEnd_941277 := by
    simpa [prefixWord, tailWord_941277, baseEnd_941277] using wordTrace_append hprefix tailTrace_941277
  have hstable : (prefixWord ++ tailWord_941277).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941277).length < 2 ^ (prefixWord ++ tailWord_941277).sum := by decide
  have hdescent : baseEnd_941277 < baseStart_941277 := by decide
  rcases family_descends (prefixWord ++ tailWord_941277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941316 : List Nat := [2, 3, 2, 2, 2, 10]
def baseStart_941316 : Nat := 118140960795 + 941316 * 2 ^ 59
def prefixEnd_941316 : Nat := 4983230072969 + 3 ^ 40 * 941316 * 2
def baseEnd_941316 : Nat := 7956338366547231778123

theorem tailTrace_941316 : CollatzResearch.WordTrace tailWord_941316 prefixEnd_941316 7956338366547231778123 := by
  unfold tailWord_941316
  simp only [CollatzResearch.WordTrace]
  refine ⟨17166307528890185409417901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22888410038520247212557201 17166307528890185409417901)
  ·
    refine ⟨6437365323333819528531713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17166307528890185409417901 6437365323333819528531713)
    ·
      refine ⟨4828023992500364646398785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6437365323333819528531713 4828023992500364646398785)
      ·
        refine ⟨3621017994375273484799089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4828023992500364646398785 3621017994375273484799089)
        ·
          refine ⟨2715763495781455113599317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3621017994375273484799089 2715763495781455113599317)
          ·
            refine ⟨7956338366547231778123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2715763495781455113599317 7956338366547231778123)
            ·
              rfl

theorem cell21_941316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 10].length) (baseStart_941316 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_941316 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_941316 prefixEnd_941316 := by exact prefixLift 941316
  have htrace : WordTrace (prefixWord ++ tailWord_941316) baseStart_941316 baseEnd_941316 := by
    simpa [prefixWord, tailWord_941316, baseEnd_941316] using wordTrace_append hprefix tailTrace_941316
  have hstable : (prefixWord ++ tailWord_941316).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941316).length < 2 ^ (prefixWord ++ tailWord_941316).sum := by decide
  have hdescent : baseEnd_941316 < baseStart_941316 := by decide
  rcases family_descends (prefixWord ++ tailWord_941316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941347 : List Nat := [1, 1, 1, 4, 2, 4, 1, 2, 5]
def baseStart_941347 : Nat := 118140960795 + 941347 * 2 ^ 59
def prefixEnd_941347 : Nat := 4983230072969 + 3 ^ 40 * 941347 * 2
def baseEnd_941347 : Nat := 214828210519126092992591

theorem tailTrace_941347 : CollatzResearch.WordTrace tailWord_941347 prefixEnd_941347 214828210519126092992591 := by
  unfold tailWord_941347
  simp only [CollatzResearch.WordTrace]
  refine ⟨34333745720668063113214295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22889163813778708742142863 34333745720668063113214295)
  ·
    refine ⟨51500618581002094669821443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34333745720668063113214295 51500618581002094669821443)
    ·
      refine ⟨77250927871503142004732165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51500618581002094669821443 77250927871503142004732165)
      ·
        refine ⟨14484548975906839125887281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77250927871503142004732165 14484548975906839125887281)
        ·
          refine ⟨10863411731930129344415461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14484548975906839125887281 10863411731930129344415461)
          ·
            refine ⟨2036889699736899252077899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10863411731930129344415461 2036889699736899252077899)
            ·
              refine ⟨3055334549605348878116849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2036889699736899252077899 3055334549605348878116849)
              ·
                refine ⟨2291500912204011658587637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3055334549605348878116849 2291500912204011658587637)
                ·
                  refine ⟨214828210519126092992591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2291500912204011658587637 214828210519126092992591)
                  ·
                    rfl

theorem cell21_941347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 2, 5].length) (baseStart_941347 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_941347 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_941347 prefixEnd_941347 := by exact prefixLift 941347
  have htrace : WordTrace (prefixWord ++ tailWord_941347) baseStart_941347 baseEnd_941347 := by
    simpa [prefixWord, tailWord_941347, baseEnd_941347] using wordTrace_append hprefix tailTrace_941347
  have hstable : (prefixWord ++ tailWord_941347).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941347).length < 2 ^ (prefixWord ++ tailWord_941347).sum := by decide
  have hdescent : baseEnd_941347 < baseStart_941347 := by decide
  rcases family_descends (prefixWord ++ tailWord_941347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941437 : List Nat := [1, 4, 1, 1, 2, 2, 1, 3, 6]
def baseStart_941437 : Nat := 118140960795 + 941437 * 2 ^ 59
def prefixEnd_941437 : Nat := 4983230072969 + 3 ^ 40 * 941437 * 2
def baseEnd_941437 : Nat := 214848749745305936492407

theorem tailTrace_941437 : CollatzResearch.WordTrace tailWord_941437 prefixEnd_941437 214848749745305936492407 := by
  unfold tailWord_941437
  simp only [CollatzResearch.WordTrace]
  refine ⟨34337028290342008483990565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22891352193561338989327043 34337028290342008483990565)
  ·
    refine ⟨6438192804439126590748231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34337028290342008483990565 6438192804439126590748231)
    ·
      refine ⟨9657289206658689886122347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6438192804439126590748231 9657289206658689886122347)
      ·
        refine ⟨14485933809988034829183521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9657289206658689886122347 14485933809988034829183521)
        ·
          refine ⟨10864450357491026121887641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14485933809988034829183521 10864450357491026121887641)
          ·
            refine ⟨8148337768118269591415731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10864450357491026121887641 8148337768118269591415731)
            ·
              refine ⟨12222506652177404387123597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8148337768118269591415731 12222506652177404387123597)
              ·
                refine ⟨4583439994566526645171349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12222506652177404387123597 4583439994566526645171349)
                ·
                  refine ⟨214848749745305936492407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4583439994566526645171349 214848749745305936492407)
                  ·
                    rfl

theorem cell21_941437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_941437 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_941437 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_941437 prefixEnd_941437 := by exact prefixLift 941437
  have htrace : WordTrace (prefixWord ++ tailWord_941437) baseStart_941437 baseEnd_941437 := by
    simpa [prefixWord, tailWord_941437, baseEnd_941437] using wordTrace_append hprefix tailTrace_941437
  have hstable : (prefixWord ++ tailWord_941437).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941437).length < 2 ^ (prefixWord ++ tailWord_941437).sum := by decide
  have hdescent : baseEnd_941437 < baseStart_941437 := by decide
  rcases family_descends (prefixWord ++ tailWord_941437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941527 : List Nat := [1, 1, 3, 2, 1, 1, 1, 11]
def baseStart_941527 : Nat := 118140960795 + 941527 * 2 ^ 59
def prefixEnd_941527 : Nat := 4983230072969 + 3 ^ 40 * 941527 * 2
def baseEnd_941527 : Nat := 71623096323828593330741

theorem tailTrace_941527 : CollatzResearch.WordTrace tailWord_941527 prefixEnd_941527 71623096323828593330741 := by
  unfold tailWord_941527
  simp only [CollatzResearch.WordTrace]
  refine ⟨34340310860015953854766835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22893540573343969236511223 34340310860015953854766835)
  ·
    refine ⟨51510466290023930782150253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34340310860015953854766835 51510466290023930782150253)
    ·
      refine ⟨19316424858758974043306345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51510466290023930782150253 19316424858758974043306345)
      ·
        refine ⟨14487318644069230532479759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19316424858758974043306345 14487318644069230532479759)
        ·
          refine ⟨21730977966103845798719639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14487318644069230532479759 21730977966103845798719639)
          ·
            refine ⟨32596466949155768698079459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21730977966103845798719639 32596466949155768698079459)
            ·
              refine ⟨48894700423733653047119189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32596466949155768698079459 48894700423733653047119189)
              ·
                refine ⟨71623096323828593330741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 48894700423733653047119189 71623096323828593330741)
                ·
                  rfl

theorem cell21_941527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 11].length) (baseStart_941527 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_941527 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_941527 prefixEnd_941527 := by exact prefixLift 941527
  have htrace : WordTrace (prefixWord ++ tailWord_941527) baseStart_941527 baseEnd_941527 := by
    simpa [prefixWord, tailWord_941527, baseEnd_941527] using wordTrace_append hprefix tailTrace_941527
  have hstable : (prefixWord ++ tailWord_941527).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941527).length < 2 ^ (prefixWord ++ tailWord_941527).sum := by decide
  have hdescent : baseEnd_941527 < baseStart_941527 := by decide
  rcases family_descends (prefixWord ++ tailWord_941527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941533 : List Nat := [1, 4, 3, 1, 1, 3, 2, 3, 3]
def baseStart_941533 : Nat := 118140960795 + 941533 * 2 ^ 59
def prefixEnd_941533 : Nat := 4983230072969 + 3 ^ 40 * 941533 * 2
def baseEnd_941533 : Nat := 214870658253231102892211

theorem tailTrace_941533 : CollatzResearch.WordTrace tailWord_941533 prefixEnd_941533 214870658253231102892211 := by
  unfold tailWord_941533
  simp only [CollatzResearch.WordTrace]
  refine ⟨34340529697994216879485253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22893686465329477919656835 34340529697994216879485253)
  ·
    refine ⟨6438849318373915664903485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34340529697994216879485253 6438849318373915664903485)
    ·
      refine ⟨2414568494390218374338807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6438849318373915664903485 2414568494390218374338807)
      ·
        refine ⟨3621852741585327561508211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2414568494390218374338807 3621852741585327561508211)
        ·
          refine ⟨5432779112377991342262317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3621852741585327561508211 5432779112377991342262317)
          ·
            refine ⟨2037292167141746753348369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5432779112377991342262317 2037292167141746753348369)
            ·
              refine ⟨1527969125356310065011277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2037292167141746753348369 1527969125356310065011277)
              ·
                refine ⟨572988422008616274379229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1527969125356310065011277 572988422008616274379229)
                ·
                  refine ⟨214870658253231102892211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 572988422008616274379229 214870658253231102892211)
                  ·
                    rfl

theorem cell21_941533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 3, 3].length) (baseStart_941533 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_941533 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_941533 prefixEnd_941533 := by exact prefixLift 941533
  have htrace : WordTrace (prefixWord ++ tailWord_941533) baseStart_941533 baseEnd_941533 := by
    simpa [prefixWord, tailWord_941533, baseEnd_941533] using wordTrace_append hprefix tailTrace_941533
  have hstable : (prefixWord ++ tailWord_941533).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941533).length < 2 ^ (prefixWord ++ tailWord_941533).sum := by decide
  have hdescent : baseEnd_941533 < baseStart_941533 := by decide
  rcases family_descends (prefixWord ++ tailWord_941533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941575 : List Nat := [1, 1, 4, 3, 2, 1, 2, 2, 5]
def baseStart_941575 : Nat := 118140960795 + 941575 * 2 ^ 59
def prefixEnd_941575 : Nat := 4983230072969 + 3 ^ 40 * 941575 * 2
def baseEnd_941575 : Nat := 214880243225448363192125

theorem tailTrace_941575 : CollatzResearch.WordTrace tailWord_941575 prefixEnd_941575 214880243225448363192125 := by
  unfold tailWord_941575
  simp only [CollatzResearch.WordTrace]
  refine ⟨34342061563842058052514179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22894707709228038701676119 34342061563842058052514179)
  ·
    refine ⟨51513092345763087078771269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34342061563842058052514179 51513092345763087078771269)
    ·
      refine ⟨9658704814830578827269613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51513092345763087078771269 9658704814830578827269613)
      ·
        refine ⟨3622014305561467060226105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9658704814830578827269613 3622014305561467060226105)
        ·
          refine ⟨2716510729171100295169579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3622014305561467060226105 2716510729171100295169579)
          ·
            refine ⟨4074766093756650442754369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2716510729171100295169579 4074766093756650442754369)
            ·
              refine ⟨3056074570317487832065777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4074766093756650442754369 3056074570317487832065777)
              ·
                refine ⟨2292055927738115874049333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3056074570317487832065777 2292055927738115874049333)
                ·
                  refine ⟨214880243225448363192125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2292055927738115874049333 214880243225448363192125)
                  ·
                    rfl

theorem cell21_941575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 2, 5].length) (baseStart_941575 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_941575 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_941575 prefixEnd_941575 := by exact prefixLift 941575
  have htrace : WordTrace (prefixWord ++ tailWord_941575) baseStart_941575 baseEnd_941575 := by
    simpa [prefixWord, tailWord_941575, baseEnd_941575] using wordTrace_append hprefix tailTrace_941575
  have hstable : (prefixWord ++ tailWord_941575).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941575).length < 2 ^ (prefixWord ++ tailWord_941575).sum := by decide
  have hdescent : baseEnd_941575 < baseStart_941575 := by decide
  rcases family_descends (prefixWord ++ tailWord_941575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941589 : List Nat := [1, 3, 2, 1, 3, 2, 1, 2, 6]
def baseStart_941589 : Nat := 118140960795 + 941589 * 2 ^ 59
def prefixEnd_941589 : Nat := 4983230072969 + 3 ^ 40 * 941589 * 2
def baseEnd_941589 : Nat := 214883438216187449958763

theorem tailTrace_941589 : CollatzResearch.WordTrace tailWord_941589 prefixEnd_941589 214883438216187449958763 := by
  unfold tailWord_941589
  simp only [CollatzResearch.WordTrace]
  refine ⟨34342572185791338443523821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22895048123860892295682547 34342572185791338443523821)
  ·
    refine ⟨12878464569671751916321433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34342572185791338443523821 12878464569671751916321433)
    ·
      refine ⟨9658848427253813937241075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12878464569671751916321433 9658848427253813937241075)
      ·
        refine ⟨14488272640880720905861613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9658848427253813937241075 14488272640880720905861613)
        ·
          refine ⟨5433102240330270339698105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14488272640880720905861613 5433102240330270339698105)
          ·
            refine ⟨4074826680247702754773579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5433102240330270339698105 4074826680247702754773579)
            ·
              refine ⟨6112240020371554132160369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4074826680247702754773579 6112240020371554132160369)
              ·
                refine ⟨4584180015278665599120277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6112240020371554132160369 4584180015278665599120277)
                ·
                  refine ⟨214883438216187449958763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4584180015278665599120277 214883438216187449958763)
                  ·
                    rfl

theorem cell21_941589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 6].length) (baseStart_941589 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_941589 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_941589 prefixEnd_941589 := by exact prefixLift 941589
  have htrace : WordTrace (prefixWord ++ tailWord_941589) baseStart_941589 baseEnd_941589 := by
    simpa [prefixWord, tailWord_941589, baseEnd_941589] using wordTrace_append hprefix tailTrace_941589
  have hstable : (prefixWord ++ tailWord_941589).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941589).length < 2 ^ (prefixWord ++ tailWord_941589).sum := by decide
  have hdescent : baseEnd_941589 < baseStart_941589 := by decide
  rcases family_descends (prefixWord ++ tailWord_941589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941623 : List Nat := [1, 1, 3, 1, 2, 6, 2, 1, 4]
def baseStart_941623 : Nat := 118140960795 + 941623 * 2 ^ 59
def prefixEnd_941623 : Nat := 4983230072969 + 3 ^ 40 * 941623 * 2
def baseEnd_941623 : Nat := 214891197479410946392027

theorem tailTrace_941623 : CollatzResearch.WordTrace tailWord_941623 prefixEnd_941623 214891197479410946392027 := by
  unfold tailWord_941623
  simp only [CollatzResearch.WordTrace]
  refine ⟨34343812267668162250261523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22895874845112108166841015 34343812267668162250261523)
  ·
    refine ⟨51515718401502243375392285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34343812267668162250261523 51515718401502243375392285)
    ·
      refine ⟨19318394400563341265772107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51515718401502243375392285 19318394400563341265772107)
      ·
        refine ⟨28977591600845011898658161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19318394400563341265772107 28977591600845011898658161)
        ·
          refine ⟨21733193700633758923993621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28977591600845011898658161 21733193700633758923993621)
          ·
            refine ⟨1018743454717207449562201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 21733193700633758923993621 1018743454717207449562201)
            ·
              refine ⟨764057591037905587171651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1018743454717207449562201 764057591037905587171651)
              ·
                refine ⟨1146086386556858380757477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 764057591037905587171651 1146086386556858380757477)
                ·
                  refine ⟨214891197479410946392027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1146086386556858380757477 214891197479410946392027)
                  ·
                    rfl

theorem cell21_941623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 2, 1, 4].length) (baseStart_941623 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_941623 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_941623 prefixEnd_941623 := by exact prefixLift 941623
  have htrace : WordTrace (prefixWord ++ tailWord_941623) baseStart_941623 baseEnd_941623 := by
    simpa [prefixWord, tailWord_941623, baseEnd_941623] using wordTrace_append hprefix tailTrace_941623
  have hstable : (prefixWord ++ tailWord_941623).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941623).length < 2 ^ (prefixWord ++ tailWord_941623).sum := by decide
  have hdescent : baseEnd_941623 < baseStart_941623 := by decide
  rcases family_descends (prefixWord ++ tailWord_941623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941654 : List Nat := [5, 2, 2, 2, 1, 9]
def baseStart_941654 : Nat := 118140960795 + 941654 * 2 ^ 59
def prefixEnd_941654 : Nat := 4983230072969 + 3 ^ 40 * 941654 * 2
def baseEnd_941654 : Nat := 7959195263028214125011

theorem tailTrace_941654 : CollatzResearch.WordTrace tailWord_941654 prefixEnd_941654 7959195263028214125011 := by
  unfold tailWord_941654
  simp only [CollatzResearch.WordTrace]
  refine ⟨2146558933159740909040001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22896628620370569696426677 2146558933159740909040001)
  ·
    refine ⟨1609919199869805681780001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2146558933159740909040001 1609919199869805681780001)
    ·
      refine ⟨1207439399902354261335001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1609919199869805681780001 1207439399902354261335001)
      ·
        refine ⟨905579549926765696001251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1207439399902354261335001 905579549926765696001251)
        ·
          refine ⟨1358369324890148544001877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 905579549926765696001251 1358369324890148544001877)
          ·
            refine ⟨7959195263028214125011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1358369324890148544001877 7959195263028214125011)
            ·
              rfl

theorem cell21_941654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 9].length) (baseStart_941654 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_941654 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_941654 prefixEnd_941654 := by exact prefixLift 941654
  have htrace : WordTrace (prefixWord ++ tailWord_941654) baseStart_941654 baseEnd_941654 := by
    simpa [prefixWord, tailWord_941654, baseEnd_941654] using wordTrace_append hprefix tailTrace_941654
  have hstable : (prefixWord ++ tailWord_941654).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941654).length < 2 ^ (prefixWord ++ tailWord_941654).sum := by decide
  have hdescent : baseEnd_941654 < baseStart_941654 := by decide
  rcases family_descends (prefixWord ++ tailWord_941654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941668 : List Nat := [2, 3, 1, 1, 2, 4, 1, 4, 3]
def baseStart_941668 : Nat := 118140960795 + 941668 * 2 ^ 59
def prefixEnd_941668 : Nat := 4983230072969 + 3 ^ 40 * 941668 * 2
def baseEnd_941668 : Nat := 214901467092500868141935

theorem tailTrace_941668 : CollatzResearch.WordTrace tailWord_941668 prefixEnd_941668 214901467092500868141935 := by
  unfold tailWord_941668
  simp only [CollatzResearch.WordTrace]
  refine ⟨17172726776252567467824829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22896969035003423290433105 17172726776252567467824829)
  ·
    refine ⟨6439772541094712800434311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17172726776252567467824829 6439772541094712800434311)
    ·
      refine ⟨9659658811642069200651467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6439772541094712800434311 9659658811642069200651467)
      ·
        refine ⟨14489488217463103800977201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9659658811642069200651467 14489488217463103800977201)
        ·
          refine ⟨10867116163097327850732901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14489488217463103800977201 10867116163097327850732901)
          ·
            refine ⟨2037584280580748972012419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10867116163097327850732901 2037584280580748972012419)
            ·
              refine ⟨3056376420871123458018629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2037584280580748972012419 3056376420871123458018629)
              ·
                refine ⟨573070578913335648378493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3056376420871123458018629 573070578913335648378493)
                ·
                  refine ⟨214901467092500868141935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 573070578913335648378493 214901467092500868141935)
                  ·
                    rfl

theorem cell21_941668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 4, 3].length) (baseStart_941668 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_941668 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_941668 prefixEnd_941668 := by exact prefixLift 941668
  have htrace : WordTrace (prefixWord ++ tailWord_941668) baseStart_941668 baseEnd_941668 := by
    simpa [prefixWord, tailWord_941668, baseEnd_941668] using wordTrace_append hprefix tailTrace_941668
  have hstable : (prefixWord ++ tailWord_941668).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941668).length < 2 ^ (prefixWord ++ tailWord_941668).sum := by decide
  have hdescent : baseEnd_941668 < baseStart_941668 := by decide
  rcases family_descends (prefixWord ++ tailWord_941668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941682 : List Nat := [3, 2, 1, 2, 3, 1, 2, 3, 4]
def baseStart_941682 : Nat := 118140960795 + 941682 * 2 ^ 59
def prefixEnd_941682 : Nat := 4983230072969 + 3 ^ 40 * 941682 * 2
def baseEnd_941682 : Nat := 214904662083239954908573

theorem tailTrace_941682 : CollatzResearch.WordTrace tailWord_941682 prefixEnd_941682 214904662083239954908573 := by
  unfold tailWord_941682
  simp only [CollatzResearch.WordTrace]
  refine ⟨8586491043613603831664825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22897309449636276884439533 8586491043613603831664825)
  ·
    refine ⟨6439868282710202873748619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8586491043613603831664825 6439868282710202873748619)
    ·
      refine ⟨9659802424065304310622929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6439868282710202873748619 9659802424065304310622929)
      ·
        refine ⟨7244851818048978232967197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9659802424065304310622929 7244851818048978232967197)
        ·
          refine ⟨2716819431768366837362699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7244851818048978232967197 2716819431768366837362699)
          ·
            refine ⟨4075229147652550256044049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2716819431768366837362699 4075229147652550256044049)
            ·
              refine ⟨3056421860739412692033037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4075229147652550256044049 3056421860739412692033037)
              ·
                refine ⟨1146158197777279759512389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3056421860739412692033037 1146158197777279759512389)
                ·
                  refine ⟨214904662083239954908573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1146158197777279759512389 214904662083239954908573)
                  ·
                    rfl

theorem cell21_941682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 3, 4].length) (baseStart_941682 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_941682 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_941682 prefixEnd_941682 := by exact prefixLift 941682
  have htrace : WordTrace (prefixWord ++ tailWord_941682) baseStart_941682 baseEnd_941682 := by
    simpa [prefixWord, tailWord_941682, baseEnd_941682] using wordTrace_append hprefix tailTrace_941682
  have hstable : (prefixWord ++ tailWord_941682).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941682).length < 2 ^ (prefixWord ++ tailWord_941682).sum := by decide
  have hdescent : baseEnd_941682 < baseStart_941682 := by decide
  rcases family_descends (prefixWord ++ tailWord_941682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941696 : List Nat := [2, 1, 1, 2, 1, 4, 5, 5]
def baseStart_941696 : Nat := 118140960795 + 941696 * 2 ^ 59
def prefixEnd_941696 : Nat := 4983230072969 + 3 ^ 40 * 941696 * 2
def baseEnd_941696 : Nat := 71635952357993013891737

theorem tailTrace_941696 : CollatzResearch.WordTrace tailWord_941696 prefixEnd_941696 71635952357993013891737 := by
  unfold tailWord_941696
  simp only [CollatzResearch.WordTrace]
  refine ⟨17173237398201847858834471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22897649864269130478445961 17173237398201847858834471)
  ·
    refine ⟨25759856097302771788251707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17173237398201847858834471 25759856097302771788251707)
    ·
      refine ⟨38639784145954157682377561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25759856097302771788251707 38639784145954157682377561)
      ·
        refine ⟨28979838109465618261783171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38639784145954157682377561 28979838109465618261783171)
        ·
          refine ⟨43469757164198427392674757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28979838109465618261783171 43469757164198427392674757)
          ·
            refine ⟨8150579468287205136126517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43469757164198427392674757 8150579468287205136126517)
            ·
              refine ⟨764116825151925481511861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8150579468287205136126517 764116825151925481511861)
              ·
                refine ⟨71635952357993013891737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 764116825151925481511861 71635952357993013891737)
                ·
                  rfl

theorem cell21_941696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 5, 5].length) (baseStart_941696 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_941696 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_941696 prefixEnd_941696 := by exact prefixLift 941696
  have htrace : WordTrace (prefixWord ++ tailWord_941696) baseStart_941696 baseEnd_941696 := by
    simpa [prefixWord, tailWord_941696, baseEnd_941696] using wordTrace_append hprefix tailTrace_941696
  have hstable : (prefixWord ++ tailWord_941696).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941696).length < 2 ^ (prefixWord ++ tailWord_941696).sum := by decide
  have hdescent : baseEnd_941696 < baseStart_941696 := by decide
  rcases family_descends (prefixWord ++ tailWord_941696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941716 : List Nat := [2, 4, 2, 2, 2, 2, 1, 2, 4]
def baseStart_941716 : Nat := 118140960795 + 941716 * 2 ^ 59
def prefixEnd_941716 : Nat := 4983230072969 + 3 ^ 40 * 941716 * 2
def baseEnd_941716 : Nat := 214912421346463451341837

theorem tailTrace_941716 : CollatzResearch.WordTrace tailWord_941716 prefixEnd_941716 214912421346463451341837 := by
  unfold tailWord_941716
  simp only [CollatzResearch.WordTrace]
  refine ⟨17173602128165619566698501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22898136170887492755598001 17173602128165619566698501)
  ·
    refine ⟨3220050399031053668755969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17173602128165619566698501 3220050399031053668755969)
    ·
      refine ⟨2415037799273290251566977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3220050399031053668755969 2415037799273290251566977)
      ·
        refine ⟨1811278349454967688675233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2415037799273290251566977 1811278349454967688675233)
        ·
          refine ⟨1358458762091225766506425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1811278349454967688675233 1358458762091225766506425)
          ·
            refine ⟨1018844071568419324879819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1358458762091225766506425 1018844071568419324879819)
            ·
              refine ⟨1528266107352628987319729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1018844071568419324879819 1528266107352628987319729)
              ·
                refine ⟨1146199580514471740489797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1528266107352628987319729 1146199580514471740489797)
                ·
                  refine ⟨214912421346463451341837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1146199580514471740489797 214912421346463451341837)
                  ·
                    rfl

theorem cell21_941716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_941716 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_941716 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_941716 prefixEnd_941716 := by exact prefixLift 941716
  have htrace : WordTrace (prefixWord ++ tailWord_941716) baseStart_941716 baseEnd_941716 := by
    simpa [prefixWord, tailWord_941716, baseEnd_941716] using wordTrace_append hprefix tailTrace_941716
  have hstable : (prefixWord ++ tailWord_941716).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941716).length < 2 ^ (prefixWord ++ tailWord_941716).sum := by decide
  have hdescent : baseEnd_941716 < baseStart_941716 := by decide
  rcases family_descends (prefixWord ++ tailWord_941716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941831 : List Nat := [1, 1, 4, 4, 11]
def baseStart_941831 : Nat := 118140960795 + 941831 * 2 ^ 59
def prefixEnd_941831 : Nat := 4983230072969 + 3 ^ 40 * 941831 * 2
def baseEnd_941831 : Nat := 2653563776706775394135

theorem tailTrace_941831 : CollatzResearch.WordTrace tailWord_941831 prefixEnd_941831 2653563776706775394135 := by
  unfold tailWord_941831
  simp only [CollatzResearch.WordTrace]
  refine ⟨34351398650914613773833347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22900932433943075849222231 34351398650914613773833347)
  ·
    refine ⟨51527097976371920660750021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34351398650914613773833347 51527097976371920660750021)
    ·
      refine ⟨9661330870569735123890629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51527097976371920660750021 9661330870569735123890629)
      ·
        refine ⟨1811499538231825335729493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9661330870569735123890629 1811499538231825335729493)
        ·
          refine ⟨2653563776706775394135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1811499538231825335729493 2653563776706775394135)
          ·
            rfl

theorem cell21_941831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 11].length) (baseStart_941831 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_941831 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_941831 prefixEnd_941831 := by exact prefixLift 941831
  have htrace : WordTrace (prefixWord ++ tailWord_941831) baseStart_941831 baseEnd_941831 := by
    simpa [prefixWord, tailWord_941831, baseEnd_941831] using wordTrace_append hprefix tailTrace_941831
  have hstable : (prefixWord ++ tailWord_941831).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941831).length < 2 ^ (prefixWord ++ tailWord_941831).sum := by decide
  have hdescent : baseEnd_941831 < baseStart_941831 := by decide
  rcases family_descends (prefixWord ++ tailWord_941831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941834 : List Nat := [3, 1, 2, 2, 1, 4, 2, 2, 4]
def baseStart_941834 : Nat := 118140960795 + 941834 * 2 ^ 59
def prefixEnd_941834 : Nat := 4983230072969 + 3 ^ 40 * 941834 * 2
def baseEnd_941834 : Nat := 214939350554121468374929

theorem tailTrace_941834 : CollatzResearch.WordTrace tailWord_941834 prefixEnd_941834 214939350554121468374929 := by
  unfold tailWord_941834
  simp only [CollatzResearch.WordTrace]
  refine ⟨8587877017475936321548139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22901005379935830190795037 8587877017475936321548139)
  ·
    refine ⟨12881815526213904482322209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8587877017475936321548139 12881815526213904482322209)
    ·
      refine ⟨9661361644660428361741657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12881815526213904482322209 9661361644660428361741657)
      ·
        refine ⟨7246021233495321271306243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9661361644660428361741657 7246021233495321271306243)
        ·
          refine ⟨10869031850242981906959365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7246021233495321271306243 10869031850242981906959365)
          ·
            refine ⟨2037943471920559107554881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10869031850242981906959365 2037943471920559107554881)
            ·
              refine ⟨1528457603940419330666161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2037943471920559107554881 1528457603940419330666161)
              ·
                refine ⟨1146343202955314497999621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1528457603940419330666161 1146343202955314497999621)
                ·
                  refine ⟨214939350554121468374929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1146343202955314497999621 214939350554121468374929)
                  ·
                    rfl

theorem cell21_941834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 2, 4].length) (baseStart_941834 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_941834 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_941834 prefixEnd_941834 := by exact prefixLift 941834
  have htrace : WordTrace (prefixWord ++ tailWord_941834) baseStart_941834 baseEnd_941834 := by
    simpa [prefixWord, tailWord_941834, baseEnd_941834] using wordTrace_append hprefix tailTrace_941834
  have hstable : (prefixWord ++ tailWord_941834).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941834).length < 2 ^ (prefixWord ++ tailWord_941834).sum := by decide
  have hdescent : baseEnd_941834 < baseStart_941834 := by decide
  rcases family_descends (prefixWord ++ tailWord_941834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941924 : List Nat := [2, 3, 1, 1, 5, 1, 1, 7]
def baseStart_941924 : Nat := 118140960795 + 941924 * 2 ^ 59
def prefixEnd_941924 : Nat := 4983230072969 + 3 ^ 40 * 941924 * 2
def baseEnd_941924 : Nat := 71653296593433770624915

theorem tailTrace_941924 : CollatzResearch.WordTrace tailWord_941924 prefixEnd_941924 71653296593433770624915 := by
  unfold tailWord_941924
  simp only [CollatzResearch.WordTrace]
  refine ⟨17177395319788845328484413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22903193759718460437979217 17177395319788845328484413)
  ·
    refine ⟨6441523244920816998181655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17177395319788845328484413 6441523244920816998181655)
    ·
      refine ⟨9662284867381225497272483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6441523244920816998181655 9662284867381225497272483)
      ·
        refine ⟨14493427301071838245908725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9662284867381225497272483 14493427301071838245908725)
        ·
          refine ⟨1358758809475484835553943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14493427301071838245908725 1358758809475484835553943)
          ·
            refine ⟨2038138214213227253330915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1358758809475484835553943 2038138214213227253330915)
            ·
              refine ⟨3057207321319840879996373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2038138214213227253330915 3057207321319840879996373)
              ·
                refine ⟨71653296593433770624915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3057207321319840879996373 71653296593433770624915)
                ·
                  rfl

theorem cell21_941924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 7].length) (baseStart_941924 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_941924 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_941924 prefixEnd_941924 := by exact prefixLift 941924
  have htrace : WordTrace (prefixWord ++ tailWord_941924) baseStart_941924 baseEnd_941924 := by
    simpa [prefixWord, tailWord_941924, baseEnd_941924] using wordTrace_append hprefix tailTrace_941924
  have hstable : (prefixWord ++ tailWord_941924).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941924).length < 2 ^ (prefixWord ++ tailWord_941924).sum := by decide
  have hdescent : baseEnd_941924 < baseStart_941924 := by decide
  rcases family_descends (prefixWord ++ tailWord_941924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941930 : List Nat := [3, 1, 3, 4, 1, 2, 1, 3, 3]
def baseStart_941930 : Nat := 118140960795 + 941930 * 2 ^ 59
def prefixEnd_941930 : Nat := 4983230072969 + 3 ^ 40 * 941930 * 2
def baseEnd_941930 : Nat := 214961259062046634774733

theorem tailTrace_941930 : CollatzResearch.WordTrace tailWord_941930 prefixEnd_941930 214961259062046634774733 := by
  unfold tailWord_941930
  simp only [CollatzResearch.WordTrace]
  refine ⟨8588752369388988420421811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22903339651703969121124829 8588752369388988420421811)
  ·
    refine ⟨12883128554083482630632717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8588752369388988420421811 12883128554083482630632717)
    ·
      refine ⟨4831173207781305986487269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12883128554083482630632717 4831173207781305986487269)
      ·
        refine ⟨905844976458994872466363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4831173207781305986487269 905844976458994872466363)
        ·
          refine ⟨1358767464688492308699545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 905844976458994872466363 1358767464688492308699545)
          ·
            refine ⟨1019075598516369231524659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1358767464688492308699545 1019075598516369231524659)
            ·
              refine ⟨1528613397774553847286989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1019075598516369231524659 1528613397774553847286989)
              ·
                refine ⟨573230024165457692732621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1528613397774553847286989 573230024165457692732621)
                ·
                  refine ⟨214961259062046634774733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 573230024165457692732621 214961259062046634774733)
                  ·
                    rfl

theorem cell21_941930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 3, 3].length) (baseStart_941930 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_941930 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_941930 prefixEnd_941930 := by exact prefixLift 941930
  have htrace : WordTrace (prefixWord ++ tailWord_941930) baseStart_941930 baseEnd_941930 := by
    simpa [prefixWord, tailWord_941930, baseEnd_941930] using wordTrace_append hprefix tailTrace_941930
  have hstable : (prefixWord ++ tailWord_941930).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941930).length < 2 ^ (prefixWord ++ tailWord_941930).sum := by decide
  have hdescent : baseEnd_941930 < baseStart_941930 := by decide
  rcases family_descends (prefixWord ++ tailWord_941930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941952 : List Nat := [2, 1, 1, 2, 1, 2, 3, 3, 6]
def baseStart_941952 : Nat := 118140960795 + 941952 * 2 ^ 59
def prefixEnd_941952 : Nat := 4983230072969 + 3 ^ 40 * 941952 * 2
def baseEnd_941952 : Nat := 214966279761779485408021

theorem tailTrace_941952 : CollatzResearch.WordTrace tailWord_941952 prefixEnd_941952 214966279761779485408021 := by
  unfold tailWord_941952
  simp only [CollatzResearch.WordTrace]
  refine ⟨17177905941738125719494055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22903874588984167625992073 17177905941738125719494055)
  ·
    refine ⟨25766858912607188579241083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17177905941738125719494055 25766858912607188579241083)
    ·
      refine ⟨38650288368910782868861625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25766858912607188579241083 38650288368910782868861625)
      ·
        refine ⟨28987716276683087151646219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38650288368910782868861625 28987716276683087151646219)
        ·
          refine ⟨43481574415024630727469329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28987716276683087151646219 43481574415024630727469329)
          ·
            refine ⟨32611180811268473045601997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43481574415024630727469329 32611180811268473045601997)
            ·
              refine ⟨12229192804225677392100749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32611180811268473045601997 12229192804225677392100749)
              ·
                refine ⟨4585947301584629022037781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12229192804225677392100749 4585947301584629022037781)
                ·
                  refine ⟨214966279761779485408021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4585947301584629022037781 214966279761779485408021)
                  ·
                    rfl

theorem cell21_941952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 6].length) (baseStart_941952 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_941952 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_941952 prefixEnd_941952 := by exact prefixLift 941952
  have htrace : WordTrace (prefixWord ++ tailWord_941952) baseStart_941952 baseEnd_941952 := by
    simpa [prefixWord, tailWord_941952, baseEnd_941952] using wordTrace_append hprefix tailTrace_941952
  have hstable : (prefixWord ++ tailWord_941952).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941952).length < 2 ^ (prefixWord ++ tailWord_941952).sum := by decide
  have hdescent : baseEnd_941952 < baseStart_941952 := by decide
  rcases family_descends (prefixWord ++ tailWord_941952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941955 : List Nat := [1, 1, 1, 3, 4, 4, 1, 1, 5]
def baseStart_941955 : Nat := 118140960795 + 941955 * 2 ^ 59
def prefixEnd_941955 : Nat := 4983230072969 + 3 ^ 40 * 941955 * 2
def baseEnd_941955 : Nat := 214966964402652146858015

theorem tailTrace_941955 : CollatzResearch.WordTrace tailWord_941955 prefixEnd_941955 214966964402652146858015 := by
  unfold tailWord_941955
  simp only [CollatzResearch.WordTrace]
  refine ⟨34355921302465382951347319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22903947534976921967564879 34355921302465382951347319)
  ·
    refine ⟨51533881953698074427020979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34355921302465382951347319 51533881953698074427020979)
    ·
      refine ⟨77300822930547111640531469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51533881953698074427020979 77300822930547111640531469)
      ·
        refine ⟨28987808598955166865199301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77300822930547111640531469 28987808598955166865199301)
        ·
          refine ⟨5435214112304093787224869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28987808598955166865199301 5435214112304093787224869)
          ·
            refine ⟨1019102646057017585104663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5435214112304093787224869 1019102646057017585104663)
            ·
              refine ⟨1528653969085526377656995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1019102646057017585104663 1528653969085526377656995)
              ·
                refine ⟨2292980953628289566485493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1528653969085526377656995 2292980953628289566485493)
                ·
                  refine ⟨214966964402652146858015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2292980953628289566485493 214966964402652146858015)
                  ·
                    rfl

theorem cell21_941955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 1, 5].length) (baseStart_941955 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_941955 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_941955 prefixEnd_941955 := by exact prefixLift 941955
  have htrace : WordTrace (prefixWord ++ tailWord_941955) baseStart_941955 baseEnd_941955 := by
    simpa [prefixWord, tailWord_941955, baseEnd_941955] using wordTrace_append hprefix tailTrace_941955
  have hstable : (prefixWord ++ tailWord_941955).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941955).length < 2 ^ (prefixWord ++ tailWord_941955).sum := by decide
  have hdescent : baseEnd_941955 < baseStart_941955 := by decide
  rcases family_descends (prefixWord ++ tailWord_941955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942062 : List Nat := [4, 1, 2, 1, 3, 1, 3, 2, 4]
def baseStart_942062 : Nat := 118140960795 + 942062 * 2 ^ 59
def prefixEnd_942062 : Nat := 4983230072969 + 3 ^ 40 * 942062 * 2
def baseEnd_942062 : Nat := 214991383260443738574463

theorem tailTrace_942062 : CollatzResearch.WordTrace tailWord_942062 prefixEnd_942062 214991383260443738574463 := by
  unfold tailWord_942062
  simp only [CollatzResearch.WordTrace]
  refine ⟨4294977989134717528186555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22906549275385160150328293 4294977989134717528186555)
  ·
    refine ⟨6442466983702076292279833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4294977989134717528186555 6442466983702076292279833)
    ·
      refine ⟨4831850237776557219209875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6442466983702076292279833 4831850237776557219209875)
      ·
        refine ⟨7247775356664835828814813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4831850237776557219209875 7247775356664835828814813)
        ·
          refine ⟨2717915758749313435805555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7247775356664835828814813 2717915758749313435805555)
          ·
            refine ⟨4076873638123970153708333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2717915758749313435805555 4076873638123970153708333)
            ·
              refine ⟨1528827614296488807640625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4076873638123970153708333 1528827614296488807640625)
              ·
                refine ⟨1146620710722366605730469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1528827614296488807640625 1146620710722366605730469)
                ·
                  refine ⟨214991383260443738574463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1146620710722366605730469 214991383260443738574463)
                  ·
                    rfl

theorem cell21_942062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 2, 4].length) (baseStart_942062 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_942062 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_942062 prefixEnd_942062 := by exact prefixLift 942062
  have htrace : WordTrace (prefixWord ++ tailWord_942062) baseStart_942062 baseEnd_942062 := by
    simpa [prefixWord, tailWord_942062, baseEnd_942062] using wordTrace_append hprefix tailTrace_942062
  have hstable : (prefixWord ++ tailWord_942062).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942062).length < 2 ^ (prefixWord ++ tailWord_942062).sum := by decide
  have hdescent : baseEnd_942062 < baseStart_942062 := by decide
  rcases family_descends (prefixWord ++ tailWord_942062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942104 : List Nat := [2, 1, 2, 3, 2, 1, 1, 1, 8]
def baseStart_942104 : Nat := 118140960795 + 942104 * 2 ^ 59
def prefixEnd_942104 : Nat := 4983230072969 + 3 ^ 40 * 942104 * 2
def baseEnd_942104 : Nat := 215000968232660998874377

theorem tailTrace_942104 : CollatzResearch.WordTrace tailWord_942104 prefixEnd_942104 215000968232660998874377 := by
  unfold tailWord_942104
  simp only [CollatzResearch.WordTrace]
  refine ⟨17180677889462790699260683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22907570519283720932347577 17180677889462790699260683)
  ·
    refine ⟨25771016834194186048891025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17180677889462790699260683 25771016834194186048891025)
    ·
      refine ⟨19328262625645639536668269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25771016834194186048891025 19328262625645639536668269)
      ·
        refine ⟨7248098484617114826250601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19328262625645639536668269 7248098484617114826250601)
        ·
          refine ⟨5436073863462836119687951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7248098484617114826250601 5436073863462836119687951)
          ·
            refine ⟨8154110795194254179531927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5436073863462836119687951 8154110795194254179531927)
            ·
              refine ⟨12231166192791381269297891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8154110795194254179531927 12231166192791381269297891)
              ·
                refine ⟨18346749289187071903946837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12231166192791381269297891 18346749289187071903946837)
                ·
                  refine ⟨215000968232660998874377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18346749289187071903946837 215000968232660998874377)
                  ·
                    rfl

theorem cell21_942104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 8].length) (baseStart_942104 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_942104 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_942104 prefixEnd_942104 := by exact prefixLift 942104
  have htrace : WordTrace (prefixWord ++ tailWord_942104) baseStart_942104 baseEnd_942104 := by
    simpa [prefixWord, tailWord_942104, baseEnd_942104] using wordTrace_append hprefix tailTrace_942104
  have hstable : (prefixWord ++ tailWord_942104).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942104).length < 2 ^ (prefixWord ++ tailWord_942104).sum := by decide
  have hdescent : baseEnd_942104 < baseStart_942104 := by decide
  rcases family_descends (prefixWord ++ tailWord_942104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942149 : List Nat := [1, 3, 1, 1, 1, 3, 1, 3, 7]
def baseStart_942149 : Nat := 118140960795 + 942149 * 2 ^ 59
def prefixEnd_942149 : Nat := 4983230072969 + 3 ^ 40 * 942149 * 2
def baseEnd_942149 : Nat := 215011237845750920624285

theorem tailTrace_942149 : CollatzResearch.WordTrace tailWord_942149 prefixEnd_942149 215011237845750920624285 := by
  unfold tailWord_942149
  simp only [CollatzResearch.WordTrace]
  refine ⟨34362997063762554083909501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22908664709175036055939667 34362997063762554083909501)
  ·
    refine ⟨12886123898910957781466063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34362997063762554083909501 12886123898910957781466063)
    ·
      refine ⟨19329185848366436672199095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12886123898910957781466063 19329185848366436672199095)
      ·
        refine ⟨28993778772549655008298643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19329185848366436672199095 28993778772549655008298643)
        ·
          refine ⟨43490668158824482512447965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28993778772549655008298643 43490668158824482512447965)
          ·
            refine ⟨16309000559559180942167987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43490668158824482512447965 16309000559559180942167987)
            ·
              refine ⟨24463500839338771413251981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16309000559559180942167987 24463500839338771413251981)
              ·
                refine ⟨9173812814752039279969493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24463500839338771413251981 9173812814752039279969493)
                ·
                  refine ⟨215011237845750920624285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9173812814752039279969493 215011237845750920624285)
                  ·
                    rfl

theorem cell21_942149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 7].length) (baseStart_942149 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_942149 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_942149 prefixEnd_942149 := by exact prefixLift 942149
  have htrace : WordTrace (prefixWord ++ tailWord_942149) baseStart_942149 baseEnd_942149 := by
    simpa [prefixWord, tailWord_942149, baseEnd_942149] using wordTrace_append hprefix tailTrace_942149
  have hstable : (prefixWord ++ tailWord_942149).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942149).length < 2 ^ (prefixWord ++ tailWord_942149).sum := by decide
  have hdescent : baseEnd_942149 < baseStart_942149 := by decide
  rcases family_descends (prefixWord ++ tailWord_942149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942180 : List Nat := [2, 3, 1, 1, 2, 1, 2, 3, 6]
def baseStart_942180 : Nat := 118140960795 + 942180 * 2 ^ 59
def prefixEnd_942180 : Nat := 4983230072969 + 3 ^ 40 * 942180 * 2
def baseEnd_942180 : Nat := 215018312468101755607555

theorem tailTrace_942180 : CollatzResearch.WordTrace tailWord_942180 prefixEnd_942180 215018312468101755607555 := by
  unfold tailWord_942180
  simp only [CollatzResearch.WordTrace]
  refine ⟨17182063863325123189143997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22909418484433497585525329 17182063863325123189143997)
  ·
    refine ⟨6443273948746921195928999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17182063863325123189143997 6443273948746921195928999)
    ·
      refine ⟨9664910923120381793893499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6443273948746921195928999 9664910923120381793893499)
      ·
        refine ⟨14497366384680572690840249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9664910923120381793893499 14497366384680572690840249)
        ·
          refine ⟨10873024788510429518130187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14497366384680572690840249 10873024788510429518130187)
          ·
            refine ⟨16309537182765644277195281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10873024788510429518130187 16309537182765644277195281)
            ·
              refine ⟨12232152887074233207896461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16309537182765644277195281 12232152887074233207896461)
              ·
                refine ⟨4587057332652837452961173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12232152887074233207896461 4587057332652837452961173)
                ·
                  refine ⟨215018312468101755607555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4587057332652837452961173 215018312468101755607555)
                  ·
                    rfl

theorem cell21_942180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_942180 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_942180 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_942180 prefixEnd_942180 := by exact prefixLift 942180
  have htrace : WordTrace (prefixWord ++ tailWord_942180) baseStart_942180 baseEnd_942180 := by
    simpa [prefixWord, tailWord_942180, baseEnd_942180] using wordTrace_append hprefix tailTrace_942180
  have hstable : (prefixWord ++ tailWord_942180).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942180).length < 2 ^ (prefixWord ++ tailWord_942180).sum := by decide
  have hdescent : baseEnd_942180 < baseStart_942180 := by decide
  rcases family_descends (prefixWord ++ tailWord_942180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942183 : List Nat := [1, 1, 5, 1, 1, 2, 3, 4, 3]
def baseStart_942183 : Nat := 118140960795 + 942183 * 2 ^ 59
def prefixEnd_942183 : Nat := 4983230072969 + 3 ^ 40 * 942183 * 2
def baseEnd_942183 : Nat := 215018997108974417057549

theorem tailTrace_942183 : CollatzResearch.WordTrace tailWord_942183 prefixEnd_942183 215018997108974417057549 := by
  unfold tailWord_942183
  simp only [CollatzResearch.WordTrace]
  refine ⟨34364237145639377890647203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22909491430426251927098135 34364237145639377890647203)
  ·
    refine ⟨51546355718459066835970805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34364237145639377890647203 51546355718459066835970805)
    ·
      refine ⟨4832470848605537515872263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51546355718459066835970805 4832470848605537515872263)
      ·
        refine ⟨7248706272908306273808395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4832470848605537515872263 7248706272908306273808395)
        ·
          refine ⟨10873059409362459410712593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7248706272908306273808395 10873059409362459410712593)
          ·
            refine ⟨8154794557021844558034445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10873059409362459410712593 8154794557021844558034445)
            ·
              refine ⟨3058047958883191709262917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8154794557021844558034445 3058047958883191709262917)
              ·
                refine ⟨573383992290598445486797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3058047958883191709262917 573383992290598445486797)
                ·
                  refine ⟨215018997108974417057549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 573383992290598445486797 215018997108974417057549)
                  ·
                    rfl

theorem cell21_942183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 4, 3].length) (baseStart_942183 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_942183 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_942183 prefixEnd_942183 := by exact prefixLift 942183
  have htrace : WordTrace (prefixWord ++ tailWord_942183) baseStart_942183 baseEnd_942183 := by
    simpa [prefixWord, tailWord_942183, baseEnd_942183] using wordTrace_append hprefix tailTrace_942183
  have hstable : (prefixWord ++ tailWord_942183).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942183).length < 2 ^ (prefixWord ++ tailWord_942183).sum := by decide
  have hdescent : baseEnd_942183 < baseStart_942183 := by decide
  rcases family_descends (prefixWord ++ tailWord_942183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942231 : List Nat := [1, 1, 3, 3, 5, 1, 1, 2, 4]
def baseStart_942231 : Nat := 118140960795 + 942231 * 2 ^ 59
def prefixEnd_942231 : Nat := 4983230072969 + 3 ^ 40 * 942231 * 2
def baseEnd_942231 : Nat := 215029951362937000257451

theorem tailTrace_942231 : CollatzResearch.WordTrace tailWord_942231 prefixEnd_942231 215029951362937000257451 := by
  unfold tailWord_942231
  simp only [CollatzResearch.WordTrace]
  refine ⟨34365987849465482088394547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22910658566310321392263031 34365987849465482088394547)
  ·
    refine ⟨51548981774198223132591821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34365987849465482088394547 51548981774198223132591821)
    ·
      refine ⟨19330868165324333674721933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51548981774198223132591821 19330868165324333674721933)
      ·
        refine ⟨7249075561996625128020725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19330868165324333674721933 7249075561996625128020725)
        ·
          refine ⟨679600833937183605751943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7249075561996625128020725 679600833937183605751943)
          ·
            refine ⟨1019401250905775408627915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 679600833937183605751943 1019401250905775408627915)
            ·
              refine ⟨1529101876358663112941873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1019401250905775408627915 1529101876358663112941873)
              ·
                refine ⟨1146826407268997334706405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1529101876358663112941873 1146826407268997334706405)
                ·
                  refine ⟨215029951362937000257451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1146826407268997334706405 215029951362937000257451)
                  ·
                    rfl

theorem cell21_942231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 2, 4].length) (baseStart_942231 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_942231 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_942231 prefixEnd_942231 := by exact prefixLift 942231
  have htrace : WordTrace (prefixWord ++ tailWord_942231) baseStart_942231 baseEnd_942231 := by
    simpa [prefixWord, tailWord_942231, baseEnd_942231] using wordTrace_append hprefix tailTrace_942231
  have hstable : (prefixWord ++ tailWord_942231).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942231).length < 2 ^ (prefixWord ++ tailWord_942231).sum := by decide
  have hdescent : baseEnd_942231 < baseStart_942231 := by decide
  rcases family_descends (prefixWord ++ tailWord_942231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942276 : List Nat := [2, 3, 3, 1, 2, 1, 3, 3, 3]
def baseStart_942276 : Nat := 118140960795 + 942276 * 2 ^ 59
def prefixEnd_942276 : Nat := 4983230072969 + 3 ^ 40 * 942276 * 2
def baseEnd_942276 : Nat := 215040220976026922007359

theorem tailTrace_942276 : CollatzResearch.WordTrace tailWord_942276 prefixEnd_942276 215040220976026922007359 := by
  unfold tailWord_942276
  simp only [CollatzResearch.WordTrace]
  refine ⟨17183814567151227386891341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22911752756201636515855121 17183814567151227386891341)
  ·
    refine ⟨6443930462681710270084253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17183814567151227386891341 6443930462681710270084253)
    ·
      refine ⟨2416473923505641351281595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6443930462681710270084253 2416473923505641351281595)
      ·
        refine ⟨3624710885258462026922393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2416473923505641351281595 3624710885258462026922393)
        ·
          refine ⟨2718533163943846520191795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3624710885258462026922393 2718533163943846520191795)
          ·
            refine ⟨4077799745915769780287693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2718533163943846520191795 4077799745915769780287693)
            ·
              refine ⟨1529174904718413667607885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4077799745915769780287693 1529174904718413667607885)
              ·
                refine ⟨573440589269405125352957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1529174904718413667607885 573440589269405125352957)
                ·
                  refine ⟨215040220976026922007359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 573440589269405125352957 215040220976026922007359)
                  ·
                    rfl

theorem cell21_942276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 3, 3].length) (baseStart_942276 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_942276 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_942276 prefixEnd_942276 := by exact prefixLift 942276
  have htrace : WordTrace (prefixWord ++ tailWord_942276) baseStart_942276 baseEnd_942276 := by
    simpa [prefixWord, tailWord_942276, baseEnd_942276] using wordTrace_append hprefix tailTrace_942276
  have hstable : (prefixWord ++ tailWord_942276).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942276).length < 2 ^ (prefixWord ++ tailWord_942276).sum := by decide
  have hdescent : baseEnd_942276 < baseStart_942276 := by decide
  rcases family_descends (prefixWord ++ tailWord_942276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942293 : List Nat := [1, 3, 2, 4, 2, 1, 3, 2, 3]
def baseStart_942293 : Nat := 118140960795 + 942293 * 2 ^ 59
def prefixEnd_942293 : Nat := 4983230072969 + 3 ^ 40 * 942293 * 2
def baseEnd_942293 : Nat := 215044100607638670223991

theorem tailTrace_942293 : CollatzResearch.WordTrace tailWord_942293 prefixEnd_942293 215044100607638670223991 := by
  unfold tailWord_942293
  simp only [CollatzResearch.WordTrace]
  refine ⟨34368249175240866677151533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22912166116827244451434355 34368249175240866677151533)
  ·
    refine ⟨12888093440715325003931825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34368249175240866677151533 12888093440715325003931825)
    ·
      refine ⟨9666070080536493752948869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12888093440715325003931825 9666070080536493752948869)
      ·
        refine ⟨1812388140100592578677913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9666070080536493752948869 1812388140100592578677913)
        ·
          refine ⟨1359291105075444434008435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1812388140100592578677913 1359291105075444434008435)
          ·
            refine ⟨2038936657613166651012653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1359291105075444434008435 2038936657613166651012653)
            ·
              refine ⟨764601246604937494129745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2038936657613166651012653 764601246604937494129745)
              ·
                refine ⟨573450934953703120597309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 764601246604937494129745 573450934953703120597309)
                ·
                  refine ⟨215044100607638670223991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 573450934953703120597309 215044100607638670223991)
                  ·
                    rfl

theorem cell21_942293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 3, 2, 3].length) (baseStart_942293 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_942293 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_942293 prefixEnd_942293 := by exact prefixLift 942293
  have htrace : WordTrace (prefixWord ++ tailWord_942293) baseStart_942293 baseEnd_942293 := by
    simpa [prefixWord, tailWord_942293, baseEnd_942293] using wordTrace_append hprefix tailTrace_942293
  have hstable : (prefixWord ++ tailWord_942293).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942293).length < 2 ^ (prefixWord ++ tailWord_942293).sum := by decide
  have hdescent : baseEnd_942293 < baseStart_942293 := by decide
  rcases family_descends (prefixWord ++ tailWord_942293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942439 : List Nat := [1, 1, 5, 1, 3, 2, 1, 7]
def baseStart_942439 : Nat := 118140960795 + 942439 * 2 ^ 59
def prefixEnd_942439 : Nat := 4983230072969 + 3 ^ 40 * 942439 * 2
def baseEnd_942439 : Nat := 71692473265591620263453

theorem tailTrace_942439 : CollatzResearch.WordTrace tailWord_942439 prefixEnd_942439 71692473265591620263453 := by
  unfold tailWord_942439
  simp only [CollatzResearch.WordTrace]
  refine ⟨34373574232711933611966371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22915716155141289074644247 34373574232711933611966371)
  ·
    refine ⟨51560361349067900417949557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34373574232711933611966371 51560361349067900417949557)
    ·
      refine ⟨4833783876475115664182771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51560361349067900417949557 4833783876475115664182771)
      ·
        refine ⟨7250675814712673496274157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4833783876475115664182771 7250675814712673496274157)
        ·
          refine ⟨2719003430517252561102809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7250675814712673496274157 2719003430517252561102809)
          ·
            refine ⟨2039252572887939420827107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2719003430517252561102809 2039252572887939420827107)
            ·
              refine ⟨3058878859331909131240661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2039252572887939420827107 3058878859331909131240661)
              ·
                refine ⟨71692473265591620263453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3058878859331909131240661 71692473265591620263453)
                ·
                  rfl

theorem cell21_942439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 7].length) (baseStart_942439 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_942439 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_942439 prefixEnd_942439 := by exact prefixLift 942439
  have htrace : WordTrace (prefixWord ++ tailWord_942439) baseStart_942439 baseEnd_942439 := by
    simpa [prefixWord, tailWord_942439, baseEnd_942439] using wordTrace_append hprefix tailTrace_942439
  have hstable : (prefixWord ++ tailWord_942439).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942439).length < 2 ^ (prefixWord ++ tailWord_942439).sum := by decide
  have hdescent : baseEnd_942439 < baseStart_942439 := by decide
  rcases family_descends (prefixWord ++ tailWord_942439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942543 : List Nat := [1, 1, 2, 1, 1, 4, 1, 2, 8]
def baseStart_942543 : Nat := 118140960795 + 942543 * 2 ^ 59
def prefixEnd_942543 : Nat := 4983230072969 + 3 ^ 40 * 942543 * 2
def baseEnd_942543 : Nat := 215101154013693791056813

theorem tailTrace_942543 : CollatzResearch.WordTrace tailWord_942543 prefixEnd_942543 215101154013693791056813 := by
  unfold tailWord_942543
  simp only [CollatzResearch.WordTrace]
  refine ⟨34377367424335159373752283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22918244949556772915834855 34377367424335159373752283)
  ·
    refine ⟨51566051136502739060628425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34377367424335159373752283 51566051136502739060628425)
    ·
      refine ⟨38674538352377054295471319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51566051136502739060628425 38674538352377054295471319)
      ·
        refine ⟨58011807528565581443206979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38674538352377054295471319 58011807528565581443206979)
        ·
          refine ⟨87017711292848372164810469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58011807528565581443206979 87017711292848372164810469)
          ·
            refine ⟨16315820867409069780901963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87017711292848372164810469 16315820867409069780901963)
            ·
              refine ⟨24473731301113604671352945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16315820867409069780901963 24473731301113604671352945)
              ·
                refine ⟨18355298475835203503514709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24473731301113604671352945 18355298475835203503514709)
                ·
                  refine ⟨215101154013693791056813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18355298475835203503514709 215101154013693791056813)
                  ·
                    rfl

theorem cell21_942543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 8].length) (baseStart_942543 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_942543 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_942543 prefixEnd_942543 := by exact prefixLift 942543
  have htrace : WordTrace (prefixWord ++ tailWord_942543) baseStart_942543 baseEnd_942543 := by
    simpa [prefixWord, tailWord_942543, baseEnd_942543] using wordTrace_append hprefix tailTrace_942543
  have hstable : (prefixWord ++ tailWord_942543).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942543).length < 2 ^ (prefixWord ++ tailWord_942543).sum := by decide
  have hdescent : baseEnd_942543 < baseStart_942543 := by decide
  rcases family_descends (prefixWord ++ tailWord_942543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942650 : List Nat := [3, 1, 1, 1, 3, 3, 1, 8]
def baseStart_942650 : Nat := 118140960795 + 942650 * 2 ^ 59
def prefixEnd_942650 : Nat := 4983230072969 + 3 ^ 40 * 942650 * 2
def baseEnd_942650 : Nat := 71708524290495127591087

theorem tailTrace_942650 : CollatzResearch.WordTrace tailWord_942650 prefixEnd_942650 71708524290495127591087 := by
  unfold tailWord_942650
  simp only [CollatzResearch.WordTrace]
  refine ⟨8595317508736879161974351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22920846689965011098598269 8595317508736879161974351)
  ·
    refine ⟨12892976263105318742961527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8595317508736879161974351 12892976263105318742961527)
    ·
      refine ⟨19339464394657978114442291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12892976263105318742961527 19339464394657978114442291)
      ·
        refine ⟨29009196591986967171663437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19339464394657978114442291 29009196591986967171663437)
        ·
          refine ⟨10878448721995112689373789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29009196591986967171663437 10878448721995112689373789)
          ·
            refine ⟨4079418270748167258515171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10878448721995112689373789 4079418270748167258515171)
            ·
              refine ⟨6119127406122250887772757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4079418270748167258515171 6119127406122250887772757)
              ·
                refine ⟨71708524290495127591087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6119127406122250887772757 71708524290495127591087)
                ·
                  rfl

theorem cell21_942650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 8].length) (baseStart_942650 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_942650 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_942650 prefixEnd_942650 := by exact prefixLift 942650
  have htrace : WordTrace (prefixWord ++ tailWord_942650) baseStart_942650 baseEnd_942650 := by
    simpa [prefixWord, tailWord_942650, baseEnd_942650] using wordTrace_append hprefix tailTrace_942650
  have hstable : (prefixWord ++ tailWord_942650).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942650).length < 2 ^ (prefixWord ++ tailWord_942650).sum := by decide
  have hdescent : baseEnd_942650 < baseStart_942650 := by decide
  rcases family_descends (prefixWord ++ tailWord_942650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942653 : List Nat := [1, 4, 1, 3, 2, 2, 1, 3, 4]
def baseStart_942653 : Nat := 118140960795 + 942653 * 2 ^ 59
def prefixEnd_942653 : Nat := 4983230072969 + 3 ^ 40 * 942653 * 2
def baseEnd_942653 : Nat := 215126257512358044223255

theorem tailTrace_942653 : CollatzResearch.WordTrace tailWord_942653 prefixEnd_942653 215126257512358044223255 := by
  unfold tailWord_942653
  simp only [CollatzResearch.WordTrace]
  refine ⟨34381379453936648160256613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22920919635957765440171075 34381379453936648160256613)
  ·
    refine ⟨6446508647613121530048115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34381379453936648160256613 6446508647613121530048115)
    ·
      refine ⟨9669762971419682295072173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6446508647613121530048115 9669762971419682295072173)
      ·
        refine ⟨3626161114282380860652065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9669762971419682295072173 3626161114282380860652065)
        ·
          refine ⟨2719620835711785645489049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3626161114282380860652065 2719620835711785645489049)
          ·
            refine ⟨2039715626783839234116787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2719620835711785645489049 2039715626783839234116787)
            ·
              refine ⟨3059573440175758851175181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2039715626783839234116787 3059573440175758851175181)
              ·
                refine ⟨1147340040065909569190693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3059573440175758851175181 1147340040065909569190693)
                ·
                  refine ⟨215126257512358044223255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1147340040065909569190693 215126257512358044223255)
                  ·
                    rfl

theorem cell21_942653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 3, 4].length) (baseStart_942653 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_942653 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_942653 prefixEnd_942653 := by exact prefixLift 942653
  have htrace : WordTrace (prefixWord ++ tailWord_942653) baseStart_942653 baseEnd_942653 := by
    simpa [prefixWord, tailWord_942653, baseEnd_942653] using wordTrace_append hprefix tailTrace_942653
  have hstable : (prefixWord ++ tailWord_942653).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942653).length < 2 ^ (prefixWord ++ tailWord_942653).sum := by decide
  have hdescent : baseEnd_942653 < baseStart_942653 := by decide
  rcases family_descends (prefixWord ++ tailWord_942653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942690 : List Nat := [3, 3, 2, 3, 1, 2, 2, 2, 3]
def baseStart_942690 : Nat := 118140960795 + 942690 * 2 ^ 59
def prefixEnd_942690 : Nat := 4983230072969 + 3 ^ 40 * 942690 * 2
def baseEnd_942690 : Nat := 215134701416454202106513

theorem tailTrace_942690 : CollatzResearch.WordTrace tailWord_942690 prefixEnd_942690 215134701416454202106513 := by
  unfold tailWord_942690
  simp only [CollatzResearch.WordTrace]
  refine ⟨8595682238700650869838381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22921819303201735652902349 8595682238700650869838381)
  ·
    refine ⟨3223380839512744076189393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8595682238700650869838381 3223380839512744076189393)
    ·
      refine ⟨2417535629634558057142045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3223380839512744076189393 2417535629634558057142045)
      ·
        refine ⟨906575861112959271428267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2417535629634558057142045 906575861112959271428267)
        ·
          refine ⟨1359863791669438907142401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 906575861112959271428267 1359863791669438907142401)
          ·
            refine ⟨1019897843752079180356801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1359863791669438907142401 1019897843752079180356801)
            ·
              refine ⟨764923382814059385267601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1019897843752079180356801 764923382814059385267601)
              ·
                refine ⟨573692537110544538950701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 764923382814059385267601 573692537110544538950701)
                ·
                  refine ⟨215134701416454202106513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 573692537110544538950701 215134701416454202106513)
                  ·
                    rfl

theorem cell21_942690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 2, 2, 3].length) (baseStart_942690 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_942690 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_942690 prefixEnd_942690 := by exact prefixLift 942690
  have htrace : WordTrace (prefixWord ++ tailWord_942690) baseStart_942690 baseEnd_942690 := by
    simpa [prefixWord, tailWord_942690, baseEnd_942690] using wordTrace_append hprefix tailTrace_942690
  have hstable : (prefixWord ++ tailWord_942690).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942690).length < 2 ^ (prefixWord ++ tailWord_942690).sum := by decide
  have hdescent : baseEnd_942690 < baseStart_942690 := by decide
  rcases family_descends (prefixWord ++ tailWord_942690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942788 : List Nat := [2, 3, 3, 1, 1, 2, 1, 2, 6]
def baseStart_942788 : Nat := 118140960795 + 942788 * 2 ^ 59
def prefixEnd_942788 : Nat := 4983230072969 + 3 ^ 40 * 942788 * 2
def baseEnd_942788 : Nat := 215157066351627809472979

theorem tailTrace_942788 : CollatzResearch.WordTrace tailWord_942788 prefixEnd_942788 215157066351627809472979 := by
  unfold tailWord_942788
  simp only [CollatzResearch.WordTrace]
  refine ⟨17193151654223783108210509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22924202205631710810947345 17193151654223783108210509)
  ·
    refine ⟨6447431870333918665578941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17193151654223783108210509 6447431870333918665578941)
    ·
      refine ⟨2417786951375219499592103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6447431870333918665578941 2417786951375219499592103)
      ·
        refine ⟨3626680427062829249388155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2417786951375219499592103 3626680427062829249388155)
        ·
          refine ⟨5440020640594243874082233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3626680427062829249388155 5440020640594243874082233)
          ·
            refine ⟨4080015480445682905561675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5440020640594243874082233 4080015480445682905561675)
            ·
              refine ⟨6120023220668524358342513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4080015480445682905561675 6120023220668524358342513)
              ·
                refine ⟨4590017415501393268756885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6120023220668524358342513 4590017415501393268756885)
                ·
                  refine ⟨215157066351627809472979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4590017415501393268756885 215157066351627809472979)
                  ·
                    rfl

theorem cell21_942788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 6].length) (baseStart_942788 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_942788 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_942788 prefixEnd_942788 := by exact prefixLift 942788
  have htrace : WordTrace (prefixWord ++ tailWord_942788) baseStart_942788 baseEnd_942788 := by
    simpa [prefixWord, tailWord_942788, baseEnd_942788] using wordTrace_append hprefix tailTrace_942788
  have hstable : (prefixWord ++ tailWord_942788).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942788).length < 2 ^ (prefixWord ++ tailWord_942788).sum := by decide
  have hdescent : baseEnd_942788 < baseStart_942788 := by decide
  rcases family_descends (prefixWord ++ tailWord_942788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942819 : List Nat := [1, 1, 1, 7, 1, 2, 2, 6]
def baseStart_942819 : Nat := 118140960795 + 942819 * 2 ^ 59
def prefixEnd_942819 : Nat := 4983230072969 + 3 ^ 40 * 942819 * 2
def baseEnd_942819 : Nat := 71721380324659548152083

theorem tailTrace_942819 : CollatzResearch.WordTrace tailWord_942819 prefixEnd_942819 71721380324659548152083 := by
  unfold tailWord_942819
  simp only [CollatzResearch.WordTrace]
  refine ⟨34387433971335258510799511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22924955980890172340533007 34387433971335258510799511)
  ·
    refine ⟨51581150957002887766199267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34387433971335258510799511 51581150957002887766199267)
    ·
      refine ⟨77371726435504331649298901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51581150957002887766199267 77371726435504331649298901)
      ·
        refine ⟨1813399838332132773030443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 77371726435504331649298901 1813399838332132773030443)
        ·
          refine ⟨2720099757498199159545665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1813399838332132773030443 2720099757498199159545665)
          ·
            refine ⟨2040074818123649369659249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2720099757498199159545665 2040074818123649369659249)
            ·
              refine ⟨1530056113592737027244437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2040074818123649369659249 1530056113592737027244437)
              ·
                refine ⟨71721380324659548152083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1530056113592737027244437 71721380324659548152083)
                ·
                  rfl

theorem cell21_942819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 6].length) (baseStart_942819 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_942819 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_942819 prefixEnd_942819 := by exact prefixLift 942819
  have htrace : WordTrace (prefixWord ++ tailWord_942819) baseStart_942819 baseEnd_942819 := by
    simpa [prefixWord, tailWord_942819, baseEnd_942819] using wordTrace_append hprefix tailTrace_942819
  have hstable : (prefixWord ++ tailWord_942819).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942819).length < 2 ^ (prefixWord ++ tailWord_942819).sum := by decide
  have hdescent : baseEnd_942819 < baseStart_942819 := by decide
  rcases family_descends (prefixWord ++ tailWord_942819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942985 : List Nat := [1, 2, 1, 1, 5, 2, 3, 1, 5]
def baseStart_942985 : Nat := 118140960795 + 942985 * 2 ^ 59
def prefixEnd_942985 : Nat := 4983230072969 + 3 ^ 40 * 942985 * 2
def baseEnd_942985 : Nat := 215202024435599244689243

theorem tailTrace_942985 : CollatzResearch.WordTrace tailWord_942985 prefixEnd_942985 215202024435599244689243 := by
  unfold tailWord_942985
  simp only [CollatzResearch.WordTrace]
  refine ⟨34393488488733868861342409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22928992325822579240894939 34393488488733868861342409)
  ·
    refine ⟨25795116366550401646006807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34393488488733868861342409 25795116366550401646006807)
    ·
      refine ⟨38692674549825602469010211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25795116366550401646006807 38692674549825602469010211)
      ·
        refine ⟨58039011824738403703515317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38692674549825602469010211 58039011824738403703515317)
        ·
          refine ⟨5441157358569225347204561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58039011824738403703515317 5441157358569225347204561)
          ·
            refine ⟨4080868018926919010403421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5441157358569225347204561 4080868018926919010403421)
            ·
              refine ⟨1530325507097594628901283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4080868018926919010403421 1530325507097594628901283)
              ·
                refine ⟨2295488260646391943351925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1530325507097594628901283 2295488260646391943351925)
                ·
                  refine ⟨215202024435599244689243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2295488260646391943351925 215202024435599244689243)
                  ·
                    rfl

theorem cell21_942985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 1, 5].length) (baseStart_942985 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_942985 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_942985 prefixEnd_942985 := by exact prefixLift 942985
  have htrace : WordTrace (prefixWord ++ tailWord_942985) baseStart_942985 baseEnd_942985 := by
    simpa [prefixWord, tailWord_942985, baseEnd_942985] using wordTrace_append hprefix tailTrace_942985
  have hstable : (prefixWord ++ tailWord_942985).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942985).length < 2 ^ (prefixWord ++ tailWord_942985).sum := by decide
  have hdescent : baseEnd_942985 < baseStart_942985 := by decide
  rcases family_descends (prefixWord ++ tailWord_942985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943075 : List Nat := [1, 1, 1, 6, 1, 1, 2, 2, 6]
def baseStart_943075 : Nat := 118140960795 + 943075 * 2 ^ 59
def prefixEnd_943075 : Nat := 4983230072969 + 3 ^ 40 * 943075 * 2
def baseEnd_943075 : Nat := 215222563661779088189059

theorem tailTrace_943075 : CollatzResearch.WordTrace tailWord_943075 prefixEnd_943075 215222563661779088189059 := by
  unfold tailWord_943075
  simp only [CollatzResearch.WordTrace]
  refine ⟨34396771058407814232118679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22931180705605209488079119 34396771058407814232118679)
  ·
    refine ⟨51595156587611721348178019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34396771058407814232118679 51595156587611721348178019)
    ·
      refine ⟨77392734881417582022267029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51595156587611721348178019 77392734881417582022267029)
      ·
        refine ⟨3627784447566449157293767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 77392734881417582022267029 3627784447566449157293767)
        ·
          refine ⟨5441676671349673735940651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3627784447566449157293767 5441676671349673735940651)
          ·
            refine ⟨8162515007024510603910977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5441676671349673735940651 8162515007024510603910977)
            ·
              refine ⟨6121886255268382952933233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8162515007024510603910977 6121886255268382952933233)
              ·
                refine ⟨4591414691451287214699925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6121886255268382952933233 4591414691451287214699925)
                ·
                  refine ⟨215222563661779088189059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4591414691451287214699925 215222563661779088189059)
                  ·
                    rfl

theorem cell21_943075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 6].length) (baseStart_943075 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_943075 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_943075 prefixEnd_943075 := by exact prefixLift 943075
  have htrace : WordTrace (prefixWord ++ tailWord_943075) baseStart_943075 baseEnd_943075 := by
    simpa [prefixWord, tailWord_943075, baseEnd_943075] using wordTrace_append hprefix tailTrace_943075
  have hstable : (prefixWord ++ tailWord_943075).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943075).length < 2 ^ (prefixWord ++ tailWord_943075).sum := by decide
  have hdescent : baseEnd_943075 < baseStart_943075 := by decide
  rcases family_descends (prefixWord ++ tailWord_943075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943258 : List Nat := [3, 1, 1, 5, 1, 2, 8]
def baseStart_943258 : Nat := 118140960795 + 943258 * 2 ^ 59
def prefixEnd_943258 : Nat := 4983230072969 + 3 ^ 40 * 943258 * 2
def baseEnd_943258 : Nat := 23918258528334604070965

theorem tailTrace_943258 : CollatzResearch.WordTrace tailWord_943258 prefixEnd_943258 23918258528334604070965 := by
  unfold tailWord_943258
  simp only [CollatzResearch.WordTrace]
  refine ⟨8600861404186209121507607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22935630411163224324020285 8600861404186209121507607)
  ·
    refine ⟨12901292106279313682261411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8600861404186209121507607 12901292106279313682261411)
    ·
      refine ⟨19351938159418970523392117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12901292106279313682261411 19351938159418970523392117)
      ·
        refine ⟨1814244202445528486568011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19351938159418970523392117 1814244202445528486568011)
        ·
          refine ⟨2721366303668292729852017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1814244202445528486568011 2721366303668292729852017)
          ·
            refine ⟨2041024727751219547389013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2721366303668292729852017 2041024727751219547389013)
            ·
              refine ⟨23918258528334604070965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2041024727751219547389013 23918258528334604070965)
              ·
                rfl

theorem cell21_943258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 8].length) (baseStart_943258 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_943258 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_943258 prefixEnd_943258 := by exact prefixLift 943258
  have htrace : WordTrace (prefixWord ++ tailWord_943258) baseStart_943258 baseEnd_943258 := by
    simpa [prefixWord, tailWord_943258, baseEnd_943258] using wordTrace_append hprefix tailTrace_943258
  have hstable : (prefixWord ++ tailWord_943258).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943258).length < 2 ^ (prefixWord ++ tailWord_943258).sum := by decide
  have hdescent : baseEnd_943258 < baseStart_943258 := by decide
  rcases family_descends (prefixWord ++ tailWord_943258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943298 : List Nat := [3, 5, 1, 1, 3, 1, 1, 3, 3]
def baseStart_943298 : Nat := 118140960795 + 943298 * 2 ^ 59
def prefixEnd_943298 : Nat := 4983230072969 + 3 ^ 40 * 943298 * 2
def baseEnd_943298 : Nat := 215273455299980255971937

theorem tailTrace_943298 : CollatzResearch.WordTrace tailWord_943298 prefixEnd_943298 215273455299980255971937 := by
  unfold tailWord_943298
  simp only [CollatzResearch.WordTrace]
  refine ⟨8601226134149980829371637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22936603024399948878324365 8601226134149980829371637)
  ·
    refine ⟨806364950076560702753591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8601226134149980829371637 806364950076560702753591)
    ·
      refine ⟨1209547425114841054130387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 806364950076560702753591 1209547425114841054130387)
      ·
        refine ⟨1814321137672261581195581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1209547425114841054130387 1814321137672261581195581)
        ·
          refine ⟨680370426627098092948343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1814321137672261581195581 680370426627098092948343)
          ·
            refine ⟨1020555639940647139422515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 680370426627098092948343 1020555639940647139422515)
            ·
              refine ⟨1530833459910970709133773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1020555639940647139422515 1530833459910970709133773)
              ·
                refine ⟨574062547466614015925165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1530833459910970709133773 574062547466614015925165)
                ·
                  refine ⟨215273455299980255971937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 574062547466614015925165 215273455299980255971937)
                  ·
                    rfl

theorem cell21_943298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_943298 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_943298 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_943298 prefixEnd_943298 := by exact prefixLift 943298
  have htrace : WordTrace (prefixWord ++ tailWord_943298) baseStart_943298 baseEnd_943298 := by
    simpa [prefixWord, tailWord_943298, baseEnd_943298] using wordTrace_append hprefix tailTrace_943298
  have hstable : (prefixWord ++ tailWord_943298).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943298).length < 2 ^ (prefixWord ++ tailWord_943298).sum := by decide
  have hdescent : baseEnd_943298 < baseStart_943298 := by decide
  rcases family_descends (prefixWord ++ tailWord_943298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943306 : List Nat := [3, 1, 2, 1, 3, 2, 3, 3, 3]
def baseStart_943306 : Nat := 118140960795 + 943306 * 2 ^ 59
def prefixEnd_943306 : Nat := 4983230072969 + 3 ^ 40 * 943306 * 2
def baseEnd_943306 : Nat := 215275281008974019838587

theorem tailTrace_943306 : CollatzResearch.WordTrace tailWord_943306 prefixEnd_943306 215275281008974019838587 := by
  unfold tailWord_943306
  simp only [CollatzResearch.WordTrace]
  refine ⟨8601299080142735170944443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22936797547047293789185181 8601299080142735170944443)
  ·
    refine ⟨12901948620214102756416665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8601299080142735170944443 12901948620214102756416665)
    ·
      refine ⟨9676461465160577067312499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12901948620214102756416665 9676461465160577067312499)
      ·
        refine ⟨14514692197740865600968749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9676461465160577067312499 14514692197740865600968749)
        ·
          refine ⟨5443009574152824600363281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14514692197740865600968749 5443009574152824600363281)
          ·
            refine ⟨4082257180614618450272461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5443009574152824600363281 4082257180614618450272461)
            ·
              refine ⟨1530846442730481918852173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4082257180614618450272461 1530846442730481918852173)
              ·
                refine ⟨574067416023930719569565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1530846442730481918852173 574067416023930719569565)
                ·
                  refine ⟨215275281008974019838587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 574067416023930719569565 215275281008974019838587)
                  ·
                    rfl

theorem cell21_943306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 3, 3].length) (baseStart_943306 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_943306 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_943306 prefixEnd_943306 := by exact prefixLift 943306
  have htrace : WordTrace (prefixWord ++ tailWord_943306) baseStart_943306 baseEnd_943306 := by
    simpa [prefixWord, tailWord_943306, baseEnd_943306] using wordTrace_append hprefix tailTrace_943306
  have hstable : (prefixWord ++ tailWord_943306).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943306).length < 2 ^ (prefixWord ++ tailWord_943306).sum := by decide
  have hdescent : baseEnd_943306 < baseStart_943306 := by decide
  rcases family_descends (prefixWord ++ tailWord_943306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943309 : List Nat := [1, 6, 2, 2, 2, 1, 7]
def baseStart_943309 : Nat := 118140960795 + 943309 * 2 ^ 59
def prefixEnd_943309 : Nat := 4983230072969 + 3 ^ 40 * 943309 * 2
def baseEnd_943309 : Nat := 23919551738871853476509

theorem tailTrace_943309 : CollatzResearch.WordTrace tailWord_943309 prefixEnd_943309 23919551738871853476509 := by
  unfold tailWord_943309
  simp only [CollatzResearch.WordTrace]
  refine ⟨34405305739560072196136981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22936870493040048130757987 34405305739560072196136981)
  ·
    refine ⟨1612748706541878384193921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 34405305739560072196136981 1612748706541878384193921)
    ·
      refine ⟨1209561529906408788145441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1612748706541878384193921 1209561529906408788145441)
      ·
        refine ⟨907171147429806591109081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1209561529906408788145441 907171147429806591109081)
        ·
          refine ⟨680378360572354943331811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 907171147429806591109081 680378360572354943331811)
          ·
            refine ⟨1020567540858532414997717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 680378360572354943331811 1020567540858532414997717)
            ·
              refine ⟨23919551738871853476509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1020567540858532414997717 23919551738871853476509)
              ·
                rfl

theorem cell21_943309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 7].length) (baseStart_943309 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_943309 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_943309 prefixEnd_943309 := by exact prefixLift 943309
  have htrace : WordTrace (prefixWord ++ tailWord_943309) baseStart_943309 baseEnd_943309 := by
    simpa [prefixWord, tailWord_943309, baseEnd_943309] using wordTrace_append hprefix tailTrace_943309
  have hstable : (prefixWord ++ tailWord_943309).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943309).length < 2 ^ (prefixWord ++ tailWord_943309).sum := by decide
  have hdescent : baseEnd_943309 < baseStart_943309 := by decide
  rcases family_descends (prefixWord ++ tailWord_943309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943365 : List Nat := [1, 3, 1, 1, 2, 1, 4, 5, 3]
def baseStart_943365 : Nat := 118140960795 + 943365 * 2 ^ 59
def prefixEnd_943365 : Nat := 4983230072969 + 3 ^ 40 * 943365 * 2
def baseEnd_943365 : Nat := 215288745612803028355133

theorem tailTrace_943365 : CollatzResearch.WordTrace tailWord_943365 prefixEnd_943365 215288745612803028355133 := by
  unfold tailWord_943365
  simp only [CollatzResearch.WordTrace]
  refine ⟨34407348227357193760175549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22938232151571462506783699 34407348227357193760175549)
  ·
    refine ⟨12902755585258947660065831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34407348227357193760175549 12902755585258947660065831)
    ·
      refine ⟨19354133377888421490098747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12902755585258947660065831 19354133377888421490098747)
      ·
        refine ⟨29031200066832632235148121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19354133377888421490098747 29031200066832632235148121)
        ·
          refine ⟨21773400050124474176361091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29031200066832632235148121 21773400050124474176361091)
          ·
            refine ⟨32660100075186711264541637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21773400050124474176361091 32660100075186711264541637)
            ·
              refine ⟨6123768764097508362101557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32660100075186711264541637 6123768764097508362101557)
              ·
                refine ⟨574103321634141408947021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6123768764097508362101557 574103321634141408947021)
                ·
                  refine ⟨215288745612803028355133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 574103321634141408947021 215288745612803028355133)
                  ·
                    rfl

theorem cell21_943365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 5, 3].length) (baseStart_943365 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_943365 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_943365 prefixEnd_943365 := by exact prefixLift 943365
  have htrace : WordTrace (prefixWord ++ tailWord_943365) baseStart_943365 baseEnd_943365 := by
    simpa [prefixWord, tailWord_943365, baseEnd_943365] using wordTrace_append hprefix tailTrace_943365
  have hstable : (prefixWord ++ tailWord_943365).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943365).length < 2 ^ (prefixWord ++ tailWord_943365).sum := by decide
  have hdescent : baseEnd_943365 < baseStart_943365 := by decide
  rcases family_descends (prefixWord ++ tailWord_943365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943430 : List Nat := [6, 1, 1, 3, 1, 1, 1, 1, 6]
def baseStart_943430 : Nat := 118140960795 + 943430 * 2 ^ 59
def prefixEnd_943430 : Nat := 4983230072969 + 3 ^ 40 * 943430 * 2
def baseEnd_943430 : Nat := 215303579498377359771667

theorem tailTrace_943430 : CollatzResearch.WordTrace tailWord_943430 prefixEnd_943430 215303579498377359771667 := by
  unfold tailWord_943430
  simp only [CollatzResearch.WordTrace]
  refine ⟨1075303717878803433165367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 22939812648081139907527829 1075303717878803433165367)
  ·
    refine ⟨1612955576818205149748051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1075303717878803433165367 1612955576818205149748051)
    ·
      refine ⟨2419433365227307724622077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1612955576818205149748051 2419433365227307724622077)
      ·
        refine ⟨907287511960240396733279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2419433365227307724622077 907287511960240396733279)
        ·
          refine ⟨1360931267940360595099919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 907287511960240396733279 1360931267940360595099919)
          ·
            refine ⟨2041396901910540892649879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1360931267940360595099919 2041396901910540892649879)
            ·
              refine ⟨3062095352865811338974819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2041396901910540892649879 3062095352865811338974819)
              ·
                refine ⟨4593143029298717008462229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3062095352865811338974819 4593143029298717008462229)
                ·
                  refine ⟨215303579498377359771667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4593143029298717008462229 215303579498377359771667)
                  ·
                    rfl

theorem cell21_943430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_943430 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_943430 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_943430 prefixEnd_943430 := by exact prefixLift 943430
  have htrace : WordTrace (prefixWord ++ tailWord_943430) baseStart_943430 baseEnd_943430 := by
    simpa [prefixWord, tailWord_943430, baseEnd_943430] using wordTrace_append hprefix tailTrace_943430
  have hstable : (prefixWord ++ tailWord_943430).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943430).length < 2 ^ (prefixWord ++ tailWord_943430).sum := by decide
  have hdescent : baseEnd_943430 < baseStart_943430 := by decide
  rcases family_descends (prefixWord ++ tailWord_943430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943441 : List Nat := [1, 2, 2, 1, 4, 1, 1, 6, 3]
def baseStart_943441 : Nat := 118140960795 + 943441 * 2 ^ 59
def prefixEnd_943441 : Nat := 4983230072969 + 3 ^ 40 * 943441 * 2
def baseEnd_943441 : Nat := 215306089848243785088311

theorem tailTrace_943441 : CollatzResearch.WordTrace tailWord_943441 prefixEnd_943441 215306089848243785088311 := by
  unfold tailWord_943441
  simp only [CollatzResearch.WordTrace]
  refine ⟨34410120175081858739942177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22940080116721239159961451 34410120175081858739942177)
  ·
    refine ⟨25807590131311394054956633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34410120175081858739942177 25807590131311394054956633)
    ·
      refine ⟨19355692598483545541217475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25807590131311394054956633 19355692598483545541217475)
      ·
        refine ⟨29033538897725318311826213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19355692598483545541217475 29033538897725318311826213)
        ·
          refine ⟨5443788543323497183467415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29033538897725318311826213 5443788543323497183467415)
          ·
            refine ⟨8165682814985245775201123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5443788543323497183467415 8165682814985245775201123)
            ·
              refine ⟨12248524222477868662801685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8165682814985245775201123 12248524222477868662801685)
              ·
                refine ⟨574149572928650093568829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12248524222477868662801685 574149572928650093568829)
                ·
                  refine ⟨215306089848243785088311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 574149572928650093568829 215306089848243785088311)
                  ·
                    rfl

theorem cell21_943441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 6, 3].length) (baseStart_943441 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_943441 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_943441 prefixEnd_943441 := by exact prefixLift 943441
  have htrace : WordTrace (prefixWord ++ tailWord_943441) baseStart_943441 baseEnd_943441 := by
    simpa [prefixWord, tailWord_943441, baseEnd_943441] using wordTrace_append hprefix tailTrace_943441
  have hstable : (prefixWord ++ tailWord_943441).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943441).length < 2 ^ (prefixWord ++ tailWord_943441).sum := by decide
  have hdescent : baseEnd_943441 < baseStart_943441 := by decide
  rcases family_descends (prefixWord ++ tailWord_943441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943545 : List Nat := [1, 2, 1, 4, 4, 9]
def baseStart_943545 : Nat := 118140960795 + 943545 * 2 ^ 59
def prefixEnd_943545 : Nat := 4983230072969 + 3 ^ 40 * 943545 * 2
def baseEnd_943545 : Nat := 7975178669080100568695

theorem tailTrace_943545 : CollatzResearch.WordTrace tailWord_943545 prefixEnd_943545 7975178669080100568695 := by
  unfold tailWord_943545
  simp only [CollatzResearch.WordTrace]
  refine ⟨34413913366705084501728089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22942608911136723001152059 34413913366705084501728089)
  ·
    refine ⟨25810435025028813376296067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34413913366705084501728089 25810435025028813376296067)
    ·
      refine ⟨38715652537543220064444101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25810435025028813376296067 38715652537543220064444101)
      ·
        refine ⟨7259184850789353762083269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38715652537543220064444101 7259184850789353762083269)
        ·
          refine ⟨1361097159523003830390613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7259184850789353762083269 1361097159523003830390613)
          ·
            refine ⟨7975178669080100568695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1361097159523003830390613 7975178669080100568695)
            ·
              rfl

theorem cell21_943545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 9].length) (baseStart_943545 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_943545 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_943545 prefixEnd_943545 := by exact prefixLift 943545
  have htrace : WordTrace (prefixWord ++ tailWord_943545) baseStart_943545 baseEnd_943545 := by
    simpa [prefixWord, tailWord_943545, baseEnd_943545] using wordTrace_append hprefix tailTrace_943545
  have hstable : (prefixWord ++ tailWord_943545).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943545).length < 2 ^ (prefixWord ++ tailWord_943545).sum := by decide
  have hdescent : baseEnd_943545 < baseStart_943545 := by decide
  rcases family_descends (prefixWord ++ tailWord_943545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943554 : List Nat := [3, 5, 2, 1, 1, 2, 1, 6]
def baseStart_943554 : Nat := 118140960795 + 943554 * 2 ^ 59
def prefixEnd_943554 : Nat := 4983230072969 + 3 ^ 40 * 943554 * 2
def baseEnd_943554 : Nat := 71777292662593566568249

theorem tailTrace_943554 : CollatzResearch.WordTrace tailWord_943554 prefixEnd_943554 71777292662593566568249 := by
  unfold tailWord_943554
  simp only [CollatzResearch.WordTrace]
  refine ⟨8603560405918119759701429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22942827749114986025870477 8603560405918119759701429)
  ·
    refine ⟨806583788054823727472009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8603560405918119759701429 806583788054823727472009)
    ·
      refine ⟨604937841041117795604007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 806583788054823727472009 604937841041117795604007)
      ·
        refine ⟨907406761561676693406011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 604937841041117795604007 907406761561676693406011)
        ·
          refine ⟨1361110142342515040109017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 907406761561676693406011 1361110142342515040109017)
          ·
            refine ⟨1020832606756886280081763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1361110142342515040109017 1020832606756886280081763)
            ·
              refine ⟨1531248910135329420122645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1020832606756886280081763 1531248910135329420122645)
              ·
                refine ⟨71777292662593566568249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1531248910135329420122645 71777292662593566568249)
                ·
                  rfl

theorem cell21_943554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 6].length) (baseStart_943554 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_943554 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_943554 prefixEnd_943554 := by exact prefixLift 943554
  have htrace : WordTrace (prefixWord ++ tailWord_943554) baseStart_943554 baseEnd_943554 := by
    simpa [prefixWord, tailWord_943554, baseEnd_943554] using wordTrace_append hprefix tailTrace_943554
  have hstable : (prefixWord ++ tailWord_943554).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943554).length < 2 ^ (prefixWord ++ tailWord_943554).sum := by decide
  have hdescent : baseEnd_943554 < baseStart_943554 := by decide
  rcases family_descends (prefixWord ++ tailWord_943554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943562 : List Nat := [3, 1, 2, 1, 2, 5, 1, 6]
def baseStart_943562 : Nat := 118140960795 + 943562 * 2 ^ 59
def prefixEnd_943562 : Nat := 4983230072969 + 3 ^ 40 * 943562 * 2
def baseEnd_943562 : Nat := 71777901232258154523799

theorem tailTrace_943562 : CollatzResearch.WordTrace tailWord_943562 prefixEnd_943562 71777901232258154523799 := by
  unfold tailWord_943562
  simp only [CollatzResearch.WordTrace]
  refine ⟨8603633351910874101274235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22943022271762330936731293 8603633351910874101274235)
  ·
    refine ⟨12905450027866311151911353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8603633351910874101274235 12905450027866311151911353)
    ·
      refine ⟨9679087520899733363933515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12905450027866311151911353 9679087520899733363933515)
      ·
        refine ⟨14518631281349600045900273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9679087520899733363933515 14518631281349600045900273)
        ·
          refine ⟨10888973461012200034425205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14518631281349600045900273 10888973461012200034425205)
          ·
            refine ⟨1020841261969893753227363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10888973461012200034425205 1020841261969893753227363)
            ·
              refine ⟨1531261892954840629841045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1020841261969893753227363 1531261892954840629841045)
              ·
                refine ⟨71777901232258154523799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1531261892954840629841045 71777901232258154523799)
                ·
                  rfl

theorem cell21_943562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 6].length) (baseStart_943562 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_943562 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_943562 prefixEnd_943562 := by exact prefixLift 943562
  have htrace : WordTrace (prefixWord ++ tailWord_943562) baseStart_943562 baseEnd_943562 := by
    simpa [prefixWord, tailWord_943562, baseEnd_943562] using wordTrace_append hprefix tailTrace_943562
  have hstable : (prefixWord ++ tailWord_943562).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943562).length < 2 ^ (prefixWord ++ tailWord_943562).sum := by decide
  have hdescent : baseEnd_943562 < baseStart_943562 := by decide
  rcases family_descends (prefixWord ++ tailWord_943562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943669 : List Nat := [1, 3, 3, 1, 1, 5, 1, 1, 5]
def baseStart_943669 : Nat := 118140960795 + 943669 * 2 ^ 59
def prefixEnd_943669 : Nat := 4983230072969 + 3 ^ 40 * 943669 * 2
def baseEnd_943669 : Nat := 215358122554566055287845

theorem tailTrace_943669 : CollatzResearch.WordTrace tailWord_943669 prefixEnd_943669 215358122554566055287845 := by
  unfold tailWord_943669
  simp only [CollatzResearch.WordTrace]
  refine ⟨34418436018255853679242061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22945624012170569119494707 34418436018255853679242061)
  ·
    refine ⟨12906913506845945129715773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34418436018255853679242061 12906913506845945129715773)
    ·
      refine ⟨4840092565067229423643415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12906913506845945129715773 4840092565067229423643415)
      ·
        refine ⟨7260138847600844135465123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4840092565067229423643415 7260138847600844135465123)
        ·
          refine ⟨10890208271401266203197685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7260138847600844135465123 10890208271401266203197685)
          ·
            refine ⟨1020957025443868706549783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10890208271401266203197685 1020957025443868706549783)
            ·
              refine ⟨1531435538165803059824675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1020957025443868706549783 1531435538165803059824675)
              ·
                refine ⟨2297153307248704589737013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1531435538165803059824675 2297153307248704589737013)
                ·
                  refine ⟨215358122554566055287845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2297153307248704589737013 215358122554566055287845)
                  ·
                    rfl

theorem cell21_943669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 1, 5].length) (baseStart_943669 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_943669 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_943669 prefixEnd_943669 := by exact prefixLift 943669
  have htrace : WordTrace (prefixWord ++ tailWord_943669) baseStart_943669 baseEnd_943669 := by
    simpa [prefixWord, tailWord_943669, baseEnd_943669] using wordTrace_append hprefix tailTrace_943669
  have hstable : (prefixWord ++ tailWord_943669).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943669).length < 2 ^ (prefixWord ++ tailWord_943669).sum := by decide
  have hdescent : baseEnd_943669 < baseStart_943669 := by decide
  rcases family_descends (prefixWord ++ tailWord_943669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943776 : List Nat := [2, 1, 1, 4, 3, 3, 1, 2, 4]
def baseStart_943776 : Nat := 118140960795 + 943776 * 2 ^ 59
def prefixEnd_943776 : Nat := 4983230072969 + 3 ^ 40 * 943776 * 2
def baseEnd_943776 : Nat := 215382541412357647004293

theorem tailTrace_943776 : CollatzResearch.WordTrace tailWord_943776 prefixEnd_943776 215382541412357647004293 := by
  unfold tailWord_943776
  simp only [CollatzResearch.WordTrace]
  refine ⟨17211169314434105476693591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22948225752578807302258121 17211169314434105476693591)
  ·
    refine ⟨25816753971651158215040387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17211169314434105476693591 25816753971651158215040387)
    ·
      refine ⟨38725130957476737322560581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25816753971651158215040387 38725130957476737322560581)
      ·
        refine ⟨7260962054526888247980109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38725130957476737322560581 7260962054526888247980109)
        ·
          refine ⟨2722860770447583092992541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7260962054526888247980109 2722860770447583092992541)
          ·
            refine ⟨1021072788917843659872203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2722860770447583092992541 1021072788917843659872203)
            ·
              refine ⟨1531609183376765489808305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1021072788917843659872203 1531609183376765489808305)
              ·
                refine ⟨1148706887532574117356229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1531609183376765489808305 1148706887532574117356229)
                ·
                  refine ⟨215382541412357647004293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1148706887532574117356229 215382541412357647004293)
                  ·
                    rfl

theorem cell21_943776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 2, 4].length) (baseStart_943776 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_943776 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_943776 prefixEnd_943776 := by exact prefixLift 943776
  have htrace : WordTrace (prefixWord ++ tailWord_943776) baseStart_943776 baseEnd_943776 := by
    simpa [prefixWord, tailWord_943776, baseEnd_943776] using wordTrace_append hprefix tailTrace_943776
  have hstable : (prefixWord ++ tailWord_943776).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943776).length < 2 ^ (prefixWord ++ tailWord_943776).sum := by decide
  have hdescent : baseEnd_943776 < baseStart_943776 := by decide
  rcases family_descends (prefixWord ++ tailWord_943776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943804 : List Nat := [2, 2, 2, 3, 1, 2, 2, 2, 5]
def baseStart_943804 : Nat := 118140960795 + 943804 * 2 ^ 59
def prefixEnd_943804 : Nat := 4983230072969 + 3 ^ 40 * 943804 * 2
def baseEnd_943804 : Nat := 215388931393835820537569

theorem tailTrace_943804 : CollatzResearch.WordTrace tailWord_943804 prefixEnd_943804 215388931393835820537569 := by
  unfold tailWord_943804
  simp only [CollatzResearch.WordTrace]
  refine ⟨17211679936383385867703233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22948906581844514490270977 17211679936383385867703233)
  ·
    refine ⟨12908759952287539400777425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17211679936383385867703233 12908759952287539400777425)
    ·
      refine ⟨9681569964215654550583069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12908759952287539400777425 9681569964215654550583069)
      ·
        refine ⟨3630588736580870456468651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9681569964215654550583069 3630588736580870456468651)
        ·
          refine ⟨5445883104871305684702977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3630588736580870456468651 5445883104871305684702977)
          ·
            refine ⟨4084412328653479263527233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5445883104871305684702977 4084412328653479263527233)
            ·
              refine ⟨3063309246490109447645425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4084412328653479263527233 3063309246490109447645425)
              ·
                refine ⟨2297481934867582085734069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3063309246490109447645425 2297481934867582085734069)
                ·
                  refine ⟨215388931393835820537569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2297481934867582085734069 215388931393835820537569)
                  ·
                    rfl

theorem cell21_943804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 2, 5].length) (baseStart_943804 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_943804 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_943804 prefixEnd_943804 := by exact prefixLift 943804
  have htrace : WordTrace (prefixWord ++ tailWord_943804) baseStart_943804 baseEnd_943804 := by
    simpa [prefixWord, tailWord_943804, baseEnd_943804] using wordTrace_append hprefix tailTrace_943804
  have hstable : (prefixWord ++ tailWord_943804).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943804).length < 2 ^ (prefixWord ++ tailWord_943804).sum := by decide
  have hdescent : baseEnd_943804 < baseStart_943804 := by decide
  rcases family_descends (prefixWord ++ tailWord_943804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943863 : List Nat := [1, 1, 3, 1, 1, 1, 4, 4, 5]
def baseStart_943863 : Nat := 118140960795 + 943863 * 2 ^ 59
def prefixEnd_943863 : Nat := 4983230072969 + 3 ^ 40 * 943863 * 2
def baseEnd_943863 : Nat := 215402395997664829054115

theorem tailTrace_943863 : CollatzResearch.WordTrace tailWord_943863 prefixEnd_943863 215402395997664829054115 := by
  unfold tailWord_943863
  simp only [CollatzResearch.WordTrace]
  refine ⟨34425511779553024811804243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22950341186368683207869495 34425511779553024811804243)
  ·
    refine ⟨51638267669329537217706365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34425511779553024811804243 51638267669329537217706365)
    ·
      refine ⟨19364350375998576456639887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51638267669329537217706365 19364350375998576456639887)
      ·
        refine ⟨29046525563997864684959831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19364350375998576456639887 29046525563997864684959831)
        ·
          refine ⟨43569788345996797027439747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29046525563997864684959831 43569788345996797027439747)
          ·
            refine ⟨65354682518995195541159621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43569788345996797027439747 65354682518995195541159621)
            ·
              refine ⟨12254002972311599163967429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65354682518995195541159621 12254002972311599163967429)
              ·
                refine ⟨2297625557308424843243893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12254002972311599163967429 2297625557308424843243893)
                ·
                  refine ⟨215402395997664829054115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2297625557308424843243893 215402395997664829054115)
                  ·
                    rfl

theorem cell21_943863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 4, 5].length) (baseStart_943863 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_943863 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_943863 prefixEnd_943863 := by exact prefixLift 943863
  have htrace : WordTrace (prefixWord ++ tailWord_943863) baseStart_943863 baseEnd_943863 := by
    simpa [prefixWord, tailWord_943863, baseEnd_943863] using wordTrace_append hprefix tailTrace_943863
  have hstable : (prefixWord ++ tailWord_943863).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943863).length < 2 ^ (prefixWord ++ tailWord_943863).sum := by decide
  have hdescent : baseEnd_943863 < baseStart_943863 := by decide
  rcases family_descends (prefixWord ++ tailWord_943863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943956 : List Nat := [2, 4, 1, 1, 3, 1, 1, 3, 5]
def baseStart_943956 : Nat := 118140960795 + 943956 * 2 ^ 59
def prefixEnd_943956 : Nat := 4983230072969 + 3 ^ 40 * 943956 * 2
def baseEnd_943956 : Nat := 215423619864717334003925

theorem tailTrace_943956 : CollatzResearch.WordTrace tailWord_943956 prefixEnd_943956 215423619864717334003925 := by
  unfold tailWord_943956
  simp only [CollatzResearch.WordTrace]
  refine ⟨17214451884108050847469861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22952602512144067796626481 17214451884108050847469861)
  ·
    refine ⟨3227709728270259533900599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17214451884108050847469861 3227709728270259533900599)
    ·
      refine ⟨4841564592405389300850899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3227709728270259533900599 4841564592405389300850899)
      ·
        refine ⟨7262346888608083951276349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4841564592405389300850899 7262346888608083951276349)
        ·
          refine ⟨2723380083228031481728631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7262346888608083951276349 2723380083228031481728631)
          ·
            refine ⟨4085070124842047222592947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2723380083228031481728631 4085070124842047222592947)
            ·
              refine ⟨6127605187263070833889421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4085070124842047222592947 6127605187263070833889421)
              ·
                refine ⟨2297851945223651562708533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6127605187263070833889421 2297851945223651562708533)
                ·
                  refine ⟨215423619864717334003925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2297851945223651562708533 215423619864717334003925)
                  ·
                    rfl

theorem cell21_943956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_943956 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_943956 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_943956 prefixEnd_943956 := by exact prefixLift 943956
  have htrace : WordTrace (prefixWord ++ tailWord_943956) baseStart_943956 baseEnd_943956 := by
    simpa [prefixWord, tailWord_943956, baseEnd_943956] using wordTrace_append hprefix tailTrace_943956
  have hstable : (prefixWord ++ tailWord_943956).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943956).length < 2 ^ (prefixWord ++ tailWord_943956).sum := by decide
  have hdescent : baseEnd_943956 < baseStart_943956 := by decide
  rcases family_descends (prefixWord ++ tailWord_943956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944018 : List Nat := [3, 2, 3, 2, 1, 2, 2, 6]
def baseStart_944018 : Nat := 118140960795 + 944018 * 2 ^ 59
def prefixEnd_944018 : Nat := 4983230072969 + 3 ^ 40 * 944018 * 2
def baseEnd_944018 : Nat := 71812589703139667990155

theorem tailTrace_944018 : CollatzResearch.WordTrace tailWord_944018 prefixEnd_944018 71812589703139667990155 := by
  unfold tailWord_944018
  simp only [CollatzResearch.WordTrace]
  refine ⟨8607791273497871570924177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22954110062660990855797805 8607791273497871570924177)
  ·
    refine ⟨6455843455123403678193133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8607791273497871570924177 6455843455123403678193133)
    ·
      refine ⟨2420941295671276379322425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6455843455123403678193133 2420941295671276379322425)
      ·
        refine ⟨1815705971753457284491819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2420941295671276379322425 1815705971753457284491819)
        ·
          refine ⟨2723558957630185926737729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1815705971753457284491819 2723558957630185926737729)
          ·
            refine ⟨2042669218222639445053297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2723558957630185926737729 2042669218222639445053297)
            ·
              refine ⟨1532001913666979583789973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2042669218222639445053297 1532001913666979583789973)
              ·
                refine ⟨71812589703139667990155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1532001913666979583789973 71812589703139667990155)
                ·
                  rfl

theorem cell21_944018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 6].length) (baseStart_944018 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_944018 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_944018 prefixEnd_944018 := by exact prefixLift 944018
  have htrace : WordTrace (prefixWord ++ tailWord_944018) baseStart_944018 baseEnd_944018 := by
    simpa [prefixWord, tailWord_944018, baseEnd_944018] using wordTrace_append hprefix tailTrace_944018
  have hstable : (prefixWord ++ tailWord_944018).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944018).length < 2 ^ (prefixWord ++ tailWord_944018).sum := by decide
  have hdescent : baseEnd_944018 < baseStart_944018 := by decide
  rcases family_descends (prefixWord ++ tailWord_944018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944136 : List Nat := [2, 1, 3, 2, 1, 2, 2, 8]
def baseStart_944136 : Nat := 118140960795 + 944136 * 2 ^ 59
def prefixEnd_944136 : Nat := 4983230072969 + 3 ^ 40 * 944136 * 2
def baseEnd_944136 : Nat := 71821566105692340334519

theorem tailTrace_944136 : CollatzResearch.WordTrace tailWord_944136 prefixEnd_944136 71821566105692340334519 := by
  unfold tailWord_944136
  simp only [CollatzResearch.WordTrace]
  refine ⟨17217734453781996218246131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22956979271709328290994841 17217734453781996218246131)
  ·
    refine ⟨25826601680672994327369197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17217734453781996218246131 25826601680672994327369197)
    ·
      refine ⟨9684975630252372872763449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25826601680672994327369197 9684975630252372872763449)
      ·
        refine ⟨7263731722689279654572587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9684975630252372872763449 7263731722689279654572587)
        ·
          refine ⟨10895597584033919481858881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7263731722689279654572587 10895597584033919481858881)
          ·
            refine ⟨8171698188025439611394161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10895597584033919481858881 8171698188025439611394161)
            ·
              refine ⟨6128773641019079708545621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8171698188025439611394161 6128773641019079708545621)
              ·
                refine ⟨71821566105692340334519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6128773641019079708545621 71821566105692340334519)
                ·
                  rfl

theorem cell21_944136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 8].length) (baseStart_944136 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_944136 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_944136 prefixEnd_944136 := by exact prefixLift 944136
  have htrace : WordTrace (prefixWord ++ tailWord_944136) baseStart_944136 baseEnd_944136 := by
    simpa [prefixWord, tailWord_944136, baseEnd_944136] using wordTrace_append hprefix tailTrace_944136
  have hstable : (prefixWord ++ tailWord_944136).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944136).length < 2 ^ (prefixWord ++ tailWord_944136).sum := by decide
  have hdescent : baseEnd_944136 < baseStart_944136 := by decide
  rcases family_descends (prefixWord ++ tailWord_944136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944139 : List Nat := [1, 1, 1, 1, 6, 1, 5, 1, 4]
def baseStart_944139 : Nat := 118140960795 + 944139 * 2 ^ 59
def prefixEnd_944139 : Nat := 4983230072969 + 3 ^ 40 * 944139 * 2
def baseEnd_944139 : Nat := 215465382957949682453551

theorem tailTrace_944139 : CollatzResearch.WordTrace tailWord_944139 prefixEnd_944139 215465382957949682453551 := by
  unfold tailWord_944139
  simp only [CollatzResearch.WordTrace]
  refine ⟨34435578326553123948851471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22957052217702082632567647 34435578326553123948851471)
  ·
    refine ⟨51653367489829685923277207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34435578326553123948851471 51653367489829685923277207)
    ·
      refine ⟨77480051234744528884915811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51653367489829685923277207 77480051234744528884915811)
      ·
        refine ⟨116220076852116793327373717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77480051234744528884915811 116220076852116793327373717)
        ·
          refine ⟨5447816102442974687220643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 116220076852116793327373717 5447816102442974687220643)
          ·
            refine ⟨8171724153664462030830965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5447816102442974687220643 8171724153664462030830965)
            ·
              refine ⟨766099139406043315390403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8171724153664462030830965 766099139406043315390403)
              ·
                refine ⟨1149148709109064973085605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 766099139406043315390403 1149148709109064973085605)
                ·
                  refine ⟨215465382957949682453551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1149148709109064973085605 215465382957949682453551)
                  ·
                    rfl

theorem cell21_944139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 5, 1, 4].length) (baseStart_944139 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_944139 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_944139 prefixEnd_944139 := by exact prefixLift 944139
  have htrace : WordTrace (prefixWord ++ tailWord_944139) baseStart_944139 baseEnd_944139 := by
    simpa [prefixWord, tailWord_944139, baseEnd_944139] using wordTrace_append hprefix tailTrace_944139
  have hstable : (prefixWord ++ tailWord_944139).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944139).length < 2 ^ (prefixWord ++ tailWord_944139).sum := by decide
  have hdescent : baseEnd_944139 < baseStart_944139 := by decide
  rcases family_descends (prefixWord ++ tailWord_944139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944190 : List Nat := [4, 2, 1, 3, 3, 1, 2, 1, 4]
def baseStart_944190 : Nat := 118140960795 + 944190 * 2 ^ 59
def prefixEnd_944190 : Nat := 4983230072969 + 3 ^ 40 * 944190 * 2
def baseEnd_944190 : Nat := 215477021852784927103447

theorem tailTrace_944190 : CollatzResearch.WordTrace tailWord_944190 prefixEnd_944190 215477021852784927103447 := by
  unfold tailWord_944190
  simp only [CollatzResearch.WordTrace]
  refine ⟨4304679806171044957369753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22958292299578906439305349 4304679806171044957369753)
  ·
    refine ⟨3228509854628283718027315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4304679806171044957369753 3228509854628283718027315)
    ·
      refine ⟨4842764781942425577040973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3228509854628283718027315 4842764781942425577040973)
      ·
        refine ⟨1816036793228409591390365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4842764781942425577040973 1816036793228409591390365)
        ·
          refine ⟨681013797460653596771387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1816036793228409591390365 681013797460653596771387)
          ·
            refine ⟨1021520696190980395157081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 681013797460653596771387 1021520696190980395157081)
            ·
              refine ⟨766140522143235296367811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1021520696190980395157081 766140522143235296367811)
              ·
                refine ⟨1149210783214852944551717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 766140522143235296367811 1149210783214852944551717)
                ·
                  refine ⟨215477021852784927103447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1149210783214852944551717 215477021852784927103447)
                  ·
                    rfl

theorem cell21_944190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 2, 1, 4].length) (baseStart_944190 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_944190 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_944190 prefixEnd_944190 := by exact prefixLift 944190
  have htrace : WordTrace (prefixWord ++ tailWord_944190) baseStart_944190 baseEnd_944190 := by
    simpa [prefixWord, tailWord_944190, baseEnd_944190] using wordTrace_append hprefix tailTrace_944190
  have hstable : (prefixWord ++ tailWord_944190).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944190).length < 2 ^ (prefixWord ++ tailWord_944190).sum := by decide
  have hdescent : baseEnd_944190 < baseStart_944190 := by decide
  rcases family_descends (prefixWord ++ tailWord_944190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944246 : List Nat := [5, 1, 1, 2, 1, 4, 1, 6]
def baseStart_944246 : Nat := 118140960795 + 944246 * 2 ^ 59
def prefixEnd_944246 : Nat := 4983230072969 + 3 ^ 40 * 944246 * 2
def baseEnd_944246 : Nat := 71829933938580424723333

theorem tailTrace_944246 : CollatzResearch.WordTrace tailWord_944246 prefixEnd_944246 71829933938580424723333 := by
  unfold tailWord_944246
  simp only [CollatzResearch.WordTrace]
  refine ⟨2152467558572842576437287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22959653958110320815331061 2152467558572842576437287)
  ·
    refine ⟨3228701337859263864655931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2152467558572842576437287 3228701337859263864655931)
    ·
      refine ⟨4843052006788895796983897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3228701337859263864655931 4843052006788895796983897)
      ·
        refine ⟨3632289005091671847737923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4843052006788895796983897 3632289005091671847737923)
        ·
          refine ⟨5448433507637507771606885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3632289005091671847737923 5448433507637507771606885)
          ·
            refine ⟨1021581282682032707176291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5448433507637507771606885 1021581282682032707176291)
            ·
              refine ⟨1532371924023049060764437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1021581282682032707176291 1532371924023049060764437)
              ·
                refine ⟨71829933938580424723333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1532371924023049060764437 71829933938580424723333)
                ·
                  rfl

theorem cell21_944246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 6].length) (baseStart_944246 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_944246 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_944246 prefixEnd_944246 := by exact prefixLift 944246
  have htrace : WordTrace (prefixWord ++ tailWord_944246) baseStart_944246 baseEnd_944246 := by
    simpa [prefixWord, tailWord_944246, baseEnd_944246] using wordTrace_append hprefix tailTrace_944246
  have hstable : (prefixWord ++ tailWord_944246).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944246).length < 2 ^ (prefixWord ++ tailWord_944246).sum := by decide
  have hdescent : baseEnd_944246 < baseStart_944246 := by decide
  rcases family_descends (prefixWord ++ tailWord_944246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
