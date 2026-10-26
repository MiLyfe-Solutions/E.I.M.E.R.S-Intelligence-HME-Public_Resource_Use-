import V185TrunkScan22Chunk403

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3604698 : List Nat := [3, 1, 1, 2, 2, 1, 2, 2, 5, 3]
def baseStart_3604698 : Nat := 118140960795 + 3604698 * 2 ^ 59
def prefixEnd_3604698 : Nat := 4983230072969 + 3 ^ 40 * 3604698 * 2
def baseEnd_3604698 : Nat := 1233961792200561890798201

theorem tailTrace_3604698 : CollatzResearch.WordTrace tailWord_3604698 prefixEnd_3604698 1233961792200561890798201 := by
  unfold tailWord_3604698
  simp only [CollatzResearch.WordTrace]
  refine ⟨32868534273700563562607687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87649424729868169500287165 32868534273700563562607687)
  ·
    refine ⟨49302801410550845343911531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32868534273700563562607687 49302801410550845343911531)
    ·
      refine ⟨73954202115826268015867297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49302801410550845343911531 73954202115826268015867297)
      ·
        refine ⟨55465651586869701011900473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73954202115826268015867297 55465651586869701011900473)
        ·
          refine ⟨41599238690152275758925355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55465651586869701011900473 41599238690152275758925355)
          ·
            refine ⟨62398858035228413638388033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41599238690152275758925355 62398858035228413638388033)
            ·
              refine ⟨46799143526421310228791025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62398858035228413638388033 46799143526421310228791025)
              ·
                refine ⟨35099357644815982671593269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46799143526421310228791025 35099357644815982671593269)
                ·
                  refine ⟨3290564779201498375461869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35099357644815982671593269 3290564779201498375461869)
                  ·
                    refine ⟨1233961792200561890798201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3290564779201498375461869 1233961792200561890798201)
                    ·
                      rfl

theorem cell22_3604698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 5, 3].length) (baseStart_3604698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3604698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3604698 prefixEnd_3604698 := by exact prefixLift 3604698
  have htrace : WordTrace (prefixWord ++ tailWord_3604698) baseStart_3604698 baseEnd_3604698 := by
    simpa [prefixWord, tailWord_3604698, baseEnd_3604698] using wordTrace_append hprefix tailTrace_3604698
  have hstable : (prefixWord ++ tailWord_3604698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3604698).length < 2 ^ (prefixWord ++ tailWord_3604698).sum := by decide
  have hdescent : baseEnd_3604698 < baseStart_3604698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3604698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3604706 : List Nat := [3, 3, 4, 1, 2, 1, 1, 1, 6]
def baseStart_3604706 : Nat := 118140960795 + 3604706 * 2 ^ 59
def prefixEnd_3604706 : Nat := 4983230072969 + 3 ^ 40 * 3604706 * 2
def baseEnd_3604706 : Nat := 411321510254684178866059

theorem tailTrace_3604706 : CollatzResearch.WordTrace tailWord_3604706 prefixEnd_3604706 411321510254684178866059 := by
  unfold tailWord_3604706
  simp only [CollatzResearch.WordTrace]
  refine ⟨32868607219693317904180493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87649619252515514411147981 32868607219693317904180493)
  ·
    refine ⟨12325727707384994214067685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32868607219693317904180493 12325727707384994214067685)
    ·
      refine ⟨2311073945134686415137691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12325727707384994214067685 2311073945134686415137691)
      ·
        refine ⟨3466610917702029622706537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2311073945134686415137691 3466610917702029622706537)
        ·
          refine ⟨2599958188276522217029903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3466610917702029622706537 2599958188276522217029903)
          ·
            refine ⟨3899937282414783325544855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2599958188276522217029903 3899937282414783325544855)
            ·
              refine ⟨5849905923622174988317283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3899937282414783325544855 5849905923622174988317283)
              ·
                refine ⟨8774858885433262482475925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5849905923622174988317283 8774858885433262482475925)
                ·
                  refine ⟨411321510254684178866059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8774858885433262482475925 411321510254684178866059)
                  ·
                    rfl

theorem cell22_3604706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 1, 6].length) (baseStart_3604706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3604706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3604706 prefixEnd_3604706 := by exact prefixLift 3604706
  have htrace : WordTrace (prefixWord ++ tailWord_3604706) baseStart_3604706 baseEnd_3604706 := by
    simpa [prefixWord, tailWord_3604706, baseEnd_3604706] using wordTrace_append hprefix tailTrace_3604706
  have hstable : (prefixWord ++ tailWord_3604706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3604706).length < 2 ^ (prefixWord ++ tailWord_3604706).sum := by decide
  have hdescent : baseEnd_3604706 < baseStart_3604706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3604706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3604766 : List Nat := [4, 3, 2, 1, 1, 2, 1, 4, 1, 3]
def baseStart_3604766 : Nat := 118140960795 + 3604766 * 2 ^ 59
def prefixEnd_3604766 : Nat := 4983230072969 + 3 ^ 40 * 3604766 * 2
def baseEnd_3604766 : Nat := 1233985069990232380097993

theorem tailTrace_3604766 : CollatzResearch.WordTrace tailWord_3604766 prefixEnd_3604766 1233985069990232380097993 := by
  unfold tailWord_3604766
  simp only [CollatzResearch.WordTrace]
  refine ⟨16434577157319487732988269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87651078172370601242604101 16434577157319487732988269)
  ·
    refine ⟨6162966433994807899870601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16434577157319487732988269 6162966433994807899870601)
    ·
      refine ⟨4622224825496105924902951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6162966433994807899870601 4622224825496105924902951)
      ·
        refine ⟨6933337238244158887354427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4622224825496105924902951 6933337238244158887354427)
        ·
          refine ⟨10400005857366238331031641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6933337238244158887354427 10400005857366238331031641)
          ·
            refine ⟨7800004393024678748273731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10400005857366238331031641 7800004393024678748273731)
            ·
              refine ⟨11700006589537018122410597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7800004393024678748273731 11700006589537018122410597)
              ·
                refine ⟨2193751235538190897951987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11700006589537018122410597 2193751235538190897951987)
                ·
                  refine ⟨3290626853307286346927981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2193751235538190897951987 3290626853307286346927981)
                  ·
                    refine ⟨1233985069990232380097993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3290626853307286346927981 1233985069990232380097993)
                    ·
                      rfl

theorem cell22_3604766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_3604766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3604766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3604766 prefixEnd_3604766 := by exact prefixLift 3604766
  have htrace : WordTrace (prefixWord ++ tailWord_3604766) baseStart_3604766 baseEnd_3604766 := by
    simpa [prefixWord, tailWord_3604766, baseEnd_3604766] using wordTrace_append hprefix tailTrace_3604766
  have hstable : (prefixWord ++ tailWord_3604766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3604766).length < 2 ^ (prefixWord ++ tailWord_3604766).sum := by decide
  have hdescent : baseEnd_3604766 < baseStart_3604766 := by decide
  rcases family_descends (prefixWord ++ tailWord_3604766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3604839 : List Nat := [1, 1, 5, 1, 3, 2, 3, 1, 2, 3]
def baseStart_3604839 : Nat := 118140960795 + 3604839 * 2 ^ 59
def prefixEnd_3604839 : Nat := 4983230072969 + 3 ^ 40 * 3604839 * 2
def baseEnd_3604839 : Nat := 1234010059382084523022769

theorem tailTrace_3604839 : CollatzResearch.WordTrace tailWord_3604839 prefixEnd_3604839 1234010059382084523022769 := by
  unfold tailWord_3604839
  simp only [CollatzResearch.WordTrace]
  refine ⟨131479279787291435331313571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87652853191527623554209047 131479279787291435331313571)
  ·
    refine ⟨197218919680937152996970357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131479279787291435331313571 197218919680937152996970357)
    ·
      refine ⟨18489273720087858093465971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 197218919680937152996970357 18489273720087858093465971)
      ·
        refine ⟨27733910580131787140198957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18489273720087858093465971 27733910580131787140198957)
        ·
          refine ⟨10400216467549420177574609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27733910580131787140198957 10400216467549420177574609)
          ·
            refine ⟨7800162350662065133180957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10400216467549420177574609 7800162350662065133180957)
            ·
              refine ⟨2925060881498274424942859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7800162350662065133180957 2925060881498274424942859)
              ·
                refine ⟨4387591322247411637414289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2925060881498274424942859 4387591322247411637414289)
                ·
                  refine ⟨3290693491685558728060717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4387591322247411637414289 3290693491685558728060717)
                  ·
                    refine ⟨1234010059382084523022769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3290693491685558728060717 1234010059382084523022769)
                    ·
                      rfl

theorem cell22_3604839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 3, 1, 2, 3].length) (baseStart_3604839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3604839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3604839 prefixEnd_3604839 := by exact prefixLift 3604839
  have htrace : WordTrace (prefixWord ++ tailWord_3604839) baseStart_3604839 baseEnd_3604839 := by
    simpa [prefixWord, tailWord_3604839, baseEnd_3604839] using wordTrace_append hprefix tailTrace_3604839
  have hstable : (prefixWord ++ tailWord_3604839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3604839).length < 2 ^ (prefixWord ++ tailWord_3604839).sum := by decide
  have hdescent : baseEnd_3604839 < baseStart_3604839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3604839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3604886 : List Nat := [5, 3, 1, 2, 1, 1, 2, 7]
def baseStart_3604886 : Nat := 118140960795 + 3604886 * 2 ^ 59
def prefixEnd_3604886 : Nat := 4983230072969 + 3 ^ 40 * 3604886 * 2
def baseEnd_3604886 : Nat := 137114016493621340788625

theorem tailTrace_3604886 : CollatzResearch.WordTrace tailWord_3604886 prefixEnd_3604886 137114016493621340788625 := by
  unfold tailWord_3604886
  simp only [CollatzResearch.WordTrace]
  refine ⟨8217562126132572647392157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87653996012080774905516341 8217562126132572647392157)
  ·
    refine ⟨3081585797299714742772059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8217562126132572647392157 3081585797299714742772059)
    ·
      refine ⟨4622378695949572114158089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3081585797299714742772059 4622378695949572114158089)
      ·
        refine ⟨3466784021962179085618567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4622378695949572114158089 3466784021962179085618567)
        ·
          refine ⟨5200176032943268628427851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3466784021962179085618567 5200176032943268628427851)
          ·
            refine ⟨7800264049414902942641777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5200176032943268628427851 7800264049414902942641777)
            ·
              refine ⟨5850198037061177206981333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7800264049414902942641777 5850198037061177206981333)
              ·
                refine ⟨137114016493621340788625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5850198037061177206981333 137114016493621340788625)
                ·
                  rfl

theorem cell22_3604886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 7].length) (baseStart_3604886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3604886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3604886 prefixEnd_3604886 := by exact prefixLift 3604886
  have htrace : WordTrace (prefixWord ++ tailWord_3604886) baseStart_3604886 baseEnd_3604886 := by
    simpa [prefixWord, tailWord_3604886, baseEnd_3604886] using wordTrace_append hprefix tailTrace_3604886
  have hstable : (prefixWord ++ tailWord_3604886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3604886).length < 2 ^ (prefixWord ++ tailWord_3604886).sum := by decide
  have hdescent : baseEnd_3604886 < baseStart_3604886 := by decide
  rcases family_descends (prefixWord ++ tailWord_3604886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3604908 : List Nat := [2, 2, 1, 1, 1, 1, 3, 3, 8]
def baseStart_3604908 : Nat := 118140960795 + 3604908 * 2 ^ 59
def prefixEnd_3604908 : Nat := 4983230072969 + 3 ^ 40 * 3604908 * 2
def baseEnd_3604908 : Nat := 411344559830730447682519

theorem tailTrace_3604908 : CollatzResearch.WordTrace tailWord_3604908 prefixEnd_3604908 411344559830730447682519 := by
  unfold tailWord_3604908
  simp only [CollatzResearch.WordTrace]
  refine ⟨65740898212020730057787689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87654530949360973410383585 65740898212020730057787689)
  ·
    refine ⟨49305673659015547543340767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65740898212020730057787689 49305673659015547543340767)
    ·
      refine ⟨73958510488523321315011151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49305673659015547543340767 73958510488523321315011151)
      ·
        refine ⟨110937765732784981972516727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73958510488523321315011151 110937765732784981972516727)
        ·
          refine ⟨166406648599177472958775091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110937765732784981972516727 166406648599177472958775091)
          ·
            refine ⟨249609972898766209438162637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166406648599177472958775091 249609972898766209438162637)
            ·
              refine ⟨93603739837037328539310989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 249609972898766209438162637 93603739837037328539310989)
              ·
                refine ⟨35101402438888998202241621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93603739837037328539310989 35101402438888998202241621)
                ·
                  refine ⟨411344559830730447682519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35101402438888998202241621 411344559830730447682519)
                  ·
                    rfl

theorem cell22_3604908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 8].length) (baseStart_3604908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3604908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3604908 prefixEnd_3604908 := by exact prefixLift 3604908
  have htrace : WordTrace (prefixWord ++ tailWord_3604908) baseStart_3604908 baseEnd_3604908 := by
    simpa [prefixWord, tailWord_3604908, baseEnd_3604908] using wordTrace_append hprefix tailTrace_3604908
  have hstable : (prefixWord ++ tailWord_3604908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3604908).length < 2 ^ (prefixWord ++ tailWord_3604908).sum := by decide
  have hdescent : baseEnd_3604908 < baseStart_3604908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3604908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3604957 : List Nat := [1, 4, 3, 1, 1, 1, 4, 1, 1, 5]
def baseStart_3604957 : Nat := 118140960795 + 3604957 * 2 ^ 59
def prefixEnd_3604957 : Nat := 4983230072969 + 3 ^ 40 * 3604957 * 2
def baseEnd_3604957 : Nat := 1234050453193571548572407

theorem tailTrace_3604957 : CollatzResearch.WordTrace tailWord_3604957 prefixEnd_3604957 1234050453193571548572407 := by
  unfold tailWord_3604957
  simp only [CollatzResearch.WordTrace]
  refine ⟨131483583600863941484109125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87655722400575960989406083 131483583600863941484109125)
  ·
    refine ⟨24653171925161989028270461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131483583600863941484109125 24653171925161989028270461)
    ·
      refine ⟨9244939471935745885601423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24653171925161989028270461 9244939471935745885601423)
      ·
        refine ⟨13867409207903618828402135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9244939471935745885601423 13867409207903618828402135)
        ·
          refine ⟨20801113811855428242603203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13867409207903618828402135 20801113811855428242603203)
          ·
            refine ⟨31201670717783142363904805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20801113811855428242603203 31201670717783142363904805)
            ·
              refine ⟨5850313259584339193232151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31201670717783142363904805 5850313259584339193232151)
              ·
                refine ⟨8775469889376508789848227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5850313259584339193232151 8775469889376508789848227)
                ·
                  refine ⟨13163204834064763184772341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8775469889376508789848227 13163204834064763184772341)
                  ·
                    refine ⟨1234050453193571548572407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13163204834064763184772341 1234050453193571548572407)
                    ·
                      rfl

theorem cell22_3604957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_3604957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3604957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3604957 prefixEnd_3604957 := by exact prefixLift 3604957
  have htrace : WordTrace (prefixWord ++ tailWord_3604957) baseStart_3604957 baseEnd_3604957 := by
    simpa [prefixWord, tailWord_3604957, baseEnd_3604957] using wordTrace_append hprefix tailTrace_3604957
  have hstable : (prefixWord ++ tailWord_3604957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3604957).length < 2 ^ (prefixWord ++ tailWord_3604957).sum := by decide
  have hdescent : baseEnd_3604957 < baseStart_3604957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3604957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3604978 : List Nat := [3, 2, 1, 4, 3, 1, 2, 1, 1, 4]
def baseStart_3604978 : Nat := 118140960795 + 3604978 * 2 ^ 59
def prefixEnd_3604978 : Nat := 4983230072969 + 3 ^ 40 * 3604978 * 2
def baseEnd_3604978 : Nat := 1234057641922734493797343

theorem tailTrace_3604978 : CollatzResearch.WordTrace tailWord_3604978 prefixEnd_3604978 1234057641922734493797343 := by
  unfold tailWord_3604978
  simp only [CollatzResearch.WordTrace]
  refine ⟨32871087383446965517655897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87656233022525241380415725 32871087383446965517655897)
  ·
    refine ⟨24653315537585224138241923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32871087383446965517655897 24653315537585224138241923)
    ·
      refine ⟨36979973306377836207362885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24653315537585224138241923 36979973306377836207362885)
      ·
        refine ⟨6933744994945844288880541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36979973306377836207362885 6933744994945844288880541)
        ·
          refine ⟨2600154373104691608330203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6933744994945844288880541 2600154373104691608330203)
          ·
            refine ⟨3900231559657037412495305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2600154373104691608330203 3900231559657037412495305)
            ·
              refine ⟨2925173669742778059371479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3900231559657037412495305 2925173669742778059371479)
              ·
                refine ⟨4387760504614167089057219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2925173669742778059371479 4387760504614167089057219)
                ·
                  refine ⟨6581640756921250633585829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4387760504614167089057219 6581640756921250633585829)
                  ·
                    refine ⟨1234057641922734493797343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6581640756921250633585829 1234057641922734493797343)
                    ·
                      rfl

theorem cell22_3604978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 2, 1, 1, 4].length) (baseStart_3604978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3604978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3604978 prefixEnd_3604978 := by exact prefixLift 3604978
  have htrace : WordTrace (prefixWord ++ tailWord_3604978) baseStart_3604978 baseEnd_3604978 := by
    simpa [prefixWord, tailWord_3604978, baseEnd_3604978] using wordTrace_append hprefix tailTrace_3604978
  have hstable : (prefixWord ++ tailWord_3604978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3604978).length < 2 ^ (prefixWord ++ tailWord_3604978).sum := by decide
  have hdescent : baseEnd_3604978 < baseStart_3604978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3604978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605032 : List Nat := [2, 1, 5, 2, 1, 1, 1, 2, 7]
def baseStart_3605032 : Nat := 118140960795 + 3605032 * 2 ^ 59
def prefixEnd_3605032 : Nat := 4983230072969 + 3 ^ 40 * 3605032 * 2
def baseEnd_3605032 : Nat := 411358709075432117649059

theorem tailTrace_3605032 : CollatzResearch.WordTrace tailWord_3605032 prefixEnd_3605032 411358709075432117649059 := by
  unfold tailWord_3605032
  simp only [CollatzResearch.WordTrace]
  refine ⟨65743159537796114646544675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87657546050394819528726233 65743159537796114646544675)
  ·
    refine ⟨98614739306694171969817013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65743159537796114646544675 98614739306694171969817013)
    ·
      refine ⟨9245131810002578622170345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 98614739306694171969817013 9245131810002578622170345)
      ·
        refine ⟨6933848857501933966627759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9245131810002578622170345 6933848857501933966627759)
        ·
          refine ⟨10400773286252900949941639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6933848857501933966627759 10400773286252900949941639)
          ·
            refine ⟨15601159929379351424912459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10400773286252900949941639 15601159929379351424912459)
            ·
              refine ⟨23401739894069027137368689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15601159929379351424912459 23401739894069027137368689)
              ·
                refine ⟨17551304920551770353026517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23401739894069027137368689 17551304920551770353026517)
                ·
                  refine ⟨411358709075432117649059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17551304920551770353026517 411358709075432117649059)
                  ·
                    rfl

theorem cell22_3605032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 7].length) (baseStart_3605032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3605032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3605032 prefixEnd_3605032 := by exact prefixLift 3605032
  have htrace : WordTrace (prefixWord ++ tailWord_3605032) baseStart_3605032 baseEnd_3605032 := by
    simpa [prefixWord, tailWord_3605032, baseEnd_3605032] using wordTrace_append hprefix tailTrace_3605032
  have hstable : (prefixWord ++ tailWord_3605032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605032).length < 2 ^ (prefixWord ++ tailWord_3605032).sum := by decide
  have hdescent : baseEnd_3605032 < baseStart_3605032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605053 : List Nat := [1, 4, 1, 3, 2, 2, 3, 2, 1, 3]
def baseStart_3605053 : Nat := 118140960795 + 3605053 * 2 ^ 59
def prefixEnd_3605053 : Nat := 4983230072969 + 3 ^ 40 * 3605053 * 2
def baseEnd_3605053 : Nat := 1234083315955459298172113

theorem tailTrace_3605053 : CollatzResearch.WordTrace tailWord_3605053 prefixEnd_3605053 1234083315955459298172113 := by
  unfold tailWord_3605053
  simp only [CollatzResearch.WordTrace]
  refine ⟨131487085008516149879603813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87658056672344099919735875 131487085008516149879603813)
  ·
    refine ⟨24653828439096778102425715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131487085008516149879603813 24653828439096778102425715)
    ·
      refine ⟨36980742658645167153638573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24653828439096778102425715 36980742658645167153638573)
      ·
        refine ⟨13867778496991937682614465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36980742658645167153638573 13867778496991937682614465)
        ·
          refine ⟨10400833872743953261960849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13867778496991937682614465 10400833872743953261960849)
          ·
            refine ⟨7800625404557964946470637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10400833872743953261960849 7800625404557964946470637)
            ·
              refine ⟨2925234526709236854926489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7800625404557964946470637 2925234526709236854926489)
              ·
                refine ⟨2193925895031927641194867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2925234526709236854926489 2193925895031927641194867)
                ·
                  refine ⟨3290888842547891461792301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2193925895031927641194867 3290888842547891461792301)
                  ·
                    refine ⟨1234083315955459298172113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3290888842547891461792301 1234083315955459298172113)
                    ·
                      rfl

theorem cell22_3605053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 3, 2, 1, 3].length) (baseStart_3605053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3605053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3605053 prefixEnd_3605053 := by exact prefixLift 3605053
  have htrace : WordTrace (prefixWord ++ tailWord_3605053) baseStart_3605053 baseEnd_3605053 := by
    simpa [prefixWord, tailWord_3605053, baseEnd_3605053] using wordTrace_append hprefix tailTrace_3605053
  have hstable : (prefixWord ++ tailWord_3605053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605053).length < 2 ^ (prefixWord ++ tailWord_3605053).sum := by decide
  have hdescent : baseEnd_3605053 < baseStart_3605053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605092 : List Nat := [2, 3, 1, 1, 2, 2, 3, 2, 1, 5]
def baseStart_3605092 : Nat := 118140960795 + 3605092 * 2 ^ 59
def prefixEnd_3605092 : Nat := 4983230072969 + 3 ^ 40 * 3605092 * 2
def baseEnd_3605092 : Nat := 1234096666452476196446993

theorem tailTrace_3605092 : CollatzResearch.WordTrace tailWord_3605092 prefixEnd_3605092 1234096666452476196446993 := by
  unfold tailWord_3605092
  simp only [CollatzResearch.WordTrace]
  refine ⟨65744253727687429770136765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87659004970249906360182353 65744253727687429770136765)
  ·
    refine ⟨24654095147882786163801287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65744253727687429770136765 24654095147882786163801287)
    ·
      refine ⟨36981142721824179245701931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24654095147882786163801287 36981142721824179245701931)
      ·
        refine ⟨55471714082736268868552897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36981142721824179245701931 55471714082736268868552897)
        ·
          refine ⟨41603785562052201651414673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55471714082736268868552897 41603785562052201651414673)
          ·
            refine ⟨31202839171539151238561005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41603785562052201651414673 31202839171539151238561005)
            ·
              refine ⟨11701064689327181714460377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31202839171539151238561005 11701064689327181714460377)
              ·
                refine ⟨8775798516995386285845283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11701064689327181714460377 8775798516995386285845283)
                ·
                  refine ⟨13163697775493079428767925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8775798516995386285845283 13163697775493079428767925)
                  ·
                    refine ⟨1234096666452476196446993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13163697775493079428767925 1234096666452476196446993)
                    ·
                      rfl

theorem cell22_3605092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 2, 1, 5].length) (baseStart_3605092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3605092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3605092 prefixEnd_3605092 := by exact prefixLift 3605092
  have htrace : WordTrace (prefixWord ++ tailWord_3605092) baseStart_3605092 baseEnd_3605092 := by
    simpa [prefixWord, tailWord_3605092, baseEnd_3605092] using wordTrace_append hprefix tailTrace_3605092
  have hstable : (prefixWord ++ tailWord_3605092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605092).length < 2 ^ (prefixWord ++ tailWord_3605092).sum := by decide
  have hdescent : baseEnd_3605092 < baseStart_3605092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605167 : List Nat := [1, 1, 2, 1, 2, 6, 1, 1, 7]
def baseStart_3605167 : Nat := 118140960795 + 3605167 * 2 ^ 59
def prefixEnd_3605167 : Nat := 4983230072969 + 3 ^ 40 * 3605167 * 2
def baseEnd_3605167 : Nat := 411374113495067000273921

theorem tailTrace_3605167 : CollatzResearch.WordTrace tailWord_3605167 prefixEnd_3605167 411374113495067000273921 := by
  unfold tailWord_3605167
  simp only [CollatzResearch.WordTrace]
  refine ⟨131491242930103147349253755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87660828620068764899502503 131491242930103147349253755)
  ·
    refine ⟨197236864395154721023880633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131491242930103147349253755 197236864395154721023880633)
    ·
      refine ⟨147927648296366040767910475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197236864395154721023880633 147927648296366040767910475)
      ·
        refine ⟨221891472444549061151865713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147927648296366040767910475 221891472444549061151865713)
        ·
          refine ⟨166418604333411795863899285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221891472444549061151865713 166418604333411795863899285)
          ·
            refine ⟨7800872078128677931120279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 166418604333411795863899285 7800872078128677931120279)
            ·
              refine ⟨11701308117193016896680419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7800872078128677931120279 11701308117193016896680419)
              ·
                refine ⟨17551962175789525345020629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11701308117193016896680419 17551962175789525345020629)
                ·
                  refine ⟨411374113495067000273921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17551962175789525345020629 411374113495067000273921)
                  ·
                    rfl

theorem cell22_3605167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 7].length) (baseStart_3605167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3605167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3605167 prefixEnd_3605167 := by exact prefixLift 3605167
  have htrace : WordTrace (prefixWord ++ tailWord_3605167) baseStart_3605167 baseEnd_3605167 := by
    simpa [prefixWord, tailWord_3605167, baseEnd_3605167] using wordTrace_append hprefix tailTrace_3605167
  have hstable : (prefixWord ++ tailWord_3605167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605167).length < 2 ^ (prefixWord ++ tailWord_3605167).sum := by decide
  have hdescent : baseEnd_3605167 < baseStart_3605167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605171 : List Nat := [1, 1, 1, 2, 3, 4, 2, 4, 1, 3]
def baseStart_3605171 : Nat := 118140960795 + 3605171 * 2 ^ 59
def prefixEnd_3605171 : Nat := 4983230072969 + 3 ^ 40 * 3605171 * 2
def baseEnd_3605171 : Nat := 1234123709766946323721751

theorem tailTrace_3605171 : CollatzResearch.WordTrace tailWord_3605171 prefixEnd_3605171 1234123709766946323721751 := by
  unfold tailWord_3605171
  simp only [CollatzResearch.WordTrace]
  refine ⟨131491388822088656032399367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87660925881392437354932911 131491388822088656032399367)
  ·
    refine ⟨197237083233132984048599051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131491388822088656032399367 197237083233132984048599051)
    ·
      refine ⟨295855624849699476072898577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197237083233132984048599051 295855624849699476072898577)
      ·
        refine ⟨221891718637274607054673933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295855624849699476072898577 221891718637274607054673933)
        ·
          refine ⟨83209394488977977645502725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221891718637274607054673933 83209394488977977645502725)
          ·
            refine ⟨15601761466683370808531761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83209394488977977645502725 15601761466683370808531761)
            ·
              refine ⟨11701321100012528106398821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15601761466683370808531761 11701321100012528106398821)
              ·
                refine ⟨2193997706252349019949779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11701321100012528106398821 2193997706252349019949779)
                ·
                  refine ⟨3290996559378523529924669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2193997706252349019949779 3290996559378523529924669)
                  ·
                    refine ⟨1234123709766946323721751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3290996559378523529924669 1234123709766946323721751)
                    ·
                      rfl

theorem cell22_3605171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 4, 1, 3].length) (baseStart_3605171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3605171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3605171 prefixEnd_3605171 := by exact prefixLift 3605171
  have htrace : WordTrace (prefixWord ++ tailWord_3605171) baseStart_3605171 baseEnd_3605171 := by
    simpa [prefixWord, tailWord_3605171, baseEnd_3605171] using wordTrace_append hprefix tailTrace_3605171
  have hstable : (prefixWord ++ tailWord_3605171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605171).length < 2 ^ (prefixWord ++ tailWord_3605171).sum := by decide
  have hdescent : baseEnd_3605171 < baseStart_3605171 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605190 : List Nat := [6, 1, 2, 1, 2, 2, 2, 6]
def baseStart_3605190 : Nat := 118140960795 + 3605190 * 2 ^ 59
def prefixEnd_3605190 : Nat := 4983230072969 + 3 ^ 40 * 3605190 * 2
def baseEnd_3605190 : Nat := 137125579317248511944077

theorem tailTrace_3605190 : CollatzResearch.WordTrace tailWord_3605190 prefixEnd_3605190 137125579317248511944077 := by
  unfold tailWord_3605190
  simp only [CollatzResearch.WordTrace]
  refine ⟨4109127556531869446166907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 87661387872679881518227349 4109127556531869446166907)
  ·
    refine ⟨6163691334797804169250361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4109127556531869446166907 6163691334797804169250361)
    ·
      refine ⟨4622768501098353126937771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6163691334797804169250361 4622768501098353126937771)
      ·
        refine ⟨6934152751647529690406657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4622768501098353126937771 6934152751647529690406657)
        ·
          refine ⟨5200614563735647267804993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6934152751647529690406657 5200614563735647267804993)
          ·
            refine ⟨3900460922801735450853745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5200614563735647267804993 3900460922801735450853745)
            ·
              refine ⟨2925345692101301588140309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3900460922801735450853745 2925345692101301588140309)
              ·
                refine ⟨137125579317248511944077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2925345692101301588140309 137125579317248511944077)
                ·
                  rfl

theorem cell22_3605190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_3605190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3605190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3605190 prefixEnd_3605190 := by exact prefixLift 3605190
  have htrace : WordTrace (prefixWord ++ tailWord_3605190) baseStart_3605190 baseEnd_3605190 := by
    simpa [prefixWord, tailWord_3605190, baseEnd_3605190] using wordTrace_append hprefix tailTrace_3605190
  have hstable : (prefixWord ++ tailWord_3605190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605190).length < 2 ^ (prefixWord ++ tailWord_3605190).sum := by decide
  have hdescent : baseEnd_3605190 < baseStart_3605190 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605242 : List Nat := [3, 1, 1, 1, 1, 3, 2, 1, 3, 6]
def baseStart_3605242 : Nat := 118140960795 + 3605242 * 2 ^ 59
def prefixEnd_3605242 : Nat := 4983230072969 + 3 ^ 40 * 3605242 * 2
def baseEnd_3605242 : Nat := 1234148014517925805196533

theorem tailTrace_3605242 : CollatzResearch.WordTrace tailWord_3605242 prefixEnd_3605242 1234148014517925805196533 := by
  unfold tailWord_3605242
  simp only [CollatzResearch.WordTrace]
  refine ⟨32873494601207858789558495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87662652269887623438822653 32873494601207858789558495)
  ·
    refine ⟨49310241901811788184337743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32873494601207858789558495 49310241901811788184337743)
    ·
      refine ⟨73965362852717682276506615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49310241901811788184337743 73965362852717682276506615)
      ·
        refine ⟨110948044279076523414759923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73965362852717682276506615 110948044279076523414759923)
        ·
          refine ⟨166422066418614785122139885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110948044279076523414759923 166422066418614785122139885)
          ·
            refine ⟨62408274906980544420802457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166422066418614785122139885 62408274906980544420802457)
            ·
              refine ⟨46806206180235408315601843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62408274906980544420802457 46806206180235408315601843)
              ·
                refine ⟨70209309270353112473402765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46806206180235408315601843 70209309270353112473402765)
                ·
                  refine ⟨26328490976382417177526037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70209309270353112473402765 26328490976382417177526037)
                  ·
                    refine ⟨1234148014517925805196533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26328490976382417177526037 1234148014517925805196533)
                    ·
                      rfl

theorem cell22_3605242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 3, 6].length) (baseStart_3605242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3605242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3605242 prefixEnd_3605242 := by exact prefixLift 3605242
  have htrace : WordTrace (prefixWord ++ tailWord_3605242) baseStart_3605242 baseEnd_3605242 := by
    simpa [prefixWord, tailWord_3605242, baseEnd_3605242] using wordTrace_append hprefix tailTrace_3605242
  have hstable : (prefixWord ++ tailWord_3605242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605242).length < 2 ^ (prefixWord ++ tailWord_3605242).sum := by decide
  have hdescent : baseEnd_3605242 < baseStart_3605242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605257 : List Nat := [1, 2, 1, 1, 3, 2, 4, 8]
def baseStart_3605257 : Nat := 118140960795 + 3605257 * 2 ^ 59
def prefixEnd_3605257 : Nat := 4983230072969 + 3 ^ 40 * 3605257 * 2
def baseEnd_3605257 : Nat := 137128127702718974007943

theorem tailTrace_3605257 : CollatzResearch.WordTrace tailWord_3605257 prefixEnd_3605257 137128127702718974007943 := by
  unfold tailWord_3605257
  simp only [CollatzResearch.WordTrace]
  refine ⟨131494525499777092720030025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87663016999851395146686683 131494525499777092720030025)
  ·
    refine ⟨98620894124832819540022519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131494525499777092720030025 98620894124832819540022519)
    ·
      refine ⟨147931341187249229310033779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98620894124832819540022519 147931341187249229310033779)
      ·
        refine ⟨221897011780873843965050669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147931341187249229310033779 221897011780873843965050669)
        ·
          refine ⟨83211379417827691486894001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221897011780873843965050669 83211379417827691486894001)
          ·
            refine ⟨62408534563370768615170501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83211379417827691486894001 62408534563370768615170501)
            ·
              refine ⟨11701600230632019115344469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62408534563370768615170501 11701600230632019115344469)
              ·
                refine ⟨137128127702718974007943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11701600230632019115344469 137128127702718974007943)
                ·
                  rfl

theorem cell22_3605257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 8].length) (baseStart_3605257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3605257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3605257 prefixEnd_3605257 := by exact prefixLift 3605257
  have htrace : WordTrace (prefixWord ++ tailWord_3605257) baseStart_3605257 baseEnd_3605257 := by
    simpa [prefixWord, tailWord_3605257, baseEnd_3605257] using wordTrace_append hprefix tailTrace_3605257
  have hstable : (prefixWord ++ tailWord_3605257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605257).length < 2 ^ (prefixWord ++ tailWord_3605257).sum := by decide
  have hdescent : baseEnd_3605257 < baseStart_3605257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605310 : List Nat := [4, 2, 1, 2, 4, 1, 1, 1, 2, 4]
def baseStart_3605310 : Nat := 118140960795 + 3605310 * 2 ^ 59
def prefixEnd_3605310 : Nat := 4983230072969 + 3 ^ 40 * 3605310 * 2
def baseEnd_3605310 : Nat := 1234171292307596294496325

theorem tailTrace_3605310 : CollatzResearch.WordTrace tailWord_3605310 prefixEnd_3605310 1234171292307596294496325 := by
  unfold tailWord_3605310
  simp only [CollatzResearch.WordTrace]
  refine ⟨16437057321073135346463673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87664305712390055181139589 16437057321073135346463673)
  ·
    refine ⟨12327792990804851509847755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16437057321073135346463673 12327792990804851509847755)
    ·
      refine ⟨18491689486207277264771633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12327792990804851509847755 18491689486207277264771633)
      ·
        refine ⟨13868767114655457948578725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18491689486207277264771633 13868767114655457948578725)
        ·
          refine ⟨2600393833997898365358511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13868767114655457948578725 2600393833997898365358511)
          ·
            refine ⟨3900590750996847548037767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2600393833997898365358511 3900590750996847548037767)
            ·
              refine ⟨5850886126495271322056651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3900590750996847548037767 5850886126495271322056651)
              ·
                refine ⟨8776329189742906983084977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5850886126495271322056651 8776329189742906983084977)
                ·
                  refine ⟨6582246892307180237313733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8776329189742906983084977 6582246892307180237313733)
                  ·
                    refine ⟨1234171292307596294496325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6582246892307180237313733 1234171292307596294496325)
                    ·
                      rfl

theorem cell22_3605310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 1, 2, 4].length) (baseStart_3605310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3605310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3605310 prefixEnd_3605310 := by exact prefixLift 3605310
  have htrace : WordTrace (prefixWord ++ tailWord_3605310) baseStart_3605310 baseEnd_3605310 := by
    simpa [prefixWord, tailWord_3605310, baseEnd_3605310] using wordTrace_append hprefix tailTrace_3605310
  have hstable : (prefixWord ++ tailWord_3605310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605310).length < 2 ^ (prefixWord ++ tailWord_3605310).sum := by decide
  have hdescent : baseEnd_3605310 < baseStart_3605310 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605340 : List Nat := [2, 2, 4, 2, 1, 1, 2, 4, 1, 3]
def baseStart_3605340 : Nat := 118140960795 + 3605340 * 2 ^ 59
def prefixEnd_3605340 : Nat := 4983230072969 + 3 ^ 40 * 3605340 * 2
def baseEnd_3605340 : Nat := 1234181561920686216246233

theorem tailTrace_3605340 : CollatzResearch.WordTrace tailWord_3605340 prefixEnd_3605340 1234181561920686216246233 := by
  unfold tailWord_3605340
  simp only [CollatzResearch.WordTrace]
  refine ⟨65748776379238198947650737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87665035172317598596867649 65748776379238198947650737)
  ·
    refine ⟨49311582284428649210738053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65748776379238198947650737 49311582284428649210738053)
    ·
      refine ⟨9245921678330371727013385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49311582284428649210738053 9245921678330371727013385)
      ·
        refine ⟨6934441258747778795260039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9245921678330371727013385 6934441258747778795260039)
        ·
          refine ⟨10401661888121668192890059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6934441258747778795260039 10401661888121668192890059)
          ·
            refine ⟨15602492832182502289335089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10401661888121668192890059 15602492832182502289335089)
            ·
              refine ⟨11701869624136876717001317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15602492832182502289335089 11701869624136876717001317)
              ·
                refine ⟨2194100554525664384437747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11701869624136876717001317 2194100554525664384437747)
                ·
                  refine ⟨3291150831788496576656621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2194100554525664384437747 3291150831788496576656621)
                  ·
                    refine ⟨1234181561920686216246233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3291150831788496576656621 1234181561920686216246233)
                    ·
                      rfl

theorem cell22_3605340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_3605340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3605340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3605340 prefixEnd_3605340 := by exact prefixLift 3605340
  have htrace : WordTrace (prefixWord ++ tailWord_3605340) baseStart_3605340 baseEnd_3605340 := by
    simpa [prefixWord, tailWord_3605340, baseEnd_3605340] using wordTrace_append hprefix tailTrace_3605340
  have hstable : (prefixWord ++ tailWord_3605340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605340).length < 2 ^ (prefixWord ++ tailWord_3605340).sum := by decide
  have hdescent : baseEnd_3605340 < baseStart_3605340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605349 : List Nat := [1, 3, 1, 3, 1, 1, 2, 1, 5, 4]
def baseStart_3605349 : Nat := 118140960795 + 3605349 * 2 ^ 59
def prefixEnd_3605349 : Nat := 4983230072969 + 3 ^ 40 * 3605349 * 2
def baseEnd_3605349 : Nat := 1234184642804613192771205

theorem tailTrace_3605349 : CollatzResearch.WordTrace tailWord_3605349 prefixEnd_3605349 1234184642804613192771205 := by
  unfold tailWord_3605349
  simp only [CollatzResearch.WordTrace]
  refine ⟨131497881015443792432379101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87665254010295861621586067 131497881015443792432379101)
  ·
    refine ⟨49311705380791422162142163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131497881015443792432379101 49311705380791422162142163)
    ·
      refine ⟨73967558071187133243213245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49311705380791422162142163 73967558071187133243213245)
      ·
        refine ⟨27737834276695174966204967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73967558071187133243213245 27737834276695174966204967)
        ·
          refine ⟨41606751415042762449307451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27737834276695174966204967 41606751415042762449307451)
          ·
            refine ⟨62410127122564143673961177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41606751415042762449307451 62410127122564143673961177)
            ·
              refine ⟨46807595341923107755470883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62410127122564143673961177 46807595341923107755470883)
              ·
                refine ⟨70211393012884661633206325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46807595341923107755470883 70211393012884661633206325)
                ·
                  refine ⟨6582318094957937028113093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70211393012884661633206325 6582318094957937028113093)
                  ·
                    refine ⟨1234184642804613192771205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6582318094957937028113093 1234184642804613192771205)
                    ·
                      rfl

theorem cell22_3605349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 5, 4].length) (baseStart_3605349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3605349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3605349 prefixEnd_3605349 := by exact prefixLift 3605349
  have htrace : WordTrace (prefixWord ++ tailWord_3605349) baseStart_3605349 baseEnd_3605349 := by
    simpa [prefixWord, tailWord_3605349, baseEnd_3605349] using wordTrace_append hprefix tailTrace_3605349
  have hstable : (prefixWord ++ tailWord_3605349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605349).length < 2 ^ (prefixWord ++ tailWord_3605349).sum := by decide
  have hdescent : baseEnd_3605349 < baseStart_3605349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605374 : List Nat := [4, 2, 3, 1, 2, 2, 1, 3, 1, 3]
def baseStart_3605374 : Nat := 118140960795 + 3605374 * 2 ^ 59
def prefixEnd_3605374 : Nat := 4983230072969 + 3 ^ 40 * 3605374 * 2
def baseEnd_3605374 : Nat := 1234193200815521460896129

theorem tailTrace_3605374 : CollatzResearch.WordTrace tailWord_3605374 prefixEnd_3605374 1234193200815521460896129 := by
  unfold tailWord_3605374
  simp only [CollatzResearch.WordTrace]
  refine ⟨16437349105044152712754897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87665861893568814468026117 16437349105044152712754897)
  ·
    refine ⟨12328011828783114534566173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16437349105044152712754897 12328011828783114534566173)
    ·
      refine ⟨4623004435793667950462315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12328011828783114534566173 4623004435793667950462315)
      ·
        refine ⟨6934506653690501925693473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4623004435793667950462315 6934506653690501925693473)
        ·
          refine ⟨5200879990267876444270105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6934506653690501925693473 5200879990267876444270105)
          ·
            refine ⟨3900659992700907333202579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5200879990267876444270105 3900659992700907333202579)
            ·
              refine ⟨5850989989051360999803869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3900659992700907333202579 5850989989051360999803869)
              ·
                refine ⟨2194121245894260374926451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5850989989051360999803869 2194121245894260374926451)
                ·
                  refine ⟨3291181868841390562389677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2194121245894260374926451 3291181868841390562389677)
                  ·
                    refine ⟨1234193200815521460896129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3291181868841390562389677 1234193200815521460896129)
                    ·
                      rfl

theorem cell22_3605374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_3605374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3605374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3605374 prefixEnd_3605374 := by exact prefixLift 3605374
  have htrace : WordTrace (prefixWord ++ tailWord_3605374) baseStart_3605374 baseEnd_3605374 := by
    simpa [prefixWord, tailWord_3605374, baseEnd_3605374] using wordTrace_append hprefix tailTrace_3605374
  have hstable : (prefixWord ++ tailWord_3605374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605374).length < 2 ^ (prefixWord ++ tailWord_3605374).sum := by decide
  have hdescent : baseEnd_3605374 < baseStart_3605374 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605379 : List Nat := [1, 1, 1, 3, 4, 1, 2, 1, 3, 5]
def baseStart_3605379 : Nat := 118140960795 + 3605379 * 2 ^ 59
def prefixEnd_3605379 : Nat := 4983230072969 + 3 ^ 40 * 3605379 * 2
def baseEnd_3605379 : Nat := 1234194912417703114521113

theorem tailTrace_3605379 : CollatzResearch.WordTrace tailWord_3605379 prefixEnd_3605379 1234194912417703114521113 := by
  unfold tailWord_3605379
  simp only [CollatzResearch.WordTrace]
  refine ⟨131498975205335107555971191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87665983470223405037314127 131498975205335107555971191)
  ·
    refine ⟨197248462808002661333956787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131498975205335107555971191 197248462808002661333956787)
    ·
      refine ⟨295872694212003992000935181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197248462808002661333956787 295872694212003992000935181)
      ·
        refine ⟨110952260329501497000350693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 295872694212003992000935181 110952260329501497000350693)
        ·
          refine ⟨20803548811781530687565755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110952260329501497000350693 20803548811781530687565755)
          ·
            refine ⟨31205323217672296031348633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20803548811781530687565755 31205323217672296031348633)
            ·
              refine ⟨23403992413254222023511475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31205323217672296031348633 23403992413254222023511475)
              ·
                refine ⟨35105988619881333035267213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23403992413254222023511475 35105988619881333035267213)
                ·
                  refine ⟨13164745732455499888225205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35105988619881333035267213 13164745732455499888225205)
                  ·
                    refine ⟨1234194912417703114521113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13164745732455499888225205 1234194912417703114521113)
                    ·
                      rfl

theorem cell22_3605379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 3, 5].length) (baseStart_3605379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3605379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3605379 prefixEnd_3605379 := by exact prefixLift 3605379
  have htrace : WordTrace (prefixWord ++ tailWord_3605379) baseStart_3605379 baseEnd_3605379 := by
    simpa [prefixWord, tailWord_3605379, baseEnd_3605379] using wordTrace_append hprefix tailTrace_3605379
  have hstable : (prefixWord ++ tailWord_3605379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605379).length < 2 ^ (prefixWord ++ tailWord_3605379).sum := by decide
  have hdescent : baseEnd_3605379 < baseStart_3605379 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605499 : List Nat := [1, 1, 1, 1, 1, 3, 3, 1, 10]
def baseStart_3605499 : Nat := 118140960795 + 3605499 * 2 ^ 59
def prefixEnd_3605499 : Nat := 4983230072969 + 3 ^ 40 * 3605499 * 2
def baseEnd_3605499 : Nat := 411411996956687600506915

theorem tailTrace_3605499 : CollatzResearch.WordTrace tailWord_3605499 prefixEnd_3605499 411411996956687600506915 := by
  unfold tailWord_3605499
  simp only [CollatzResearch.WordTrace]
  refine ⟨131503351964900368050339551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87668901309933578700226367 131503351964900368050339551)
  ·
    refine ⟨197255027947350552075509327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131503351964900368050339551 197255027947350552075509327)
    ·
      refine ⟨295882541921025828113263991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197255027947350552075509327 295882541921025828113263991)
      ·
        refine ⟨443823812881538742169895987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295882541921025828113263991 443823812881538742169895987)
        ·
          refine ⟨665735719322308113254843981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443823812881538742169895987 665735719322308113254843981)
          ·
            refine ⟨249650894745865542470566493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 665735719322308113254843981 249650894745865542470566493)
            ·
              refine ⟨93619085529699578426462435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 249650894745865542470566493 93619085529699578426462435)
              ·
                refine ⟨140428628294549367639693653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93619085529699578426462435 140428628294549367639693653)
                ·
                  refine ⟨411411996956687600506915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 140428628294549367639693653 411411996956687600506915)
                  ·
                    rfl

theorem cell22_3605499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 10].length) (baseStart_3605499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3605499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3605499 prefixEnd_3605499 := by exact prefixLift 3605499
  have htrace : WordTrace (prefixWord ++ tailWord_3605499) baseStart_3605499 baseEnd_3605499 := by
    simpa [prefixWord, tailWord_3605499, baseEnd_3605499] using wordTrace_append hprefix tailTrace_3605499
  have hstable : (prefixWord ++ tailWord_3605499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605499).length < 2 ^ (prefixWord ++ tailWord_3605499).sum := by decide
  have hdescent : baseEnd_3605499 < baseStart_3605499 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605516 : List Nat := [2, 2, 1, 2, 3, 2, 1, 3, 6]
def baseStart_3605516 : Nat := 118140960795 + 3605516 * 2 ^ 59
def prefixEnd_3605516 : Nat := 4983230072969 + 3 ^ 40 * 3605516 * 2
def baseEnd_3605516 : Nat := 411413936772493474615231

theorem tailTrace_3605516 : CollatzResearch.WordTrace tailWord_3605516 prefixEnd_3605516 411413936772493474615231 := by
  unfold tailWord_3605516
  simp only [CollatzResearch.WordTrace]
  refine ⟨65751986002919389976854201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87669314670559186635805601 65751986002919389976854201)
  ·
    refine ⟨49313989502189542482640651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65751986002919389976854201 49313989502189542482640651)
    ·
      refine ⟨73970984253284313723960977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49313989502189542482640651 73970984253284313723960977)
      ·
        refine ⟨55478238189963235292970733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73970984253284313723960977 55478238189963235292970733)
        ·
          refine ⟨20804339321236213234864025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55478238189963235292970733 20804339321236213234864025)
          ·
            refine ⟨15603254490927159926148019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20804339321236213234864025 15603254490927159926148019)
            ·
              refine ⟨23404881736390739889222029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15603254490927159926148019 23404881736390739889222029)
              ·
                refine ⟨8776830651146527458458261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23404881736390739889222029 8776830651146527458458261)
                ·
                  refine ⟨411413936772493474615231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8776830651146527458458261 411413936772493474615231)
                  ·
                    rfl

theorem cell22_3605516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 3, 6].length) (baseStart_3605516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3605516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3605516 prefixEnd_3605516 := by exact prefixLift 3605516
  have htrace : WordTrace (prefixWord ++ tailWord_3605516) baseStart_3605516 baseEnd_3605516 := by
    simpa [prefixWord, tailWord_3605516, baseEnd_3605516] using wordTrace_append hprefix tailTrace_3605516
  have hstable : (prefixWord ++ tailWord_3605516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605516).length < 2 ^ (prefixWord ++ tailWord_3605516).sum := by decide
  have hdescent : baseEnd_3605516 < baseStart_3605516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605561 : List Nat := [1, 2, 1, 5, 2, 1, 10]
def baseStart_3605561 : Nat := 118140960795 + 3605561 * 2 ^ 59
def prefixEnd_3605561 : Nat := 4983230072969 + 3 ^ 40 * 3605561 * 2
def baseEnd_3605561 : Nat := 45713230175448715054465

theorem tailTrace_3605561 : CollatzResearch.WordTrace tailWord_3605561 prefixEnd_3605561 45713230175448715054465 := by
  unfold tailWord_3605561
  simp only [CollatzResearch.WordTrace]
  refine ⟨131505613290675752639096537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87670408860450501759397691 131505613290675752639096537)
  ·
    refine ⟨98629209968006814479322403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131505613290675752639096537 98629209968006814479322403)
    ·
      refine ⟨147943814952010221718983605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98629209968006814479322403 147943814952010221718983605)
      ·
        refine ⟨13869732651750958286154713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 147943814952010221718983605 13869732651750958286154713)
        ·
          refine ⟨10402299488813218714616035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13869732651750958286154713 10402299488813218714616035)
          ·
            refine ⟨15603449233219828071924053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10402299488813218714616035 15603449233219828071924053)
            ·
              refine ⟨45713230175448715054465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15603449233219828071924053 45713230175448715054465)
              ·
                rfl

theorem cell22_3605561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 10].length) (baseStart_3605561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3605561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3605561 prefixEnd_3605561 := by exact prefixLift 3605561
  have htrace : WordTrace (prefixWord ++ tailWord_3605561) baseStart_3605561 baseEnd_3605561 := by
    simpa [prefixWord, tailWord_3605561, baseEnd_3605561] using wordTrace_append hprefix tailTrace_3605561
  have hstable : (prefixWord ++ tailWord_3605561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605561).length < 2 ^ (prefixWord ++ tailWord_3605561).sum := by decide
  have hdescent : baseEnd_3605561 < baseStart_3605561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605597 : List Nat := [1, 4, 4, 1, 2, 1, 2, 1, 2, 4]
def baseStart_3605597 : Nat := 118140960795 + 3605597 * 2 ^ 59
def prefixEnd_3605597 : Nat := 4983230072969 + 3 ^ 40 * 3605597 * 2
def baseEnd_3605597 : Nat := 1234269538272823212570445

theorem tailTrace_3605597 : CollatzResearch.WordTrace tailWord_3605597 prefixEnd_3605597 1234269538272823212570445 := by
  unfold tailWord_3605597
  simp only [CollatzResearch.WordTrace]
  refine ⟨131506926318545330787407045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87671284212363553858271363 131506926318545330787407045)
  ·
    refine ⟨24657548684727249522638821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131506926318545330787407045 24657548684727249522638821)
    ·
      refine ⟨4623290378386359285494779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24657548684727249522638821 4623290378386359285494779)
      ·
        refine ⟨6934935567579538928242169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4623290378386359285494779 6934935567579538928242169)
        ·
          refine ⟨5201201675684654196181627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6934935567579538928242169 5201201675684654196181627)
          ·
            refine ⟨7801802513526981294272441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5201201675684654196181627 7801802513526981294272441)
            ·
              refine ⟨5851351885145235970704331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7801802513526981294272441 5851351885145235970704331)
              ·
                refine ⟨8777027827717853956056497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5851351885145235970704331 8777027827717853956056497)
                ·
                  refine ⟨6582770870788390467042373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8777027827717853956056497 6582770870788390467042373)
                  ·
                    refine ⟨1234269538272823212570445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6582770870788390467042373 1234269538272823212570445)
                    ·
                      rfl

theorem cell22_3605597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_3605597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3605597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3605597 prefixEnd_3605597 := by exact prefixLift 3605597
  have htrace : WordTrace (prefixWord ++ tailWord_3605597) baseStart_3605597 baseEnd_3605597 := by
    simpa [prefixWord, tailWord_3605597, baseEnd_3605597] using wordTrace_append hprefix tailTrace_3605597
  have hstable : (prefixWord ++ tailWord_3605597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605597).length < 2 ^ (prefixWord ++ tailWord_3605597).sum := by decide
  have hdescent : baseEnd_3605597 < baseStart_3605597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605623 : List Nat := [1, 1, 3, 1, 1, 4, 4, 2, 5]
def baseStart_3605623 : Nat := 118140960795 + 3605623 * 2 ^ 59
def prefixEnd_3605623 : Nat := 4983230072969 + 3 ^ 40 * 3605623 * 2
def baseEnd_3605623 : Nat := 411426146201389270473455

theorem tailTrace_3605623 : CollatzResearch.WordTrace tailWord_3605623 prefixEnd_3605623 411426146201389270473455 := by
  unfold tailWord_3605623
  simp only [CollatzResearch.WordTrace]
  refine ⟨131507874616451137227853523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87671916410967424818569015 131507874616451137227853523)
  ·
    refine ⟨197261811924676705841780285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131507874616451137227853523 197261811924676705841780285)
    ·
      refine ⟨73973179471753764690667607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197261811924676705841780285 73973179471753764690667607)
      ·
        refine ⟨110959769207630647036001411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73973179471753764690667607 110959769207630647036001411)
        ·
          refine ⟨166439653811445970554002117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110959769207630647036001411 166439653811445970554002117)
          ·
            refine ⟨31207435089646119478875397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 166439653811445970554002117 31207435089646119478875397)
            ·
              refine ⟨5851394079308647402289137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31207435089646119478875397 5851394079308647402289137)
              ·
                refine ⟨4388545559481485551716853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5851394079308647402289137 4388545559481485551716853)
                ·
                  refine ⟨411426146201389270473455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4388545559481485551716853 411426146201389270473455)
                  ·
                    rfl

theorem cell22_3605623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 2, 5].length) (baseStart_3605623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3605623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3605623 prefixEnd_3605623 := by exact prefixLift 3605623
  have htrace : WordTrace (prefixWord ++ tailWord_3605623) baseStart_3605623 baseEnd_3605623 := by
    simpa [prefixWord, tailWord_3605623, baseEnd_3605623] using wordTrace_append hprefix tailTrace_3605623
  have hstable : (prefixWord ++ tailWord_3605623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605623).length < 2 ^ (prefixWord ++ tailWord_3605623).sum := by decide
  have hdescent : baseEnd_3605623 < baseStart_3605623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605651 : List Nat := [1, 1, 1, 2, 1, 2, 5, 1, 8]
def baseStart_3605651 : Nat := 118140960795 + 3605651 * 2 ^ 59
def prefixEnd_3605651 : Nat := 4983230072969 + 3 ^ 40 * 3605651 * 2
def baseEnd_3605651 : Nat := 411429341192128357240093

theorem tailTrace_3605651 : CollatzResearch.WordTrace tailWord_3605651 prefixEnd_3605651 411429341192128357240093 := by
  unfold tailWord_3605651
  simp only [CollatzResearch.WordTrace]
  refine ⟨131508895860349698009872807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87672597240233132006581871 131508895860349698009872807)
  ·
    refine ⟨197263343790524547014809211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131508895860349698009872807 197263343790524547014809211)
    ·
      refine ⟨295895015685786820522213817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197263343790524547014809211 295895015685786820522213817)
      ·
        refine ⟨221921261764340115391660363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295895015685786820522213817 221921261764340115391660363)
        ·
          refine ⟨332881892646510173087490545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221921261764340115391660363 332881892646510173087490545)
          ·
            refine ⟨249661419484882629815617909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 332881892646510173087490545 249661419484882629815617909)
            ·
              refine ⟨23405758076707746545214179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 249661419484882629815617909 23405758076707746545214179)
              ·
                refine ⟨35108637115061619817821269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23405758076707746545214179 35108637115061619817821269)
                ·
                  refine ⟨411429341192128357240093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35108637115061619817821269 411429341192128357240093)
                  ·
                    rfl

theorem cell22_3605651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 8].length) (baseStart_3605651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3605651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3605651 prefixEnd_3605651 := by exact prefixLift 3605651
  have htrace : WordTrace (prefixWord ++ tailWord_3605651) baseStart_3605651 baseEnd_3605651 := by
    simpa [prefixWord, tailWord_3605651, baseEnd_3605651] using wordTrace_append hprefix tailTrace_3605651
  have hstable : (prefixWord ++ tailWord_3605651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605651).length < 2 ^ (prefixWord ++ tailWord_3605651).sum := by decide
  have hdescent : baseEnd_3605651 < baseStart_3605651 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605792 : List Nat := [2, 1, 1, 5, 3, 1, 2, 2, 5]
def baseStart_3605792 : Nat := 118140960795 + 3605792 * 2 ^ 59
def prefixEnd_3605792 : Nat := 4983230072969 + 3 ^ 40 * 3605792 * 2
def baseEnd_3605792 : Nat := 411445430252635901314949

theorem tailTrace_3605792 : CollatzResearch.WordTrace tailWord_3605792 prefixEnd_3605792 411445430252635901314949 := by
  unfold tailWord_3605792
  simp only [CollatzResearch.WordTrace]
  refine ⟨65757019276419439545377815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87676025701892586060503753 65757019276419439545377815)
  ·
    refine ⟨98635528914629159318066723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65757019276419439545377815 98635528914629159318066723)
    ·
      refine ⟨147953293371943738977100085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98635528914629159318066723 147953293371943738977100085)
      ·
        refine ⟨13870621253619725529103133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 147953293371943738977100085 13870621253619725529103133)
        ·
          refine ⟨5201482970107397073413675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13870621253619725529103133 5201482970107397073413675)
          ·
            refine ⟨7802224455161095610120513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5201482970107397073413675 7802224455161095610120513)
            ·
              refine ⟨5851668341370821707590385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7802224455161095610120513 5851668341370821707590385)
              ·
                refine ⟨4388751256028116280692789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5851668341370821707590385 4388751256028116280692789)
                ·
                  refine ⟨411445430252635901314949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4388751256028116280692789 411445430252635901314949)
                  ·
                    rfl

theorem cell22_3605792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 2, 5].length) (baseStart_3605792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3605792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3605792 prefixEnd_3605792 := by exact prefixLift 3605792
  have htrace : WordTrace (prefixWord ++ tailWord_3605792) baseStart_3605792 baseEnd_3605792 := by
    simpa [prefixWord, tailWord_3605792, baseEnd_3605792] using wordTrace_append hprefix tailTrace_3605792
  have hstable : (prefixWord ++ tailWord_3605792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605792).length < 2 ^ (prefixWord ++ tailWord_3605792).sum := by decide
  have hdescent : baseEnd_3605792 < baseStart_3605792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605820 : List Nat := [2, 2, 2, 2, 1, 4, 1, 2, 6]
def baseStart_3605820 : Nat := 118140960795 + 3605820 * 2 ^ 59
def prefixEnd_3605820 : Nat := 4983230072969 + 3 ^ 40 * 3605820 * 2
def baseEnd_3605820 : Nat := 411448625243374988081587

theorem tailTrace_3605820 : CollatzResearch.WordTrace tailWord_3605820 prefixEnd_3605820 411448625243374988081587 := by
  unfold tailWord_3605820
  simp only [CollatzResearch.WordTrace]
  refine ⟨65757529898368719936387457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87676706531158293248516609 65757529898368719936387457)
  ·
    refine ⟨49318147423776539952290593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65757529898368719936387457 49318147423776539952290593)
    ·
      refine ⟨36988610567832404964217945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49318147423776539952290593 36988610567832404964217945)
      ·
        refine ⟨27741457925874303723163459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36988610567832404964217945 27741457925874303723163459)
        ·
          refine ⟨41612186888811455584745189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27741457925874303723163459 41612186888811455584745189)
          ·
            refine ⟨7802285041652147922139723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41612186888811455584745189 7802285041652147922139723)
            ·
              refine ⟨11703427562478221883209585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7802285041652147922139723 11703427562478221883209585)
              ·
                refine ⟨8777570671858666412407189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11703427562478221883209585 8777570671858666412407189)
                ·
                  refine ⟨411448625243374988081587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8777570671858666412407189 411448625243374988081587)
                  ·
                    rfl

theorem cell22_3605820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 2, 6].length) (baseStart_3605820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3605820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3605820 prefixEnd_3605820 := by exact prefixLift 3605820
  have htrace : WordTrace (prefixWord ++ tailWord_3605820) baseStart_3605820 baseEnd_3605820 := by
    simpa [prefixWord, tailWord_3605820, baseEnd_3605820] using wordTrace_append hprefix tailTrace_3605820
  have hstable : (prefixWord ++ tailWord_3605820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605820).length < 2 ^ (prefixWord ++ tailWord_3605820).sum := by decide
  have hdescent : baseEnd_3605820 < baseStart_3605820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605822 : List Nat := [4, 2, 1, 2, 1, 1, 2, 4, 1, 4]
def baseStart_3605822 : Nat := 118140960795 + 3605822 * 2 ^ 59
def prefixEnd_3605822 : Nat := 4983230072969 + 3 ^ 40 * 3605822 * 2
def baseEnd_3605822 : Nat := 1234346560370997625694755

theorem tailTrace_3605822 : CollatzResearch.WordTrace tailWord_3605822 prefixEnd_3605822 1234346560370997625694755 := by
  unfold tailWord_3605822
  simp only [CollatzResearch.WordTrace]
  refine ⟨16439391592841274276793465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87676755161820129476231813 16439391592841274276793465)
  ·
    refine ⟨12329543694630955707595099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16439391592841274276793465 12329543694630955707595099)
    ·
      refine ⟨18494315541946433561392649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12329543694630955707595099 18494315541946433561392649)
      ·
        refine ⟨13870736656459825171044487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18494315541946433561392649 13870736656459825171044487)
        ·
          refine ⟨20806104984689737756566731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13870736656459825171044487 20806104984689737756566731)
          ·
            refine ⟨31209157477034606634850097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20806104984689737756566731 31209157477034606634850097)
            ·
              refine ⟨23406868107775954976137573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31209157477034606634850097 23406868107775954976137573)
              ·
                refine ⟨4388787770207991558025795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23406868107775954976137573 4388787770207991558025795)
                ·
                  refine ⟨6583181655311987337038693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4388787770207991558025795 6583181655311987337038693)
                  ·
                    refine ⟨1234346560370997625694755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6583181655311987337038693 1234346560370997625694755)
                    ·
                      rfl

theorem cell22_3605822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_3605822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3605822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3605822 prefixEnd_3605822 := by exact prefixLift 3605822
  have htrace : WordTrace (prefixWord ++ tailWord_3605822) baseStart_3605822 baseEnd_3605822 := by
    simpa [prefixWord, tailWord_3605822, baseEnd_3605822] using wordTrace_append hprefix tailTrace_3605822
  have hstable : (prefixWord ++ tailWord_3605822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605822).length < 2 ^ (prefixWord ++ tailWord_3605822).sum := by decide
  have hdescent : baseEnd_3605822 < baseStart_3605822 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605830 : List Nat := [6, 1, 1, 3, 1, 1, 2, 3, 1, 3]
def baseStart_3605830 : Nat := 118140960795 + 3605830 * 2 ^ 59
def prefixEnd_3605830 : Nat := 4983230072969 + 3 ^ 40 * 3605830 * 2
def baseEnd_3605830 : Nat := 1234349298934488271494731

theorem tailTrace_3605830 : CollatzResearch.WordTrace tailWord_3605830 prefixEnd_3605830 1234349298934488271494731 := by
  unfold tailWord_3605830
  simp only [CollatzResearch.WordTrace]
  refine ⟨4109857016459412861894967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 87676949684467474387092629 4109857016459412861894967)
  ·
    refine ⟨6164785524689119292842451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4109857016459412861894967 6164785524689119292842451)
    ·
      refine ⟨9247178287033678939263677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6164785524689119292842451 9247178287033678939263677)
      ·
        refine ⟨3467691857637629602223879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9247178287033678939263677 3467691857637629602223879)
        ·
          refine ⟨5201537786456444403335819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3467691857637629602223879 5201537786456444403335819)
          ·
            refine ⟨7802306679684666605003729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5201537786456444403335819 7802306679684666605003729)
            ·
              refine ⟨5851730009763499953752797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7802306679684666605003729 5851730009763499953752797)
              ·
                refine ⟨2194398753661312482657299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5851730009763499953752797 2194398753661312482657299)
                ·
                  refine ⟨3291598130491968723985949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2194398753661312482657299 3291598130491968723985949)
                  ·
                    refine ⟨1234349298934488271494731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3291598130491968723985949 1234349298934488271494731)
                    ·
                      rfl

theorem cell22_3605830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_3605830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3605830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3605830 prefixEnd_3605830 := by exact prefixLift 3605830
  have htrace : WordTrace (prefixWord ++ tailWord_3605830) baseStart_3605830 baseEnd_3605830 := by
    simpa [prefixWord, tailWord_3605830, baseEnd_3605830] using wordTrace_append hprefix tailTrace_3605830
  have hstable : (prefixWord ++ tailWord_3605830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605830).length < 2 ^ (prefixWord ++ tailWord_3605830).sum := by decide
  have hdescent : baseEnd_3605830 < baseStart_3605830 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605848 : List Nat := [2, 1, 2, 2, 1, 1, 13]
def baseStart_3605848 : Nat := 118140960795 + 3605848 * 2 ^ 59
def prefixEnd_3605848 : Nat := 4983230072969 + 3 ^ 40 * 3605848 * 2
def baseEnd_3605848 : Nat := 45716868914901563872025

theorem tailTrace_3605848 : CollatzResearch.WordTrace tailWord_3605848 prefixEnd_3605848 45716868914901563872025 := by
  unfold tailWord_3605848
  simp only [CollatzResearch.WordTrace]
  refine ⟨65758040520318000327397099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87677387360424000436529465 65758040520318000327397099)
  ·
    refine ⟨98637060780477000491095649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65758040520318000327397099 98637060780477000491095649)
    ·
      refine ⟨73977795585357750368321737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98637060780477000491095649 73977795585357750368321737)
      ·
        refine ⟨55483346689018312776241303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73977795585357750368321737 55483346689018312776241303)
        ·
          refine ⟨83225020033527469164361955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55483346689018312776241303 83225020033527469164361955)
          ·
            refine ⟨124837530050291203746542933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83225020033527469164361955 124837530050291203746542933)
            ·
              refine ⟨45716868914901563872025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 124837530050291203746542933 45716868914901563872025)
              ·
                rfl

theorem cell22_3605848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 13].length) (baseStart_3605848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3605848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3605848 prefixEnd_3605848 := by exact prefixLift 3605848
  have htrace : WordTrace (prefixWord ++ tailWord_3605848) baseStart_3605848 baseEnd_3605848 := by
    simpa [prefixWord, tailWord_3605848, baseEnd_3605848] using wordTrace_append hprefix tailTrace_3605848
  have hstable : (prefixWord ++ tailWord_3605848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605848).length < 2 ^ (prefixWord ++ tailWord_3605848).sum := by decide
  have hdescent : baseEnd_3605848 < baseStart_3605848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605850 : List Nat := [3, 1, 1, 2, 1, 2, 2, 4, 2, 4]
def baseStart_3605850 : Nat := 118140960795 + 3605850 * 2 ^ 59
def prefixEnd_3605850 : Nat := 4983230072969 + 3 ^ 40 * 3605850 * 2
def baseEnd_3605850 : Nat := 1234356145343214885994669

theorem tailTrace_3605850 : CollatzResearch.WordTrace tailWord_3605850 prefixEnd_3605850 1234356145343214885994669 := by
  unfold tailWord_3605850
  simp only [CollatzResearch.WordTrace]
  refine ⟨32879038496657188749091751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87677435991085836664244669 32879038496657188749091751)
  ·
    refine ⟨49318557744985783123637627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32879038496657188749091751 49318557744985783123637627)
    ·
      refine ⟨73977836617478674685456441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49318557744985783123637627 73977836617478674685456441)
      ·
        refine ⟨55483377463109006014092331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73977836617478674685456441 55483377463109006014092331)
        ·
          refine ⟨83225066194663509021138497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55483377463109006014092331 83225066194663509021138497)
          ·
            refine ⟨62418799645997631765853873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83225066194663509021138497 62418799645997631765853873)
            ·
              refine ⟨46814099734498223824390405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62418799645997631765853873 46814099734498223824390405)
              ·
                refine ⟨8777643700218416967073201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46814099734498223824390405 8777643700218416967073201)
                ·
                  refine ⟨6583232775163812725304901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8777643700218416967073201 6583232775163812725304901)
                  ·
                    refine ⟨1234356145343214885994669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6583232775163812725304901 1234356145343214885994669)
                    ·
                      rfl

theorem cell22_3605850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 4, 2, 4].length) (baseStart_3605850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3605850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3605850 prefixEnd_3605850 := by exact prefixLift 3605850
  have htrace : WordTrace (prefixWord ++ tailWord_3605850) baseStart_3605850 baseEnd_3605850 := by
    simpa [prefixWord, tailWord_3605850, baseEnd_3605850] using wordTrace_append hprefix tailTrace_3605850
  have hstable : (prefixWord ++ tailWord_3605850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605850).length < 2 ^ (prefixWord ++ tailWord_3605850).sum := by decide
  have hdescent : baseEnd_3605850 < baseStart_3605850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605927 : List Nat := [1, 1, 6, 1, 1, 1, 3, 3, 5]
def baseStart_3605927 : Nat := 118140960795 + 3605927 * 2 ^ 59
def prefixEnd_3605927 : Nat := 4983230072969 + 3 ^ 40 * 3605927 * 2
def baseEnd_3605927 : Nat := 411460834672270783939811

theorem tailTrace_3605927 : CollatzResearch.WordTrace tailWord_3605927 prefixEnd_3605927 411460834672270783939811 := by
  unfold tailWord_3605927
  simp only [CollatzResearch.WordTrace]
  refine ⟨131518962407349797146920035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87679308271566531431280023 131518962407349797146920035)
  ·
    refine ⟨197278443611024695720380053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131518962407349797146920035 197278443611024695720380053)
    ·
      refine ⟨9247427044266782611892815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 197278443611024695720380053 9247427044266782611892815)
      ·
        refine ⟨13871140566400173917839223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9247427044266782611892815 13871140566400173917839223)
        ·
          refine ⟨20806710849600260876758835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13871140566400173917839223 20806710849600260876758835)
          ·
            refine ⟨31210066274400391315138253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20806710849600260876758835 31210066274400391315138253)
            ·
              refine ⟨11703774852900146743176845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31210066274400391315138253 11703774852900146743176845)
              ·
                refine ⟨4388915569837555028691317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11703774852900146743176845 4388915569837555028691317)
                ·
                  refine ⟨411460834672270783939811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4388915569837555028691317 411460834672270783939811)
                  ·
                    rfl

theorem cell22_3605927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 3, 5].length) (baseStart_3605927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3605927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3605927 prefixEnd_3605927 := by exact prefixLift 3605927
  have htrace : WordTrace (prefixWord ++ tailWord_3605927) baseStart_3605927 baseEnd_3605927 := by
    simpa [prefixWord, tailWord_3605927, baseEnd_3605927] using wordTrace_append hprefix tailTrace_3605927
  have hstable : (prefixWord ++ tailWord_3605927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605927).length < 2 ^ (prefixWord ++ tailWord_3605927).sum := by decide
  have hdescent : baseEnd_3605927 < baseStart_3605927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605974 : List Nat := [5, 2, 1, 1, 1, 2, 1, 2, 3, 4]
def baseStart_3605974 : Nat := 118140960795 + 3605974 * 2 ^ 59
def prefixEnd_3605974 : Nat := 4983230072969 + 3 ^ 40 * 3605974 * 2
def baseEnd_3605974 : Nat := 1234398593077319895894289

theorem tailTrace_3605974 : CollatzResearch.WordTrace tailWord_3605974 prefixEnd_3605974 1234398593077319895894289 := by
  unfold tailWord_3605974
  simp only [CollatzResearch.WordTrace]
  refine ⟨8220042289886220260867561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87680451092119682782587317 8220042289886220260867561)
  ·
    refine ⟨6165031717414665195650671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8220042289886220260867561 6165031717414665195650671)
    ·
      refine ⟨9247547576121997793476007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6165031717414665195650671 9247547576121997793476007)
      ·
        refine ⟨13871321364182996690214011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9247547576121997793476007 13871321364182996690214011)
        ·
          refine ⟨20806982046274495035321017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13871321364182996690214011 20806982046274495035321017)
          ·
            refine ⟨15605236534705871276490763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20806982046274495035321017 15605236534705871276490763)
            ·
              refine ⟨23407854802058806914736145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15605236534705871276490763 23407854802058806914736145)
              ·
                refine ⟨17555891101544105186052109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23407854802058806914736145 17555891101544105186052109)
                ·
                  refine ⟨6583459163079039444769541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17555891101544105186052109 6583459163079039444769541)
                  ·
                    refine ⟨1234398593077319895894289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6583459163079039444769541 1234398593077319895894289)
                    ·
                      rfl

theorem cell22_3605974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_3605974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3605974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3605974 prefixEnd_3605974 := by exact prefixLift 3605974
  have htrace : WordTrace (prefixWord ++ tailWord_3605974) baseStart_3605974 baseEnd_3605974 := by
    simpa [prefixWord, tailWord_3605974, baseEnd_3605974] using wordTrace_append hprefix tailTrace_3605974
  have hstable : (prefixWord ++ tailWord_3605974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605974).length < 2 ^ (prefixWord ++ tailWord_3605974).sum := by decide
  have hdescent : baseEnd_3605974 < baseStart_3605974 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605987 : List Nat := [1, 1, 1, 6, 2, 1, 1, 3, 1, 5]
def baseStart_3605987 : Nat := 118140960795 + 3605987 * 2 ^ 59
def prefixEnd_3605987 : Nat := 4983230072969 + 3 ^ 40 * 3605987 * 2
def baseEnd_3605987 : Nat := 1234403043242992195319249

theorem tailTrace_3605987 : CollatzResearch.WordTrace tailWord_3605987 prefixEnd_3605987 1234403043242992195319249 := by
  unfold tailWord_3605987
  simp only [CollatzResearch.WordTrace]
  refine ⟨131521150787132427394104215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87680767191421618262736143 131521150787132427394104215)
  ·
    refine ⟨197281726180698641091156323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131521150787132427394104215 197281726180698641091156323)
    ·
      refine ⟨295922589271047961636734485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197281726180698641091156323 295922589271047961636734485)
      ·
        refine ⟨13871371372080373201721929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 295922589271047961636734485 13871371372080373201721929)
        ·
          refine ⟨10403528529060279901291447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13871371372080373201721929 10403528529060279901291447)
          ·
            refine ⟨15605292793590419851937171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10403528529060279901291447 15605292793590419851937171)
            ·
              refine ⟨23407939190385629777905757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15605292793590419851937171 23407939190385629777905757)
              ·
                refine ⟨8777977196394611166714659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23407939190385629777905757 8777977196394611166714659)
                ·
                  refine ⟨13166965794591916750071989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8777977196394611166714659 13166965794591916750071989)
                  ·
                    refine ⟨1234403043242992195319249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13166965794591916750071989 1234403043242992195319249)
                    ·
                      rfl

theorem cell22_3605987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 3, 1, 5].length) (baseStart_3605987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3605987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3605987 prefixEnd_3605987 := by exact prefixLift 3605987
  have htrace : WordTrace (prefixWord ++ tailWord_3605987) baseStart_3605987 baseEnd_3605987 := by
    simpa [prefixWord, tailWord_3605987, baseEnd_3605987] using wordTrace_append hprefix tailTrace_3605987
  have hstable : (prefixWord ++ tailWord_3605987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605987).length < 2 ^ (prefixWord ++ tailWord_3605987).sum := by decide
  have hdescent : baseEnd_3605987 < baseStart_3605987 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606006 : List Nat := [5, 1, 1, 1, 2, 3, 2, 3, 4]
def baseStart_3606006 : Nat := 118140960795 + 3606006 * 2 ^ 59
def prefixEnd_3606006 : Nat := 4983230072969 + 3 ^ 40 * 3606006 * 2
def baseEnd_3606006 : Nat := 411469849110427493031397

theorem tailTrace_3606006 : CollatzResearch.WordTrace tailWord_3606006 prefixEnd_3606006 411469849110427493031397 := by
  unfold tailWord_3606006
  simp only [CollatzResearch.WordTrace]
  refine ⟨8220115235878974602440367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87681229182709062426030581 8220115235878974602440367)
  ·
    refine ⟨12330172853818461903660551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8220115235878974602440367 12330172853818461903660551)
    ·
      refine ⟨18495259280727692855490827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12330172853818461903660551 18495259280727692855490827)
      ·
        refine ⟨27742888921091539283236241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18495259280727692855490827 27742888921091539283236241)
        ·
          refine ⟨20807166690818654462427181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27742888921091539283236241 20807166690818654462427181)
          ·
            refine ⟨7802687509056995423410193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20807166690818654462427181 7802687509056995423410193)
            ·
              refine ⟨5852015631792746567557645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7802687509056995423410193 5852015631792746567557645)
              ·
                refine ⟨2194505861922279962834117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5852015631792746567557645 2194505861922279962834117)
                ·
                  refine ⟨411469849110427493031397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2194505861922279962834117 411469849110427493031397)
                  ·
                    rfl

theorem cell22_3606006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 3, 4].length) (baseStart_3606006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3606006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3606006 prefixEnd_3606006 := by exact prefixLift 3606006
  have htrace : WordTrace (prefixWord ++ tailWord_3606006) baseStart_3606006 baseEnd_3606006 := by
    simpa [prefixWord, tailWord_3606006, baseEnd_3606006] using wordTrace_append hprefix tailTrace_3606006
  have hstable : (prefixWord ++ tailWord_3606006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606006).length < 2 ^ (prefixWord ++ tailWord_3606006).sum := by decide
  have hdescent : baseEnd_3606006 < baseStart_3606006 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606017 : List Nat := [1, 2, 4, 1, 4, 1, 9]
def baseStart_3606017 : Nat := 118140960795 + 3606017 * 2 ^ 59
def prefixEnd_3606017 : Nat := 4983230072969 + 3 ^ 40 * 3606017 * 2
def baseEnd_3606017 : Nat := 45719011587262300632191

theorem tailTrace_3606017 : CollatzResearch.WordTrace tailWord_3606017 prefixEnd_3606017 45719011587262300632191 := by
  unfold tailWord_3606017
  simp only [CollatzResearch.WordTrace]
  refine ⟨131522244977023742517696305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87681496651349161678464203 131522244977023742517696305)
  ·
    refine ⟨98641683732767806888272229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131522244977023742517696305 98641683732767806888272229)
    ·
      refine ⟨18495315699893963791551043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98641683732767806888272229 18495315699893963791551043)
      ·
        refine ⟨27742973549840945687326565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18495315699893963791551043 27742973549840945687326565)
        ·
          refine ⟨5201807540595177316373731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27742973549840945687326565 5201807540595177316373731)
          ·
            refine ⟨7802711310892765974560597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5201807540595177316373731 7802711310892765974560597)
            ·
              refine ⟨45719011587262300632191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7802711310892765974560597 45719011587262300632191)
              ·
                rfl

theorem cell22_3606017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 9].length) (baseStart_3606017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3606017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3606017 prefixEnd_3606017 := by exact prefixLift 3606017
  have htrace : WordTrace (prefixWord ++ tailWord_3606017) baseStart_3606017 baseEnd_3606017 := by
    simpa [prefixWord, tailWord_3606017, baseEnd_3606017] using wordTrace_append hprefix tailTrace_3606017
  have hstable : (prefixWord ++ tailWord_3606017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606017).length < 2 ^ (prefixWord ++ tailWord_3606017).sum := by decide
  have hdescent : baseEnd_3606017 < baseStart_3606017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606049 : List Nat := [1, 2, 3, 2, 2, 2, 2, 2, 3, 3]
def baseStart_3606049 : Nat := 118140960795 + 3606049 * 2 ^ 59
def prefixEnd_3606049 : Nat := 4983230072969 + 3 ^ 40 * 3606049 * 2
def baseEnd_3606049 : Nat := 1234424267110044700269059

theorem tailTrace_3606049 : CollatzResearch.WordTrace tailWord_3606049 prefixEnd_3606049 1234424267110044700269059 := by
  unfold tailWord_3606049
  simp only [CollatzResearch.WordTrace]
  refine ⟨131523412112907811982861201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87682274741938541321907467 131523412112907811982861201)
  ·
    refine ⟨98642559084680858987145901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131523412112907811982861201 98642559084680858987145901)
    ·
      refine ⟨36990959656755322120179713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98642559084680858987145901 36990959656755322120179713)
      ·
        refine ⟨27743219742566491590134785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36990959656755322120179713 27743219742566491590134785)
        ·
          refine ⟨20807414806924868692601089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27743219742566491590134785 20807414806924868692601089)
          ·
            refine ⟨15605561105193651519450817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20807414806924868692601089 15605561105193651519450817)
            ·
              refine ⟨11704170828895238639588113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15605561105193651519450817 11704170828895238639588113)
              ·
                refine ⟨8778128121671428979691085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11704170828895238639588113 8778128121671428979691085)
                ·
                  refine ⟨3291798045626785867384157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8778128121671428979691085 3291798045626785867384157)
                  ·
                    refine ⟨1234424267110044700269059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3291798045626785867384157 1234424267110044700269059)
                    ·
                      rfl

theorem cell22_3606049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 2, 3, 3].length) (baseStart_3606049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3606049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3606049 prefixEnd_3606049 := by exact prefixLift 3606049
  have htrace : WordTrace (prefixWord ++ tailWord_3606049) baseStart_3606049 baseEnd_3606049 := by
    simpa [prefixWord, tailWord_3606049, baseEnd_3606049] using wordTrace_append hprefix tailTrace_3606049
  have hstable : (prefixWord ++ tailWord_3606049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606049).length < 2 ^ (prefixWord ++ tailWord_3606049).sum := by decide
  have hdescent : baseEnd_3606049 < baseStart_3606049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606051 : List Nat := [1, 1, 1, 4, 6, 1, 2, 6]
def baseStart_3606051 : Nat := 118140960795 + 3606051 * 2 ^ 59
def prefixEnd_3606051 : Nat := 4983230072969 + 3 ^ 40 * 3606051 * 2
def baseEnd_3606051 : Nat := 137158327972324151302117

theorem tailTrace_3606051 : CollatzResearch.WordTrace tailWord_3606051 prefixEnd_3606051 137158327972324151302117 := by
  unfold tailWord_3606051
  simp only [CollatzResearch.WordTrace]
  refine ⟨131523485058900566324434007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87682323372600377549622671 131523485058900566324434007)
  ·
    refine ⟨197285227588350849486651011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131523485058900566324434007 197285227588350849486651011)
    ·
      refine ⟨295927841382526274229976517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197285227588350849486651011 295927841382526274229976517)
      ·
        refine ⟨55486470259223676418120597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 295927841382526274229976517 55486470259223676418120597)
        ·
          refine ⟨2600928293401109832099403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 55486470259223676418120597 2600928293401109832099403)
          ·
            refine ⟨3901392440101664748149105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2600928293401109832099403 3901392440101664748149105)
            ·
              refine ⟨2926044330076248561111829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3901392440101664748149105 2926044330076248561111829)
              ·
                refine ⟨137158327972324151302117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2926044330076248561111829 137158327972324151302117)
                ·
                  rfl

theorem cell22_3606051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 2, 6].length) (baseStart_3606051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3606051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3606051 prefixEnd_3606051 := by exact prefixLift 3606051
  have htrace : WordTrace (prefixWord ++ tailWord_3606051) baseStart_3606051 baseEnd_3606051 := by
    simpa [prefixWord, tailWord_3606051, baseEnd_3606051] using wordTrace_append hprefix tailTrace_3606051
  have hstable : (prefixWord ++ tailWord_3606051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606051).length < 2 ^ (prefixWord ++ tailWord_3606051).sum := by decide
  have hdescent : baseEnd_3606051 < baseStart_3606051 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606124 : List Nat := [2, 2, 1, 1, 3, 1, 1, 7, 4]
def baseStart_3606124 : Nat := 118140960795 + 3606124 * 2 ^ 59
def prefixEnd_3606124 : Nat := 4983230072969 + 3 ^ 40 * 3606124 * 2
def baseEnd_3606124 : Nat := 411483313714256501547943

theorem tailTrace_3606124 : CollatzResearch.WordTrace tailWord_3606124 prefixEnd_3606124 411483313714256501547943 := by
  unfold tailWord_3606124
  simp only [CollatzResearch.WordTrace]
  refine ⟨65763073793818049895920713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87684098391757399861227617 65763073793818049895920713)
  ·
    refine ⟨49322305345363537421940535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65763073793818049895920713 49322305345363537421940535)
    ·
      refine ⟨73983458018045306132910803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49322305345363537421940535 73983458018045306132910803)
      ·
        refine ⟨110975187027067959199366205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73983458018045306132910803 110975187027067959199366205)
        ·
          refine ⟨41615695135150484699762327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110975187027067959199366205 41615695135150484699762327)
          ·
            refine ⟨62423542702725727049643491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41615695135150484699762327 62423542702725727049643491)
            ·
              refine ⟨93635314054088590574465237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62423542702725727049643491 93635314054088590574465237)
              ·
                refine ⟨2194577673142701341589029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 93635314054088590574465237 2194577673142701341589029)
                ·
                  refine ⟨411483313714256501547943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2194577673142701341589029 411483313714256501547943)
                  ·
                    rfl

theorem cell22_3606124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 7, 4].length) (baseStart_3606124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3606124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3606124 prefixEnd_3606124 := by exact prefixLift 3606124
  have htrace : WordTrace (prefixWord ++ tailWord_3606124) baseStart_3606124 baseEnd_3606124 := by
    simpa [prefixWord, tailWord_3606124, baseEnd_3606124] using wordTrace_append hprefix tailTrace_3606124
  have hstable : (prefixWord ++ tailWord_3606124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606124).length < 2 ^ (prefixWord ++ tailWord_3606124).sum := by decide
  have hdescent : baseEnd_3606124 < baseStart_3606124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606141 : List Nat := [1, 4, 1, 1, 4, 2, 1, 4, 4]
def baseStart_3606141 : Nat := 118140960795 + 3606141 * 2 ^ 59
def prefixEnd_3606141 : Nat := 4983230072969 + 3 ^ 40 * 3606141 * 2
def baseEnd_3606141 : Nat := 411485253530062375656259

theorem tailTrace_3606141 : CollatzResearch.WordTrace tailWord_3606141 prefixEnd_3606141 411485253530062375656259 := by
  unfold tailWord_3606141
  simp only [CollatzResearch.WordTrace]
  refine ⟨131526767628574511695210277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87684511752383007796806851 131526767628574511695210277)
  ·
    refine ⟨24661268930357720942851927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131526767628574511695210277 24661268930357720942851927)
    ·
      refine ⟨36991903395536581414277891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24661268930357720942851927 36991903395536581414277891)
      ·
        refine ⟨55487855093304872121416837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36991903395536581414277891 55487855093304872121416837)
        ·
          refine ⟨10403972829994663522765657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55487855093304872121416837 10403972829994663522765657)
          ·
            refine ⟨7802979622495997642074243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10403972829994663522765657 7802979622495997642074243)
            ·
              refine ⟨11704469433743996463111365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7802979622495997642074243 11704469433743996463111365)
              ·
                refine ⟨2194588018826999336833381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11704469433743996463111365 2194588018826999336833381)
                ·
                  refine ⟨411485253530062375656259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2194588018826999336833381 411485253530062375656259)
                  ·
                    rfl

theorem cell22_3606141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 4, 4].length) (baseStart_3606141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3606141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3606141 prefixEnd_3606141 := by exact prefixLift 3606141
  have htrace : WordTrace (prefixWord ++ tailWord_3606141) baseStart_3606141 baseEnd_3606141 := by
    simpa [prefixWord, tailWord_3606141, baseEnd_3606141] using wordTrace_append hprefix tailTrace_3606141
  have hstable : (prefixWord ++ tailWord_3606141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606141).length < 2 ^ (prefixWord ++ tailWord_3606141).sum := by decide
  have hdescent : baseEnd_3606141 < baseStart_3606141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606259 : List Nat := [1, 1, 1, 2, 2, 3, 5, 1, 6]
def baseStart_3606259 : Nat := 118140960795 + 3606259 * 2 ^ 59
def prefixEnd_3606259 : Nat := 4983230072969 + 3 ^ 40 * 3606259 * 2
def baseEnd_3606259 : Nat := 411498718133891384172805

theorem tailTrace_3606259 : CollatzResearch.WordTrace tailWord_3606259 prefixEnd_3606259 411498718133891384172805 := by
  unfold tailWord_3606259
  simp only [CollatzResearch.WordTrace]
  refine ⟨131531071442147017848005831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87687380961431345232003887 131531071442147017848005831)
  ·
    refine ⟨197296607163220526772008747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131531071442147017848005831 197296607163220526772008747)
    ·
      refine ⟨295944910744830790158013121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197296607163220526772008747 295944910744830790158013121)
      ·
        refine ⟨221958683058623092618509841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295944910744830790158013121 221958683058623092618509841)
        ·
          refine ⟨166469012293967319463882381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221958683058623092618509841 166469012293967319463882381)
          ·
            refine ⟨62425879610237744798955893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166469012293967319463882381 62425879610237744798955893)
            ·
              refine ⟨5852426213459788574902115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62425879610237744798955893 5852426213459788574902115)
              ·
                refine ⟨8778639320189682862353173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5852426213459788574902115 8778639320189682862353173)
                ·
                  refine ⟨411498718133891384172805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8778639320189682862353173 411498718133891384172805)
                  ·
                    rfl

theorem cell22_3606259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 1, 6].length) (baseStart_3606259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3606259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3606259 prefixEnd_3606259 := by exact prefixLift 3606259
  have htrace : WordTrace (prefixWord ++ tailWord_3606259) baseStart_3606259 baseEnd_3606259 := by
    simpa [prefixWord, tailWord_3606259, baseEnd_3606259] using wordTrace_append hprefix tailTrace_3606259
  have hstable : (prefixWord ++ tailWord_3606259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606259).length < 2 ^ (prefixWord ++ tailWord_3606259).sum := by decide
  have hdescent : baseEnd_3606259 < baseStart_3606259 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606306 : List Nat := [3, 3, 1, 1, 2, 1, 1, 4, 2, 4]
def baseStart_3606306 : Nat := 118140960795 + 3606306 * 2 ^ 59
def prefixEnd_3606306 : Nat := 4983230072969 + 3 ^ 40 * 3606306 * 2
def baseEnd_3606306 : Nat := 1234512243462181696593271

theorem tailTrace_3606306 : CollatzResearch.WordTrace tailWord_3606306 prefixEnd_3606306 1234512243462181696593271 := by
  unfold tailWord_3606306
  simp only [CollatzResearch.WordTrace]
  refine ⟨32883196418244186218741693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87688523781984496583311181 32883196418244186218741693)
  ·
    refine ⟨12331198656841569832028135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32883196418244186218741693 12331198656841569832028135)
    ·
      refine ⟨18496797985262354748042203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12331198656841569832028135 18496797985262354748042203)
      ·
        refine ⟨27745196977893532122063305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18496797985262354748042203 27745196977893532122063305)
        ·
          refine ⟨20808897733420149091547479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27745196977893532122063305 20808897733420149091547479)
          ·
            refine ⟨31213346600130223637321219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20808897733420149091547479 31213346600130223637321219)
            ·
              refine ⟨46820019900195335455981829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31213346600130223637321219 46820019900195335455981829)
              ·
                refine ⟨8778753731286625397996593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46820019900195335455981829 8778753731286625397996593)
                ·
                  refine ⟨6584065298464969048497445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8778753731286625397996593 6584065298464969048497445)
                  ·
                    refine ⟨1234512243462181696593271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6584065298464969048497445 1234512243462181696593271)
                    ·
                      rfl

theorem cell22_3606306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_3606306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3606306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3606306 prefixEnd_3606306 := by exact prefixLift 3606306
  have htrace : WordTrace (prefixWord ++ tailWord_3606306) baseStart_3606306 baseEnd_3606306 := by
    simpa [prefixWord, tailWord_3606306, baseEnd_3606306] using wordTrace_append hprefix tailTrace_3606306
  have hstable : (prefixWord ++ tailWord_3606306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606306).length < 2 ^ (prefixWord ++ tailWord_3606306).sum := by decide
  have hdescent : baseEnd_3606306 < baseStart_3606306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606308 : List Nat := [2, 3, 1, 3, 2, 1, 1, 4, 2, 3]
def baseStart_3606308 : Nat := 118140960795 + 3606308 * 2 ^ 59
def prefixEnd_3606308 : Nat := 4983230072969 + 3 ^ 40 * 3606308 * 2
def baseEnd_3606308 : Nat := 1234512928103054358043265

theorem tailTrace_3606308 : CollatzResearch.WordTrace tailWord_3606308 prefixEnd_3606308 1234512928103054358043265 := by
  unfold tailWord_3606308
  simp only [CollatzResearch.WordTrace]
  refine ⟨65766429309484749608269789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87688572412646332811026385 65766429309484749608269789)
  ·
    refine ⟨24662410991056781103101171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65766429309484749608269789 24662410991056781103101171)
    ·
      refine ⟨36993616486585171654651757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24662410991056781103101171 36993616486585171654651757)
      ·
        refine ⟨13872606182469439370494409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36993616486585171654651757 13872606182469439370494409)
        ·
          refine ⟨10404454636852079527870807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13872606182469439370494409 10404454636852079527870807)
          ·
            refine ⟨15606681955278119291806211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10404454636852079527870807 15606681955278119291806211)
            ·
              refine ⟨23410022932917178937709317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15606681955278119291806211 23410022932917178937709317)
              ·
                refine ⟨4389379299921971050820497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23410022932917178937709317 4389379299921971050820497)
                ·
                  refine ⟨3292034474941478288115373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4389379299921971050820497 3292034474941478288115373)
                  ·
                    refine ⟨1234512928103054358043265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3292034474941478288115373 1234512928103054358043265)
                    ·
                      rfl

theorem cell22_3606308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 4, 2, 3].length) (baseStart_3606308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3606308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3606308 prefixEnd_3606308 := by exact prefixLift 3606308
  have htrace : WordTrace (prefixWord ++ tailWord_3606308) baseStart_3606308 baseEnd_3606308 := by
    simpa [prefixWord, tailWord_3606308, baseEnd_3606308] using wordTrace_append hprefix tailTrace_3606308
  have hstable : (prefixWord ++ tailWord_3606308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606308).length < 2 ^ (prefixWord ++ tailWord_3606308).sum := by decide
  have hdescent : baseEnd_3606308 < baseStart_3606308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606321 : List Nat := [1, 2, 2, 3, 2, 4, 1, 7]
def baseStart_3606321 : Nat := 118140960795 + 3606321 * 2 ^ 59
def prefixEnd_3606321 : Nat := 4983230072969 + 3 ^ 40 * 3606321 * 2
def baseEnd_3606321 : Nat := 137168597585414073052025

theorem tailTrace_3606321 : CollatzResearch.WordTrace tailWord_3606321 prefixEnd_3606321 137168597585414073052025 := by
  unfold tailWord_3606321
  simp only [CollatzResearch.WordTrace]
  refine ⟨131533332767922402436762817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87688888511948268291175211 131533332767922402436762817)
  ·
    refine ⟨98649999575941801827572113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131533332767922402436762817 98649999575941801827572113)
    ·
      refine ⟨73987499681956351370679085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98649999575941801827572113 73987499681956351370679085)
      ·
        refine ⟨27745312380733631764004657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73987499681956351370679085 27745312380733631764004657)
        ·
          refine ⟨20808984285550223823003493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27745312380733631764004657 20808984285550223823003493)
          ·
            refine ⟨3901684553540666966813155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20808984285550223823003493 3901684553540666966813155)
            ·
              refine ⟨5852526830311000450219733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3901684553540666966813155 5852526830311000450219733)
              ·
                refine ⟨137168597585414073052025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5852526830311000450219733 137168597585414073052025)
                ·
                  rfl

theorem cell22_3606321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 7].length) (baseStart_3606321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3606321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3606321 prefixEnd_3606321 := by exact prefixLift 3606321
  have htrace : WordTrace (prefixWord ++ tailWord_3606321) baseStart_3606321 baseEnd_3606321 := by
    simpa [prefixWord, tailWord_3606321, baseEnd_3606321] using wordTrace_append hprefix tailTrace_3606321
  have hstable : (prefixWord ++ tailWord_3606321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606321).length < 2 ^ (prefixWord ++ tailWord_3606321).sum := by decide
  have hdescent : baseEnd_3606321 < baseStart_3606321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606370 : List Nat := [3, 3, 2, 1, 2, 2, 2, 1, 3, 3]
def baseStart_3606370 : Nat := 118140960795 + 3606370 * 2 ^ 59
def prefixEnd_3606370 : Nat := 4983230072969 + 3 ^ 40 * 3606370 * 2
def baseEnd_3606370 : Nat := 1234534151970106862993075

theorem tailTrace_3606370 : CollatzResearch.WordTrace tailWord_3606370 prefixEnd_3606370 1234534151970106862993075 := by
  unfold tailWord_3606370
  simp only [CollatzResearch.WordTrace]
  refine ⟨32883779986186220951324141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87690079963163255870197709 32883779986186220951324141)
  ·
    refine ⟨12331417494819832856746553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32883779986186220951324141 12331417494819832856746553)
    ·
      refine ⟨9248563121114874642559915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12331417494819832856746553 9248563121114874642559915)
      ·
        refine ⟨13872844681672311963839873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9248563121114874642559915 13872844681672311963839873)
        ·
          refine ⟨10404633511254233972879905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13872844681672311963839873 10404633511254233972879905)
          ·
            refine ⟨7803475133440675479659929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10404633511254233972879905 7803475133440675479659929)
            ·
              refine ⟨5852606350080506609744947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7803475133440675479659929 5852606350080506609744947)
              ·
                refine ⟨8778909525120759914617421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5852606350080506609744947 8778909525120759914617421)
                ·
                  refine ⟨3292091071920284967981533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8778909525120759914617421 3292091071920284967981533)
                  ·
                    refine ⟨1234534151970106862993075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3292091071920284967981533 1234534151970106862993075)
                    ·
                      rfl

theorem cell22_3606370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_3606370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3606370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3606370 prefixEnd_3606370 := by exact prefixLift 3606370
  have htrace : WordTrace (prefixWord ++ tailWord_3606370) baseStart_3606370 baseEnd_3606370 := by
    simpa [prefixWord, tailWord_3606370, baseEnd_3606370] using wordTrace_append hprefix tailTrace_3606370
  have hstable : (prefixWord ++ tailWord_3606370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606370).length < 2 ^ (prefixWord ++ tailWord_3606370).sum := by decide
  have hdescent : baseEnd_3606370 < baseStart_3606370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606381 : List Nat := [1, 5, 1, 1, 1, 1, 4, 1, 2, 5]
def baseStart_3606381 : Nat := 118140960795 + 3606381 * 2 ^ 59
def prefixEnd_3606381 : Nat := 4983230072969 + 3 ^ 40 * 3606381 * 2
def baseEnd_3606381 : Nat := 1234537917494906500968041

theorem tailTrace_3606381 : CollatzResearch.WordTrace tailWord_3606381 prefixEnd_3606381 1234537917494906500968041 := by
  unfold tailWord_3606381
  simp only [CollatzResearch.WordTrace]
  refine ⟨131535521147705032683946997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87690347431803355122631331 131535521147705032683946997)
  ·
    refine ⟨12331455107597346814120031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 131535521147705032683946997 12331455107597346814120031)
    ·
      refine ⟨18497182661396020221180047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12331455107597346814120031 18497182661396020221180047)
      ·
        refine ⟨27745773992094030331770071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18497182661396020221180047 27745773992094030331770071)
        ·
          refine ⟨41618660988141045497655107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27745773992094030331770071 41618660988141045497655107)
          ·
            refine ⟨62427991482211568246482661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41618660988141045497655107 62427991482211568246482661)
            ·
              refine ⟨11705248402914669046215499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62427991482211568246482661 11705248402914669046215499)
              ·
                refine ⟨17557872604372003569323249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11705248402914669046215499 17557872604372003569323249)
                ·
                  refine ⟨13168404453279002676992437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17557872604372003569323249 13168404453279002676992437)
                  ·
                    refine ⟨1234537917494906500968041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13168404453279002676992437 1234537917494906500968041)
                    ·
                      rfl

theorem cell22_3606381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_3606381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3606381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3606381 prefixEnd_3606381 := by exact prefixLift 3606381
  have htrace : WordTrace (prefixWord ++ tailWord_3606381) baseStart_3606381 baseEnd_3606381 := by
    simpa [prefixWord, tailWord_3606381, baseEnd_3606381] using wordTrace_append hprefix tailTrace_3606381
  have hstable : (prefixWord ++ tailWord_3606381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606381).length < 2 ^ (prefixWord ++ tailWord_3606381).sum := by decide
  have hdescent : baseEnd_3606381 < baseStart_3606381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606428 : List Nat := [2, 2, 3, 3, 1, 1, 3, 1, 6]
def baseStart_3606428 : Nat := 118140960795 + 3606428 * 2 ^ 59
def prefixEnd_3606428 : Nat := 4983230072969 + 3 ^ 40 * 3606428 * 2
def baseEnd_3606428 : Nat := 411518002185138015014299

theorem tailTrace_3606428 : CollatzResearch.WordTrace tailWord_3606428 prefixEnd_3606428 411518002185138015014299 := by
  unfold tailWord_3606428
  simp only [CollatzResearch.WordTrace]
  refine ⟨65768617689267379855453969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87691490252356506473938625 65768617689267379855453969)
  ·
    refine ⟨49326463266950534891590477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65768617689267379855453969 49326463266950534891590477)
    ·
      refine ⟨18497423725106450584346429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49326463266950534891590477 18497423725106450584346429)
      ·
        refine ⟨6936533896914918969129911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18497423725106450584346429 6936533896914918969129911)
        ·
          refine ⟨10404800845372378453694867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6936533896914918969129911 10404800845372378453694867)
          ·
            refine ⟨15607201268058567680542301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10404800845372378453694867 15607201268058567680542301)
            ·
              refine ⟨5852700475521962880203363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15607201268058567680542301 5852700475521962880203363)
              ·
                refine ⟨8779050713282944320305045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5852700475521962880203363 8779050713282944320305045)
                ·
                  refine ⟨411518002185138015014299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8779050713282944320305045 411518002185138015014299)
                  ·
                    rfl

theorem cell22_3606428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 1, 6].length) (baseStart_3606428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3606428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3606428 prefixEnd_3606428 := by exact prefixLift 3606428
  have htrace : WordTrace (prefixWord ++ tailWord_3606428) baseStart_3606428 baseEnd_3606428 := by
    simpa [prefixWord, tailWord_3606428, baseEnd_3606428] using wordTrace_append hprefix tailTrace_3606428
  have hstable : (prefixWord ++ tailWord_3606428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606428).length < 2 ^ (prefixWord ++ tailWord_3606428).sum := by decide
  have hdescent : baseEnd_3606428 < baseStart_3606428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606460 : List Nat := [2, 2, 2, 5, 1, 1, 1, 2, 1, 5]
def baseStart_3606460 : Nat := 118140960795 + 3606460 * 2 ^ 59
def prefixEnd_3606460 : Nat := 4983230072969 + 3 ^ 40 * 3606460 * 2
def baseEnd_3606460 : Nat := 1234564960809376628242799

theorem tailTrace_3606460 : CollatzResearch.WordTrace tailWord_3606460 prefixEnd_3606460 1234564960809376628242799 := by
  unfold tailWord_3606460
  simp only [CollatzResearch.WordTrace]
  refine ⟨65769201257209414588036417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87692268342945886117381889 65769201257209414588036417)
  ·
    refine ⟨49326900942907060941027313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65769201257209414588036417 49326900942907060941027313)
    ·
      refine ⟨36995175707180295705770485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49326900942907060941027313 36995175707180295705770485)
      ·
        refine ⟨3468297722548152722415983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36995175707180295705770485 3468297722548152722415983)
        ·
          refine ⟨5202446583822229083623975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3468297722548152722415983 5202446583822229083623975)
          ·
            refine ⟨7803669875733343625435963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5202446583822229083623975 7803669875733343625435963)
            ·
              refine ⟨11705504813600015438153945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7803669875733343625435963 11705504813600015438153945)
              ·
                refine ⟨8779128610200011578615459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11705504813600015438153945 8779128610200011578615459)
                ·
                  refine ⟨13168692915300017367923189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8779128610200011578615459 13168692915300017367923189)
                  ·
                    refine ⟨1234564960809376628242799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13168692915300017367923189 1234564960809376628242799)
                    ·
                      rfl

theorem cell22_3606460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 2, 1, 5].length) (baseStart_3606460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3606460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3606460 prefixEnd_3606460 := by exact prefixLift 3606460
  have htrace : WordTrace (prefixWord ++ tailWord_3606460) baseStart_3606460 baseEnd_3606460 := by
    simpa [prefixWord, tailWord_3606460, baseEnd_3606460] using wordTrace_append hprefix tailTrace_3606460
  have hstable : (prefixWord ++ tailWord_3606460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606460).length < 2 ^ (prefixWord ++ tailWord_3606460).sum := by decide
  have hdescent : baseEnd_3606460 < baseStart_3606460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606488 : List Nat := [2, 1, 2, 2, 2, 2, 2, 3, 3, 3]
def baseStart_3606488 : Nat := 118140960795 + 3606488 * 2 ^ 59
def prefixEnd_3606488 : Nat := 4983230072969 + 3 ^ 40 * 3606488 * 2
def baseEnd_3606488 : Nat := 1234574545781593888542713

theorem tailTrace_3606488 : CollatzResearch.WordTrace tailWord_3606488 prefixEnd_3606488 1234574545781593888542713 := by
  unfold tailWord_3606488
  simp only [CollatzResearch.WordTrace]
  refine ⟨65769711879158694979046059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87692949172211593305394745 65769711879158694979046059)
  ·
    refine ⟨98654567818738042468569089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65769711879158694979046059 98654567818738042468569089)
    ·
      refine ⟨73990925864053531851426817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98654567818738042468569089 73990925864053531851426817)
      ·
        refine ⟨55493194398040148888570113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73990925864053531851426817 55493194398040148888570113)
        ·
          refine ⟨41619895798530111666427585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55493194398040148888570113 41619895798530111666427585)
          ·
            refine ⟨31214921848897583749820689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41619895798530111666427585 31214921848897583749820689)
            ·
              refine ⟨23411191386673187812365517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31214921848897583749820689 23411191386673187812365517)
              ·
                refine ⟨8779196770002445429637069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23411191386673187812365517 8779196770002445429637069)
                ·
                  refine ⟨3292198788750917036113901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8779196770002445429637069 3292198788750917036113901)
                  ·
                    refine ⟨1234574545781593888542713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3292198788750917036113901 1234574545781593888542713)
                    ·
                      rfl

theorem cell22_3606488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 3, 3, 3].length) (baseStart_3606488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3606488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3606488 prefixEnd_3606488 := by exact prefixLift 3606488
  have htrace : WordTrace (prefixWord ++ tailWord_3606488) baseStart_3606488 baseEnd_3606488 := by
    simpa [prefixWord, tailWord_3606488, baseEnd_3606488] using wordTrace_append hprefix tailTrace_3606488
  have hstable : (prefixWord ++ tailWord_3606488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606488).length < 2 ^ (prefixWord ++ tailWord_3606488).sum := by decide
  have hdescent : baseEnd_3606488 < baseStart_3606488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606490 : List Nat := [3, 1, 1, 2, 6, 1, 1, 7]
def baseStart_3606490 : Nat := 118140960795 + 3606490 * 2 ^ 59
def prefixEnd_3606490 : Nat := 4983230072969 + 3 ^ 40 * 3606490 * 2
def baseEnd_3606490 : Nat := 137175025602496283332523

theorem tailTrace_3606490 : CollatzResearch.WordTrace tailWord_3606490 prefixEnd_3606490 137175025602496283332523 := by
  unfold tailWord_3606490
  simp only [CollatzResearch.WordTrace]
  refine ⟨32884874176077536074916231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87692997802873429533109949 32884874176077536074916231)
  ·
    refine ⟨49327311264116304112374347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32884874176077536074916231 49327311264116304112374347)
    ·
      refine ⟨73990966896174456168561521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49327311264116304112374347 73990966896174456168561521)
      ·
        refine ⟨55493225172130842126421141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73990966896174456168561521 55493225172130842126421141)
        ·
          refine ⟨2601244929943633224675991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 55493225172130842126421141 2601244929943633224675991)
          ·
            refine ⟨3901867394915449837013987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2601244929943633224675991 3901867394915449837013987)
            ·
              refine ⟨5852801092373174755520981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3901867394915449837013987 5852801092373174755520981)
              ·
                refine ⟨137175025602496283332523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5852801092373174755520981 137175025602496283332523)
                ·
                  rfl

theorem cell22_3606490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 7].length) (baseStart_3606490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3606490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3606490 prefixEnd_3606490 := by exact prefixLift 3606490
  have htrace : WordTrace (prefixWord ++ tailWord_3606490) baseStart_3606490 baseEnd_3606490 := by
    simpa [prefixWord, tailWord_3606490, baseEnd_3606490] using wordTrace_append hprefix tailTrace_3606490
  have hstable : (prefixWord ++ tailWord_3606490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606490).length < 2 ^ (prefixWord ++ tailWord_3606490).sum := by decide
  have hdescent : baseEnd_3606490 < baseStart_3606490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606509 : List Nat := [1, 5, 1, 4, 2, 1, 1, 1, 2, 4]
def baseStart_3606509 : Nat := 118140960795 + 3606509 * 2 ^ 59
def prefixEnd_3606509 : Nat := 4983230072969 + 3 ^ 40 * 3606509 * 2
def baseEnd_3606509 : Nat := 1234581734510756833767649

theorem tailTrace_3606509 : CollatzResearch.WordTrace tailWord_3606509 prefixEnd_3606509 1234581734510756833767649 := by
  unfold tailWord_3606509
  simp only [CollatzResearch.WordTrace]
  refine ⟨131540189691241310544606581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87693459794160873696404387 131540189691241310544606581)
  ·
    refine ⟨12331892783553872863556867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 131540189691241310544606581 12331892783553872863556867)
    ·
      refine ⟨18497839175330809295335301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12331892783553872863556867 18497839175330809295335301)
      ·
        refine ⟨3468344845374526742875369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18497839175330809295335301 3468344845374526742875369)
        ·
          refine ⟨2601258634030895057156527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3468344845374526742875369 2601258634030895057156527)
          ·
            refine ⟨3901887951046342585734791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2601258634030895057156527 3901887951046342585734791)
            ·
              refine ⟨5852831926569513878602187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3901887951046342585734791 5852831926569513878602187)
              ·
                refine ⟨8779247889854270817903281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5852831926569513878602187 8779247889854270817903281)
                ·
                  refine ⟨6584435917390703113427461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8779247889854270817903281 6584435917390703113427461)
                  ·
                    refine ⟨1234581734510756833767649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6584435917390703113427461 1234581734510756833767649)
                    ·
                      rfl

theorem cell22_3606509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 1, 2, 4].length) (baseStart_3606509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3606509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3606509 prefixEnd_3606509 := by exact prefixLift 3606509
  have htrace : WordTrace (prefixWord ++ tailWord_3606509) baseStart_3606509 baseEnd_3606509 := by
    simpa [prefixWord, tailWord_3606509, baseEnd_3606509] using wordTrace_append hprefix tailTrace_3606509
  have hstable : (prefixWord ++ tailWord_3606509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606509).length < 2 ^ (prefixWord ++ tailWord_3606509).sum := by decide
  have hdescent : baseEnd_3606509 < baseStart_3606509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606535 : List Nat := [1, 1, 4, 3, 1, 4, 1, 2, 5]
def baseStart_3606535 : Nat := 118140960795 + 3606535 * 2 ^ 59
def prefixEnd_3606535 : Nat := 4983230072969 + 3 ^ 40 * 3606535 * 2
def baseEnd_3606535 : Nat := 411530211614033810872523

theorem tailTrace_3606535 : CollatzResearch.WordTrace tailWord_3606535 prefixEnd_3606535 411530211614033810872523 := by
  unfold tailWord_3606535
  simp only [CollatzResearch.WordTrace]
  refine ⟨131541137989147116985053059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87694091992764744656702039 131541137989147116985053059)
  ·
    refine ⟨197311706983720675477579589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131541137989147116985053059 197311706983720675477579589)
    ·
      refine ⟨36995945059447626652046173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 197311706983720675477579589 36995945059447626652046173)
      ·
        refine ⟨13873479397292859994517315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36995945059447626652046173 13873479397292859994517315)
        ·
          refine ⟨20810219095939289991775973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13873479397292859994517315 20810219095939289991775973)
          ·
            refine ⟨3901916080488616873457995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20810219095939289991775973 3901916080488616873457995)
            ·
              refine ⟨5852874120732925310186993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3901916080488616873457995 5852874120732925310186993)
              ·
                refine ⟨4389655590549693982640245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5852874120732925310186993 4389655590549693982640245)
                ·
                  refine ⟨411530211614033810872523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4389655590549693982640245 411530211614033810872523)
                  ·
                    rfl

theorem cell22_3606535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 2, 5].length) (baseStart_3606535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3606535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3606535 prefixEnd_3606535 := by exact prefixLift 3606535
  have htrace : WordTrace (prefixWord ++ tailWord_3606535) baseStart_3606535 baseEnd_3606535 := by
    simpa [prefixWord, tailWord_3606535, baseEnd_3606535] using wordTrace_append hprefix tailTrace_3606535
  have hstable : (prefixWord ++ tailWord_3606535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606535).length < 2 ^ (prefixWord ++ tailWord_3606535).sum := by decide
  have hdescent : baseEnd_3606535 < baseStart_3606535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606565 : List Nat := [1, 3, 1, 2, 2, 4, 2, 2, 1, 4]
def baseStart_3606565 : Nat := 118140960795 + 3606565 * 2 ^ 59
def prefixEnd_3606565 : Nat := 4983230072969 + 3 ^ 40 * 3606565 * 2
def baseEnd_3606565 : Nat := 1234600904455191354367477

theorem tailTrace_3606565 : CollatzResearch.WordTrace tailWord_3606565 prefixEnd_3606565 1234600904455191354367477 := by
  unfold tailWord_3606565
  simp only [CollatzResearch.WordTrace]
  refine ⟨131542232179038432108645149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87694821452692288072430099 131542232179038432108645149)
  ·
    refine ⟨49328337067139412040741931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131542232179038432108645149 49328337067139412040741931)
    ·
      refine ⟨73992505600709118061112897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49328337067139412040741931 73992505600709118061112897)
      ·
        refine ⟨55494379200531838545834673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73992505600709118061112897 55494379200531838545834673)
        ·
          refine ⟨41620784400398878909376005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55494379200531838545834673 41620784400398878909376005)
          ·
            refine ⟨7803897075074789795508001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41620784400398878909376005 7803897075074789795508001)
            ·
              refine ⟨5852922806306092346631001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7803897075074789795508001 5852922806306092346631001)
              ·
                refine ⟨4389692104729569259973251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5852922806306092346631001 4389692104729569259973251)
                ·
                  refine ⟨6584538157094353889959877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4389692104729569259973251 6584538157094353889959877)
                  ·
                    refine ⟨1234600904455191354367477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6584538157094353889959877 1234600904455191354367477)
                    ·
                      rfl

theorem cell22_3606565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 2, 1, 4].length) (baseStart_3606565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3606565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3606565 prefixEnd_3606565 := by exact prefixLift 3606565
  have htrace : WordTrace (prefixWord ++ tailWord_3606565) baseStart_3606565 baseEnd_3606565 := by
    simpa [prefixWord, tailWord_3606565, baseEnd_3606565] using wordTrace_append hprefix tailTrace_3606565
  have hstable : (prefixWord ++ tailWord_3606565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606565).length < 2 ^ (prefixWord ++ tailWord_3606565).sum := by decide
  have hdescent : baseEnd_3606565 < baseStart_3606565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606591 : List Nat := [1, 1, 2, 2, 3, 1, 12]
def baseStart_3606591 : Nat := 118140960795 + 3606591 * 2 ^ 59
def prefixEnd_3606591 : Nat := 4983230072969 + 3 ^ 40 * 3606591 * 2
def baseEnd_3606591 : Nat := 45726289066167998267311

theorem tailTrace_3606591 : CollatzResearch.WordTrace tailWord_3606591 prefixEnd_3606591 45726289066167998267311 := by
  unfold tailWord_3606591
  simp only [CollatzResearch.WordTrace]
  refine ⟨131543180476944238549091627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87695453651296159032727751 131543180476944238549091627)
  ·
    refine ⟨197314770715416357823637441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131543180476944238549091627 197314770715416357823637441)
    ·
      refine ⟨147986078036562268367728081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197314770715416357823637441 147986078036562268367728081)
      ·
        refine ⟨110989558527421701275796061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147986078036562268367728081 110989558527421701275796061)
        ·
          refine ⟨41621084447783137978423523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110989558527421701275796061 41621084447783137978423523)
          ·
            refine ⟨62431626671674706967635285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41621084447783137978423523 62431626671674706967635285)
            ·
              refine ⟨45726289066167998267311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 62431626671674706967635285 45726289066167998267311)
              ·
                rfl

theorem cell22_3606591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 12].length) (baseStart_3606591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3606591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3606591 prefixEnd_3606591 := by exact prefixLift 3606591
  have htrace : WordTrace (prefixWord ++ tailWord_3606591) baseStart_3606591 baseEnd_3606591 := by
    simpa [prefixWord, tailWord_3606591, baseEnd_3606591] using wordTrace_append hprefix tailTrace_3606591
  have hstable : (prefixWord ++ tailWord_3606591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606591).length < 2 ^ (prefixWord ++ tailWord_3606591).sum := by decide
  have hdescent : baseEnd_3606591 < baseStart_3606591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606683 : List Nat := [1, 1, 1, 1, 1, 1, 2, 7, 3, 4]
def baseStart_3606683 : Nat := 118140960795 + 3606683 * 2 ^ 59
def prefixEnd_3606683 : Nat := 4983230072969 + 3 ^ 40 * 3606683 * 2
def baseEnd_3606683 : Nat := 1234641298266678379917115

theorem tailTrace_3606683 : CollatzResearch.WordTrace tailWord_3606683 prefixEnd_3606683 1234641298266678379917115 := by
  unfold tailWord_3606683
  simp only [CollatzResearch.WordTrace]
  refine ⟨131546535992610938261440703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87697690661740625507627135 131546535992610938261440703)
  ·
    refine ⟨197319803988916407392161055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131546535992610938261440703 197319803988916407392161055)
    ·
      refine ⟨295979705983374611088241583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197319803988916407392161055 295979705983374611088241583)
      ·
        refine ⟨443969558975061916632362375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295979705983374611088241583 443969558975061916632362375)
        ·
          refine ⟨665954338462592874948543563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443969558975061916632362375 665954338462592874948543563)
          ·
            refine ⟨998931507693889312422815345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 665954338462592874948543563 998931507693889312422815345)
            ·
              refine ⟨749198630770416984317111509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 998931507693889312422815345 749198630770416984317111509)
              ·
                refine ⟨17559342908681648069932301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 749198630770416984317111509 17559342908681648069932301)
                ·
                  refine ⟨6584753590755618026224613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17559342908681648069932301 6584753590755618026224613)
                  ·
                    refine ⟨1234641298266678379917115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6584753590755618026224613 1234641298266678379917115)
                    ·
                      rfl

theorem cell22_3606683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 3, 4].length) (baseStart_3606683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3606683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3606683 prefixEnd_3606683 := by exact prefixLift 3606683
  have htrace : WordTrace (prefixWord ++ tailWord_3606683) baseStart_3606683 baseEnd_3606683 := by
    simpa [prefixWord, tailWord_3606683, baseEnd_3606683] using wordTrace_append hprefix tailTrace_3606683
  have hstable : (prefixWord ++ tailWord_3606683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606683).length < 2 ^ (prefixWord ++ tailWord_3606683).sum := by decide
  have hdescent : baseEnd_3606683 < baseStart_3606683 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606708 : List Nat := [2, 5, 3, 1, 1, 1, 2, 1, 3, 3]
def baseStart_3606708 : Nat := 118140960795 + 3606708 * 2 ^ 59
def prefixEnd_3606708 : Nat := 4983230072969 + 3 ^ 40 * 3606708 * 2
def baseEnd_3606708 : Nat := 1234649856277586648042039

theorem tailTrace_3606708 : CollatzResearch.WordTrace tailWord_3606708 prefixEnd_3606708 1234649856277586648042039 := by
  unfold tailWord_3606708
  simp only [CollatzResearch.WordTrace]
  refine ⟨65773723908760183765550389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87698298545013578354067185 65773723908760183765550389)
  ·
    refine ⟨6166286616446267228020349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65773723908760183765550389 6166286616446267228020349)
    ·
      refine ⟨2312357481167350210507631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6166286616446267228020349 2312357481167350210507631)
      ·
        refine ⟨3468536221751025315761447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2312357481167350210507631 3468536221751025315761447)
        ·
          refine ⟨5202804332626537973642171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3468536221751025315761447 5202804332626537973642171)
          ·
            refine ⟨7804206498939806960463257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5202804332626537973642171 7804206498939806960463257)
            ·
              refine ⟨5853154874204855220347443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7804206498939806960463257 5853154874204855220347443)
              ·
                refine ⟨8779732311307282830521165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5853154874204855220347443 8779732311307282830521165)
                ·
                  refine ⟨3292399616740231061445437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8779732311307282830521165 3292399616740231061445437)
                  ·
                    refine ⟨1234649856277586648042039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3292399616740231061445437 1234649856277586648042039)
                    ·
                      rfl

theorem cell22_3606708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_3606708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3606708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3606708 prefixEnd_3606708 := by exact prefixLift 3606708
  have htrace : WordTrace (prefixWord ++ tailWord_3606708) baseStart_3606708 baseEnd_3606708 := by
    simpa [prefixWord, tailWord_3606708, baseEnd_3606708] using wordTrace_append hprefix tailTrace_3606708
  have hstable : (prefixWord ++ tailWord_3606708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606708).length < 2 ^ (prefixWord ++ tailWord_3606708).sum := by decide
  have hdescent : baseEnd_3606708 < baseStart_3606708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606715 : List Nat := [1, 1, 1, 1, 1, 2, 5, 6, 4]
def baseStart_3606715 : Nat := 118140960795 + 3606715 * 2 ^ 59
def prefixEnd_3606715 : Nat := 4983230072969 + 3 ^ 40 * 3606715 * 2
def baseEnd_3606715 : Nat := 411550750840213654372339

theorem tailTrace_3606715 : CollatzResearch.WordTrace tailWord_3606715 prefixEnd_3606715 411550750840213654372339 := by
  unfold tailWord_3606715
  simp only [CollatzResearch.WordTrace]
  refine ⟨131547703128495007726605599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87698468752330005151070399 131547703128495007726605599)
  ·
    refine ⟨197321554692742511589908399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131547703128495007726605599 197321554692742511589908399)
    ·
      refine ⟨295982332039113767384862599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197321554692742511589908399 295982332039113767384862599)
      ·
        refine ⟨443973498058670651077293899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295982332039113767384862599 443973498058670651077293899)
        ·
          refine ⟨665960247088005976615940849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443973498058670651077293899 665960247088005976615940849)
          ·
            refine ⟨499470185316004482461955637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 665960247088005976615940849 499470185316004482461955637)
            ·
              refine ⟨46825329873375420230808341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 499470185316004482461955637 46825329873375420230808341)
              ·
                refine ⟨2194937337814472823319141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 46825329873375420230808341 2194937337814472823319141)
                ·
                  refine ⟨411550750840213654372339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2194937337814472823319141 411550750840213654372339)
                  ·
                    rfl

theorem cell22_3606715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 6, 4].length) (baseStart_3606715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3606715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3606715 prefixEnd_3606715 := by exact prefixLift 3606715
  have htrace : WordTrace (prefixWord ++ tailWord_3606715) baseStart_3606715 baseEnd_3606715 := by
    simpa [prefixWord, tailWord_3606715, baseEnd_3606715] using wordTrace_append hprefix tailTrace_3606715
  have hstable : (prefixWord ++ tailWord_3606715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606715).length < 2 ^ (prefixWord ++ tailWord_3606715).sum := by decide
  have hdescent : baseEnd_3606715 < baseStart_3606715 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606749 : List Nat := [1, 4, 3, 2, 1, 1, 3, 3, 4]
def baseStart_3606749 : Nat := 118140960795 + 3606749 * 2 ^ 59
def prefixEnd_3606749 : Nat := 4983230072969 + 3 ^ 40 * 3606749 * 2
def baseEnd_3606749 : Nat := 411554630471825402588971

theorem tailTrace_3606749 : CollatzResearch.WordTrace tailWord_3606749 prefixEnd_3606749 411554630471825402588971 := by
  unfold tailWord_3606749
  simp only [CollatzResearch.WordTrace]
  refine ⟨131548943210371831533343301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87699295473581221022228867 131548943210371831533343301)
  ·
    refine ⟨24665426851944718412501869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131548943210371831533343301 24665426851944718412501869)
    ·
      refine ⟨9249535069479269404688201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24665426851944718412501869 9249535069479269404688201)
      ·
        refine ⟨6937151302109452053516151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9249535069479269404688201 6937151302109452053516151)
        ·
          refine ⟨10405726953164178080274227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6937151302109452053516151 10405726953164178080274227)
          ·
            refine ⟨15608590429746267120411341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10405726953164178080274227 15608590429746267120411341)
            ·
              refine ⟨5853221411154850170154253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15608590429746267120411341 5853221411154850170154253)
              ·
                refine ⟨2194958029183068813807845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5853221411154850170154253 2194958029183068813807845)
                ·
                  refine ⟨411554630471825402588971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2194958029183068813807845 411554630471825402588971)
                  ·
                    rfl

theorem cell22_3606749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 3, 4].length) (baseStart_3606749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3606749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3606749 prefixEnd_3606749 := by exact prefixLift 3606749
  have htrace : WordTrace (prefixWord ++ tailWord_3606749) baseStart_3606749 baseEnd_3606749 := by
    simpa [prefixWord, tailWord_3606749, baseEnd_3606749] using wordTrace_append hprefix tailTrace_3606749
  have hstable : (prefixWord ++ tailWord_3606749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606749).length < 2 ^ (prefixWord ++ tailWord_3606749).sum := by decide
  have hdescent : baseEnd_3606749 < baseStart_3606749 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606760 : List Nat := [2, 1, 4, 1, 2, 4, 8]
def baseStart_3606760 : Nat := 118140960795 + 3606760 * 2 ^ 59
def prefixEnd_3606760 : Nat := 4983230072969 + 3 ^ 40 * 3606760 * 2
def baseEnd_3606760 : Nat := 45728431738528735027477

theorem tailTrace_3606760 : CollatzResearch.WordTrace tailWord_3606760 prefixEnd_3606760 45728431738528735027477 := by
  unfold tailWord_3606760
  simp only [CollatzResearch.WordTrace]
  refine ⟨65774672206665990205996867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87699562942221320274662489 65774672206665990205996867)
  ·
    refine ⟨98662008309998985308995301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65774672206665990205996867 98662008309998985308995301)
    ·
      refine ⟨18499126558124809745436619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98662008309998985308995301 18499126558124809745436619)
      ·
        refine ⟨27748689837187214618154929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18499126558124809745436619 27748689837187214618154929)
        ·
          refine ⟨20811517377890410963616197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27748689837187214618154929 20811517377890410963616197)
          ·
            refine ⟨3902159508354452055678037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20811517377890410963616197 3902159508354452055678037)
            ·
              refine ⟨45728431738528735027477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3902159508354452055678037 45728431738528735027477)
              ·
                rfl

theorem cell22_3606760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 8].length) (baseStart_3606760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3606760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3606760 prefixEnd_3606760 := by exact prefixLift 3606760
  have htrace : WordTrace (prefixWord ++ tailWord_3606760) baseStart_3606760 baseEnd_3606760 := by
    simpa [prefixWord, tailWord_3606760, baseEnd_3606760] using wordTrace_append hprefix tailTrace_3606760
  have hstable : (prefixWord ++ tailWord_3606760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606760).length < 2 ^ (prefixWord ++ tailWord_3606760).sum := by decide
  have hdescent : baseEnd_3606760 < baseStart_3606760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606835 : List Nat := [1, 1, 1, 2, 5, 1, 1, 1, 5, 4]
def baseStart_3606835 : Nat := 118140960795 + 3606835 * 2 ^ 59
def prefixEnd_3606835 : Nat := 4983230072969 + 3 ^ 40 * 3606835 * 2
def baseEnd_3606835 : Nat := 1234693330973000650116649

theorem tailTrace_3606835 : CollatzResearch.WordTrace tailWord_3606835 prefixEnd_3606835 1234693330973000650116649 := by
  unfold tailWord_3606835
  simp only [CollatzResearch.WordTrace]
  refine ⟨131552079888060268220973959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87701386592040178813982639 131552079888060268220973959)
  ·
    refine ⟨197328119832090402331460939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131552079888060268220973959 197328119832090402331460939)
    ·
      refine ⟨295992179748135603497191409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197328119832090402331460939 295992179748135603497191409)
      ·
        refine ⟨221994134811101702622893557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295992179748135603497191409 221994134811101702622893557)
        ·
          refine ⟨20811950138540784620896271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 221994134811101702622893557 20811950138540784620896271)
          ·
            refine ⟨31217925207811176931344407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20811950138540784620896271 31217925207811176931344407)
            ·
              refine ⟨46826887811716765397016611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31217925207811176931344407 46826887811716765397016611)
              ·
                refine ⟨70240331717575148095524917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46826887811716765397016611 70240331717575148095524917)
                ·
                  refine ⟨6585031098522670133955461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70240331717575148095524917 6585031098522670133955461)
                  ·
                    refine ⟨1234693330973000650116649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6585031098522670133955461 1234693330973000650116649)
                    ·
                      rfl

theorem cell22_3606835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 5, 4].length) (baseStart_3606835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3606835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3606835 prefixEnd_3606835 := by exact prefixLift 3606835
  have htrace : WordTrace (prefixWord ++ tailWord_3606835) baseStart_3606835 baseEnd_3606835 := by
    simpa [prefixWord, tailWord_3606835, baseEnd_3606835] using wordTrace_append hprefix tailTrace_3606835
  have hstable : (prefixWord ++ tailWord_3606835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606835).length < 2 ^ (prefixWord ++ tailWord_3606835).sum := by decide
  have hdescent : baseEnd_3606835 < baseStart_3606835 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606869 : List Nat := [1, 3, 2, 2, 4, 1, 1, 3, 1, 4]
def baseStart_3606869 : Nat := 118140960795 + 3606869 * 2 ^ 59
def prefixEnd_3606869 : Nat := 4983230072969 + 3 ^ 40 * 3606869 * 2
def baseEnd_3606869 : Nat := 1234704969867835894766545

theorem tailTrace_3606869 : CollatzResearch.WordTrace tailWord_3606869 prefixEnd_3606869 1234704969867835894766545 := by
  unfold tailWord_3606869
  simp only [CollatzResearch.WordTrace]
  refine ⟨131553319969937092027711661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87702213313291394685141107 131553319969937092027711661)
  ·
    refine ⟨49332494988726409510391873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131553319969937092027711661 49332494988726409510391873)
    ·
      refine ⟨36999371241544807132793905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49332494988726409510391873 36999371241544807132793905)
      ·
        refine ⟨27749528431158605349595429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36999371241544807132793905 27749528431158605349595429)
        ·
          refine ⟨5203036580842238503049143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27749528431158605349595429 5203036580842238503049143)
          ·
            refine ⟨7804554871263357754573715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5203036580842238503049143 7804554871263357754573715)
            ·
              refine ⟨11706832306895036631860573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7804554871263357754573715 11706832306895036631860573)
              ·
                refine ⟨4390062115085638736947715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11706832306895036631860573 4390062115085638736947715)
                ·
                  refine ⟨6585093172628458105421573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4390062115085638736947715 6585093172628458105421573)
                  ·
                    refine ⟨1234704969867835894766545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6585093172628458105421573 1234704969867835894766545)
                    ·
                      rfl

theorem cell22_3606869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 3, 1, 4].length) (baseStart_3606869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3606869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3606869 prefixEnd_3606869 := by exact prefixLift 3606869
  have htrace : WordTrace (prefixWord ++ tailWord_3606869) baseStart_3606869 baseEnd_3606869 := by
    simpa [prefixWord, tailWord_3606869, baseEnd_3606869] using wordTrace_append hprefix tailTrace_3606869
  have hstable : (prefixWord ++ tailWord_3606869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606869).length < 2 ^ (prefixWord ++ tailWord_3606869).sum := by decide
  have hdescent : baseEnd_3606869 < baseStart_3606869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606944 : List Nat := [2, 1, 1, 4, 1, 3, 3, 1, 3, 3]
def baseStart_3606944 : Nat := 118140960795 + 3606944 * 2 ^ 59
def prefixEnd_3606944 : Nat := 4983230072969 + 3 ^ 40 * 3606944 * 2
def baseEnd_3606944 : Nat := 1234730643900560699141315

theorem tailTrace_3606944 : CollatzResearch.WordTrace tailWord_3606944 prefixEnd_3606944 1234730643900560699141315 := by
  unfold tailWord_3606944
  simp only [CollatzResearch.WordTrace]
  refine ⟨65778027722332689918345943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87704036963110253224461257 65778027722332689918345943)
  ·
    refine ⟨98667041583499034877518915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65778027722332689918345943 98667041583499034877518915)
    ·
      refine ⟨148000562375248552316278373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98667041583499034877518915 148000562375248552316278373)
      ·
        refine ⟨27750105445359103559302195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148000562375248552316278373 27750105445359103559302195)
        ·
          refine ⟨41625158168038655338953293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27750105445359103559302195 41625158168038655338953293)
          ·
            refine ⟨15609434313014495752107485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41625158168038655338953293 15609434313014495752107485)
            ·
              refine ⟨5853537867380435907040307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15609434313014495752107485 5853537867380435907040307)
              ·
                refine ⟨8780306801070653860560461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5853537867380435907040307 8780306801070653860560461)
                ·
                  refine ⟨3292615050401495197710173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8780306801070653860560461 3292615050401495197710173)
                  ·
                    refine ⟨1234730643900560699141315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3292615050401495197710173 1234730643900560699141315)
                    ·
                      rfl

theorem cell22_3606944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 1, 3, 3].length) (baseStart_3606944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3606944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3606944 prefixEnd_3606944 := by exact prefixLift 3606944
  have htrace : WordTrace (prefixWord ++ tailWord_3606944) baseStart_3606944 baseEnd_3606944 := by
    simpa [prefixWord, tailWord_3606944, baseEnd_3606944] using wordTrace_append hprefix tailTrace_3606944
  have hstable : (prefixWord ++ tailWord_3606944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606944).length < 2 ^ (prefixWord ++ tailWord_3606944).sum := by decide
  have hdescent : baseEnd_3606944 < baseStart_3606944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607002 : List Nat := [3, 1, 1, 2, 3, 1, 2, 3, 6]
def baseStart_3607002 : Nat := 118140960795 + 3607002 * 2 ^ 59
def prefixEnd_3607002 : Nat := 4983230072969 + 3 ^ 40 * 3607002 * 2
def baseEnd_3607002 : Nat := 411583499495289293730379

theorem tailTrace_3607002 : CollatzResearch.WordTrace tailWord_3607002 prefixEnd_3607002 411583499495289293730379 := by
  unfold tailWord_3607002
  simp only [CollatzResearch.WordTrace]
  refine ⟨32889542719613813935575815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87705447252303503828202173 32889542719613813935575815)
  ·
    refine ⟨49334314079420720903363723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32889542719613813935575815 49334314079420720903363723)
    ·
      refine ⟨74001471119131081355045585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49334314079420720903363723 74001471119131081355045585)
      ·
        refine ⟨55501103339348311016284189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74001471119131081355045585 55501103339348311016284189)
        ·
          refine ⟨20812913752255616631106571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55501103339348311016284189 20812913752255616631106571)
          ·
            refine ⟨31219370628383424946659857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20812913752255616631106571 31219370628383424946659857)
            ·
              refine ⟨23414527971287568709994893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31219370628383424946659857 23414527971287568709994893)
              ·
                refine ⟨8780447989232838266248085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23414527971287568709994893 8780447989232838266248085)
                ·
                  refine ⟨411583499495289293730379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8780447989232838266248085 411583499495289293730379)
                  ·
                    rfl

theorem cell22_3607002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 3, 6].length) (baseStart_3607002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3607002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3607002 prefixEnd_3607002 := by exact prefixLift 3607002
  have htrace : WordTrace (prefixWord ++ tailWord_3607002) baseStart_3607002 baseEnd_3607002 := by
    simpa [prefixWord, tailWord_3607002, baseEnd_3607002] using wordTrace_append hprefix tailTrace_3607002
  have hstable : (prefixWord ++ tailWord_3607002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607002).length < 2 ^ (prefixWord ++ tailWord_3607002).sum := by decide
  have hdescent : baseEnd_3607002 < baseStart_3607002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607032 : List Nat := [2, 1, 2, 1, 1, 4, 3, 1, 1, 6]
def baseStart_3607032 : Nat := 118140960795 + 3607032 * 2 ^ 59
def prefixEnd_3607032 : Nat := 4983230072969 + 3 ^ 40 * 3607032 * 2
def baseEnd_3607032 : Nat := 1234760768098957802941045

theorem tailTrace_3607032 : CollatzResearch.WordTrace tailWord_3607032 prefixEnd_3607032 1234760768098957802941045 := by
  unfold tailWord_3607032
  simp only [CollatzResearch.WordTrace]
  refine ⟨65779632534173285432947675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87706176712231047243930233 65779632534173285432947675)
  ·
    refine ⟨98669448801259928149421513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65779632534173285432947675 98669448801259928149421513)
    ·
      refine ⟨74002086600944946112066135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98669448801259928149421513 74002086600944946112066135)
      ·
        refine ⟨111003129901417419168099203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74002086600944946112066135 111003129901417419168099203)
        ·
          refine ⟨166504694852126128752148805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111003129901417419168099203 166504694852126128752148805)
          ·
            refine ⟨31219630284773649141027901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 166504694852126128752148805 31219630284773649141027901)
            ·
              refine ⟨11707361356790118427885463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31219630284773649141027901 11707361356790118427885463)
              ·
                refine ⟨17561042035185177641828195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11707361356790118427885463 17561042035185177641828195)
                ·
                  refine ⟨26341563052777766462742293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17561042035185177641828195 26341563052777766462742293)
                  ·
                    refine ⟨1234760768098957802941045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26341563052777766462742293 1234760768098957802941045)
                    ·
                      rfl

theorem cell22_3607032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 1, 6].length) (baseStart_3607032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3607032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3607032 prefixEnd_3607032 := by exact prefixLift 3607032
  have htrace : WordTrace (prefixWord ++ tailWord_3607032) baseStart_3607032 baseEnd_3607032 := by
    simpa [prefixWord, tailWord_3607032, baseEnd_3607032] using wordTrace_append hprefix tailTrace_3607032
  have hstable : (prefixWord ++ tailWord_3607032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607032).length < 2 ^ (prefixWord ++ tailWord_3607032).sum := by decide
  have hdescent : baseEnd_3607032 < baseStart_3607032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607051 : List Nat := [1, 1, 1, 1, 7, 1, 3, 2, 2, 3]
def baseStart_3607051 : Nat := 118140960795 + 3607051 * 2 ^ 59
def prefixEnd_3607051 : Nat := 4983230072969 + 3 ^ 40 * 3607051 * 2
def baseEnd_3607051 : Nat := 1234767272187248086715987

theorem tailTrace_3607051 : CollatzResearch.WordTrace tailWord_3607051 prefixEnd_3607051 1234767272187248086715987 := by
  unfold tailWord_3607051
  simp only [CollatzResearch.WordTrace]
  refine ⟨131559958055277737110837007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87706638703518491407224671 131559958055277737110837007)
  ·
    refine ⟨197339937082916605666255511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131559958055277737110837007 197339937082916605666255511)
    ·
      refine ⟨296009905624374908499383267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197339937082916605666255511 296009905624374908499383267)
      ·
        refine ⟨444014858436562362749074901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296009905624374908499383267 444014858436562362749074901)
        ·
          refine ⟨10406598244606930376931443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 444014858436562362749074901 10406598244606930376931443)
          ·
            refine ⟨15609897366910395565397165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10406598244606930376931443 15609897366910395565397165)
            ·
              refine ⟨5853711512591398337023937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15609897366910395565397165 5853711512591398337023937)
              ·
                refine ⟨4390283634443548752767953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5853711512591398337023937 4390283634443548752767953)
                ·
                  refine ⟨3292712725832661564575965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4390283634443548752767953 3292712725832661564575965)
                  ·
                    refine ⟨1234767272187248086715987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3292712725832661564575965 1234767272187248086715987)
                    ·
                      rfl

theorem cell22_3607051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 2, 2, 3].length) (baseStart_3607051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3607051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3607051 prefixEnd_3607051 := by exact prefixLift 3607051
  have htrace : WordTrace (prefixWord ++ tailWord_3607051) baseStart_3607051 baseEnd_3607051 := by
    simpa [prefixWord, tailWord_3607051, baseEnd_3607051] using wordTrace_append hprefix tailTrace_3607051
  have hstable : (prefixWord ++ tailWord_3607051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607051).length < 2 ^ (prefixWord ++ tailWord_3607051).sum := by decide
  have hdescent : baseEnd_3607051 < baseStart_3607051 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607053 : List Nat := [1, 7, 1, 1, 1, 2, 2, 1, 6]
def baseStart_3607053 : Nat := 118140960795 + 3607053 * 2 ^ 59
def prefixEnd_3607053 : Nat := 4983230072969 + 3 ^ 40 * 3607053 * 2
def baseEnd_3607053 : Nat := 411589318942706916055327

theorem tailTrace_3607053 : CollatzResearch.WordTrace tailWord_3607053 prefixEnd_3607053 411589318942706916055327 := by
  unfold tailWord_3607053
  simp only [CollatzResearch.WordTrace]
  refine ⟨131560031001270491452409813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87706687334180327634939875 131560031001270491452409813)
  ·
    refine ⟨3083438226592277143415855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 131560031001270491452409813 3083438226592277143415855)
    ·
      refine ⟨4625157339888415715123783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3083438226592277143415855 4625157339888415715123783)
      ·
        refine ⟨6937736009832623572685675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4625157339888415715123783 6937736009832623572685675)
        ·
          refine ⟨10406604014748935359028513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6937736009832623572685675 10406604014748935359028513)
          ·
            refine ⟨7804953011061701519271385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10406604014748935359028513 7804953011061701519271385)
            ·
              refine ⟨5853714758296276139453539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7804953011061701519271385 5853714758296276139453539)
              ·
                refine ⟨8780572137444414209180309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5853714758296276139453539 8780572137444414209180309)
                ·
                  refine ⟨411589318942706916055327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8780572137444414209180309 411589318942706916055327)
                  ·
                    rfl

theorem cell22_3607053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_3607053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3607053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3607053 prefixEnd_3607053 := by exact prefixLift 3607053
  have htrace : WordTrace (prefixWord ++ tailWord_3607053) baseStart_3607053 baseEnd_3607053 := by
    simpa [prefixWord, tailWord_3607053, baseEnd_3607053] using wordTrace_append hprefix tailTrace_3607053
  have hstable : (prefixWord ++ tailWord_3607053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607053).length < 2 ^ (prefixWord ++ tailWord_3607053).sum := by decide
  have hdescent : baseEnd_3607053 < baseStart_3607053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607068 : List Nat := [2, 2, 3, 1, 2, 3, 3, 1, 2, 3]
def baseStart_3607068 : Nat := 118140960795 + 3607068 * 2 ^ 59
def prefixEnd_3607068 : Nat := 4983230072969 + 3 ^ 40 * 3607068 * 2
def baseEnd_3607068 : Nat := 1234773091634665709040935

theorem tailTrace_3607068 : CollatzResearch.WordTrace tailWord_3607068 prefixEnd_3607068 1234773091634665709040935 := by
  unfold tailWord_3607068
  simp only [CollatzResearch.WordTrace]
  refine ⟨65780289048108074507102929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87707052064144099342803905 65780289048108074507102929)
  ·
    refine ⟨49335216786081055880327197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65780289048108074507102929 49335216786081055880327197)
    ·
      refine ⟨18500706294780395955122699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49335216786081055880327197 18500706294780395955122699)
      ·
        refine ⟨27751059442170593932684049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18500706294780395955122699 27751059442170593932684049)
        ·
          refine ⟨20813294581627945449513037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27751059442170593932684049 20813294581627945449513037)
          ·
            refine ⟨7804985468110479543567389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20813294581627945449513037 7804985468110479543567389)
            ·
              refine ⟨2926869550541429828837771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7804985468110479543567389 2926869550541429828837771)
              ·
                refine ⟨4390304325812144743256657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2926869550541429828837771 4390304325812144743256657)
                ·
                  refine ⟨3292728244359108557442493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4390304325812144743256657 3292728244359108557442493)
                  ·
                    refine ⟨1234773091634665709040935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3292728244359108557442493 1234773091634665709040935)
                    ·
                      rfl

theorem cell22_3607068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 3, 1, 2, 3].length) (baseStart_3607068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3607068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3607068 prefixEnd_3607068 := by exact prefixLift 3607068
  have htrace : WordTrace (prefixWord ++ tailWord_3607068) baseStart_3607068 baseEnd_3607068 := by
    simpa [prefixWord, tailWord_3607068, baseEnd_3607068] using wordTrace_append hprefix tailTrace_3607068
  have hstable : (prefixWord ++ tailWord_3607068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607068).length < 2 ^ (prefixWord ++ tailWord_3607068).sum := by decide
  have hdescent : baseEnd_3607068 < baseStart_3607068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607077 : List Nat := [1, 3, 1, 2, 2, 1, 2, 2, 2, 6]
def baseStart_3607077 : Nat := 118140960795 + 3607077 * 2 ^ 59
def prefixEnd_3607077 : Nat := 4983230072969 + 3 ^ 40 * 3607077 * 2
def baseEnd_3607077 : Nat := 1234776172518592685565907

theorem tailTrace_3607077 : CollatzResearch.WordTrace tailWord_3607077 prefixEnd_3607077 1234776172518592685565907 := by
  unfold tailWord_3607077
  simp only [CollatzResearch.WordTrace]
  refine ⟨131560906353183543551283485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87707270902122362367522323 131560906353183543551283485)
  ·
    refine ⟨49335339882443828831731307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131560906353183543551283485 49335339882443828831731307)
    ·
      refine ⟨74003009823665743247596961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49335339882443828831731307 74003009823665743247596961)
      ·
        refine ⟨55502257367749307435697721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74003009823665743247596961 55502257367749307435697721)
        ·
          refine ⟨41626693025811980576773291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55502257367749307435697721 41626693025811980576773291)
          ·
            refine ⟨62440039538717970865159937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41626693025811980576773291 62440039538717970865159937)
            ·
              refine ⟨46830029654038478148869953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62440039538717970865159937 46830029654038478148869953)
              ·
                refine ⟨35122522240528858611652465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46830029654038478148869953 35122522240528858611652465)
                ·
                  refine ⟨26341891680396643958739349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35122522240528858611652465 26341891680396643958739349)
                  ·
                    refine ⟨1234776172518592685565907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26341891680396643958739349 1234776172518592685565907)
                    ·
                      rfl

theorem cell22_3607077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 6].length) (baseStart_3607077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3607077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3607077 prefixEnd_3607077 := by exact prefixLift 3607077
  have htrace : WordTrace (prefixWord ++ tailWord_3607077) baseStart_3607077 baseEnd_3607077 := by
    simpa [prefixWord, tailWord_3607077, baseEnd_3607077] using wordTrace_append hprefix tailTrace_3607077
  have hstable : (prefixWord ++ tailWord_3607077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607077).length < 2 ^ (prefixWord ++ tailWord_3607077).sum := by decide
  have hdescent : baseEnd_3607077 < baseStart_3607077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607107 : List Nat := [1, 1, 1, 3, 1, 2, 1, 3, 4, 5]
def baseStart_3607107 : Nat := 118140960795 + 3607107 * 2 ^ 59
def prefixEnd_3607107 : Nat := 4983230072969 + 3 ^ 40 * 3607107 * 2
def baseEnd_3607107 : Nat := 1234786442131682607315815

theorem tailTrace_3607107 : CollatzResearch.WordTrace tailWord_3607107 prefixEnd_3607107 1234786442131682607315815 := by
  unfold tailWord_3607107
  simp only [CollatzResearch.WordTrace]
  refine ⟨131562000543074858674875575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87708000362049905783250383 131562000543074858674875575)
  ·
    refine ⟨197343000814612288012313363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131562000543074858674875575 197343000814612288012313363)
    ·
      refine ⟨296014501221918432018470045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197343000814612288012313363 296014501221918432018470045)
      ·
        refine ⟨111005437958219412006926267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 296014501221918432018470045 111005437958219412006926267)
        ·
          refine ⟨166508156937329118010389401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111005437958219412006926267 166508156937329118010389401)
          ·
            refine ⟨124881117702996838507792051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166508156937329118010389401 124881117702996838507792051)
            ·
              refine ⟨187321676554495257761688077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124881117702996838507792051 187321676554495257761688077)
              ·
                refine ⟨70245628707935721660633029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 187321676554495257761688077 70245628707935721660633029)
                ·
                  refine ⟨13171055382737947811368693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70245628707935721660633029 13171055382737947811368693)
                  ·
                    refine ⟨1234786442131682607315815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13171055382737947811368693 1234786442131682607315815)
                    ·
                      rfl

theorem cell22_3607107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 4, 5].length) (baseStart_3607107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3607107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3607107 prefixEnd_3607107 := by exact prefixLift 3607107
  have htrace : WordTrace (prefixWord ++ tailWord_3607107) baseStart_3607107 baseEnd_3607107 := by
    simpa [prefixWord, tailWord_3607107, baseEnd_3607107] using wordTrace_append hprefix tailTrace_3607107
  have hstable : (prefixWord ++ tailWord_3607107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607107).length < 2 ^ (prefixWord ++ tailWord_3607107).sum := by decide
  have hdescent : baseEnd_3607107 < baseStart_3607107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607139 : List Nat := [1, 1, 1, 5, 1, 2, 3, 1, 3, 4]
def baseStart_3607139 : Nat := 118140960795 + 3607139 * 2 ^ 59
def prefixEnd_3607139 : Nat := 4983230072969 + 3 ^ 40 * 3607139 * 2
def baseEnd_3607139 : Nat := 1234797396385645190515717

theorem tailTrace_3607139 : CollatzResearch.WordTrace tailWord_3607139 prefixEnd_3607139 1234797396385645190515717 := by
  unfold tailWord_3607139
  simp only [CollatzResearch.WordTrace]
  refine ⟨131563167678958928140040471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87708778452639285426693647 131563167678958928140040471)
  ·
    refine ⟨197344751518438392210060707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131563167678958928140040471 197344751518438392210060707)
    ·
      refine ⟨296017127277657588315091061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197344751518438392210060707 296017127277657588315091061)
      ·
        refine ⟨27751605682280398904539787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 296017127277657588315091061 27751605682280398904539787)
        ·
          refine ⟨41627408523420598356809681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27751605682280398904539787 41627408523420598356809681)
          ·
            refine ⟨31220556392565448767607261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41627408523420598356809681 31220556392565448767607261)
            ·
              refine ⟨11707708647212043287852723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31220556392565448767607261 11707708647212043287852723)
              ·
                refine ⟨17561562970818064931779085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11707708647212043287852723 17561562970818064931779085)
                ·
                  refine ⟨6585586114056774349417157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17561562970818064931779085 6585586114056774349417157)
                  ·
                    refine ⟨1234797396385645190515717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6585586114056774349417157 1234797396385645190515717)
                    ·
                      rfl

theorem cell22_3607139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 3, 4].length) (baseStart_3607139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3607139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3607139 prefixEnd_3607139 := by exact prefixLift 3607139
  have htrace : WordTrace (prefixWord ++ tailWord_3607139) baseStart_3607139 baseEnd_3607139 := by
    simpa [prefixWord, tailWord_3607139, baseEnd_3607139] using wordTrace_append hprefix tailTrace_3607139
  have hstable : (prefixWord ++ tailWord_3607139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607139).length < 2 ^ (prefixWord ++ tailWord_3607139).sum := by decide
  have hdescent : baseEnd_3607139 < baseStart_3607139 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607169 : List Nat := [1, 2, 4, 2, 1, 1, 1, 2, 3, 5]
def baseStart_3607169 : Nat := 118140960795 + 3607169 * 2 ^ 59
def prefixEnd_3607169 : Nat := 4983230072969 + 3 ^ 40 * 3607169 * 2
def baseEnd_3607169 : Nat := 1234807665998735112265625

theorem tailTrace_3607169 : CollatzResearch.WordTrace tailWord_3607169 prefixEnd_3607169 1234807665998735112265625 := by
  unfold tailWord_3607169
  simp only [CollatzResearch.WordTrace]
  refine ⟨131564261868850243263632561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87709507912566828842421707 131564261868850243263632561)
  ·
    refine ⟨98673196401637682447724421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131564261868850243263632561 98673196401637682447724421)
    ·
      refine ⟨18501224325307065458948329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98673196401637682447724421 18501224325307065458948329)
      ·
        refine ⟨13875918243980299094211247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18501224325307065458948329 13875918243980299094211247)
        ·
          refine ⟨20813877365970448641316871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13875918243980299094211247 20813877365970448641316871)
          ·
            refine ⟨31220816048955672961975307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20813877365970448641316871 31220816048955672961975307)
            ·
              refine ⟨46831224073433509442962961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31220816048955672961975307 46831224073433509442962961)
              ·
                refine ⟨35123418055075132082222221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46831224073433509442962961 35123418055075132082222221)
                ·
                  refine ⟨13171281770653174530833333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35123418055075132082222221 13171281770653174530833333)
                  ·
                    refine ⟨1234807665998735112265625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13171281770653174530833333 1234807665998735112265625)
                    ·
                      rfl

theorem cell22_3607169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_3607169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3607169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3607169 prefixEnd_3607169 := by exact prefixLift 3607169
  have htrace : WordTrace (prefixWord ++ tailWord_3607169) baseStart_3607169 baseEnd_3607169 := by
    simpa [prefixWord, tailWord_3607169, baseEnd_3607169] using wordTrace_append hprefix tailTrace_3607169
  have hstable : (prefixWord ++ tailWord_3607169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607169).length < 2 ^ (prefixWord ++ tailWord_3607169).sum := by decide
  have hdescent : baseEnd_3607169 < baseStart_3607169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607186 : List Nat := [3, 2, 3, 1, 2, 1, 1, 3, 1, 5]
def baseStart_3607186 : Nat := 118140960795 + 3607186 * 2 ^ 59
def prefixEnd_3607186 : Nat := 4983230072969 + 3 ^ 40 * 3607186 * 2
def baseEnd_3607186 : Nat := 1234813485446152734590573

theorem tailTrace_3607186 : CollatzResearch.WordTrace tailWord_3607186 prefixEnd_3607186 1234813485446152734590573 := by
  unfold tailWord_3607186
  simp only [CollatzResearch.WordTrace]
  refine ⟨32891220477447163791750353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87709921273192436778000941 32891220477447163791750353)
  ·
    refine ⟨24668415358085372843812765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32891220477447163791750353 24668415358085372843812765)
    ·
      refine ⟨9250655759282014816429787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24668415358085372843812765 9250655759282014816429787)
      ·
        refine ⟨13875983638923022224644681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9250655759282014816429787 13875983638923022224644681)
        ·
          refine ⟨10406987729192266668483511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13875983638923022224644681 10406987729192266668483511)
          ·
            refine ⟨15610481593788400002725267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10406987729192266668483511 15610481593788400002725267)
            ·
              refine ⟨23415722390682600004087901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15610481593788400002725267 23415722390682600004087901)
              ·
                refine ⟨8780895896505975001532963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23415722390682600004087901 8780895896505975001532963)
                ·
                  refine ⟨13171343844758962502299445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8780895896505975001532963 13171343844758962502299445)
                  ·
                    refine ⟨1234813485446152734590573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13171343844758962502299445 1234813485446152734590573)
                    ·
                      rfl

theorem cell22_3607186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_3607186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3607186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3607186 prefixEnd_3607186 := by exact prefixLift 3607186
  have htrace : WordTrace (prefixWord ++ tailWord_3607186) baseStart_3607186 baseEnd_3607186 := by
    simpa [prefixWord, tailWord_3607186, baseEnd_3607186] using wordTrace_append hprefix tailTrace_3607186
  have hstable : (prefixWord ++ tailWord_3607186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607186).length < 2 ^ (prefixWord ++ tailWord_3607186).sum := by decide
  have hdescent : baseEnd_3607186 < baseStart_3607186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607201 : List Nat := [1, 2, 3, 3, 3, 1, 1, 1, 1, 6]
def baseStart_3607201 : Nat := 118140960795 + 3607201 * 2 ^ 59
def prefixEnd_3607201 : Nat := 4983230072969 + 3 ^ 40 * 3607201 * 2
def baseEnd_3607201 : Nat := 1234818620252697695465527

theorem tailTrace_3607201 : CollatzResearch.WordTrace tailWord_3607201 prefixEnd_3607201 1234818620252697695465527 := by
  unfold tailWord_3607201
  simp only [CollatzResearch.WordTrace]
  refine ⟨131565429004734312728797457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87710286003156208485864971 131565429004734312728797457)
  ·
    refine ⟨98674071753550734546598093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131565429004734312728797457 98674071753550734546598093)
    ·
      refine ⟨37002776907581525454974285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98674071753550734546598093 37002776907581525454974285)
      ·
        refine ⟨13876041340343072045615357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37002776907581525454974285 13876041340343072045615357)
        ·
          refine ⟨5203515502628652017105759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13876041340343072045615357 5203515502628652017105759)
          ·
            refine ⟨7805273253942978025658639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5203515502628652017105759 7805273253942978025658639)
            ·
              refine ⟨11707909880914467038487959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7805273253942978025658639 11707909880914467038487959)
              ·
                refine ⟨17561864821371700557731939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11707909880914467038487959 17561864821371700557731939)
                ·
                  refine ⟨26342797232057550836597909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17561864821371700557731939 26342797232057550836597909)
                  ·
                    refine ⟨1234818620252697695465527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26342797232057550836597909 1234818620252697695465527)
                    ·
                      rfl

theorem cell22_3607201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 6].length) (baseStart_3607201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3607201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3607201 prefixEnd_3607201 := by exact prefixLift 3607201
  have htrace : WordTrace (prefixWord ++ tailWord_3607201) baseStart_3607201 baseEnd_3607201 := by
    simpa [prefixWord, tailWord_3607201, baseEnd_3607201] using wordTrace_append hprefix tailTrace_3607201
  have hstable : (prefixWord ++ tailWord_3607201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607201).length < 2 ^ (prefixWord ++ tailWord_3607201).sum := by decide
  have hdescent : baseEnd_3607201 < baseStart_3607201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607207 : List Nat := [1, 1, 6, 3, 1, 2, 2, 1, 1, 4]
def baseStart_3607207 : Nat := 118140960795 + 3607207 * 2 ^ 59
def prefixEnd_3607207 : Nat := 4983230072969 + 3 ^ 40 * 3607207 * 2
def baseEnd_3607207 : Nat := 1234820674175315679815509

theorem tailTrace_3607207 : CollatzResearch.WordTrace tailWord_3607207 prefixEnd_3607207 1234820674175315679815509 := by
  unfold tailWord_3607207
  simp only [CollatzResearch.WordTrace]
  refine ⟨131565647842712575753515875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87710431895141717169010583 131565647842712575753515875)
  ·
    refine ⟨197348471764068863630273813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131565647842712575753515875 197348471764068863630273813)
    ·
      refine ⟨9250709613940727982669085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 197348471764068863630273813 9250709613940727982669085)
      ·
        refine ⟨3469016105227772993500907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9250709613940727982669085 3469016105227772993500907)
        ·
          refine ⟨5203524157841659490251361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3469016105227772993500907 5203524157841659490251361)
          ·
            refine ⟨3902643118381244617688521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5203524157841659490251361 3902643118381244617688521)
            ·
              refine ⟨2926982338785933463266391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3902643118381244617688521 2926982338785933463266391)
              ·
                refine ⟨4390473508178900194899587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2926982338785933463266391 4390473508178900194899587)
                ·
                  refine ⟨6585710262268350292349381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4390473508178900194899587 6585710262268350292349381)
                  ·
                    refine ⟨1234820674175315679815509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6585710262268350292349381 1234820674175315679815509)
                    ·
                      rfl

theorem cell22_3607207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_3607207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3607207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3607207 prefixEnd_3607207 := by exact prefixLift 3607207
  have htrace : WordTrace (prefixWord ++ tailWord_3607207) baseStart_3607207 baseEnd_3607207 := by
    simpa [prefixWord, tailWord_3607207, baseEnd_3607207] using wordTrace_append hprefix tailTrace_3607207
  have hstable : (prefixWord ++ tailWord_3607207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607207).length < 2 ^ (prefixWord ++ tailWord_3607207).sum := by decide
  have hdescent : baseEnd_3607207 < baseStart_3607207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607231 : List Nat := [1, 1, 2, 2, 2, 4, 1, 3, 3, 3]
def baseStart_3607231 : Nat := 118140960795 + 3607231 * 2 ^ 59
def prefixEnd_3607231 : Nat := 4983230072969 + 3 ^ 40 * 3607231 * 2
def baseEnd_3607231 : Nat := 1234828889865787617215435

theorem tailTrace_3607231 : CollatzResearch.WordTrace tailWord_3607231 prefixEnd_3607231 1234828889865787617215435 := by
  unfold tailWord_3607231
  simp only [CollatzResearch.WordTrace]
  refine ⟨131566523194625627852389547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87711015463083751901593031 131566523194625627852389547)
  ·
    refine ⟨197349784791938441778584321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131566523194625627852389547 197349784791938441778584321)
    ·
      refine ⟨148012338593953831333938241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197349784791938441778584321 148012338593953831333938241)
      ·
        refine ⟨111009253945465373500453681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148012338593953831333938241 111009253945465373500453681)
        ·
          refine ⟨83256940459099030125340261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111009253945465373500453681 83256940459099030125340261)
          ·
            refine ⟨15610676336081068148501299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83256940459099030125340261 15610676336081068148501299)
            ·
              refine ⟨23416014504121602222751949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15610676336081068148501299 23416014504121602222751949)
              ·
                refine ⟨8781005439045600833531981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23416014504121602222751949 8781005439045600833531981)
                ·
                  refine ⟨3292877039642100312574493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8781005439045600833531981 3292877039642100312574493)
                  ·
                    refine ⟨1234828889865787617215435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3292877039642100312574493 1234828889865787617215435)
                    ·
                      rfl

theorem cell22_3607231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 3, 3, 3].length) (baseStart_3607231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3607231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3607231 prefixEnd_3607231 := by exact prefixLift 3607231
  have htrace : WordTrace (prefixWord ++ tailWord_3607231) baseStart_3607231 baseEnd_3607231 := by
    simpa [prefixWord, tailWord_3607231, baseEnd_3607231] using wordTrace_append hprefix tailTrace_3607231
  have hstable : (prefixWord ++ tailWord_3607231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607231).length < 2 ^ (prefixWord ++ tailWord_3607231).sum := by decide
  have hdescent : baseEnd_3607231 < baseStart_3607231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607250 : List Nat := [3, 2, 2, 2, 4, 1, 2, 6]
def baseStart_3607250 : Nat := 118140960795 + 3607250 * 2 ^ 59
def prefixEnd_3607250 : Nat := 4983230072969 + 3 ^ 40 * 3607250 * 2
def baseEnd_3607250 : Nat := 137203932661564211221153

theorem tailTrace_3607250 : CollatzResearch.WordTrace tailWord_3607250 prefixEnd_3607250 137203932661564211221153 := by
  unfold tailWord_3607250
  simp only [CollatzResearch.WordTrace]
  refine ⟨32891804045389198524332801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87711477454371196064887469 32891804045389198524332801)
  ·
    refine ⟨24668853034041898893249601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32891804045389198524332801 24668853034041898893249601)
    ·
      refine ⟨18501639775531424169937201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24668853034041898893249601 18501639775531424169937201)
      ·
        refine ⟨13876229831648568127452901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18501639775531424169937201 13876229831648568127452901)
        ·
          refine ⟨2601793093434106523897419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13876229831648568127452901 2601793093434106523897419)
          ·
            refine ⟨3902689640151159785846129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2601793093434106523897419 3902689640151159785846129)
            ·
              refine ⟨2927017230113369839384597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3902689640151159785846129 2927017230113369839384597)
              ·
                refine ⟨137203932661564211221153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2927017230113369839384597 137203932661564211221153)
                ·
                  rfl

theorem cell22_3607250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 2, 6].length) (baseStart_3607250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3607250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3607250 prefixEnd_3607250 := by exact prefixLift 3607250
  have htrace : WordTrace (prefixWord ++ tailWord_3607250) baseStart_3607250 baseEnd_3607250 := by
    simpa [prefixWord, tailWord_3607250, baseEnd_3607250] using wordTrace_append hprefix tailTrace_3607250
  have hstable : (prefixWord ++ tailWord_3607250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607250).length < 2 ^ (prefixWord ++ tailWord_3607250).sum := by decide
  have hdescent : baseEnd_3607250 < baseStart_3607250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607265 : List Nat := [1, 2, 3, 1, 4, 1, 3, 3, 1, 3]
def baseStart_3607265 : Nat := 118140960795 + 3607265 * 2 ^ 59
def prefixEnd_3607265 : Nat := 4983230072969 + 3 ^ 40 * 3607265 * 2
def baseEnd_3607265 : Nat := 1234840528760622861865331

theorem tailTrace_3607265 : CollatzResearch.WordTrace tailWord_3607265 prefixEnd_3607265 1234840528760622861865331 := by
  unfold tailWord_3607265
  simp only [CollatzResearch.WordTrace]
  refine ⟨131567763276502451659127249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87711842184334967772751499 131567763276502451659127249)
  ·
    refine ⟨98675822457376838744345437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131567763276502451659127249 98675822457376838744345437)
    ·
      refine ⟨37003433421516314529129539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98675822457376838744345437 37003433421516314529129539)
      ·
        refine ⟨55505150132274471793694309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37003433421516314529129539 55505150132274471793694309)
        ·
          refine ⟨10407215649801463461317683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55505150132274471793694309 10407215649801463461317683)
          ·
            refine ⟨15610823474702195191976525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10407215649801463461317683 15610823474702195191976525)
            ·
              refine ⟨5854058803013323196991197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15610823474702195191976525 5854058803013323196991197)
              ·
                refine ⟨2195272051129996198871699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5854058803013323196991197 2195272051129996198871699)
                ·
                  refine ⟨3292908076694994298307549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2195272051129996198871699 3292908076694994298307549)
                  ·
                    refine ⟨1234840528760622861865331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3292908076694994298307549 1234840528760622861865331)
                    ·
                      rfl

theorem cell22_3607265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 3, 1, 3].length) (baseStart_3607265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3607265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3607265 prefixEnd_3607265 := by exact prefixLift 3607265
  have htrace : WordTrace (prefixWord ++ tailWord_3607265) baseStart_3607265 baseEnd_3607265 := by
    simpa [prefixWord, tailWord_3607265, baseEnd_3607265] using wordTrace_append hprefix tailTrace_3607265
  have hstable : (prefixWord ++ tailWord_3607265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607265).length < 2 ^ (prefixWord ++ tailWord_3607265).sum := by decide
  have hdescent : baseEnd_3607265 < baseStart_3607265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607282 : List Nat := [3, 2, 1, 3, 1, 3, 3, 2, 1, 3]
def baseStart_3607282 : Nat := 118140960795 + 3607282 * 2 ^ 59
def prefixEnd_3607282 : Nat := 4983230072969 + 3 ^ 40 * 3607282 * 2
def baseEnd_3607282 : Nat := 1234846348208040484190279

theorem tailTrace_3607282 : CollatzResearch.WordTrace tailWord_3607282 prefixEnd_3607282 1234846348208040484190279 := by
  unfold tailWord_3607282
  simp only [CollatzResearch.WordTrace]
  refine ⟨32892095829360215890624025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87712255544960575708330733 32892095829360215890624025)
  ·
    refine ⟨24669071872020161917968019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32892095829360215890624025 24669071872020161917968019)
    ·
      refine ⟨37003607808030242876952029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24669071872020161917968019 37003607808030242876952029)
      ·
        refine ⟨13876352928011341078857011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37003607808030242876952029 13876352928011341078857011)
        ·
          refine ⟨20814529392017011618285517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13876352928011341078857011 20814529392017011618285517)
          ·
            refine ⟨7805448522006379356857069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20814529392017011618285517 7805448522006379356857069)
            ·
              refine ⟨2927043195752392258821401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7805448522006379356857069 2927043195752392258821401)
              ·
                refine ⟨2195282396814294194116051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2927043195752392258821401 2195282396814294194116051)
                ·
                  refine ⟨3292923595221441291174077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2195282396814294194116051 3292923595221441291174077)
                  ·
                    refine ⟨1234846348208040484190279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3292923595221441291174077 1234846348208040484190279)
                    ·
                      rfl

theorem cell22_3607282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 3, 2, 1, 3].length) (baseStart_3607282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3607282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3607282 prefixEnd_3607282 := by exact prefixLift 3607282
  have htrace : WordTrace (prefixWord ++ tailWord_3607282) baseStart_3607282 baseEnd_3607282 := by
    simpa [prefixWord, tailWord_3607282, baseEnd_3607282] using wordTrace_append hprefix tailTrace_3607282
  have hstable : (prefixWord ++ tailWord_3607282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607282).length < 2 ^ (prefixWord ++ tailWord_3607282).sum := by decide
  have hdescent : baseEnd_3607282 < baseStart_3607282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607321 : List Nat := [1, 2, 1, 2, 1, 1, 1, 6, 4, 3]
def baseStart_3607321 : Nat := 118140960795 + 3607321 * 2 ^ 59
def prefixEnd_3607321 : Nat := 4983230072969 + 3 ^ 40 * 3607321 * 2
def baseEnd_3607321 : Nat := 1234859698705057382465159

theorem tailTrace_3607321 : CollatzResearch.WordTrace tailWord_3607321 prefixEnd_3607321 1234859698705057382465159 := by
  unfold tailWord_3607321
  simp only [CollatzResearch.WordTrace]
  refine ⟨131569805764299573223165817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87713203842866382148777211 131569805764299573223165817)
  ·
    refine ⟨98677354323224679917374363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131569805764299573223165817 98677354323224679917374363)
    ·
      refine ⟨148016031484837019876061545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98677354323224679917374363 148016031484837019876061545)
      ·
        refine ⟨111012023613627764907046159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148016031484837019876061545 111012023613627764907046159)
        ·
          refine ⟨166518035420441647360569239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111012023613627764907046159 166518035420441647360569239)
          ·
            refine ⟨249777053130662471040853859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166518035420441647360569239 249777053130662471040853859)
            ·
              refine ⟨374665579695993706561280789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249777053130662471040853859 374665579695993706561280789)
              ·
                refine ⟨17562449048249704995060037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 374665579695993706561280789 17562449048249704995060037)
                ·
                  refine ⟨3292959196546819686573757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17562449048249704995060037 3292959196546819686573757)
                  ·
                    refine ⟨1234859698705057382465159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3292959196546819686573757 1234859698705057382465159)
                    ·
                      rfl

theorem cell22_3607321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 4, 3].length) (baseStart_3607321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3607321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3607321 prefixEnd_3607321 := by exact prefixLift 3607321
  have htrace : WordTrace (prefixWord ++ tailWord_3607321) baseStart_3607321 baseEnd_3607321 := by
    simpa [prefixWord, tailWord_3607321, baseEnd_3607321] using wordTrace_append hprefix tailTrace_3607321
  have hstable : (prefixWord ++ tailWord_3607321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607321).length < 2 ^ (prefixWord ++ tailWord_3607321).sum := by decide
  have hdescent : baseEnd_3607321 < baseStart_3607321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607400 : List Nat := [2, 1, 4, 2, 1, 3, 2, 1, 3, 3]
def baseStart_3607400 : Nat := 118140960795 + 3607400 * 2 ^ 59
def prefixEnd_3607400 : Nat := 4983230072969 + 3 ^ 40 * 3607400 * 2
def baseEnd_3607400 : Nat := 1234886742019527509739917

theorem tailTrace_3607400 : CollatzResearch.WordTrace tailWord_3607400 prefixEnd_3607400 1234886742019527509739917 := by
  unfold tailWord_3607400
  simp only [CollatzResearch.WordTrace]
  refine ⟨65786343565506684857645827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87715124754008913143527769 65786343565506684857645827)
  ·
    refine ⟨98679515348260027286468741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65786343565506684857645827 98679515348260027286468741)
    ·
      refine ⟨18502409127798755116212889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98679515348260027286468741 18502409127798755116212889)
      ·
        refine ⟨13876806845849066337159667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18502409127798755116212889 13876806845849066337159667)
        ·
          refine ⟨20815210268773599505739501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13876806845849066337159667 20815210268773599505739501)
          ·
            refine ⟨7805703850790099814652313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20815210268773599505739501 7805703850790099814652313)
            ·
              refine ⟨5854277888092574860989235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7805703850790099814652313 5854277888092574860989235)
              ·
                refine ⟨8781416832138862291483853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5854277888092574860989235 8781416832138862291483853)
                ·
                  refine ⟨3293031312052073359306445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8781416832138862291483853 3293031312052073359306445)
                  ·
                    refine ⟨1234886742019527509739917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3293031312052073359306445 1234886742019527509739917)
                    ·
                      rfl

theorem cell22_3607400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 1, 3, 3].length) (baseStart_3607400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3607400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3607400 prefixEnd_3607400 := by exact prefixLift 3607400
  have htrace : WordTrace (prefixWord ++ tailWord_3607400) baseStart_3607400 baseEnd_3607400 := by
    simpa [prefixWord, tailWord_3607400, baseEnd_3607400] using wordTrace_append hprefix tailTrace_3607400
  have hstable : (prefixWord ++ tailWord_3607400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607400).length < 2 ^ (prefixWord ++ tailWord_3607400).sum := by decide
  have hdescent : baseEnd_3607400 < baseStart_3607400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607411 : List Nat := [1, 1, 1, 2, 2, 1, 6, 1, 2, 5]
def baseStart_3607411 : Nat := 118140960795 + 3607411 * 2 ^ 59
def prefixEnd_3607411 : Nat := 4983230072969 + 3 ^ 40 * 3607411 * 2
def baseEnd_3607411 : Nat := 1234890507544327147714883

theorem tailTrace_3607411 : CollatzResearch.WordTrace tailWord_3607411 prefixEnd_3607411 1234890507544327147714883 := by
  unfold tailWord_3607411
  simp only [CollatzResearch.WordTrace]
  refine ⟨131573088333973518593942087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87715392222649012395961391 131573088333973518593942087)
  ·
    refine ⟨197359632500960277890913131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131573088333973518593942087 197359632500960277890913131)
    ·
      refine ⟨296039448751440416836369697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197359632500960277890913131 296039448751440416836369697)
      ·
        refine ⟨222029586563580312627277273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296039448751440416836369697 222029586563580312627277273)
        ·
          refine ⟨166522189922685234470457955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222029586563580312627277273 166522189922685234470457955)
          ·
            refine ⟨249783284884027851705686933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166522189922685234470457955 249783284884027851705686933)
            ·
              refine ⟨11708591478938805548704075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 249783284884027851705686933 11708591478938805548704075)
              ·
                refine ⟨17562887218408208323056113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11708591478938805548704075 17562887218408208323056113)
                ·
                  refine ⟨13172165413806156242292085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17562887218408208323056113 13172165413806156242292085)
                  ·
                    refine ⟨1234890507544327147714883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13172165413806156242292085 1234890507544327147714883)
                    ·
                      rfl

theorem cell22_3607411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 2, 5].length) (baseStart_3607411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3607411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3607411 prefixEnd_3607411 := by exact prefixLift 3607411
  have htrace : WordTrace (prefixWord ++ tailWord_3607411) baseStart_3607411 baseEnd_3607411 := by
    simpa [prefixWord, tailWord_3607411, baseEnd_3607411] using wordTrace_append hprefix tailTrace_3607411
  have hstable : (prefixWord ++ tailWord_3607411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607411).length < 2 ^ (prefixWord ++ tailWord_3607411).sum := by decide
  have hdescent : baseEnd_3607411 < baseStart_3607411 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607434 : List Nat := [3, 1, 2, 4, 1, 3, 1, 3, 1, 3]
def baseStart_3607434 : Nat := 118140960795 + 3607434 * 2 ^ 59
def prefixEnd_3607434 : Nat := 4983230072969 + 3 ^ 40 * 3607434 * 2
def baseEnd_3607434 : Nat := 1234898380914362754389813

theorem tailTrace_3607434 : CollatzResearch.WordTrace tailWord_3607434 prefixEnd_3607434 1234898380914362754389813 := by
  unfold tailWord_3607434
  simp only [CollatzResearch.WordTrace]
  refine ⟨32893481803222548380507339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87715951475260129014686237 32893481803222548380507339)
  ·
    refine ⟨49340222704833822570761009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32893481803222548380507339 49340222704833822570761009)
    ·
      refine ⟨37005167028625366928070757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49340222704833822570761009 37005167028625366928070757)
      ·
        refine ⟨6938468817867256299013267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37005167028625366928070757 6938468817867256299013267)
        ·
          refine ⟨10407703226800884448519901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6938468817867256299013267 10407703226800884448519901)
          ·
            refine ⟨3902888710050331668194963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10407703226800884448519901 3902888710050331668194963)
            ·
              refine ⟨5854333065075497502292445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3902888710050331668194963 5854333065075497502292445)
              ·
                refine ⟨2195374899403311563359667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5854333065075497502292445 2195374899403311563359667)
                ·
                  refine ⟨3293062349104967345039501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2195374899403311563359667 3293062349104967345039501)
                  ·
                    refine ⟨1234898380914362754389813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3293062349104967345039501 1234898380914362754389813)
                    ·
                      rfl

theorem cell22_3607434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 3, 1, 3].length) (baseStart_3607434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3607434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3607434 prefixEnd_3607434 := by exact prefixLift 3607434
  have htrace : WordTrace (prefixWord ++ tailWord_3607434) baseStart_3607434 baseEnd_3607434 := by
    simpa [prefixWord, tailWord_3607434, baseEnd_3607434] using wordTrace_append hprefix tailTrace_3607434
  have hstable : (prefixWord ++ tailWord_3607434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607434).length < 2 ^ (prefixWord ++ tailWord_3607434).sum := by decide
  have hdescent : baseEnd_3607434 < baseStart_3607434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607471 : List Nat := [1, 1, 2, 1, 2, 2, 2, 4, 1, 6]
def baseStart_3607471 : Nat := 118140960795 + 3607471 * 2 ^ 59
def prefixEnd_3607471 : Nat := 4983230072969 + 3 ^ 40 * 3607471 * 2
def baseEnd_3607471 : Nat := 1234911046770506991214699

theorem tailTrace_3607471 : CollatzResearch.WordTrace tailWord_3607471 prefixEnd_3607471 1234911046770506991214699 := by
  unfold tailWord_3607471
  simp only [CollatzResearch.WordTrace]
  refine ⟨131575276713756148841126267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87716851142504099227417511 131575276713756148841126267)
  ·
    refine ⟨197362915070634223261689401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131575276713756148841126267 197362915070634223261689401)
    ·
      refine ⟨148022186302975667446267051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197362915070634223261689401 148022186302975667446267051)
      ·
        refine ⟨222033279454463501169400577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148022186302975667446267051 222033279454463501169400577)
        ·
          refine ⟨166524959590847625877050433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222033279454463501169400577 166524959590847625877050433)
          ·
            refine ⟨124893719693135719407787825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166524959590847625877050433 124893719693135719407787825)
            ·
              refine ⟨93670289769851789555840869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124893719693135719407787825 93670289769851789555840869)
              ·
                refine ⟨17563179331847210541720163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93670289769851789555840869 17563179331847210541720163)
                ·
                  refine ⟨26344768997770815812580245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17563179331847210541720163 26344768997770815812580245)
                  ·
                    refine ⟨1234911046770506991214699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26344768997770815812580245 1234911046770506991214699)
                    ·
                      rfl

theorem cell22_3607471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 6].length) (baseStart_3607471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3607471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3607471 prefixEnd_3607471 := by exact prefixLift 3607471
  have htrace : WordTrace (prefixWord ++ tailWord_3607471) baseStart_3607471 baseEnd_3607471 := by
    simpa [prefixWord, tailWord_3607471, baseEnd_3607471] using wordTrace_append hprefix tailTrace_3607471
  have hstable : (prefixWord ++ tailWord_3607471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607471).length < 2 ^ (prefixWord ++ tailWord_3607471).sum := by decide
  have hdescent : baseEnd_3607471 < baseStart_3607471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607488 : List Nat := [2, 1, 1, 2, 3, 3, 1, 3, 2, 4]
def baseStart_3607488 : Nat := 118140960795 + 3607488 * 2 ^ 59
def prefixEnd_3607488 : Nat := 4983230072969 + 3 ^ 40 * 3607488 * 2
def baseEnd_3607488 : Nat := 1234916866217924613539647

theorem tailTrace_3607488 : CollatzResearch.WordTrace tailWord_3607488 prefixEnd_3607488 1234916866217924613539647 := by
  unfold tailWord_3607488
  simp only [CollatzResearch.WordTrace]
  refine ⟨65787948377347280372247559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87717264503129707162996745 65787948377347280372247559)
  ·
    refine ⟨98681922566020920558371339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65787948377347280372247559 98681922566020920558371339)
    ·
      refine ⟨148022883849031380837557009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98681922566020920558371339 148022883849031380837557009)
      ·
        refine ⟨111017162886773535628167757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148022883849031380837557009 111017162886773535628167757)
        ·
          refine ⟨41631436082540075860562909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111017162886773535628167757 41631436082540075860562909)
          ·
            refine ⟨15611788530952528447711091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41631436082540075860562909 15611788530952528447711091)
            ·
              refine ⟨23417682796428792671566637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15611788530952528447711091 23417682796428792671566637)
              ·
                refine ⟨8781631048660797251837489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23417682796428792671566637 8781631048660797251837489)
                ·
                  refine ⟨6586223286495597938878117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8781631048660797251837489 6586223286495597938878117)
                  ·
                    refine ⟨1234916866217924613539647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6586223286495597938878117 1234916866217924613539647)
                    ·
                      rfl

theorem cell22_3607488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 3, 2, 4].length) (baseStart_3607488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3607488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3607488 prefixEnd_3607488 := by exact prefixLift 3607488
  have htrace : WordTrace (prefixWord ++ tailWord_3607488) baseStart_3607488 baseEnd_3607488 := by
    simpa [prefixWord, tailWord_3607488, baseEnd_3607488] using wordTrace_append hprefix tailTrace_3607488
  have hstable : (prefixWord ++ tailWord_3607488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607488).length < 2 ^ (prefixWord ++ tailWord_3607488).sum := by decide
  have hdescent : baseEnd_3607488 < baseStart_3607488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607509 : List Nat := [1, 3, 2, 3, 3, 2, 2, 2, 4]
def baseStart_3607509 : Nat := 118140960795 + 3607509 * 2 ^ 59
def prefixEnd_3607509 : Nat := 4983230072969 + 3 ^ 40 * 3607509 * 2
def baseEnd_3607509 : Nat := 411641351649029186254861

theorem tailTrace_3607509 : CollatzResearch.WordTrace tailWord_3607509 prefixEnd_3607509 411641351649029186254861 := by
  unfold tailWord_3607509
  simp only [CollatzResearch.WordTrace]
  refine ⟨131576662687618481331009581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87717775125078987554006387 131576662687618481331009581)
  ·
    refine ⟨49341248507856930499128593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131576662687618481331009581 49341248507856930499128593)
    ·
      refine ⟨37005936380892697874346445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49341248507856930499128593 37005936380892697874346445)
      ·
        refine ⟨13877226142834761702879917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37005936380892697874346445 13877226142834761702879917)
        ·
          refine ⟨5203959803563035638579969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13877226142834761702879917 5203959803563035638579969)
          ·
            refine ⟨3902969852672276728934977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5203959803563035638579969 3902969852672276728934977)
            ·
              refine ⟨2927227389504207546701233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3902969852672276728934977 2927227389504207546701233)
              ·
                refine ⟨2195420542128155660025925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2927227389504207546701233 2195420542128155660025925)
                ·
                  refine ⟨411641351649029186254861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2195420542128155660025925 411641351649029186254861)
                  ·
                    rfl

theorem cell22_3607509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 2, 2, 4].length) (baseStart_3607509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3607509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3607509 prefixEnd_3607509 := by exact prefixLift 3607509
  have htrace : WordTrace (prefixWord ++ tailWord_3607509) baseStart_3607509 baseEnd_3607509 := by
    simpa [prefixWord, tailWord_3607509, baseEnd_3607509] using wordTrace_append hprefix tailTrace_3607509
  have hstable : (prefixWord ++ tailWord_3607509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607509).length < 2 ^ (prefixWord ++ tailWord_3607509).sum := by decide
  have hdescent : baseEnd_3607509 < baseStart_3607509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607531 : List Nat := [1, 1, 1, 1, 2, 3, 1, 1, 11]
def baseStart_3607531 : Nat := 118140960795 + 3607531 * 2 ^ 59
def prefixEnd_3607531 : Nat := 4983230072969 + 3 ^ 40 * 3607531 * 2
def baseEnd_3607531 : Nat := 411643861998895611571505

theorem tailTrace_3607531 : CollatzResearch.WordTrace tailWord_3607531 prefixEnd_3607531 411643861998895611571505 := by
  unfold tailWord_3607531
  simp only [CollatzResearch.WordTrace]
  refine ⟨131577465093538779088310447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87718310062359186058873631 131577465093538779088310447)
  ·
    refine ⟨197366197640308168632465671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131577465093538779088310447 197366197640308168632465671)
    ·
      refine ⟨296049296460462252948698507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197366197640308168632465671 296049296460462252948698507)
      ·
        refine ⟨444073944690693379423047761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296049296460462252948698507 444073944690693379423047761)
        ·
          refine ⟨333055458518020034567285821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 444073944690693379423047761 333055458518020034567285821)
          ·
            refine ⟨124895796944257512962732183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 333055458518020034567285821 124895796944257512962732183)
            ·
              refine ⟨187343695416386269444098275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124895796944257512962732183 187343695416386269444098275)
              ·
                refine ⟨281015543124579404166147413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187343695416386269444098275 281015543124579404166147413)
                ·
                  refine ⟨411643861998895611571505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 281015543124579404166147413 411643861998895611571505)
                  ·
                    rfl

theorem cell22_3607531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 11].length) (baseStart_3607531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3607531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3607531 prefixEnd_3607531 := by exact prefixLift 3607531
  have htrace : WordTrace (prefixWord ++ tailWord_3607531) baseStart_3607531 baseEnd_3607531 := by
    simpa [prefixWord, tailWord_3607531, baseEnd_3607531] using wordTrace_append hprefix tailTrace_3607531
  have hstable : (prefixWord ++ tailWord_3607531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607531).length < 2 ^ (prefixWord ++ tailWord_3607531).sum := by decide
  have hdescent : baseEnd_3607531 < baseStart_3607531 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607535 : List Nat := [1, 1, 2, 1, 4, 4, 1, 2, 3, 3]
def baseStart_3607535 : Nat := 118140960795 + 3607535 * 2 ^ 59
def prefixEnd_3607535 : Nat := 4983230072969 + 3 ^ 40 * 3607535 * 2
def baseEnd_3607535 : Nat := 1234932955278432157614503

theorem tailTrace_3607535 : CollatzResearch.WordTrace tailWord_3607535 prefixEnd_3607535 1234932955278432157614503 := by
  unfold tailWord_3607535
  simp only [CollatzResearch.WordTrace]
  refine ⟨131577610985524287771456059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87718407323682858514304039 131577610985524287771456059)
  ·
    refine ⟨197366416478286431657184089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131577610985524287771456059 197366416478286431657184089)
    ·
      refine ⟨148024812358714823742888067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197366416478286431657184089 148024812358714823742888067)
      ·
        refine ⟨222037218538072235614332101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148024812358714823742888067 222037218538072235614332101)
        ·
          refine ⟨41631978475888544177687269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 222037218538072235614332101 41631978475888544177687269)
          ·
            refine ⟨7805995964229102033316363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41631978475888544177687269 7805995964229102033316363)
            ·
              refine ⟨11708993946343653049974545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7805995964229102033316363 11708993946343653049974545)
              ·
                refine ⟨8781745459757739787480909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11708993946343653049974545 8781745459757739787480909)
                ·
                  refine ⟨3293154547409152420305341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8781745459757739787480909 3293154547409152420305341)
                  ·
                    refine ⟨1234932955278432157614503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3293154547409152420305341 1234932955278432157614503)
                    ·
                      rfl

theorem cell22_3607535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 2, 3, 3].length) (baseStart_3607535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3607535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3607535 prefixEnd_3607535 := by exact prefixLift 3607535
  have htrace : WordTrace (prefixWord ++ tailWord_3607535) baseStart_3607535 baseEnd_3607535 := by
    simpa [prefixWord, tailWord_3607535, baseEnd_3607535] using wordTrace_append hprefix tailTrace_3607535
  have hstable : (prefixWord ++ tailWord_3607535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607535).length < 2 ^ (prefixWord ++ tailWord_3607535).sum := by decide
  have hdescent : baseEnd_3607535 < baseStart_3607535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607563 : List Nat := [1, 1, 1, 1, 6, 2, 1, 2, 2, 5]
def baseStart_3607563 : Nat := 118140960795 + 3607563 * 2 ^ 59
def prefixEnd_3607563 : Nat := 4983230072969 + 3 ^ 40 * 3607563 * 2
def baseEnd_3607563 : Nat := 1234942540250649417914417

theorem tailTrace_3607563 : CollatzResearch.WordTrace tailWord_3607563 prefixEnd_3607563 1234942540250649417914417 := by
  unfold tailWord_3607563
  simp only [CollatzResearch.WordTrace]
  refine ⟨131578632229422848553475343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87719088152948565702316895 131578632229422848553475343)
  ·
    refine ⟨197367948344134272830213015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131578632229422848553475343 197367948344134272830213015)
    ·
      refine ⟨296051922516201409245319523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197367948344134272830213015 296051922516201409245319523)
      ·
        refine ⟨444077883774302113867979285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296051922516201409245319523 444077883774302113867979285)
        ·
          refine ⟨20816150801920411587561529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 444077883774302113867979285 20816150801920411587561529)
          ·
            refine ⟨15612113101440308690671147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20816150801920411587561529 15612113101440308690671147)
            ·
              refine ⟨23418169652160463036006721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15612113101440308690671147 23418169652160463036006721)
              ·
                refine ⟨17563627239120347277005041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23418169652160463036006721 17563627239120347277005041)
                ·
                  refine ⟨13172720429340260457753781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17563627239120347277005041 13172720429340260457753781)
                  ·
                    refine ⟨1234942540250649417914417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13172720429340260457753781 1234942540250649417914417)
                    ·
                      rfl

theorem cell22_3607563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 2, 5].length) (baseStart_3607563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3607563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3607563 prefixEnd_3607563 := by exact prefixLift 3607563
  have htrace : WordTrace (prefixWord ++ tailWord_3607563) baseStart_3607563 baseEnd_3607563 := by
    simpa [prefixWord, tailWord_3607563, baseEnd_3607563] using wordTrace_append hprefix tailTrace_3607563
  have hstable : (prefixWord ++ tailWord_3607563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607563).length < 2 ^ (prefixWord ++ tailWord_3607563).sum := by decide
  have hdescent : baseEnd_3607563 < baseStart_3607563 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607595 : List Nat := [1, 1, 1, 1, 2, 1, 8, 2, 1, 4]
def baseStart_3607595 : Nat := 118140960795 + 3607595 * 2 ^ 59
def prefixEnd_3607595 : Nat := 4983230072969 + 3 ^ 40 * 3607595 * 2
def baseEnd_3607595 : Nat := 1234953494504612001114319

theorem tailTrace_3607595 : CollatzResearch.WordTrace tailWord_3607595 prefixEnd_3607595 1234953494504612001114319 := by
  unfold tailWord_3607595
  simp only [CollatzResearch.WordTrace]
  refine ⟨131579799365306918018640239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87719866243537945345760159 131579799365306918018640239)
  ·
    refine ⟨197369699047960377027960359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131579799365306918018640239 197369699047960377027960359)
    ·
      refine ⟨296054548571940565541940539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197369699047960377027960359 296054548571940565541940539)
      ·
        refine ⟨444081822857910848312910809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296054548571940565541940539 444081822857910848312910809)
        ·
          refine ⟨333061367143433136234683107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 444081822857910848312910809 333061367143433136234683107)
          ·
            refine ⟨499592050715149704352024661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333061367143433136234683107 499592050715149704352024661)
            ·
              refine ⟨5854594344318160597875289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 499592050715149704352024661 5854594344318160597875289)
              ·
                refine ⟨4390945758238620448406467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5854594344318160597875289 4390945758238620448406467)
                ·
                  refine ⟨6586418637357930672609701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4390945758238620448406467 6586418637357930672609701)
                  ·
                    refine ⟨1234953494504612001114319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6586418637357930672609701 1234953494504612001114319)
                    ·
                      rfl

theorem cell22_3607595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 2, 1, 4].length) (baseStart_3607595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3607595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3607595 prefixEnd_3607595 := by exact prefixLift 3607595
  have htrace : WordTrace (prefixWord ++ tailWord_3607595) baseStart_3607595 baseEnd_3607595 := by
    simpa [prefixWord, tailWord_3607595, baseEnd_3607595] using wordTrace_append hprefix tailTrace_3607595
  have hstable : (prefixWord ++ tailWord_3607595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607595).length < 2 ^ (prefixWord ++ tailWord_3607595).sum := by decide
  have hdescent : baseEnd_3607595 < baseStart_3607595 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607646 : List Nat := [4, 4, 1, 1, 1, 1, 3, 2, 1, 4]
def baseStart_3607646 : Nat := 118140960795 + 3607646 * 2 ^ 59
def prefixEnd_3607646 : Nat := 4983230072969 + 3 ^ 40 * 3607646 * 2
def baseEnd_3607646 : Nat := 1234970952846864868089163

theorem tailTrace_3607646 : CollatzResearch.WordTrace tailWord_3607646 prefixEnd_3607646 1234970952846864868089163 := by
  unfold tailWord_3607646
  simp only [CollatzResearch.WordTrace]
  refine ⟨16447707436015269216093349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87721106325414769152497861 16447707436015269216093349)
  ·
    refine ⟨3083945144252862978017503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16447707436015269216093349 3083945144252862978017503)
    ·
      refine ⟨4625917716379294467026255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3083945144252862978017503 4625917716379294467026255)
      ·
        refine ⟨6938876574568941700539383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4625917716379294467026255 6938876574568941700539383)
        ·
          refine ⟨10408314861853412550809075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6938876574568941700539383 10408314861853412550809075)
          ·
            refine ⟨15612472292780118826213613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10408314861853412550809075 15612472292780118826213613)
            ·
              refine ⟨5854677109792544559830105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15612472292780118826213613 5854677109792544559830105)
              ·
                refine ⟨4391007832344408419872579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5854677109792544559830105 4391007832344408419872579)
                ·
                  refine ⟨6586511748516612629808869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4391007832344408419872579 6586511748516612629808869)
                  ·
                    refine ⟨1234970952846864868089163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6586511748516612629808869 1234970952846864868089163)
                    ·
                      rfl

theorem cell22_3607646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_3607646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3607646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3607646 prefixEnd_3607646 := by exact prefixLift 3607646
  have htrace : WordTrace (prefixWord ++ tailWord_3607646) baseStart_3607646 baseEnd_3607646 := by
    simpa [prefixWord, tailWord_3607646, baseEnd_3607646] using wordTrace_append hprefix tailTrace_3607646
  have hstable : (prefixWord ++ tailWord_3607646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607646).length < 2 ^ (prefixWord ++ tailWord_3607646).sum := by decide
  have hdescent : baseEnd_3607646 < baseStart_3607646 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607678 : List Nat := [4, 2, 4, 1, 1, 1, 1, 4, 4]
def baseStart_3607678 : Nat := 118140960795 + 3607678 * 2 ^ 59
def prefixEnd_3607678 : Nat := 4983230072969 + 3 ^ 40 * 3607678 * 2
def baseEnd_3607678 : Nat := 411660635700275817096355

theorem tailTrace_3607678 : CollatzResearch.WordTrace tailWord_3607678 prefixEnd_3607678 411660635700275817096355 := by
  unfold tailWord_3607678
  simp only [CollatzResearch.WordTrace]
  refine ⟨16447853328000777899238961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87721884416004148795941125 16447853328000777899238961)
  ·
    refine ⟨12335889996000583424429221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16447853328000777899238961 12335889996000583424429221)
    ·
      refine ⟨2312979374250109392080479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12335889996000583424429221 2312979374250109392080479)
      ·
        refine ⟨3469469061375164088120719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2312979374250109392080479 3469469061375164088120719)
        ·
          refine ⟨5204203592062746132181079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3469469061375164088120719 5204203592062746132181079)
          ·
            refine ⟨7806305388094119198271619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5204203592062746132181079 7806305388094119198271619)
            ·
              refine ⟨11709458082141178797407429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7806305388094119198271619 11709458082141178797407429)
              ·
                refine ⟨2195523390401471024513893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11709458082141178797407429 2195523390401471024513893)
                ·
                  refine ⟨411660635700275817096355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2195523390401471024513893 411660635700275817096355)
                  ·
                    rfl

theorem cell22_3607678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 4, 4].length) (baseStart_3607678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3607678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3607678 prefixEnd_3607678 := by exact prefixLift 3607678
  have htrace : WordTrace (prefixWord ++ tailWord_3607678) baseStart_3607678 baseEnd_3607678 := by
    simpa [prefixWord, tailWord_3607678, baseEnd_3607678] using wordTrace_append hprefix tailTrace_3607678
  have hstable : (prefixWord ++ tailWord_3607678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607678).length < 2 ^ (prefixWord ++ tailWord_3607678).sum := by decide
  have hdescent : baseEnd_3607678 < baseStart_3607678 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607775 : List Nat := [1, 1, 2, 3, 2, 1, 4, 1, 1, 6]
def baseStart_3607775 : Nat := 118140960795 + 3607775 * 2 ^ 59
def prefixEnd_3607775 : Nat := 4983230072969 + 3 ^ 40 * 3607775 * 2
def baseEnd_3607775 : Nat := 1235015112183151531613767

theorem tailTrace_3607775 : CollatzResearch.WordTrace tailWord_3607775 prefixEnd_3607775 1235015112183151531613767 := by
  unfold tailWord_3607775
  simp only [CollatzResearch.WordTrace]
  refine ⟨131586364504654808760192779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87724243003103205840128519 131586364504654808760192779)
  ·
    refine ⟨197379546756982213140289169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131586364504654808760192779 197379546756982213140289169)
    ·
      refine ⟨148034660067736659855216877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197379546756982213140289169 148034660067736659855216877)
      ·
        refine ⟨55512997525401247445706329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148034660067736659855216877 55512997525401247445706329)
        ·
          refine ⟨41634748144050935584279747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55512997525401247445706329 41634748144050935584279747)
          ·
            refine ⟨62452122216076403376419621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41634748144050935584279747 62452122216076403376419621)
            ·
              refine ⟨11709772915514325633078679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62452122216076403376419621 11709772915514325633078679)
              ·
                refine ⟨17564659373271488449618019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11709772915514325633078679 17564659373271488449618019)
                ·
                  refine ⟨26346989059907232674427029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17564659373271488449618019 26346989059907232674427029)
                  ·
                    refine ⟨1235015112183151531613767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26346989059907232674427029 1235015112183151531613767)
                    ·
                      rfl

theorem cell22_3607775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 6].length) (baseStart_3607775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3607775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3607775 prefixEnd_3607775 := by exact prefixLift 3607775
  have htrace : WordTrace (prefixWord ++ tailWord_3607775) baseStart_3607775 baseEnd_3607775 := by
    simpa [prefixWord, tailWord_3607775, baseEnd_3607775] using wordTrace_append hprefix tailTrace_3607775
  have hstable : (prefixWord ++ tailWord_3607775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607775).length < 2 ^ (prefixWord ++ tailWord_3607775).sum := by decide
  have hdescent : baseEnd_3607775 < baseStart_3607775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607777 : List Nat := [1, 2, 3, 1, 3, 2, 1, 2, 4, 3]
def baseStart_3607777 : Nat := 118140960795 + 3607777 * 2 ^ 59
def prefixEnd_3607777 : Nat := 4983230072969 + 3 ^ 40 * 3607777 * 2
def baseEnd_3607777 : Nat := 1235015796824024193063761

theorem tailTrace_3607777 : CollatzResearch.WordTrace tailWord_3607777 prefixEnd_3607777 1235015796824024193063761 := by
  unfold tailWord_3607777
  simp only [CollatzResearch.WordTrace]
  refine ⟨131586437450647563101765585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87724291633765042067843723 131586437450647563101765585)
  ·
    refine ⟨98689828087985672326324189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131586437450647563101765585 98689828087985672326324189)
    ·
      refine ⟨37008685532994627122371571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98689828087985672326324189 37008685532994627122371571)
      ·
        refine ⟨55513028299491940683557357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37008685532994627122371571 55513028299491940683557357)
        ·
          refine ⟨20817385612309477756334009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55513028299491940683557357 20817385612309477756334009)
          ·
            refine ⟨15613039209232108317250507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20817385612309477756334009 15613039209232108317250507)
            ·
              refine ⟨23419558813848162475875761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15613039209232108317250507 23419558813848162475875761)
              ·
                refine ⟨17564669110386121856906821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23419558813848162475875761 17564669110386121856906821)
                ·
                  refine ⟨3293375458197397848170029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17564669110386121856906821 3293375458197397848170029)
                  ·
                    refine ⟨1235015796824024193063761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3293375458197397848170029 1235015796824024193063761)
                    ·
                      rfl

theorem cell22_3607777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 4, 3].length) (baseStart_3607777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3607777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3607777 prefixEnd_3607777 := by exact prefixLift 3607777
  have htrace : WordTrace (prefixWord ++ tailWord_3607777) baseStart_3607777 baseEnd_3607777 := by
    simpa [prefixWord, tailWord_3607777, baseEnd_3607777] using wordTrace_append hprefix tailTrace_3607777
  have hstable : (prefixWord ++ tailWord_3607777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607777).length < 2 ^ (prefixWord ++ tailWord_3607777).sum := by decide
  have hdescent : baseEnd_3607777 < baseStart_3607777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607790 : List Nat := [4, 1, 2, 1, 1, 1, 12]
def baseStart_3607790 : Nat := 118140960795 + 3607790 * 2 ^ 59
def prefixEnd_3607790 : Nat := 4983230072969 + 3 ^ 40 * 3607790 * 2
def baseEnd_3607790 : Nat := 45741490629248018240323

theorem tailTrace_3607790 : CollatzResearch.WordTrace tailWord_3607790 prefixEnd_3607790 45741490629248018240323 := by
  unfold tailWord_3607790
  simp only [CollatzResearch.WordTrace]
  refine ⟨16448363949950058290248603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87724607733066977547992549 16448363949950058290248603)
  ·
    refine ⟨24672545924925087435372905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16448363949950058290248603 24672545924925087435372905)
    ·
      refine ⟨18504409443693815576529679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24672545924925087435372905 18504409443693815576529679)
      ·
        refine ⟨27756614165540723364794519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18504409443693815576529679 27756614165540723364794519)
        ·
          refine ⟨41634921248311085047191779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27756614165540723364794519 41634921248311085047191779)
          ·
            refine ⟨62452381872466627570787669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41634921248311085047191779 62452381872466627570787669)
            ·
              refine ⟨45741490629248018240323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 62452381872466627570787669 45741490629248018240323)
              ·
                rfl

theorem cell22_3607790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 12].length) (baseStart_3607790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3607790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3607790 prefixEnd_3607790 := by exact prefixLift 3607790
  have htrace : WordTrace (prefixWord ++ tailWord_3607790) baseStart_3607790 baseEnd_3607790 := by
    simpa [prefixWord, tailWord_3607790, baseEnd_3607790] using wordTrace_append hprefix tailTrace_3607790
  have hstable : (prefixWord ++ tailWord_3607790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607790).length < 2 ^ (prefixWord ++ tailWord_3607790).sum := by decide
  have hdescent : baseEnd_3607790 < baseStart_3607790 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607811 : List Nat := [1, 1, 1, 3, 2, 6, 2, 1, 2, 3]
def baseStart_3607811 : Nat := 118140960795 + 3607811 * 2 ^ 59
def prefixEnd_3607811 : Nat := 4983230072969 + 3 ^ 40 * 3607811 * 2
def baseEnd_3607811 : Nat := 1235027435718859437713657

theorem tailTrace_3607811 : CollatzResearch.WordTrace tailWord_3607811 prefixEnd_3607811 1235027435718859437713657 := by
  unfold tailWord_3607811
  simp only [CollatzResearch.WordTrace]
  refine ⟨131587677532524386908503287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87725118355016257939002191 131587677532524386908503287)
  ·
    refine ⟨197381516298786580362754931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131587677532524386908503287 197381516298786580362754931)
    ·
      refine ⟨296072274448179870544132397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197381516298786580362754931 296072274448179870544132397)
      ·
        refine ⟨111027102918067451454049649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 296072274448179870544132397 111027102918067451454049649)
        ·
          refine ⟨83270327188550588590537237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111027102918067451454049649 83270327188550588590537237)
          ·
            refine ⟨3903296586963308840181433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 83270327188550588590537237 3903296586963308840181433)
            ·
              refine ⟨2927472440222481630136075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3903296586963308840181433 2927472440222481630136075)
              ·
                refine ⟨4391208660333722445204113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2927472440222481630136075 4391208660333722445204113)
                ·
                  refine ⟨3293406495250291833903085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4391208660333722445204113 3293406495250291833903085)
                  ·
                    refine ⟨1235027435718859437713657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3293406495250291833903085 1235027435718859437713657)
                    ·
                      rfl

theorem cell22_3607811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 2, 1, 2, 3].length) (baseStart_3607811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3607811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3607811 prefixEnd_3607811 := by exact prefixLift 3607811
  have htrace : WordTrace (prefixWord ++ tailWord_3607811) baseStart_3607811 baseEnd_3607811 := by
    simpa [prefixWord, tailWord_3607811, baseEnd_3607811] using wordTrace_append hprefix tailTrace_3607811
  have hstable : (prefixWord ++ tailWord_3607811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607811).length < 2 ^ (prefixWord ++ tailWord_3607811).sum := by decide
  have hdescent : baseEnd_3607811 < baseStart_3607811 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607929 : List Nat := [1, 2, 1, 3, 2, 1, 2, 5, 2, 3]
def baseStart_3607929 : Nat := 118140960795 + 3607929 * 2 ^ 59
def prefixEnd_3607929 : Nat := 4983230072969 + 3 ^ 40 * 3607929 * 2
def baseEnd_3607929 : Nat := 1235067829530346463263295

theorem tailTrace_3607929 : CollatzResearch.WordTrace tailWord_3607929 prefixEnd_3607929 1235067829530346463263295 := by
  unfold tailWord_3607929
  simp only [CollatzResearch.WordTrace]
  refine ⟨131591981346096893061298841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87727987564064595374199227 131591981346096893061298841)
  ·
    refine ⟨98693986009572669795974131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131591981346096893061298841 98693986009572669795974131)
    ·
      refine ⟨148040979014359004693961197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98693986009572669795974131 148040979014359004693961197)
      ·
        refine ⟨55515367130384626760235449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148040979014359004693961197 55515367130384626760235449)
        ·
          refine ⟨41636525347788470070176587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55515367130384626760235449 41636525347788470070176587)
          ·
            refine ⟨62454788021682705105264881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41636525347788470070176587 62454788021682705105264881)
            ·
              refine ⟨46841091016262028828948661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62454788021682705105264881 46841091016262028828948661)
              ·
                refine ⟨4391352282774565202713937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46841091016262028828948661 4391352282774565202713937)
                ·
                  refine ⟨3293514212080923902035453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4391352282774565202713937 3293514212080923902035453)
                  ·
                    refine ⟨1235067829530346463263295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3293514212080923902035453 1235067829530346463263295)
                    ·
                      rfl

theorem cell22_3607929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 5, 2, 3].length) (baseStart_3607929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3607929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3607929 prefixEnd_3607929 := by exact prefixLift 3607929
  have htrace : WordTrace (prefixWord ++ tailWord_3607929) baseStart_3607929 baseEnd_3607929 := by
    simpa [prefixWord, tailWord_3607929, baseEnd_3607929] using wordTrace_append hprefix tailTrace_3607929
  have hstable : (prefixWord ++ tailWord_3607929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607929).length < 2 ^ (prefixWord ++ tailWord_3607929).sum := by decide
  have hdescent : baseEnd_3607929 < baseStart_3607929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607972 : List Nat := [2, 3, 1, 2, 1, 1, 1, 3, 2, 6]
def baseStart_3607972 : Nat := 118140960795 + 3607972 * 2 ^ 59
def prefixEnd_3607972 : Nat := 4983230072969 + 3 ^ 40 * 3607972 * 2
def baseEnd_3607972 : Nat := 1235082549309108684438163

theorem tailTrace_3607972 : CollatzResearch.WordTrace tailWord_3607972 prefixEnd_3607972 1235082549309108684438163 := by
  unfold tailWord_3607972
  simp only [CollatzResearch.WordTrace]
  refine ⟨65796774842470555702557085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87729033123294074270076113 65796774842470555702557085)
  ·
    refine ⟨24673790565926458388458907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65796774842470555702557085 24673790565926458388458907)
    ·
      refine ⟨37010685848889687582688361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24673790565926458388458907 37010685848889687582688361)
      ·
        refine ⟨27758014386667265687016271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37010685848889687582688361 27758014386667265687016271)
        ·
          refine ⟨41637021580000898530524407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27758014386667265687016271 41637021580000898530524407)
          ·
            refine ⟨62455532370001347795786611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41637021580000898530524407 62455532370001347795786611)
            ·
              refine ⟨93683298555002021693679917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62455532370001347795786611 93683298555002021693679917)
              ·
                refine ⟨35131236958125758135129969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93683298555002021693679917 35131236958125758135129969)
                ·
                  refine ⟨26348427718594318601347477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35131236958125758135129969 26348427718594318601347477)
                  ·
                    refine ⟨1235082549309108684438163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26348427718594318601347477 1235082549309108684438163)
                    ·
                      rfl

theorem cell22_3607972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_3607972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3607972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3607972 prefixEnd_3607972 := by exact prefixLift 3607972
  have htrace : WordTrace (prefixWord ++ tailWord_3607972) baseStart_3607972 baseEnd_3607972 := by
    simpa [prefixWord, tailWord_3607972, baseEnd_3607972] using wordTrace_append hprefix tailTrace_3607972
  have hstable : (prefixWord ++ tailWord_3607972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607972).length < 2 ^ (prefixWord ++ tailWord_3607972).sum := by decide
  have hdescent : baseEnd_3607972 < baseStart_3607972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607976 : List Nat := [2, 1, 6, 1, 2, 1, 2, 7]
def baseStart_3607976 : Nat := 118140960795 + 3607976 * 2 ^ 59
def prefixEnd_3607976 : Nat := 4983230072969 + 3 ^ 40 * 3607976 * 2
def baseEnd_3607976 : Nat := 137231546510094889704239

theorem tailTrace_3607976 : CollatzResearch.WordTrace tailWord_3607976 prefixEnd_3607976 137231546510094889704239 := by
  unfold tailWord_3607976
  simp only [CollatzResearch.WordTrace]
  refine ⟨65796847788463310044129891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87729130384617746725506521 65796847788463310044129891)
  ·
    refine ⟨98695271682694965066194837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65796847788463310044129891 98695271682694965066194837)
    ·
      refine ⟨4626340860126326487477883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 98695271682694965066194837 4626340860126326487477883)
      ·
        refine ⟨6939511290189489731216825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4626340860126326487477883 6939511290189489731216825)
        ·
          refine ⟨5204633467642117298412619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6939511290189489731216825 5204633467642117298412619)
          ·
            refine ⟨7806950201463175947618929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5204633467642117298412619 7806950201463175947618929)
            ·
              refine ⟨5855212651097381960714197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7806950201463175947618929 5855212651097381960714197)
              ·
                refine ⟨137231546510094889704239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5855212651097381960714197 137231546510094889704239)
                ·
                  rfl

theorem cell22_3607976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 7].length) (baseStart_3607976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3607976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3607976 prefixEnd_3607976 := by exact prefixLift 3607976
  have htrace : WordTrace (prefixWord ++ tailWord_3607976) baseStart_3607976 baseEnd_3607976 := by
    simpa [prefixWord, tailWord_3607976, baseEnd_3607976] using wordTrace_append hprefix tailTrace_3607976
  have hstable : (prefixWord ++ tailWord_3607976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607976).length < 2 ^ (prefixWord ++ tailWord_3607976).sum := by decide
  have hdescent : baseEnd_3607976 < baseStart_3607976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608025 : List Nat := [1, 2, 1, 2, 4, 4, 2, 2, 1, 3]
def baseStart_3608025 : Nat := 118140960795 + 3608025 * 2 ^ 59
def prefixEnd_3608025 : Nat := 4983230072969 + 3 ^ 40 * 3608025 * 2
def baseEnd_3608025 : Nat := 1235100692292234212863001

theorem tailTrace_3608025 : CollatzResearch.WordTrace tailWord_3608025 prefixEnd_3608025 1235100692292234212863001 := by
  unfold tailWord_3608025
  simp only [CollatzResearch.WordTrace]
  refine ⟨131595482753749101456793529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87730321835832734304529019 131595482753749101456793529)
  ·
    refine ⟨98696612065311826092595147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131595482753749101456793529 98696612065311826092595147)
    ·
      refine ⟨148044918097967739138892721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98696612065311826092595147 148044918097967739138892721)
      ·
        refine ⟨111033688573475804354169541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148044918097967739138892721 111033688573475804354169541)
        ·
          refine ⟨20818816607526713316406789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111033688573475804354169541 20818816607526713316406789)
          ·
            refine ⟨3903528113911258746826273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20818816607526713316406789 3903528113911258746826273)
            ·
              refine ⟨2927646085433444060119705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3903528113911258746826273 2927646085433444060119705)
              ·
                refine ⟨2195734564075083045089779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2927646085433444060119705 2195734564075083045089779)
                ·
                  refine ⟨3293601846112624567634669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2195734564075083045089779 3293601846112624567634669)
                  ·
                    refine ⟨1235100692292234212863001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3293601846112624567634669 1235100692292234212863001)
                    ·
                      rfl

theorem cell22_3608025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 2, 2, 1, 3].length) (baseStart_3608025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3608025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3608025 prefixEnd_3608025 := by exact prefixLift 3608025
  have htrace : WordTrace (prefixWord ++ tailWord_3608025) baseStart_3608025 baseEnd_3608025 := by
    simpa [prefixWord, tailWord_3608025, baseEnd_3608025] using wordTrace_append hprefix tailTrace_3608025
  have hstable : (prefixWord ++ tailWord_3608025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608025).length < 2 ^ (prefixWord ++ tailWord_3608025).sum := by decide
  have hdescent : baseEnd_3608025 < baseStart_3608025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608049 : List Nat := [1, 2, 2, 2, 3, 3, 1, 2, 6]
def baseStart_3608049 : Nat := 118140960795 + 3608049 * 2 ^ 59
def prefixEnd_3608049 : Nat := 4983230072969 + 3 ^ 40 * 3608049 * 2
def baseEnd_3608049 : Nat := 411702969327568716754309

theorem tailTrace_3608049 : CollatzResearch.WordTrace tailWord_3608049 prefixEnd_3608049 411702969327568716754309 := by
  unfold tailWord_3608049
  simp only [CollatzResearch.WordTrace]
  refine ⟨131596358105662153555667201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87730905403774769037111467 131596358105662153555667201)
  ·
    refine ⟨98697268579246615166750401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131596358105662153555667201 98697268579246615166750401)
    ·
      refine ⟨74022951434434961375062801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98697268579246615166750401 74022951434434961375062801)
      ·
        refine ⟨55517213575826221031297101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74022951434434961375062801 55517213575826221031297101)
        ·
          refine ⟨20818955090934832886736413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55517213575826221031297101 20818955090934832886736413)
          ·
            refine ⟨7807108159100562332526155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20818955090934832886736413 7807108159100562332526155)
            ·
              refine ⟨11710662238650843498789233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7807108159100562332526155 11710662238650843498789233)
              ·
                refine ⟨8782996678988132624091925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11710662238650843498789233 8782996678988132624091925)
                ·
                  refine ⟨411702969327568716754309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8782996678988132624091925 411702969327568716754309)
                  ·
                    rfl

theorem cell22_3608049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 2, 6].length) (baseStart_3608049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3608049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3608049 prefixEnd_3608049 := by exact prefixLift 3608049
  have htrace : WordTrace (prefixWord ++ tailWord_3608049) baseStart_3608049 baseEnd_3608049 := by
    simpa [prefixWord, tailWord_3608049, baseEnd_3608049] using wordTrace_append hprefix tailTrace_3608049
  have hstable : (prefixWord ++ tailWord_3608049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608049).length < 2 ^ (prefixWord ++ tailWord_3608049).sum := by decide
  have hdescent : baseEnd_3608049 < baseStart_3608049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608068 : List Nat := [2, 3, 2, 3, 2, 1, 1, 3, 1, 4]
def baseStart_3608068 : Nat := 118140960795 + 3608068 * 2 ^ 59
def prefixEnd_3608068 : Nat := 4983230072969 + 3 ^ 40 * 3608068 * 2
def baseEnd_3608068 : Nat := 1235115412070996434037869

theorem tailTrace_3608068 : CollatzResearch.WordTrace tailWord_3608068 prefixEnd_3608068 1235115412070996434037869 := by
  unfold tailWord_3608068
  simp only [CollatzResearch.WordTrace]
  refine ⟨65798525546296659900304429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87731367395062213200405905 65798525546296659900304429)
  ·
    refine ⟨24674447079861247462614161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65798525546296659900304429 24674447079861247462614161)
    ·
      refine ⟨18505835309895935596960621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24674447079861247462614161 18505835309895935596960621)
      ·
        refine ⟨6939688241210975848860233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18505835309895935596960621 6939688241210975848860233)
        ·
          refine ⟨5204766180908231886645175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6939688241210975848860233 5204766180908231886645175)
          ·
            refine ⟨7807149271362347829967763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5204766180908231886645175 7807149271362347829967763)
            ·
              refine ⟨11710723907043521744951645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7807149271362347829967763 11710723907043521744951645)
              ·
                refine ⟨4391521465141320654356867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11710723907043521744951645 4391521465141320654356867)
                ·
                  refine ⟨6587282197711980981535301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4391521465141320654356867 6587282197711980981535301)
                  ·
                    refine ⟨1235115412070996434037869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6587282197711980981535301 1235115412070996434037869)
                    ·
                      rfl

theorem cell22_3608068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_3608068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3608068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3608068 prefixEnd_3608068 := by exact prefixLift 3608068
  have htrace : WordTrace (prefixWord ++ tailWord_3608068) baseStart_3608068 baseEnd_3608068 := by
    simpa [prefixWord, tailWord_3608068, baseEnd_3608068] using wordTrace_append hprefix tailTrace_3608068
  have hstable : (prefixWord ++ tailWord_3608068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608068).length < 2 ^ (prefixWord ++ tailWord_3608068).sum := by decide
  have hdescent : baseEnd_3608068 < baseStart_3608068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608139 : List Nat := [1, 1, 1, 1, 3, 1, 3, 6, 5]
def baseStart_3608139 : Nat := 118140960795 + 3608139 * 2 ^ 59
def prefixEnd_3608139 : Nat := 4983230072969 + 3 ^ 40 * 3608139 * 2
def baseEnd_3608139 : Nat := 411713238940658638504217

theorem tailTrace_3608139 : CollatzResearch.WordTrace tailWord_3608139 prefixEnd_3608139 411713238940658638504217 := by
  unfold tailWord_3608139
  simp only [CollatzResearch.WordTrace]
  refine ⟨131599640675336098926443471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87733093783557399284295647 131599640675336098926443471)
  ·
    refine ⟨197399461013004148389665207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131599640675336098926443471 197399461013004148389665207)
    ·
      refine ⟨296099191519506222584497811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197399461013004148389665207 296099191519506222584497811)
      ·
        refine ⟨444148787279259333876746717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296099191519506222584497811 444148787279259333876746717)
        ·
          refine ⟨166555795229722250203780019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 444148787279259333876746717 166555795229722250203780019)
          ·
            refine ⟨249833692844583375305670029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166555795229722250203780019 249833692844583375305670029)
            ·
              refine ⟨93687634816718765739626261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 249833692844583375305670029 93687634816718765739626261)
              ·
                refine ⟨4391607882033692144044981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 93687634816718765739626261 4391607882033692144044981)
                ·
                  refine ⟨411713238940658638504217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4391607882033692144044981 411713238940658638504217)
                  ·
                    rfl

theorem cell22_3608139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 6, 5].length) (baseStart_3608139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3608139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3608139 prefixEnd_3608139 := by exact prefixLift 3608139
  have htrace : WordTrace (prefixWord ++ tailWord_3608139) baseStart_3608139 baseEnd_3608139 := by
    simpa [prefixWord, tailWord_3608139, baseEnd_3608139] using wordTrace_append hprefix tailTrace_3608139
  have hstable : (prefixWord ++ tailWord_3608139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608139).length < 2 ^ (prefixWord ++ tailWord_3608139).sum := by decide
  have hdescent : baseEnd_3608139 < baseStart_3608139 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608154 : List Nat := [3, 1, 1, 2, 1, 1, 1, 5, 2, 5]
def baseStart_3608154 : Nat := 118140960795 + 3608154 * 2 ^ 59
def prefixEnd_3608154 : Nat := 4983230072969 + 3 ^ 40 * 3608154 * 2
def baseEnd_3608154 : Nat := 1235144851628520876387605

theorem tailTrace_3608154 : CollatzResearch.WordTrace tailWord_3608154 prefixEnd_3608154 1235144851628520876387605 := by
  unfold tailWord_3608154
  simp only [CollatzResearch.WordTrace]
  refine ⟨32900046942570439122059879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87733458513521170992159677 32900046942570439122059879)
  ·
    refine ⟨49350070413855658683089819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32900046942570439122059879 49350070413855658683089819)
    ·
      refine ⟨74025105620783488024634729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49350070413855658683089819 74025105620783488024634729)
      ·
        refine ⟨55518829215587616018476047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74025105620783488024634729 55518829215587616018476047)
        ·
          refine ⟨83278243823381424027714071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55518829215587616018476047 83278243823381424027714071)
          ·
            refine ⟨124917365735072136041571107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83278243823381424027714071 124917365735072136041571107)
            ·
              refine ⟨187376048602608204062356661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124917365735072136041571107 187376048602608204062356661)
              ·
                refine ⟨17566504556494519130845937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 187376048602608204062356661 17566504556494519130845937)
                ·
                  refine ⟨13174878417370889348134453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17566504556494519130845937 13174878417370889348134453)
                  ·
                    refine ⟨1235144851628520876387605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13174878417370889348134453 1235144851628520876387605)
                    ·
                      rfl

theorem cell22_3608154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 2, 5].length) (baseStart_3608154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3608154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3608154 prefixEnd_3608154 := by exact prefixLift 3608154
  have htrace : WordTrace (prefixWord ++ tailWord_3608154) baseStart_3608154 baseEnd_3608154 := by
    simpa [prefixWord, tailWord_3608154, baseEnd_3608154] using wordTrace_append hprefix tailTrace_3608154
  have hstable : (prefixWord ++ tailWord_3608154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608154).length < 2 ^ (prefixWord ++ tailWord_3608154).sum := by decide
  have hdescent : baseEnd_3608154 < baseStart_3608154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608216 : List Nat := [2, 1, 2, 4, 1, 2, 1, 3, 1, 5]
def baseStart_3608216 : Nat := 118140960795 + 3608216 * 2 ^ 59
def prefixEnd_3608216 : Nat := 4983230072969 + 3 ^ 40 * 3608216 * 2
def baseEnd_3608216 : Nat := 1235166075495573381337415

theorem tailTrace_3608216 : CollatzResearch.WordTrace tailWord_3608216 prefixEnd_3608216 1235166075495573381337415 := by
  unfold tailWord_3608216
  simp only [CollatzResearch.WordTrace]
  refine ⟨65801224548028570538498251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87734966064038094051331001 65801224548028570538498251)
  ·
    refine ⟨98701836822042855807747377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65801224548028570538498251 98701836822042855807747377)
    ·
      refine ⟨74026377616532141855810533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98701836822042855807747377 74026377616532141855810533)
      ·
        refine ⟨13879945803099776597964475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74026377616532141855810533 13879945803099776597964475)
        ·
          refine ⟨20819918704649664896946713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13879945803099776597964475 20819918704649664896946713)
          ·
            refine ⟨15614939028487248672710035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20819918704649664896946713 15614939028487248672710035)
            ·
              refine ⟨23422408542730873009065053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15614939028487248672710035 23422408542730873009065053)
              ·
                refine ⟨8783403203524077378399395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23422408542730873009065053 8783403203524077378399395)
                ·
                  refine ⟨13175104805286116067599093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8783403203524077378399395 13175104805286116067599093)
                  ·
                    refine ⟨1235166075495573381337415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13175104805286116067599093 1235166075495573381337415)
                    ·
                      rfl

theorem cell22_3608216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 3, 1, 5].length) (baseStart_3608216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3608216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3608216 prefixEnd_3608216 := by exact prefixLift 3608216
  have htrace : WordTrace (prefixWord ++ tailWord_3608216) baseStart_3608216 baseEnd_3608216 := by
    simpa [prefixWord, tailWord_3608216, baseEnd_3608216] using wordTrace_append hprefix tailTrace_3608216
  have hstable : (prefixWord ++ tailWord_3608216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608216).length < 2 ^ (prefixWord ++ tailWord_3608216).sum := by decide
  have hdescent : baseEnd_3608216 < baseStart_3608216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608229 : List Nat := [1, 3, 1, 2, 1, 2, 2, 10]
def baseStart_3608229 : Nat := 118140960795 + 3608229 * 2 ^ 59
def prefixEnd_3608229 : Nat := 4983230072969 + 3 ^ 40 * 3608229 * 2
def baseEnd_3608229 : Nat := 137241169517916186751375

theorem tailTrace_3608229 : CollatzResearch.WordTrace tailWord_3608229 prefixEnd_3608229 137241169517916186751375 := by
  unfold tailWord_3608229
  simp only [CollatzResearch.WordTrace]
  refine ⟨131602923245010044297219741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87735282163340029531479827 131602923245010044297219741)
  ·
    refine ⟨49351096216878766611457403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131602923245010044297219741 49351096216878766611457403)
    ·
      refine ⟨74026644325318149917186105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49351096216878766611457403 74026644325318149917186105)
      ·
        refine ⟨55519983243988612437889579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74026644325318149917186105 55519983243988612437889579)
        ·
          refine ⟨83279974865982918656834369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55519983243988612437889579 83279974865982918656834369)
          ·
            refine ⟨62459981149487188992625777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83279974865982918656834369 62459981149487188992625777)
            ·
              refine ⟨46844985862115391744469333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62459981149487188992625777 46844985862115391744469333)
              ·
                refine ⟨137241169517916186751375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 46844985862115391744469333 137241169517916186751375)
                ·
                  rfl

theorem cell22_3608229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 10].length) (baseStart_3608229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3608229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3608229 prefixEnd_3608229 := by exact prefixLift 3608229
  have htrace : WordTrace (prefixWord ++ tailWord_3608229) baseStart_3608229 baseEnd_3608229 := by
    simpa [prefixWord, tailWord_3608229, baseEnd_3608229] using wordTrace_append hprefix tailTrace_3608229
  have hstable : (prefixWord ++ tailWord_3608229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608229).length < 2 ^ (prefixWord ++ tailWord_3608229).sum := by decide
  have hdescent : baseEnd_3608229 < baseStart_3608229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608250 : List Nat := [3, 1, 1, 1, 2, 6, 1, 2, 2, 3]
def baseStart_3608250 : Nat := 118140960795 + 3608250 * 2 ^ 59
def prefixEnd_3608250 : Nat := 4983230072969 + 3 ^ 40 * 3608250 * 2
def baseEnd_3608250 : Nat := 1235177714390408625987311

theorem tailTrace_3608250 : CollatzResearch.WordTrace tailWord_3608250 prefixEnd_3608250 1235177714390408625987311 := by
  unfold tailWord_3608250
  simp only [CollatzResearch.WordTrace]
  refine ⟨32900922294483491220933551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87735792785289309922489469 32900922294483491220933551)
  ·
    refine ⟨49351383441725236831400327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32900922294483491220933551 49351383441725236831400327)
    ·
      refine ⟨74027075162587855247100491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49351383441725236831400327 74027075162587855247100491)
      ·
        refine ⟨111040612743881782870650737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74027075162587855247100491 111040612743881782870650737)
        ·
          refine ⟨83280459557911337152988053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111040612743881782870650737 83280459557911337152988053)
          ·
            refine ⟨3903771541777093929046315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 83280459557911337152988053 3903771541777093929046315)
            ·
              refine ⟨5855657312665640893569473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3903771541777093929046315 5855657312665640893569473)
              ·
                refine ⟨4391742984499230670177105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5855657312665640893569473 4391742984499230670177105)
                ·
                  refine ⟨3293807238374423002632829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4391742984499230670177105 3293807238374423002632829)
                  ·
                    refine ⟨1235177714390408625987311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3293807238374423002632829 1235177714390408625987311)
                    ·
                      rfl

theorem cell22_3608250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 2, 2, 3].length) (baseStart_3608250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3608250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3608250 prefixEnd_3608250 := by exact prefixLift 3608250
  have htrace : WordTrace (prefixWord ++ tailWord_3608250) baseStart_3608250 baseEnd_3608250 := by
    simpa [prefixWord, tailWord_3608250, baseEnd_3608250] using wordTrace_append hprefix tailTrace_3608250
  have hstable : (prefixWord ++ tailWord_3608250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608250).length < 2 ^ (prefixWord ++ tailWord_3608250).sum := by decide
  have hdescent : baseEnd_3608250 < baseStart_3608250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608261 : List Nat := [1, 3, 1, 1, 1, 1, 2, 2, 7, 3]
def baseStart_3608261 : Nat := 118140960795 + 3608261 * 2 ^ 59
def prefixEnd_3608261 : Nat := 4983230072969 + 3 ^ 40 * 3608261 * 2
def baseEnd_3608261 : Nat := 1235181479915208263962277

theorem tailTrace_3608261 : CollatzResearch.WordTrace tailWord_3608261 prefixEnd_3608261 1235181479915208263962277 := by
  unfold tailWord_3608261
  simp only [CollatzResearch.WordTrace]
  refine ⟨131604090380894113762384637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87736060253929409174923091 131604090380894113762384637)
  ·
    refine ⟨49351533892835292660894239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131604090380894113762384637 49351533892835292660894239)
    ·
      refine ⟨74027300839252938991341359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49351533892835292660894239 74027300839252938991341359)
      ·
        refine ⟨111040951258879408487012039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74027300839252938991341359 111040951258879408487012039)
        ·
          refine ⟨166561426888319112730518059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111040951258879408487012039 166561426888319112730518059)
          ·
            refine ⟨249842140332478669095777089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166561426888319112730518059 249842140332478669095777089)
            ·
              refine ⟨187381605249359001821832817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 249842140332478669095777089 187381605249359001821832817)
              ·
                refine ⟨140536203937019251366374613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 187381605249359001821832817 140536203937019251366374613)
                ·
                  refine ⟨3293817279773888703899405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 140536203937019251366374613 3293817279773888703899405)
                  ·
                    refine ⟨1235181479915208263962277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3293817279773888703899405 1235181479915208263962277)
                    ·
                      rfl

theorem cell22_3608261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 7, 3].length) (baseStart_3608261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3608261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3608261 prefixEnd_3608261 := by exact prefixLift 3608261
  have htrace : WordTrace (prefixWord ++ tailWord_3608261) baseStart_3608261 baseEnd_3608261 := by
    simpa [prefixWord, tailWord_3608261, baseEnd_3608261] using wordTrace_append hprefix tailTrace_3608261
  have hstable : (prefixWord ++ tailWord_3608261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608261).length < 2 ^ (prefixWord ++ tailWord_3608261).sum := by decide
  have hdescent : baseEnd_3608261 < baseStart_3608261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608370 : List Nat := [3, 2, 1, 1, 3, 3, 1, 4, 4]
def baseStart_3608370 : Nat := 118140960795 + 3608370 * 2 ^ 59
def prefixEnd_3608370 : Nat := 4983230072969 + 3 ^ 40 * 3608370 * 2
def baseEnd_3608370 : Nat := 411739597614256104328981

theorem tailTrace_3608370 : CollatzResearch.WordTrace tailWord_3608370 prefixEnd_3608370 411739597614256104328981 := by
  unfold tailWord_3608370
  simp only [CollatzResearch.WordTrace]
  refine ⟨32902016484374806344525641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87738710624999483585401709 32902016484374806344525641)
  ·
    refine ⟨24676512363281104758394231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32902016484374806344525641 24676512363281104758394231)
    ·
      refine ⟨37014768544921657137591347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24676512363281104758394231 37014768544921657137591347)
      ·
        refine ⟨55522152817382485706387021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37014768544921657137591347 55522152817382485706387021)
        ·
          refine ⟨20820807306518432139895133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55522152817382485706387021 20820807306518432139895133)
          ·
            refine ⟨7807802739944412052460675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20820807306518432139895133 7807802739944412052460675)
            ·
              refine ⟨11711704109916618078691013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7807802739944412052460675 11711704109916618078691013)
              ·
                refine ⟨2195944520609365889754565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11711704109916618078691013 2195944520609365889754565)
                ·
                  refine ⟨411739597614256104328981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2195944520609365889754565 411739597614256104328981)
                  ·
                    rfl

theorem cell22_3608370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 4, 4].length) (baseStart_3608370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3608370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3608370 prefixEnd_3608370 := by exact prefixLift 3608370
  have htrace : WordTrace (prefixWord ++ tailWord_3608370) baseStart_3608370 baseEnd_3608370 := by
    simpa [prefixWord, tailWord_3608370, baseEnd_3608370] using wordTrace_append hprefix tailTrace_3608370
  have hstable : (prefixWord ++ tailWord_3608370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608370).length < 2 ^ (prefixWord ++ tailWord_3608370).sum := by decide
  have hdescent : baseEnd_3608370 < baseStart_3608370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608419 : List Nat := [1, 1, 1, 5, 5, 1, 1, 2, 2, 3]
def baseStart_3608419 : Nat := 118140960795 + 3608419 * 2 ^ 59
def prefixEnd_3608419 : Nat := 4983230072969 + 3 ^ 40 * 3608419 * 2
def baseEnd_3608419 : Nat := 1235235566544148518511793

theorem tailTrace_3608419 : CollatzResearch.WordTrace tailWord_3608419 prefixEnd_3608419 1235235566544148518511793 := by
  unfold tailWord_3608419
  simp only [CollatzResearch.WordTrace]
  refine ⟨131609853114321706746636311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87739902076214471164424207 131609853114321706746636311)
  ·
    refine ⟨197414779671482560119954467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131609853114321706746636311 197414779671482560119954467)
    ·
      refine ⟨296122169507223840179931701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197414779671482560119954467 296122169507223840179931701)
      ·
        refine ⟨27761453391302235016868597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 296122169507223840179931701 27761453391302235016868597)
        ·
          refine ⟨2602636255434584532831431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27761453391302235016868597 2602636255434584532831431)
          ·
            refine ⟨3903954383151876799247147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2602636255434584532831431 3903954383151876799247147)
            ·
              refine ⟨5855931574727815198870721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3903954383151876799247147 5855931574727815198870721)
              ·
                refine ⟨4391948681045861399153041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5855931574727815198870721 4391948681045861399153041)
                ·
                  refine ⟨3293961510784396049364781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4391948681045861399153041 3293961510784396049364781)
                  ·
                    refine ⟨1235235566544148518511793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3293961510784396049364781 1235235566544148518511793)
                    ·
                      rfl

theorem cell22_3608419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 2, 2, 3].length) (baseStart_3608419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3608419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3608419 prefixEnd_3608419 := by exact prefixLift 3608419
  have htrace : WordTrace (prefixWord ++ tailWord_3608419) baseStart_3608419 baseEnd_3608419 := by
    simpa [prefixWord, tailWord_3608419, baseEnd_3608419] using wordTrace_append hprefix tailTrace_3608419
  have hstable : (prefixWord ++ tailWord_3608419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608419).length < 2 ^ (prefixWord ++ tailWord_3608419).sum := by decide
  have hdescent : baseEnd_3608419 < baseStart_3608419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608449 : List Nat := [1, 2, 4, 4, 2, 1, 2, 6]
def baseStart_3608449 : Nat := 118140960795 + 3608449 * 2 ^ 59
def prefixEnd_3608449 : Nat := 4983230072969 + 3 ^ 40 * 3608449 * 2
def baseEnd_3608449 : Nat := 137249537350804271140189

theorem tailTrace_3608449 : CollatzResearch.WordTrace tailWord_3608449 prefixEnd_3608449 137249537350804271140189 := by
  unfold tailWord_3608449
  simp only [CollatzResearch.WordTrace]
  refine ⟨131610947304213021870228401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87740631536142014580152267 131610947304213021870228401)
  ·
    refine ⟨98708210478159766402671301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131610947304213021870228401 98708210478159766402671301)
    ·
      refine ⟨18507789464654956200500869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98708210478159766402671301 18507789464654956200500869)
      ·
        refine ⟨3470210524622804287593913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18507789464654956200500869 3470210524622804287593913)
        ·
          refine ⟨2602657893467103215695435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3470210524622804287593913 2602657893467103215695435)
          ·
            refine ⟨3903986840200654823543153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2602657893467103215695435 3903986840200654823543153)
            ·
              refine ⟨2927990130150491117657365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3903986840200654823543153 2927990130150491117657365)
              ·
                refine ⟨137249537350804271140189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2927990130150491117657365 137249537350804271140189)
                ·
                  rfl

theorem cell22_3608449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 2, 6].length) (baseStart_3608449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3608449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3608449 prefixEnd_3608449 := by exact prefixLift 3608449
  have htrace : WordTrace (prefixWord ++ tailWord_3608449) baseStart_3608449 baseEnd_3608449 := by
    simpa [prefixWord, tailWord_3608449, baseEnd_3608449] using wordTrace_append hprefix tailTrace_3608449
  have hstable : (prefixWord ++ tailWord_3608449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608449).length < 2 ^ (prefixWord ++ tailWord_3608449).sum := by decide
  have hdescent : baseEnd_3608449 < baseStart_3608449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608481 : List Nat := [1, 2, 3, 4, 2, 1, 3, 2, 1, 3]
def baseStart_3608481 : Nat := 118140960795 + 3608481 * 2 ^ 59
def prefixEnd_3608481 : Nat := 4983230072969 + 3 ^ 40 * 3608481 * 2
def baseEnd_3608481 : Nat := 1235256790411201023461603

theorem tailTrace_3608481 : CollatzResearch.WordTrace tailWord_3608481 prefixEnd_3608481 1235256790411201023461603 := by
  unfold tailWord_3608481
  simp only [CollatzResearch.WordTrace]
  refine ⟨131612114440097091335393297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87741409626731394223595531 131612114440097091335393297)
  ·
    refine ⟨98709085830072818501544973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131612114440097091335393297 98709085830072818501544973)
    ·
      refine ⟨37015907186277306938079365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98709085830072818501544973 37015907186277306938079365)
      ·
        refine ⟨6940482597426995050889881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37015907186277306938079365 6940482597426995050889881)
        ·
          refine ⟨5205361948070246288167411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6940482597426995050889881 5205361948070246288167411)
          ·
            refine ⟨7808042922105369432251117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5205361948070246288167411 7808042922105369432251117)
            ·
              refine ⟨2928016095789513537094169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7808042922105369432251117 2928016095789513537094169)
              ·
                refine ⟨2196012071842135152820627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2928016095789513537094169 2196012071842135152820627)
                ·
                  refine ⟨3294018107763202729230941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2196012071842135152820627 3294018107763202729230941)
                  ·
                    refine ⟨1235256790411201023461603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3294018107763202729230941 1235256790411201023461603)
                    ·
                      rfl

theorem cell22_3608481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 3, 2, 1, 3].length) (baseStart_3608481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3608481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3608481 prefixEnd_3608481 := by exact prefixLift 3608481
  have htrace : WordTrace (prefixWord ++ tailWord_3608481) baseStart_3608481 baseEnd_3608481 := by
    simpa [prefixWord, tailWord_3608481, baseEnd_3608481] using wordTrace_append hprefix tailTrace_3608481
  have hstable : (prefixWord ++ tailWord_3608481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608481).length < 2 ^ (prefixWord ++ tailWord_3608481).sum := by decide
  have hdescent : baseEnd_3608481 < baseStart_3608481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608503 : List Nat := [1, 1, 3, 1, 3, 1, 1, 5, 1, 5]
def baseStart_3608503 : Nat := 118140960795 + 3608503 * 2 ^ 59
def prefixEnd_3608503 : Nat := 4983230072969 + 3 ^ 40 * 3608503 * 2
def baseEnd_3608503 : Nat := 1235264321460800299411535

theorem tailTrace_3608503 : CollatzResearch.WordTrace tailWord_3608503 prefixEnd_3608503 1235264321460800299411535 := by
  unfold tailWord_3608503
  simp only [CollatzResearch.WordTrace]
  refine ⟨131612916846017389092694163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87741944564011592728462775 131612916846017389092694163)
  ·
    refine ⟨197419375269026083639041245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131612916846017389092694163 197419375269026083639041245)
    ·
      refine ⟨74032265725884781364640467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197419375269026083639041245 74032265725884781364640467)
      ·
        refine ⟨111048398588827172046960701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74032265725884781364640467 111048398588827172046960701)
        ·
          refine ⟨41643149470810189517610263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111048398588827172046960701 41643149470810189517610263)
          ·
            refine ⟨62464724206215284276415395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41643149470810189517610263 62464724206215284276415395)
            ·
              refine ⟨93697086309322926414623093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62464724206215284276415395 93697086309322926414623093)
              ·
                refine ⟨8784101841499024351370915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93697086309322926414623093 8784101841499024351370915)
                ·
                  refine ⟨13176152762248536527056373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8784101841499024351370915 13176152762248536527056373)
                  ·
                    refine ⟨1235264321460800299411535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13176152762248536527056373 1235264321460800299411535)
                    ·
                      rfl

theorem cell22_3608503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 5, 1, 5].length) (baseStart_3608503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3608503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3608503 prefixEnd_3608503 := by exact prefixLift 3608503
  have htrace : WordTrace (prefixWord ++ tailWord_3608503) baseStart_3608503 baseEnd_3608503 := by
    simpa [prefixWord, tailWord_3608503, baseEnd_3608503] using wordTrace_append hprefix tailTrace_3608503
  have hstable : (prefixWord ++ tailWord_3608503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608503).length < 2 ^ (prefixWord ++ tailWord_3608503).sum := by decide
  have hdescent : baseEnd_3608503 < baseStart_3608503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608520 : List Nat := [2, 1, 3, 1, 4, 2, 1, 2, 1, 5]
def baseStart_3608520 : Nat := 118140960795 + 3608520 * 2 ^ 59
def prefixEnd_3608520 : Nat := 4983230072969 + 3 ^ 40 * 3608520 * 2
def baseEnd_3608520 : Nat := 1235270140908217921736483

theorem tailTrace_3608520 : CollatzResearch.WordTrace tailWord_3608520 prefixEnd_3608520 1235270140908217921736483 := by
  unfold tailWord_3608520
  simp only [CollatzResearch.WordTrace]
  refine ⟨65806768443477900498031507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87742357924637200664042009 65806768443477900498031507)
  ·
    refine ⟨98710152665216850747047261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65806768443477900498031507 98710152665216850747047261)
    ·
      refine ⟨37016307249456319030142723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98710152665216850747047261 37016307249456319030142723)
      ·
        refine ⟨55524460874184478545214085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37016307249456319030142723 55524460874184478545214085)
        ·
          refine ⟨10410836413909589727227641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55524460874184478545214085 10410836413909589727227641)
          ·
            refine ⟨7808127310432192295420731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10410836413909589727227641 7808127310432192295420731)
            ·
              refine ⟨11712190965648288443131097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7808127310432192295420731 11712190965648288443131097)
              ·
                refine ⟨8784143224236216332348323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11712190965648288443131097 8784143224236216332348323)
                ·
                  refine ⟨13176214836354324498522485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8784143224236216332348323 13176214836354324498522485)
                  ·
                    refine ⟨1235270140908217921736483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13176214836354324498522485 1235270140908217921736483)
                    ·
                      rfl

theorem cell22_3608520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 2, 1, 5].length) (baseStart_3608520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3608520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3608520 prefixEnd_3608520 := by exact prefixLift 3608520
  have htrace : WordTrace (prefixWord ++ tailWord_3608520) baseStart_3608520 baseEnd_3608520 := by
    simpa [prefixWord, tailWord_3608520, baseEnd_3608520] using wordTrace_append hprefix tailTrace_3608520
  have hstable : (prefixWord ++ tailWord_3608520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608520).length < 2 ^ (prefixWord ++ tailWord_3608520).sum := by decide
  have hdescent : baseEnd_3608520 < baseStart_3608520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608533 : List Nat := [1, 3, 2, 3, 2, 11]
def baseStart_3608533 : Nat := 118140960795 + 3608533 * 2 ^ 59
def prefixEnd_3608533 : Nat := 4983230072969 + 3 ^ 40 * 3608533 * 2
def baseEnd_3608533 : Nat := 15250303593504817545203

theorem tailTrace_3608533 : CollatzResearch.WordTrace tailWord_3608533 prefixEnd_3608533 15250303593504817545203 := by
  unfold tailWord_3608533
  simp only [CollatzResearch.WordTrace]
  refine ⟨131614011035908704216286253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87742674023939136144190835 131614011035908704216286253)
  ·
    refine ⟨49355254138465764081107345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131614011035908704216286253 49355254138465764081107345)
    ·
      refine ⟨37016440603849323060830509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49355254138465764081107345 37016440603849323060830509)
      ·
        refine ⟨13881165226443496147811441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37016440603849323060830509 13881165226443496147811441)
        ·
          refine ⟨10410873919832622110858581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13881165226443496147811441 10410873919832622110858581)
          ·
            refine ⟨15250303593504817545203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10410873919832622110858581 15250303593504817545203)
            ·
              rfl

theorem cell22_3608533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 11].length) (baseStart_3608533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3608533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3608533 prefixEnd_3608533 := by exact prefixLift 3608533
  have htrace : WordTrace (prefixWord ++ tailWord_3608533) baseStart_3608533 baseEnd_3608533 := by
    simpa [prefixWord, tailWord_3608533, baseEnd_3608533] using wordTrace_append hprefix tailTrace_3608533
  have hstable : (prefixWord ++ tailWord_3608533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608533).length < 2 ^ (prefixWord ++ tailWord_3608533).sum := by decide
  have hdescent : baseEnd_3608533 < baseStart_3608533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608595 : List Nat := [1, 1, 1, 2, 1, 4, 5, 2, 5]
def baseStart_3608595 : Nat := 118140960795 + 3608595 * 2 ^ 59
def prefixEnd_3608595 : Nat := 4983230072969 + 3 ^ 40 * 3608595 * 2
def baseEnd_3608595 : Nat := 411765271646980908703751

theorem tailTrace_3608595 : CollatzResearch.WordTrace tailWord_3608595 prefixEnd_3608595 411765271646980908703751 := by
  unfold tailWord_3608595
  simp only [CollatzResearch.WordTrace]
  refine ⟨131616272361684088805043239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87744181574456059203362159 131616272361684088805043239)
  ·
    refine ⟨197424408542526133207564859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131616272361684088805043239 197424408542526133207564859)
    ·
      refine ⟨296136612813789199811347289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197424408542526133207564859 296136612813789199811347289)
      ·
        refine ⟨222102459610341899858510467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296136612813789199811347289 222102459610341899858510467)
        ·
          refine ⟨333153689415512849787765701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222102459610341899858510467 333153689415512849787765701)
          ·
            refine ⟨62466316765408659335206069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 333153689415512849787765701 62466316765408659335206069)
            ·
              refine ⟨5856217196757061812675569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62466316765408659335206069 5856217196757061812675569)
              ·
                refine ⟨4392162897567796359506677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5856217196757061812675569 4392162897567796359506677)
                ·
                  refine ⟨411765271646980908703751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4392162897567796359506677 411765271646980908703751)
                  ·
                    rfl

theorem cell22_3608595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 2, 5].length) (baseStart_3608595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3608595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3608595 prefixEnd_3608595 := by exact prefixLift 3608595
  have htrace : WordTrace (prefixWord ++ tailWord_3608595) baseStart_3608595 baseEnd_3608595 := by
    simpa [prefixWord, tailWord_3608595, baseEnd_3608595] using wordTrace_append hprefix tailTrace_3608595
  have hstable : (prefixWord ++ tailWord_3608595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608595).length < 2 ^ (prefixWord ++ tailWord_3608595).sum := by decide
  have hdescent : baseEnd_3608595 < baseStart_3608595 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608599 : List Nat := [1, 1, 3, 5, 2, 1, 2, 1, 3, 3]
def baseStart_3608599 : Nat := 118140960795 + 3608599 * 2 ^ 59
def prefixEnd_3608599 : Nat := 4983230072969 + 3 ^ 40 * 3608599 * 2
def baseEnd_3608599 : Nat := 1235297184222688049011241

theorem tailTrace_3608599 : CollatzResearch.WordTrace tailWord_3608599 prefixEnd_3608599 1235297184222688049011241 := by
  unfold tailWord_3608599
  simp only [CollatzResearch.WordTrace]
  refine ⟨131616418253669597488188851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87744278835779731658792567 131616418253669597488188851)
  ·
    refine ⟨197424627380504396232283277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131616418253669597488188851 197424627380504396232283277)
    ·
      refine ⟨74034235267689148587106229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197424627380504396232283277 74034235267689148587106229)
      ·
        refine ⟨6940709556345857680041209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74034235267689148587106229 6940709556345857680041209)
        ·
          refine ⟨5205532167259393260030907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6940709556345857680041209 5205532167259393260030907)
          ·
            refine ⟨7808298250889089890046361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5205532167259393260030907 7808298250889089890046361)
            ·
              refine ⟨5856223688166817417534771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7808298250889089890046361 5856223688166817417534771)
              ·
                refine ⟨8784335532250226126302157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5856223688166817417534771 8784335532250226126302157)
                ·
                  refine ⟨3294125824593834797363309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8784335532250226126302157 3294125824593834797363309)
                  ·
                    refine ⟨1235297184222688049011241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3294125824593834797363309 1235297184222688049011241)
                    ·
                      rfl

theorem cell22_3608599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 1, 3, 3].length) (baseStart_3608599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3608599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3608599 prefixEnd_3608599 := by exact prefixLift 3608599
  have htrace : WordTrace (prefixWord ++ tailWord_3608599) baseStart_3608599 baseEnd_3608599 := by
    simpa [prefixWord, tailWord_3608599, baseEnd_3608599] using wordTrace_append hprefix tailTrace_3608599
  have hstable : (prefixWord ++ tailWord_3608599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608599).length < 2 ^ (prefixWord ++ tailWord_3608599).sum := by decide
  have hdescent : baseEnd_3608599 < baseStart_3608599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608610 : List Nat := [3, 3, 1, 1, 1, 2, 1, 3, 2, 5]
def baseStart_3608610 : Nat := 118140960795 + 3608610 * 2 ^ 59
def prefixEnd_3608610 : Nat := 4983230072969 + 3 ^ 40 * 3608610 * 2
def baseEnd_3608610 : Nat := 1235300949747487686986207

theorem tailTrace_3608610 : CollatzResearch.WordTrace tailWord_3608610 prefixEnd_3608610 1235300949747487686986207 := by
  unfold tailWord_3608610
  simp only [CollatzResearch.WordTrace]
  refine ⟨32904204864157436591709821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87744546304419830911226189 32904204864157436591709821)
  ·
    refine ⟨12339076824059038721891183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32904204864157436591709821 12339076824059038721891183)
    ·
      refine ⟨18508615236088558082836775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12339076824059038721891183 18508615236088558082836775)
      ·
        refine ⟨27762922854132837124255163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18508615236088558082836775 27762922854132837124255163)
        ·
          refine ⟨41644384281199255686382745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27762922854132837124255163 41644384281199255686382745)
          ·
            refine ⟨31233288210899441764787059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41644384281199255686382745 31233288210899441764787059)
            ·
              refine ⟨46849932316349162647180589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31233288210899441764787059 46849932316349162647180589)
              ·
                refine ⟨17568724618630935992692721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46849932316349162647180589 17568724618630935992692721)
                ·
                  refine ⟨13176543463973201994519541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17568724618630935992692721 13176543463973201994519541)
                  ·
                    refine ⟨1235300949747487686986207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13176543463973201994519541 1235300949747487686986207)
                    ·
                      rfl

theorem cell22_3608610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_3608610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3608610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3608610 prefixEnd_3608610 := by exact prefixLift 3608610
  have htrace : WordTrace (prefixWord ++ tailWord_3608610) baseStart_3608610 baseEnd_3608610 := by
    simpa [prefixWord, tailWord_3608610, baseEnd_3608610] using wordTrace_append hprefix tailTrace_3608610
  have hstable : (prefixWord ++ tailWord_3608610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608610).length < 2 ^ (prefixWord ++ tailWord_3608610).sum := by decide
  have hdescent : baseEnd_3608610 < baseStart_3608610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608623 : List Nat := [1, 1, 2, 1, 2, 1, 1, 5, 8]
def baseStart_3608623 : Nat := 118140960795 + 3608623 * 2 ^ 59
def prefixEnd_3608623 : Nat := 4983230072969 + 3 ^ 40 * 3608623 * 2
def baseEnd_3608623 : Nat := 411768466637719995470389

theorem tailTrace_3608623 : CollatzResearch.WordTrace tailWord_3608623 prefixEnd_3608623 411768466637719995470389 := by
  unfold tailWord_3608623
  simp only [CollatzResearch.WordTrace]
  refine ⟨131617293605582649587062523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87744862403721766391375015 131617293605582649587062523)
  ·
    refine ⟨197425940408373974380593785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131617293605582649587062523 197425940408373974380593785)
    ·
      refine ⟨148069455306280480785445339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197425940408373974380593785 148069455306280480785445339)
      ·
        refine ⟨222104182959420721178168009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148069455306280480785445339 222104182959420721178168009)
        ·
          refine ⟨166578137219565540883626007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222104182959420721178168009 166578137219565540883626007)
          ·
            refine ⟨249867205829348311325439011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166578137219565540883626007 249867205829348311325439011)
            ·
              refine ⟨374800808744022466988158517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249867205829348311325439011 374800808744022466988158517)
              ·
                refine ⟨35137575819752106280139861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 374800808744022466988158517 35137575819752106280139861)
                ·
                  refine ⟨411768466637719995470389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35137575819752106280139861 411768466637719995470389)
                  ·
                    rfl

theorem cell22_3608623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 8].length) (baseStart_3608623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3608623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3608623 prefixEnd_3608623 := by exact prefixLift 3608623
  have htrace : WordTrace (prefixWord ++ tailWord_3608623) baseStart_3608623 baseEnd_3608623 := by
    simpa [prefixWord, tailWord_3608623, baseEnd_3608623] using wordTrace_append hprefix tailTrace_3608623
  have hstable : (prefixWord ++ tailWord_3608623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608623).length < 2 ^ (prefixWord ++ tailWord_3608623).sum := by decide
  have hdescent : baseEnd_3608623 < baseStart_3608623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608633 : List Nat := [1, 2, 1, 5, 4, 1, 1, 3, 1, 3]
def baseStart_3608633 : Nat := 118140960795 + 3608633 * 2 ^ 59
def prefixEnd_3608633 : Nat := 4983230072969 + 3 ^ 40 * 3608633 * 2
def baseEnd_3608633 : Nat := 1235308823117523293661137

theorem tailTrace_3608633 : CollatzResearch.WordTrace tailWord_3608633 prefixEnd_3608633 1235308823117523293661137 := by
  unfold tailWord_3608633
  simp only [CollatzResearch.WordTrace]
  refine ⟨131617658335546421294926553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87745105557030947529951035 131617658335546421294926553)
  ·
    refine ⟨98713243751659815971194915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131617658335546421294926553 98713243751659815971194915)
    ·
      refine ⟨148069865627489723956792373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98713243751659815971194915 148069865627489723956792373)
      ·
        refine ⟨13881549902577161620949285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 148069865627489723956792373 13881549902577161620949285)
        ·
          refine ⟨2602790606733217803927991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13881549902577161620949285 2602790606733217803927991)
          ·
            refine ⟨3904185910099826705891987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2602790606733217803927991 3904185910099826705891987)
            ·
              refine ⟨5856278865149740058837981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3904185910099826705891987 5856278865149740058837981)
              ·
                refine ⟨2196104574431152522064243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5856278865149740058837981 2196104574431152522064243)
                ·
                  refine ⟨3294156861646728783096365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2196104574431152522064243 3294156861646728783096365)
                  ·
                    refine ⟨1235308823117523293661137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3294156861646728783096365 1235308823117523293661137)
                    ·
                      rfl

theorem cell22_3608633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 3, 1, 3].length) (baseStart_3608633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3608633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3608633 prefixEnd_3608633 := by exact prefixLift 3608633
  have htrace : WordTrace (prefixWord ++ tailWord_3608633) baseStart_3608633 baseEnd_3608633 := by
    simpa [prefixWord, tailWord_3608633, baseEnd_3608633] using wordTrace_append hprefix tailTrace_3608633
  have hstable : (prefixWord ++ tailWord_3608633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608633).length < 2 ^ (prefixWord ++ tailWord_3608633).sum := by decide
  have hdescent : baseEnd_3608633 < baseStart_3608633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608685 : List Nat := [1, 5, 1, 1, 2, 1, 1, 10]
def baseStart_3608685 : Nat := 118140960795 + 3608685 * 2 ^ 59
def prefixEnd_3608685 : Nat := 4983230072969 + 3 ^ 40 * 3608685 * 2
def baseEnd_3608685 : Nat := 137258513753356943484553

theorem tailTrace_3608685 : CollatzResearch.WordTrace tailWord_3608685 prefixEnd_3608685 137258513753356943484553 := by
  unfold tailWord_3608685
  simp only [CollatzResearch.WordTrace]
  refine ⟨131619554931358034175819509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87746369954238689450546339 131619554931358034175819509)
  ·
    refine ⟨12339333274814815703983079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 131619554931358034175819509 12339333274814815703983079)
    ·
      refine ⟨18508999912222223555974619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12339333274814815703983079 18508999912222223555974619)
      ·
        refine ⟨27763499868333335333961929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18508999912222223555974619 27763499868333335333961929)
        ·
          refine ⟨20822624901250001500471447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27763499868333335333961929 20822624901250001500471447)
          ·
            refine ⟨31233937351875002250707171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20822624901250001500471447 31233937351875002250707171)
            ·
              refine ⟨46850906027812503376060757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31233937351875002250707171 46850906027812503376060757)
              ·
                refine ⟨137258513753356943484553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 46850906027812503376060757 137258513753356943484553)
                ·
                  rfl

theorem cell22_3608685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 10].length) (baseStart_3608685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3608685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3608685 prefixEnd_3608685 := by exact prefixLift 3608685
  have htrace : WordTrace (prefixWord ++ tailWord_3608685) baseStart_3608685 baseEnd_3608685 := by
    simpa [prefixWord, tailWord_3608685, baseEnd_3608685] using wordTrace_append hprefix tailTrace_3608685
  have hstable : (prefixWord ++ tailWord_3608685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608685).length < 2 ^ (prefixWord ++ tailWord_3608685).sum := by decide
  have hdescent : baseEnd_3608685 < baseStart_3608685 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608687 : List Nat := [1, 1, 2, 1, 3, 5, 2, 1, 2, 4]
def baseStart_3608687 : Nat := 118140960795 + 3608687 * 2 ^ 59
def prefixEnd_3608687 : Nat := 4983230072969 + 3 ^ 40 * 3608687 * 2
def baseEnd_3608687 : Nat := 1235327308421085152810971

theorem tailTrace_3608687 : CollatzResearch.WordTrace tailWord_3608687 prefixEnd_3608687 1235327308421085152810971 := by
  unfold tailWord_3608687
  simp only [CollatzResearch.WordTrace]
  refine ⟨131619627877350788517392315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87746418584900525678261543 131619627877350788517392315)
  ·
    refine ⟨197429441816026182776088473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131619627877350788517392315 197429441816026182776088473)
    ·
      refine ⟨148072081362019637082066355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197429441816026182776088473 148072081362019637082066355)
      ·
        refine ⟨222108122043029455623099533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148072081362019637082066355 222108122043029455623099533)
        ·
          refine ⟨83290545766136045858662325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 222108122043029455623099533 83290545766136045858662325)
          ·
            refine ⟨7808488665575254299249593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 83290545766136045858662325 7808488665575254299249593)
            ·
              refine ⟨5856366499181440724437195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7808488665575254299249593 5856366499181440724437195)
              ·
                refine ⟨8784549748772161086655793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5856366499181440724437195 8784549748772161086655793)
                ·
                  refine ⟨6588412311579120814991845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8784549748772161086655793 6588412311579120814991845)
                  ·
                    refine ⟨1235327308421085152810971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6588412311579120814991845 1235327308421085152810971)
                    ·
                      rfl

theorem cell22_3608687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 1, 2, 4].length) (baseStart_3608687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3608687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3608687 prefixEnd_3608687 := by exact prefixLift 3608687
  have htrace : WordTrace (prefixWord ++ tailWord_3608687) baseStart_3608687 baseEnd_3608687 := by
    simpa [prefixWord, tailWord_3608687, baseEnd_3608687] using wordTrace_append hprefix tailTrace_3608687
  have hstable : (prefixWord ++ tailWord_3608687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608687).length < 2 ^ (prefixWord ++ tailWord_3608687).sum := by decide
  have hdescent : baseEnd_3608687 < baseStart_3608687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608702 : List Nat := [4, 2, 4, 12]
def baseStart_3608702 : Nat := 118140960795 + 3608702 * 2 ^ 59
def prefixEnd_3608702 : Nat := 4983230072969 + 3 ^ 40 * 3608702 * 2
def baseEnd_3608702 : Nat := 1694557535291673681325

theorem tailTrace_3608702 : CollatzResearch.WordTrace tailWord_3608702 prefixEnd_3608702 1694557535291673681325 := by
  unfold tailWord_3608702
  simp only [CollatzResearch.WordTrace]
  refine ⟨16452521871537055759898545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87746783314864297386125573 16452521871537055759898545)
  ·
    refine ⟨12339391403652791819923909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16452521871537055759898545 12339391403652791819923909)
    ·
      refine ⟨2313635888184898466235733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12339391403652791819923909 2313635888184898466235733)
      ·
        refine ⟨1694557535291673681325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 2313635888184898466235733 1694557535291673681325)
        ·
          rfl

theorem cell22_3608702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 12].length) (baseStart_3608702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3608702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3608702 prefixEnd_3608702 := by exact prefixLift 3608702
  have htrace : WordTrace (prefixWord ++ tailWord_3608702) baseStart_3608702 baseEnd_3608702 := by
    simpa [prefixWord, tailWord_3608702, baseEnd_3608702] using wordTrace_append hprefix tailTrace_3608702
  have hstable : (prefixWord ++ tailWord_3608702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608702).length < 2 ^ (prefixWord ++ tailWord_3608702).sum := by decide
  have hdescent : baseEnd_3608702 < baseStart_3608702 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608792 : List Nat := [2, 1, 2, 2, 4, 1, 2, 2, 6]
def baseStart_3608792 : Nat := 118140960795 + 3608792 * 2 ^ 59
def prefixEnd_3608792 : Nat := 4983230072969 + 3 ^ 40 * 3608792 * 2
def baseEnd_3608792 : Nat := 411787750688966626311883

theorem tailTrace_3608792 : CollatzResearch.WordTrace tailWord_3608792 prefixEnd_3608792 411787750688966626311883 := by
  unfold tailWord_3608792
  simp only [CollatzResearch.WordTrace]
  refine ⟨65811728770985195724982315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87748971694646927633309753 65811728770985195724982315)
  ·
    refine ⟨98717593156477793587473473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65811728770985195724982315 98717593156477793587473473)
    ·
      refine ⟨74038194867358345190605105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98717593156477793587473473 74038194867358345190605105)
      ·
        refine ⟨55528646150518758892953829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74038194867358345190605105 55528646150518758892953829)
        ·
          refine ⟨10411621153222267292428843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55528646150518758892953829 10411621153222267292428843)
          ·
            refine ⟨15617431729833400938643265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10411621153222267292428843 15617431729833400938643265)
            ·
              refine ⟨11713073797375050703982449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15617431729833400938643265 11713073797375050703982449)
              ·
                refine ⟨8784805348031288027986837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11713073797375050703982449 8784805348031288027986837)
                ·
                  refine ⟨411787750688966626311883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8784805348031288027986837 411787750688966626311883)
                  ·
                    rfl

theorem cell22_3608792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 2, 6].length) (baseStart_3608792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3608792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3608792 prefixEnd_3608792 := by exact prefixLift 3608792
  have htrace : WordTrace (prefixWord ++ tailWord_3608792) baseStart_3608792 baseEnd_3608792 := by
    simpa [prefixWord, tailWord_3608792, baseEnd_3608792] using wordTrace_append hprefix tailTrace_3608792
  have hstable : (prefixWord ++ tailWord_3608792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608792).length < 2 ^ (prefixWord ++ tailWord_3608792).sum := by decide
  have hdescent : baseEnd_3608792 < baseStart_3608792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608826 : List Nat := [3, 1, 1, 1, 1, 6, 3, 2, 4]
def baseStart_3608826 : Nat := 118140960795 + 3608826 * 2 ^ 59
def prefixEnd_3608826 : Nat := 4983230072969 + 3 ^ 40 * 3608826 * 2
def baseEnd_3608826 : Nat := 411791630320578374528515

theorem tailTrace_3608826 : CollatzResearch.WordTrace tailWord_3608826 prefixEnd_3608826 411791630320578374528515 := by
  unfold tailWord_3608826
  simp only [CollatzResearch.WordTrace]
  refine ⟨32906174405961803814175583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87749798415898143504468221 32906174405961803814175583)
  ·
    refine ⟨49359261608942705721263375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32906174405961803814175583 49359261608942705721263375)
    ·
      refine ⟨74038892413414058581895063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49359261608942705721263375 74038892413414058581895063)
      ·
        refine ⟨111058338620121087872842595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74038892413414058581895063 111058338620121087872842595)
        ·
          refine ⟨166587507930181631809263893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111058338620121087872842595 166587507930181631809263893)
          ·
            refine ⟨7808789434227263991059245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 166587507930181631809263893 7808789434227263991059245)
            ·
              refine ⟨2928296037835223996647217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7808789434227263991059245 2928296037835223996647217)
              ·
                refine ⟨2196222028376417997485413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2928296037835223996647217 2196222028376417997485413)
                ·
                  refine ⟨411791630320578374528515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2196222028376417997485413 411791630320578374528515)
                  ·
                    rfl

theorem cell22_3608826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 3, 2, 4].length) (baseStart_3608826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3608826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3608826 prefixEnd_3608826 := by exact prefixLift 3608826
  have htrace : WordTrace (prefixWord ++ tailWord_3608826) baseStart_3608826 baseEnd_3608826 := by
    simpa [prefixWord, tailWord_3608826, baseEnd_3608826] using wordTrace_append hprefix tailTrace_3608826
  have hstable : (prefixWord ++ tailWord_3608826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608826).length < 2 ^ (prefixWord ++ tailWord_3608826).sum := by decide
  have hdescent : baseEnd_3608826 < baseStart_3608826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608841 : List Nat := [1, 2, 1, 1, 3, 4, 4, 1, 2, 3]
def baseStart_3608841 : Nat := 118140960795 + 3608841 * 2 ^ 59
def prefixEnd_3608841 : Nat := 4983230072969 + 3 ^ 40 * 3608841 * 2
def baseEnd_3608841 : Nat := 1235380025768280084460499

theorem tailTrace_3608841 : CollatzResearch.WordTrace tailWord_3608841 prefixEnd_3608841 1235380025768280084460499 := by
  unfold tailWord_3608841
  simp only [CollatzResearch.WordTrace]
  refine ⟨131625244718792872818498377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87750163145861915212332251 131625244718792872818498377)
  ·
    refine ⟨98718933539094654613873783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131625244718792872818498377 98718933539094654613873783)
    ·
      refine ⟨148078400308641981920810675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98718933539094654613873783 148078400308641981920810675)
      ·
        refine ⟨222117600462962972881216013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148078400308641981920810675 222117600462962972881216013)
        ·
          refine ⟨83294100173611114830456005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 222117600462962972881216013 83294100173611114830456005)
          ·
            refine ⟨15617643782552084030710501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83294100173611114830456005 15617643782552084030710501)
            ·
              refine ⟨2928308209228515755758219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15617643782552084030710501 2928308209228515755758219)
              ·
                refine ⟨4392462313842773633637329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2928308209228515755758219 4392462313842773633637329)
                ·
                  refine ⟨3294346735382080225227997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4392462313842773633637329 3294346735382080225227997)
                  ·
                    refine ⟨1235380025768280084460499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3294346735382080225227997 1235380025768280084460499)
                    ·
                      rfl

theorem cell22_3608841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 4, 1, 2, 3].length) (baseStart_3608841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3608841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3608841 prefixEnd_3608841 := by exact prefixLift 3608841
  have htrace : WordTrace (prefixWord ++ tailWord_3608841) baseStart_3608841 baseEnd_3608841 := by
    simpa [prefixWord, tailWord_3608841, baseEnd_3608841] using wordTrace_append hprefix tailTrace_3608841
  have hstable : (prefixWord ++ tailWord_3608841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608841).length < 2 ^ (prefixWord ++ tailWord_3608841).sum := by decide
  have hdescent : baseEnd_3608841 < baseStart_3608841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608871 : List Nat := [1, 1, 8, 1, 1, 10]
def baseStart_3608871 : Nat := 118140960795 + 3608871 * 2 ^ 59
def prefixEnd_3608871 : Nat := 4983230072969 + 3 ^ 40 * 3608871 * 2
def baseEnd_3608871 : Nat := 15251732041745308718647

theorem tailTrace_3608871 : CollatzResearch.WordTrace tailWord_3608871 prefixEnd_3608871 15251732041745308718647 := by
  unfold tailWord_3608871
  simp only [CollatzResearch.WordTrace]
  refine ⟨131626338908684187942090467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87750892605789458628060311 131626338908684187942090467)
  ·
    refine ⟨197439508363026281913135701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131626338908684187942090467 197439508363026281913135701)
    ·
      refine ⟨2313744238629214241169559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 197439508363026281913135701 2313744238629214241169559)
      ·
        refine ⟨3470616357943821361754339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2313744238629214241169559 3470616357943821361754339)
        ·
          refine ⟨5205924536915732042631509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3470616357943821361754339 5205924536915732042631509)
          ·
            refine ⟨15251732041745308718647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5205924536915732042631509 15251732041745308718647)
            ·
              rfl

theorem cell22_3608871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 10].length) (baseStart_3608871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3608871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3608871 prefixEnd_3608871 := by exact prefixLift 3608871
  have htrace : WordTrace (prefixWord ++ tailWord_3608871) baseStart_3608871 baseEnd_3608871 := by
    simpa [prefixWord, tailWord_3608871, baseEnd_3608871] using wordTrace_append hprefix tailTrace_3608871
  have hstable : (prefixWord ++ tailWord_3608871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608871).length < 2 ^ (prefixWord ++ tailWord_3608871).sum := by decide
  have hdescent : baseEnd_3608871 < baseStart_3608871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608877 : List Nat := [1, 5, 3, 1, 3, 1, 2, 2, 4]
def baseStart_3608877 : Nat := 118140960795 + 3608877 * 2 ^ 59
def prefixEnd_3608877 : Nat := 4983230072969 + 3 ^ 40 * 3608877 * 2
def baseEnd_3608877 : Nat := 411797449767995996853463

theorem tailTrace_3608877 : CollatzResearch.WordTrace tailWord_3608877 prefixEnd_3608877 411797449767995996853463 := by
  unfold tailWord_3608877
  simp only [CollatzResearch.WordTrace]
  refine ⟨131626557746662450966808885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87751038497774967311205923 131626557746662450966808885)
  ·
    refine ⟨12339989788749604778138333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 131626557746662450966808885 12339989788749604778138333)
    ·
      refine ⟨4627496170781101791801875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12339989788749604778138333 4627496170781101791801875)
      ·
        refine ⟨6941244256171652687702813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4627496170781101791801875 6941244256171652687702813)
        ·
          refine ⟨2602966596064369757888555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6941244256171652687702813 2602966596064369757888555)
          ·
            refine ⟨3904449894096554636832833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2602966596064369757888555 3904449894096554636832833)
            ·
              refine ⟨2928337420572415977624625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3904449894096554636832833 2928337420572415977624625)
              ·
                refine ⟨2196253065429311983218469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2928337420572415977624625 2196253065429311983218469)
                ·
                  refine ⟨411797449767995996853463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2196253065429311983218469 411797449767995996853463)
                  ·
                    rfl

theorem cell22_3608877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 2, 2, 4].length) (baseStart_3608877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3608877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3608877 prefixEnd_3608877 := by exact prefixLift 3608877
  have htrace : WordTrace (prefixWord ++ tailWord_3608877) baseStart_3608877 baseEnd_3608877 := by
    simpa [prefixWord, tailWord_3608877, baseEnd_3608877] using wordTrace_append hprefix tailTrace_3608877
  have hstable : (prefixWord ++ tailWord_3608877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608877).length < 2 ^ (prefixWord ++ tailWord_3608877).sum := by decide
  have hdescent : baseEnd_3608877 < baseStart_3608877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608884 : List Nat := [2, 5, 1, 1, 1, 2, 1, 1, 2, 6]
def baseStart_3608884 : Nat := 118140960795 + 3608884 * 2 ^ 59
def prefixEnd_3608884 : Nat := 4983230072969 + 3 ^ 40 * 3608884 * 2
def baseEnd_3608884 : Nat := 1235394745547042305635367

theorem tailTrace_3608884 : CollatzResearch.WordTrace tailWord_3608884 prefixEnd_3608884 1235394745547042305635367 := by
  unfold tailWord_3608884
  simp only [CollatzResearch.WordTrace]
  refine ⟨65813406528818545581156853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87751208705091394108209137 65813406528818545581156853)
  ·
    refine ⟨6170006862076738648233455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65813406528818545581156853 6170006862076738648233455)
    ·
      refine ⟨9255010293115107972350183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6170006862076738648233455 9255010293115107972350183)
      ·
        refine ⟨13882515439672661958525275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9255010293115107972350183 13882515439672661958525275)
        ·
          refine ⟨20823773159508992937787913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13882515439672661958525275 20823773159508992937787913)
          ·
            refine ⟨15617829869631744703340935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20823773159508992937787913 15617829869631744703340935)
            ·
              refine ⟨23426744804447617055011403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15617829869631744703340935 23426744804447617055011403)
              ·
                refine ⟨35140117206671425582517105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23426744804447617055011403 35140117206671425582517105)
                ·
                  refine ⟨26355087905003569186887829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35140117206671425582517105 26355087905003569186887829)
                  ·
                    refine ⟨1235394745547042305635367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26355087905003569186887829 1235394745547042305635367)
                    ·
                      rfl

theorem cell22_3608884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_3608884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3608884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3608884 prefixEnd_3608884 := by exact prefixLift 3608884
  have htrace : WordTrace (prefixWord ++ tailWord_3608884) baseStart_3608884 baseEnd_3608884 := by
    simpa [prefixWord, tailWord_3608884, baseEnd_3608884] using wordTrace_append hprefix tailTrace_3608884
  have hstable : (prefixWord ++ tailWord_3608884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608884).length < 2 ^ (prefixWord ++ tailWord_3608884).sum := by decide
  have hdescent : baseEnd_3608884 < baseStart_3608884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608926 : List Nat := [4, 4, 2, 1, 2, 1, 1, 2, 2, 3]
def baseStart_3608926 : Nat := 118140960795 + 3608926 * 2 ^ 59
def prefixEnd_3608926 : Nat := 4983230072969 + 3 ^ 40 * 3608926 * 2
def baseEnd_3608926 : Nat := 1235409123005368196085239

theorem tailTrace_3608926 : CollatzResearch.WordTrace tailWord_3608926 prefixEnd_3608926 1235409123005368196085239 := by
  unfold tailWord_3608926
  simp only [CollatzResearch.WordTrace]
  refine ⟨16453543115435616541917829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87752229948989954890228421 16453543115435616541917829)
  ·
    refine ⟨3085039334144178101609593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16453543115435616541917829 3085039334144178101609593)
    ·
      refine ⟨2313779500608133576207195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3085039334144178101609593 2313779500608133576207195)
      ·
        refine ⟨3470669250912200364310793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2313779500608133576207195 3470669250912200364310793)
        ·
          refine ⟨2603001938184150273233095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3470669250912200364310793 2603001938184150273233095)
          ·
            refine ⟨3904502907276225409849643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2603001938184150273233095 3904502907276225409849643)
            ·
              refine ⟨5856754360914338114774465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3904502907276225409849643 5856754360914338114774465)
              ·
                refine ⟨4392565770685753586080849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5856754360914338114774465 4392565770685753586080849)
                ·
                  refine ⟨3294424328014315189560637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4392565770685753586080849 3294424328014315189560637)
                  ·
                    refine ⟨1235409123005368196085239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3294424328014315189560637 1235409123005368196085239)
                    ·
                      rfl

theorem cell22_3608926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_3608926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3608926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3608926 prefixEnd_3608926 := by exact prefixLift 3608926
  have htrace : WordTrace (prefixWord ++ tailWord_3608926) baseStart_3608926 baseEnd_3608926 := by
    simpa [prefixWord, tailWord_3608926, baseEnd_3608926] using wordTrace_append hprefix tailTrace_3608926
  have hstable : (prefixWord ++ tailWord_3608926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608926).length < 2 ^ (prefixWord ++ tailWord_3608926).sum := by decide
  have hdescent : baseEnd_3608926 < baseStart_3608926 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608944 : List Nat := [2, 1, 1, 1, 4, 4, 2, 1, 6]
def baseStart_3608944 : Nat := 118140960795 + 3608944 * 2 ^ 59
def prefixEnd_3608944 : Nat := 4983230072969 + 3 ^ 40 * 3608944 * 2
def baseEnd_3608944 : Nat := 411805094924407383045061

theorem tailTrace_3608944 : CollatzResearch.WordTrace tailWord_3608944 prefixEnd_3608944 411805094924407383045061 := by
  unfold tailWord_3608944
  simp only [CollatzResearch.WordTrace]
  refine ⟨65814500718709860704748943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87752667624946480939665257 65814500718709860704748943)
  ·
    refine ⟨98721751078064791057123415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65814500718709860704748943 98721751078064791057123415)
    ·
      refine ⟨148082626617097186585685123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98721751078064791057123415 148082626617097186585685123)
      ·
        refine ⟨222123939925645779878527685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148082626617097186585685123 222123939925645779878527685)
        ·
          refine ⟨41648238736058583727223941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 222123939925645779878527685 41648238736058583727223941)
          ·
            refine ⟨7809044763010984448854489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41648238736058583727223941 7809044763010984448854489)
            ·
              refine ⟨5856783572258238336640867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7809044763010984448854489 5856783572258238336640867)
              ·
                refine ⟨8785175358387357504961301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5856783572258238336640867 8785175358387357504961301)
                ·
                  refine ⟨411805094924407383045061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8785175358387357504961301 411805094924407383045061)
                  ·
                    rfl

theorem cell22_3608944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 1, 6].length) (baseStart_3608944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3608944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3608944 prefixEnd_3608944 := by exact prefixLift 3608944
  have htrace : WordTrace (prefixWord ++ tailWord_3608944) baseStart_3608944 baseEnd_3608944 := by
    simpa [prefixWord, tailWord_3608944, baseEnd_3608944] using wordTrace_append hprefix tailTrace_3608944
  have hstable : (prefixWord ++ tailWord_3608944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608944).length < 2 ^ (prefixWord ++ tailWord_3608944).sum := by decide
  have hdescent : baseEnd_3608944 < baseStart_3608944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608950 : List Nat := [5, 1, 1, 4, 1, 1, 3, 1, 5]
def baseStart_3608950 : Nat := 118140960795 + 3608950 * 2 ^ 59
def prefixEnd_3608950 : Nat := 4983230072969 + 3 ^ 40 * 3608950 * 2
def baseEnd_3608950 : Nat := 411805779565280044495055

theorem tailTrace_3608950 : CollatzResearch.WordTrace tailWord_3608950 prefixEnd_3608950 411805779565280044495055 := by
  unfold tailWord_3608950
  simp only [CollatzResearch.WordTrace]
  refine ⟨8226826267212374027138519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87752813516931989622810869 8226826267212374027138519)
  ·
    refine ⟨12340239400818561040707779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8226826267212374027138519 12340239400818561040707779)
    ·
      refine ⟨18510359101227841561061669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12340239400818561040707779 18510359101227841561061669)
      ·
        refine ⟨3470692331480220292699063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18510359101227841561061669 3470692331480220292699063)
        ·
          refine ⟨5206038497220330439048595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3470692331480220292699063 5206038497220330439048595)
          ·
            refine ⟨7809057745830495658572893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5206038497220330439048595 7809057745830495658572893)
            ·
              refine ⟨2928396654686435871964835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7809057745830495658572893 2928396654686435871964835)
              ·
                refine ⟨4392594982029653807947253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2928396654686435871964835 4392594982029653807947253)
                ·
                  refine ⟨411805779565280044495055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4392594982029653807947253 411805779565280044495055)
                  ·
                    rfl

theorem cell22_3608950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 3, 1, 5].length) (baseStart_3608950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3608950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3608950 prefixEnd_3608950 := by exact prefixLift 3608950
  have htrace : WordTrace (prefixWord ++ tailWord_3608950) baseStart_3608950 baseEnd_3608950 := by
    simpa [prefixWord, tailWord_3608950, baseEnd_3608950] using wordTrace_append hprefix tailTrace_3608950
  have hstable : (prefixWord ++ tailWord_3608950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608950).length < 2 ^ (prefixWord ++ tailWord_3608950).sum := by decide
  have hdescent : baseEnd_3608950 < baseStart_3608950 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609038 : List Nat := [4, 1, 1, 1, 2, 1, 1, 7, 1, 3]
def baseStart_3609038 : Nat := 118140960795 + 3609038 * 2 ^ 59
def prefixEnd_3609038 : Nat := 4983230072969 + 3 ^ 40 * 3609038 * 2
def baseEnd_3609038 : Nat := 1235447462894237237284895

theorem tailTrace_3609038 : CollatzResearch.WordTrace tailWord_3609038 prefixEnd_3609038 1235447462894237237284895 := by
  unfold tailWord_3609038
  simp only [CollatzResearch.WordTrace]
  refine ⟨16454053737384896932927471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87754953266052783642279845 16454053737384896932927471)
  ·
    refine ⟨24681080606077345399391207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16454053737384896932927471 24681080606077345399391207)
    ·
      refine ⟨37021620909116018099086811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24681080606077345399391207 37021620909116018099086811)
      ·
        refine ⟨55532431363674027148630217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37021620909116018099086811 55532431363674027148630217)
        ·
          refine ⟨41649323522755520361472663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55532431363674027148630217 41649323522755520361472663)
          ·
            refine ⟨62473985284133280542208995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41649323522755520361472663 62473985284133280542208995)
            ·
              refine ⟨93710977926199920813313493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62473985284133280542208995 93710977926199920813313493)
              ·
                refine ⟨2196351045145310644062035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 93710977926199920813313493 2196351045145310644062035)
                ·
                  refine ⟨3294526567717965966093053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2196351045145310644062035 3294526567717965966093053)
                  ·
                    refine ⟨1235447462894237237284895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3294526567717965966093053 1235447462894237237284895)
                    ·
                      rfl

theorem cell22_3609038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 7, 1, 3].length) (baseStart_3609038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3609038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3609038 prefixEnd_3609038 := by exact prefixLift 3609038
  have htrace : WordTrace (prefixWord ++ tailWord_3609038) baseStart_3609038 baseEnd_3609038 := by
    simpa [prefixWord, tailWord_3609038, baseEnd_3609038] using wordTrace_append hprefix tailTrace_3609038
  have hstable : (prefixWord ++ tailWord_3609038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609038).length < 2 ^ (prefixWord ++ tailWord_3609038).sum := by decide
  have hdescent : baseEnd_3609038 < baseStart_3609038 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609049 : List Nat := [1, 2, 1, 2, 4, 1, 2, 2, 2, 5]
def baseStart_3609049 : Nat := 118140960795 + 3609049 * 2 ^ 59
def prefixEnd_3609049 : Nat := 4983230072969 + 3 ^ 40 * 3609049 * 2
def baseEnd_3609049 : Nat := 1235451228419036875259861

theorem tailTrace_3609049 : CollatzResearch.WordTrace tailWord_3609049 prefixEnd_3609049 1235451228419036875259861 := by
  unfold tailWord_3609049
  simp only [CollatzResearch.WordTrace]
  refine ⟨131632831102039324342070201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87755220734692882894713467 131632831102039324342070201)
  ·
    refine ⟨98724623326529493256552651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131632831102039324342070201 98724623326529493256552651)
    ·
      refine ⟨148086934989794239884828977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98724623326529493256552651 148086934989794239884828977)
      ·
        refine ⟨111065201242345679913621733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148086934989794239884828977 111065201242345679913621733)
        ·
          refine ⟨20824725232939814983804075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111065201242345679913621733 20824725232939814983804075)
          ·
            refine ⟨31237087849409722475706113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20824725232939814983804075 31237087849409722475706113)
            ·
              refine ⟨23427815887057291856779585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31237087849409722475706113 23427815887057291856779585)
              ·
                refine ⟨17570861915292968892584689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23427815887057291856779585 17570861915292968892584689)
                ·
                  refine ⟨13178146436469726669438517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17570861915292968892584689 13178146436469726669438517)
                  ·
                    refine ⟨1235451228419036875259861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13178146436469726669438517 1235451228419036875259861)
                    ·
                      rfl

theorem cell22_3609049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 2, 5].length) (baseStart_3609049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3609049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3609049 prefixEnd_3609049 := by exact prefixLift 3609049
  have htrace : WordTrace (prefixWord ++ tailWord_3609049) baseStart_3609049 baseEnd_3609049 := by
    simpa [prefixWord, tailWord_3609049, baseEnd_3609049] using wordTrace_append hprefix tailTrace_3609049
  have hstable : (prefixWord ++ tailWord_3609049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609049).length < 2 ^ (prefixWord ++ tailWord_3609049).sum := by decide
  have hdescent : baseEnd_3609049 < baseStart_3609049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609055 : List Nat := [1, 1, 2, 3, 3, 2, 4, 2, 1, 3]
def baseStart_3609055 : Nat := 118140960795 + 3609055 * 2 ^ 59
def prefixEnd_3609055 : Nat := 4983230072969 + 3 ^ 40 * 3609055 * 2
def baseEnd_3609055 : Nat := 1235453282341654859609843

theorem tailTrace_3609055 : CollatzResearch.WordTrace tailWord_3609055 prefixEnd_3609055 1235453282341654859609843 := by
  unfold tailWord_3609055
  simp only [CollatzResearch.WordTrace]
  refine ⟨131633049940017587366788619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87755366626678391577859079 131633049940017587366788619)
  ·
    refine ⟨197449574910026381050182929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131633049940017587366788619 197449574910026381050182929)
    ·
      refine ⟨148087181182519785787637197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197449574910026381050182929 148087181182519785787637197)
      ·
        refine ⟨55532692943444919670363949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148087181182519785787637197 55532692943444919670363949)
        ·
          refine ⟨20824759853791844876386481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55532692943444919670363949 20824759853791844876386481)
          ·
            refine ⟨15618569890343883657289861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20824759853791844876386481 15618569890343883657289861)
            ·
              refine ⟨2928481854439478185741849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15618569890343883657289861 2928481854439478185741849)
              ·
                refine ⟨2196361390829608639306387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2928481854439478185741849 2196361390829608639306387)
                ·
                  refine ⟨3294542086244412958959581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2196361390829608639306387 3294542086244412958959581)
                  ·
                    refine ⟨1235453282341654859609843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3294542086244412958959581 1235453282341654859609843)
                    ·
                      rfl

theorem cell22_3609055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 4, 2, 1, 3].length) (baseStart_3609055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3609055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3609055 prefixEnd_3609055 := by exact prefixLift 3609055
  have htrace : WordTrace (prefixWord ++ tailWord_3609055) baseStart_3609055 baseEnd_3609055 := by
    simpa [prefixWord, tailWord_3609055, baseEnd_3609055] using wordTrace_append hprefix tailTrace_3609055
  have hstable : (prefixWord ++ tailWord_3609055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609055).length < 2 ^ (prefixWord ++ tailWord_3609055).sum := by decide
  have hdescent : baseEnd_3609055 < baseStart_3609055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609066 : List Nat := [3, 1, 3, 1, 3, 2, 1, 1, 2, 5]
def baseStart_3609066 : Nat := 118140960795 + 3609066 * 2 ^ 59
def prefixEnd_3609066 : Nat := 4983230072969 + 3 ^ 40 * 3609066 * 2
def baseEnd_3609066 : Nat := 1235457047866454497584809

theorem tailTrace_3609066 : CollatzResearch.WordTrace tailWord_3609066 prefixEnd_3609066 1235457047866454497584809 := by
  unfold tailWord_3609066
  simp only [CollatzResearch.WordTrace]
  refine ⟨32908362785744434061359763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87755634095318490830292701 32908362785744434061359763)
  ·
    refine ⟨49362544178616651092039645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32908362785744434061359763 49362544178616651092039645)
    ·
      refine ⟨18510954066981244159514867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49362544178616651092039645 18510954066981244159514867)
      ·
        refine ⟨27766431100471866239272301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18510954066981244159514867 27766431100471866239272301)
        ·
          refine ⟨10412411662676949839727113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27766431100471866239272301 10412411662676949839727113)
          ·
            refine ⟨7809308747007712379795335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10412411662676949839727113 7809308747007712379795335)
            ·
              refine ⟨11713963120511568569693003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7809308747007712379795335 11713963120511568569693003)
              ·
                refine ⟨17570944680767352854539505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11713963120511568569693003 17570944680767352854539505)
                ·
                  refine ⟨13178208510575514640904629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17570944680767352854539505 13178208510575514640904629)
                  ·
                    refine ⟨1235457047866454497584809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13178208510575514640904629 1235457047866454497584809)
                    ·
                      rfl

theorem cell22_3609066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_3609066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3609066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3609066 prefixEnd_3609066 := by exact prefixLift 3609066
  have htrace : WordTrace (prefixWord ++ tailWord_3609066) baseStart_3609066 baseEnd_3609066 := by
    simpa [prefixWord, tailWord_3609066, baseEnd_3609066] using wordTrace_append hprefix tailTrace_3609066
  have hstable : (prefixWord ++ tailWord_3609066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609066).length < 2 ^ (prefixWord ++ tailWord_3609066).sum := by decide
  have hdescent : baseEnd_3609066 < baseStart_3609066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609128 : List Nat := [2, 1, 5, 2, 1, 1, 3, 1, 1, 5]
def baseStart_3609128 : Nat := 118140960795 + 3609128 * 2 ^ 59
def prefixEnd_3609128 : Nat := 4983230072969 + 3 ^ 40 * 3609128 * 2
def baseEnd_3609128 : Nat := 1235478271733507002534619

theorem tailTrace_3609128 : CollatzResearch.WordTrace tailWord_3609128 prefixEnd_3609128 1235478271733507002534619 := by
  unfold tailWord_3609128
  simp only [CollatzResearch.WordTrace]
  refine ⟨65817856234376560417098019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87757141645835413889464025 65817856234376560417098019)
  ·
    refine ⟨98726784351564840625647029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65817856234376560417098019 98726784351564840625647029)
    ·
      refine ⟨9255636032959203808654409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 98726784351564840625647029 9255636032959203808654409)
      ·
        refine ⟨6941727024719402856490807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9255636032959203808654409 6941727024719402856490807)
        ·
          refine ⟨10412590537079104284736211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6941727024719402856490807 10412590537079104284736211)
          ·
            refine ⟨15618885805618656427104317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10412590537079104284736211 15618885805618656427104317)
            ·
              refine ⟨5857082177106996160164119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15618885805618656427104317 5857082177106996160164119)
              ·
                refine ⟨8785623265660494240246179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5857082177106996160164119 8785623265660494240246179)
                ·
                  refine ⟨13178434898490741360369269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8785623265660494240246179 13178434898490741360369269)
                  ·
                    refine ⟨1235478271733507002534619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13178434898490741360369269 1235478271733507002534619)
                    ·
                      rfl

theorem cell22_3609128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_3609128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3609128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3609128 prefixEnd_3609128 := by exact prefixLift 3609128
  have htrace : WordTrace (prefixWord ++ tailWord_3609128) baseStart_3609128 baseEnd_3609128 := by
    simpa [prefixWord, tailWord_3609128, baseEnd_3609128] using wordTrace_append hprefix tailTrace_3609128
  have hstable : (prefixWord ++ tailWord_3609128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609128).length < 2 ^ (prefixWord ++ tailWord_3609128).sum := by decide
  have hdescent : baseEnd_3609128 < baseStart_3609128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609139 : List Nat := [1, 1, 1, 2, 4, 2, 1, 1, 2, 7]
def baseStart_3609139 : Nat := 118140960795 + 3609139 * 2 ^ 59
def prefixEnd_3609139 : Nat := 4983230072969 + 3 ^ 40 * 3609139 * 2
def baseEnd_3609139 : Nat := 1235482037258306640509585

theorem tailTrace_3609139 : CollatzResearch.WordTrace tailWord_3609139 prefixEnd_3609139 1235482037258306640509585 := by
  unfold tailWord_3609139
  simp only [CollatzResearch.WordTrace]
  refine ⟨131636113671713269712846471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87757409114475513141897647 131636113671713269712846471)
  ·
    refine ⟨197454170507569904569269707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131636113671713269712846471 197454170507569904569269707)
    ·
      refine ⟨296181255761354856853904561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197454170507569904569269707 296181255761354856853904561)
      ·
        refine ⟨222135941821016142640428421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296181255761354856853904561 222135941821016142640428421)
        ·
          refine ⟨41650489091440526745080329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 222135941821016142640428421 41650489091440526745080329)
          ·
            refine ⟨31237866818580395058810247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41650489091440526745080329 31237866818580395058810247)
            ·
              refine ⟨46856800227870592588215371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31237866818580395058810247 46856800227870592588215371)
              ·
                refine ⟨70285200341805888882323057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46856800227870592588215371 70285200341805888882323057)
                ·
                  refine ⟨52713900256354416661742293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70285200341805888882323057 52713900256354416661742293)
                  ·
                    refine ⟨1235482037258306640509585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52713900256354416661742293 1235482037258306640509585)
                    ·
                      rfl

theorem cell22_3609139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 7].length) (baseStart_3609139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3609139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3609139 prefixEnd_3609139 := by exact prefixLift 3609139
  have htrace : WordTrace (prefixWord ++ tailWord_3609139) baseStart_3609139 baseEnd_3609139 := by
    simpa [prefixWord, tailWord_3609139, baseEnd_3609139] using wordTrace_append hprefix tailTrace_3609139
  have hstable : (prefixWord ++ tailWord_3609139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609139).length < 2 ^ (prefixWord ++ tailWord_3609139).sum := by decide
  have hdescent : baseEnd_3609139 < baseStart_3609139 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609158 : List Nat := [6, 1, 1, 1, 2, 1, 10]
def baseStart_3609158 : Nat := 118140960795 + 3609158 * 2 ^ 59
def prefixEnd_3609158 : Nat := 4983230072969 + 3 ^ 40 * 3609158 * 2
def baseEnd_3609158 : Nat := 45758834864688774973501

theorem tailTrace_3609158 : CollatzResearch.WordTrace tailWord_3609158 prefixEnd_3609158 45758834864688774973501 := by
  unfold tailWord_3609158
  simp only [CollatzResearch.WordTrace]
  refine ⟨4113650208082638623680879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 87757871105762957305192085 4113650208082638623680879)
  ·
    refine ⟨6170475312123957935521319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4113650208082638623680879 6170475312123957935521319)
    ·
      refine ⟨9255712968185936903281979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6170475312123957935521319 9255712968185936903281979)
      ·
        refine ⟨13883569452278905354922969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9255712968185936903281979 13883569452278905354922969)
        ·
          refine ⟨10412677089209179016192227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13883569452278905354922969 10412677089209179016192227)
          ·
            refine ⟨15619015633813768524288341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10412677089209179016192227 15619015633813768524288341)
            ·
              refine ⟨45758834864688774973501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15619015633813768524288341 45758834864688774973501)
              ·
                rfl

theorem cell22_3609158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 10].length) (baseStart_3609158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3609158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3609158 prefixEnd_3609158 := by exact prefixLift 3609158
  have htrace : WordTrace (prefixWord ++ tailWord_3609158) baseStart_3609158 baseEnd_3609158 := by
    simpa [prefixWord, tailWord_3609158, baseEnd_3609158] using wordTrace_append hprefix tailTrace_3609158
  have hstable : (prefixWord ++ tailWord_3609158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609158).length < 2 ^ (prefixWord ++ tailWord_3609158).sum := by decide
  have hdescent : baseEnd_3609158 < baseStart_3609158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609173 : List Nat := [1, 3, 2, 2, 1, 1, 5, 1, 3, 3]
def baseStart_3609173 : Nat := 118140960795 + 3609173 * 2 ^ 59
def prefixEnd_3609173 : Nat := 4983230072969 + 3 ^ 40 * 3609173 * 2
def baseEnd_3609173 : Nat := 1235493676153141885159481

theorem tailTrace_3609173 : CollatzResearch.WordTrace tailWord_3609173 prefixEnd_3609173 1235493676153141885159481 := by
  unfold tailWord_3609173
  simp only [CollatzResearch.WordTrace]
  refine ⟨131637353753590093519584173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87758235835726729013056115 131637353753590093519584173)
  ·
    refine ⟨49364007657596285069844065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131637353753590093519584173 49364007657596285069844065)
    ·
      refine ⟨37023005743197213802383049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49364007657596285069844065 37023005743197213802383049)
      ·
        refine ⟨27767254307397910351787287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37023005743197213802383049 27767254307397910351787287)
        ·
          refine ⟨41650881461096865527680931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27767254307397910351787287 41650881461096865527680931)
          ·
            refine ⟨62476322191645298291521397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41650881461096865527680931 62476322191645298291521397)
            ·
              refine ⟨5857155205466746714830131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62476322191645298291521397 5857155205466746714830131)
              ·
                refine ⟨8785732808200120072245197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5857155205466746714830131 8785732808200120072245197)
                ·
                  refine ⟨3294649803075045027091949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8785732808200120072245197 3294649803075045027091949)
                  ·
                    refine ⟨1235493676153141885159481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3294649803075045027091949 1235493676153141885159481)
                    ·
                      rfl

theorem cell22_3609173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 1, 3, 3].length) (baseStart_3609173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3609173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3609173 prefixEnd_3609173 := by exact prefixLift 3609173
  have htrace : WordTrace (prefixWord ++ tailWord_3609173) baseStart_3609173 baseEnd_3609173 := by
    simpa [prefixWord, tailWord_3609173, baseEnd_3609173] using wordTrace_append hprefix tailTrace_3609173
  have hstable : (prefixWord ++ tailWord_3609173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609173).length < 2 ^ (prefixWord ++ tailWord_3609173).sum := by decide
  have hdescent : baseEnd_3609173 < baseStart_3609173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609248 : List Nat := [2, 1, 1, 4, 4, 1, 1, 2, 6]
def baseStart_3609248 : Nat := 118140960795 + 3609248 * 2 ^ 59
def prefixEnd_3609248 : Nat := 4983230072969 + 3 ^ 40 * 3609248 * 2
def baseEnd_3609248 : Nat := 411839783395288896511417

theorem tailTrace_3609248 : CollatzResearch.WordTrace tailWord_3609248 prefixEnd_3609248 411839783395288896511417 := by
  unfold tailWord_3609248
  simp only [CollatzResearch.WordTrace]
  refine ⟨65820044614159190664282199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87760059485545587552376265 65820044614159190664282199)
  ·
    refine ⟨98730066921238785996423299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65820044614159190664282199 98730066921238785996423299)
    ·
      refine ⟨148095100381858178994634949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98730066921238785996423299 148095100381858178994634949)
      ·
        refine ⟨27767831321598408561494053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148095100381858178994634949 27767831321598408561494053)
        ·
          refine ⟨5206468372799701605280135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27767831321598408561494053 5206468372799701605280135)
          ·
            refine ⟨7809702559199552407920203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5206468372799701605280135 7809702559199552407920203)
            ·
              refine ⟨11714553838799328611880305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7809702559199552407920203 11714553838799328611880305)
              ·
                refine ⟨8785915379099496458910229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11714553838799328611880305 8785915379099496458910229)
                ·
                  refine ⟨411839783395288896511417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8785915379099496458910229 411839783395288896511417)
                  ·
                    rfl

theorem cell22_3609248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 2, 6].length) (baseStart_3609248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3609248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3609248 prefixEnd_3609248 := by exact prefixLift 3609248
  have htrace : WordTrace (prefixWord ++ tailWord_3609248) baseStart_3609248 baseEnd_3609248 := by
    simpa [prefixWord, tailWord_3609248, baseEnd_3609248] using wordTrace_append hprefix tailTrace_3609248
  have hstable : (prefixWord ++ tailWord_3609248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609248).length < 2 ^ (prefixWord ++ tailWord_3609248).sum := by decide
  have hdescent : baseEnd_3609248 < baseStart_3609248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609276 : List Nat := [2, 2, 2, 3, 1, 1, 11]
def baseStart_3609276 : Nat := 118140960795 + 3609276 * 2 ^ 59
def prefixEnd_3609276 : Nat := 4983230072969 + 3 ^ 40 * 3609276 * 2
def baseEnd_3609276 : Nat := 45760330931780887030895

theorem tailTrace_3609276 : CollatzResearch.WordTrace tailWord_3609276 prefixEnd_3609276 45760330931780887030895 := by
  unfold tailWord_3609276
  simp only [CollatzResearch.WordTrace]
  refine ⟨65820555236108471055291841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87760740314811294740389121 65820555236108471055291841)
  ·
    refine ⟨49365416427081353291468881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65820555236108471055291841 49365416427081353291468881)
    ·
      refine ⟨37024062320311014968601661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49365416427081353291468881 37024062320311014968601661)
      ·
        refine ⟨13884023370116630613225623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37024062320311014968601661 13884023370116630613225623)
        ·
          refine ⟨20826035055174945919838435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13884023370116630613225623 20826035055174945919838435)
          ·
            refine ⟨31239052582762418879757653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20826035055174945919838435 31239052582762418879757653)
            ·
              refine ⟨45760330931780887030895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 31239052582762418879757653 45760330931780887030895)
              ·
                rfl

theorem cell22_3609276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 11].length) (baseStart_3609276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3609276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3609276 prefixEnd_3609276 := by exact prefixLift 3609276
  have htrace : WordTrace (prefixWord ++ tailWord_3609276) baseStart_3609276 baseEnd_3609276 := by
    simpa [prefixWord, tailWord_3609276, baseEnd_3609276] using wordTrace_append hprefix tailTrace_3609276
  have hstable : (prefixWord ++ tailWord_3609276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609276).length < 2 ^ (prefixWord ++ tailWord_3609276).sum := by decide
  have hdescent : baseEnd_3609276 < baseStart_3609276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609278 : List Nat := [4, 2, 1, 1, 2, 1, 2, 1, 4, 4]
def baseStart_3609278 : Nat := 118140960795 + 3609278 * 2 ^ 59
def prefixEnd_3609278 : Nat := 4983230072969 + 3 ^ 40 * 3609278 * 2
def baseEnd_3609278 : Nat := 1235529619798956611284159

theorem tailTrace_3609278 : CollatzResearch.WordTrace tailWord_3609278 prefixEnd_3609278 1235529619798956611284159 := by
  unfold tailWord_3609278
  simp only [CollatzResearch.WordTrace]
  refine ⟨16455147927276212056519561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87760788945473130968104325 16455147927276212056519561)
  ·
    refine ⟨12341360945457159042389671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16455147927276212056519561 12341360945457159042389671)
    ·
      refine ⟨18512041418185738563584507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12341360945457159042389671 18512041418185738563584507)
      ·
        refine ⟨27768062127278607845376761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18512041418185738563584507 27768062127278607845376761)
        ·
          refine ⟨20826046595458955884032571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27768062127278607845376761 20826046595458955884032571)
          ·
            refine ⟨31239069893188433826048857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20826046595458955884032571 31239069893188433826048857)
            ·
              refine ⟨23429302419891325369536643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31239069893188433826048857 23429302419891325369536643)
              ·
                refine ⟨35143953629836988054304965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23429302419891325369536643 35143953629836988054304965)
                ·
                  refine ⟨6589491305594435260182181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35143953629836988054304965 6589491305594435260182181)
                  ·
                    refine ⟨1235529619798956611284159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6589491305594435260182181 1235529619798956611284159)
                    ·
                      rfl

theorem cell22_3609278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_3609278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3609278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3609278 prefixEnd_3609278 := by exact prefixLift 3609278
  have htrace : WordTrace (prefixWord ++ tailWord_3609278) baseStart_3609278 baseEnd_3609278 := by
    simpa [prefixWord, tailWord_3609278, baseEnd_3609278] using wordTrace_append hprefix tailTrace_3609278
  have hstable : (prefixWord ++ tailWord_3609278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609278).length < 2 ^ (prefixWord ++ tailWord_3609278).sum := by decide
  have hdescent : baseEnd_3609278 < baseStart_3609278 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609280 : List Nat := [2, 1, 1, 2, 4, 2, 3, 2, 2, 3]
def baseStart_3609280 : Nat := 118140960795 + 3609280 * 2 ^ 59
def prefixEnd_3609280 : Nat := 4983230072969 + 3 ^ 40 * 3609280 * 2
def baseEnd_3609280 : Nat := 1235530304439829272734153

theorem tailTrace_3609280 : CollatzResearch.WordTrace tailWord_3609280 prefixEnd_3609280 1235530304439829272734153 := by
  unfold tailWord_3609280
  simp only [CollatzResearch.WordTrace]
  refine ⟨65820628182101225396864647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87760837576134967195819529 65820628182101225396864647)
  ·
    refine ⟨98730942273151838095296971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65820628182101225396864647 98730942273151838095296971)
    ·
      refine ⟨148096413409727757142945457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98730942273151838095296971 148096413409727757142945457)
      ·
        refine ⟨111072310057295817857209093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148096413409727757142945457 111072310057295817857209093)
        ·
          refine ⟨20826058135742965848226705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111072310057295817857209093 20826058135742965848226705)
          ·
            refine ⟨15619543601807224386170029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20826058135742965848226705 15619543601807224386170029)
            ·
              refine ⟨5857328850677709144813761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15619543601807224386170029 5857328850677709144813761)
              ·
                refine ⟨4392996638008281858610321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5857328850677709144813761 4392996638008281858610321)
                ·
                  refine ⟨3294747478506211393957741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4392996638008281858610321 3294747478506211393957741)
                  ·
                    refine ⟨1235530304439829272734153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3294747478506211393957741 1235530304439829272734153)
                    ·
                      rfl

theorem cell22_3609280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 2, 2, 3].length) (baseStart_3609280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3609280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3609280 prefixEnd_3609280 := by exact prefixLift 3609280
  have htrace : WordTrace (prefixWord ++ tailWord_3609280) baseStart_3609280 baseEnd_3609280 := by
    simpa [prefixWord, tailWord_3609280, baseEnd_3609280] using wordTrace_append hprefix tailTrace_3609280
  have hstable : (prefixWord ++ tailWord_3609280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609280).length < 2 ^ (prefixWord ++ tailWord_3609280).sum := by decide
  have hdescent : baseEnd_3609280 < baseStart_3609280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609321 : List Nat := [1, 2, 1, 1, 1, 2, 5, 2, 7]
def baseStart_3609321 : Nat := 118140960795 + 3609321 * 2 ^ 59
def prefixEnd_3609321 : Nat := 4983230072969 + 3 ^ 40 * 3609321 * 2
def baseEnd_3609321 : Nat := 411848113192572944153009

theorem tailTrace_3609321 : CollatzResearch.WordTrace tailWord_3609321 prefixEnd_3609321 411848113192572944153009 := by
  unfold tailWord_3609321
  simp only [CollatzResearch.WordTrace]
  refine ⟨131642751757053914795971817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87761834504702609863981211 131642751757053914795971817)
  ·
    refine ⟨98732063817790436096978863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131642751757053914795971817 98732063817790436096978863)
    ·
      refine ⟨148098095726685654145468295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98732063817790436096978863 148098095726685654145468295)
      ·
        refine ⟨222147143590028481218202443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148098095726685654145468295 222147143590028481218202443)
        ·
          refine ⟨333220715385042721827303665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222147143590028481218202443 333220715385042721827303665)
          ·
            refine ⟨249915536538782041370477749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 333220715385042721827303665 249915536538782041370477749)
            ·
              refine ⟨23429581550510816378482289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 249915536538782041370477749 23429581550510816378482289)
              ·
                refine ⟨17572186162883112283861717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23429581550510816378482289 17572186162883112283861717)
                ·
                  refine ⟨411848113192572944153009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17572186162883112283861717 411848113192572944153009)
                  ·
                    rfl

theorem cell22_3609321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 7].length) (baseStart_3609321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3609321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3609321 prefixEnd_3609321 := by exact prefixLift 3609321
  have htrace : WordTrace (prefixWord ++ tailWord_3609321) baseStart_3609321 baseEnd_3609321 := by
    simpa [prefixWord, tailWord_3609321, baseEnd_3609321] using wordTrace_append hprefix tailTrace_3609321
  have hstable : (prefixWord ++ tailWord_3609321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609321).length < 2 ^ (prefixWord ++ tailWord_3609321).sum := by decide
  have hdescent : baseEnd_3609321 < baseStart_3609321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609342 : List Nat := [4, 2, 2, 1, 2, 1, 3, 1, 3, 3]
def baseStart_3609342 : Nat := 118140960795 + 3609342 * 2 ^ 59
def prefixEnd_3609342 : Nat := 4983230072969 + 3 ^ 40 * 3609342 * 2
def baseEnd_3609342 : Nat := 1235551528306881777683963

theorem tailTrace_3609342 : CollatzResearch.WordTrace tailWord_3609342 prefixEnd_3609342 1235551528306881777683963 := by
  unfold tailWord_3609342
  simp only [CollatzResearch.WordTrace]
  refine ⟨16455439711247229422810785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87762345126651890254990853 16455439711247229422810785)
  ·
    refine ⟨12341579783435422067108089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16455439711247229422810785 12341579783435422067108089)
    ·
      refine ⟨9256184837576566550331067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12341579783435422067108089 9256184837576566550331067)
      ·
        refine ⟨13884277256364849825496601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9256184837576566550331067 13884277256364849825496601)
        ·
          refine ⟨10413207942273637369122451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13884277256364849825496601 10413207942273637369122451)
          ·
            refine ⟨15619811913410456053683677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10413207942273637369122451 15619811913410456053683677)
            ·
              refine ⟨5857429467528921020131379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15619811913410456053683677 5857429467528921020131379)
              ·
                refine ⟨8786144201293381530197069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5857429467528921020131379 8786144201293381530197069)
                ·
                  refine ⟨3294804075485018073823901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8786144201293381530197069 3294804075485018073823901)
                  ·
                    refine ⟨1235551528306881777683963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3294804075485018073823901 1235551528306881777683963)
                    ·
                      rfl

theorem cell22_3609342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_3609342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3609342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3609342 prefixEnd_3609342 := by exact prefixLift 3609342
  have htrace : WordTrace (prefixWord ++ tailWord_3609342) baseStart_3609342 baseEnd_3609342 := by
    simpa [prefixWord, tailWord_3609342, baseEnd_3609342] using wordTrace_append hprefix tailTrace_3609342
  have hstable : (prefixWord ++ tailWord_3609342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609342).length < 2 ^ (prefixWord ++ tailWord_3609342).sum := by decide
  have hdescent : baseEnd_3609342 < baseStart_3609342 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609389 : List Nat := [1, 5, 3, 2, 1, 1, 2, 2, 5]
def baseStart_3609389 : Nat := 118140960795 + 3609389 * 2 ^ 59
def prefixEnd_3609389 : Nat := 4983230072969 + 3 ^ 40 * 3609389 * 2
def baseEnd_3609389 : Nat := 411855872455796440586273

theorem tailTrace_3609389 : CollatzResearch.WordTrace tailWord_3609389 prefixEnd_3609389 411855872455796440586273 := by
  unfold tailWord_3609389
  simp only [CollatzResearch.WordTrace]
  refine ⟨131645231920807562409447221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87763487947205041606298147 131645231920807562409447221)
  ·
    refine ⟨12341740492575708975885677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 131645231920807562409447221 12341740492575708975885677)
    ·
      refine ⟨4628152684715890865957129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12341740492575708975885677 4628152684715890865957129)
      ·
        refine ⟨3471114513536918149467847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4628152684715890865957129 3471114513536918149467847)
        ·
          refine ⟨5206671770305377224201771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3471114513536918149467847 5206671770305377224201771)
          ·
            refine ⟨7810007655458065836302657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5206671770305377224201771 7810007655458065836302657)
            ·
              refine ⟨5857505741593549377226993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7810007655458065836302657 5857505741593549377226993)
              ·
                refine ⟨4393129306195162032920245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5857505741593549377226993 4393129306195162032920245)
                ·
                  refine ⟨411855872455796440586273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4393129306195162032920245 411855872455796440586273)
                  ·
                    rfl

theorem cell22_3609389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 2, 5].length) (baseStart_3609389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3609389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3609389 prefixEnd_3609389 := by exact prefixLift 3609389
  have htrace : WordTrace (prefixWord ++ tailWord_3609389) baseStart_3609389 baseEnd_3609389 := by
    simpa [prefixWord, tailWord_3609389, baseEnd_3609389] using wordTrace_append hprefix tailTrace_3609389
  have hstable : (prefixWord ++ tailWord_3609389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609389).length < 2 ^ (prefixWord ++ tailWord_3609389).sum := by decide
  have hdescent : baseEnd_3609389 < baseStart_3609389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609400 : List Nat := [2, 1, 2, 1, 3, 2, 3, 4, 4]
def baseStart_3609400 : Nat := 118140960795 + 3609400 * 2 ^ 59
def prefixEnd_3609400 : Nat := 4983230072969 + 3 ^ 40 * 3609400 * 2
def baseEnd_3609400 : Nat := 411857127630729653244595

theorem tailTrace_3609400 : CollatzResearch.WordTrace tailWord_3609400 prefixEnd_3609400 411857127630729653244595 := by
  unfold tailWord_3609400
  simp only [CollatzResearch.WordTrace]
  refine ⟨65822816561883855644048827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87763755415845140858731769 65822816561883855644048827)
  ·
    refine ⟨98734224842825783466073241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65822816561883855644048827 98734224842825783466073241)
    ·
      refine ⟨74050668632119337599554931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98734224842825783466073241 74050668632119337599554931)
      ·
        refine ⟨111076002948179006399332397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74050668632119337599554931 111076002948179006399332397)
        ·
          refine ⟨41653501105567127399749649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111076002948179006399332397 41653501105567127399749649)
          ·
            refine ⟨31240125829175345549812237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41653501105567127399749649 31240125829175345549812237)
            ·
              refine ⟨11715047185940754581179589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31240125829175345549812237 11715047185940754581179589)
              ·
                refine ⟨2196571347363891483971173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11715047185940754581179589 2196571347363891483971173)
                ·
                  refine ⟨411857127630729653244595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2196571347363891483971173 411857127630729653244595)
                  ·
                    rfl

theorem cell22_3609400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 4, 4].length) (baseStart_3609400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3609400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3609400 prefixEnd_3609400 := by exact prefixLift 3609400
  have htrace : WordTrace (prefixWord ++ tailWord_3609400) baseStart_3609400 baseEnd_3609400 := by
    simpa [prefixWord, tailWord_3609400, baseEnd_3609400] using wordTrace_append hprefix tailTrace_3609400
  have hstable : (prefixWord ++ tailWord_3609400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609400).length < 2 ^ (prefixWord ++ tailWord_3609400).sum := by decide
  have hdescent : baseEnd_3609400 < baseStart_3609400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609458 : List Nat := [3, 2, 1, 2, 1, 1, 2, 1, 1, 8]
def baseStart_3609458 : Nat := 118140960795 + 3609458 * 2 ^ 59
def prefixEnd_3609458 : Nat := 4983230072969 + 3 ^ 40 * 3609458 * 2
def baseEnd_3609458 : Nat := 1235591237477496141783607

theorem tailTrace_3609458 : CollatzResearch.WordTrace tailWord_3609458 prefixEnd_3609458 1235591237477496141783607 := by
  unfold tailWord_3609458
  simp only [CollatzResearch.WordTrace]
  refine ⟨32911937139389396798427257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87765165705038391462472685 32911937139389396798427257)
  ·
    refine ⟨24683952854542047598820443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32911937139389396798427257 24683952854542047598820443)
    ·
      refine ⟨37025929281813071398230665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24683952854542047598820443 37025929281813071398230665)
      ·
        refine ⟨27769446961359803548672999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37025929281813071398230665 27769446961359803548672999)
        ·
          refine ⟨41654170442039705323009499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27769446961359803548672999 41654170442039705323009499)
          ·
            refine ⟨62481255663059557984514249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41654170442039705323009499 62481255663059557984514249)
            ·
              refine ⟨46860941747294668488385687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62481255663059557984514249 46860941747294668488385687)
              ·
                refine ⟨70291412620942002732578531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46860941747294668488385687 70291412620942002732578531)
                ·
                  refine ⟨105437118931413004098867797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70291412620942002732578531 105437118931413004098867797)
                  ·
                    refine ⟨1235591237477496141783607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 105437118931413004098867797 1235591237477496141783607)
                    ·
                      rfl

theorem cell22_3609458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_3609458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3609458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3609458 prefixEnd_3609458 := by exact prefixLift 3609458
  have htrace : WordTrace (prefixWord ++ tailWord_3609458) baseStart_3609458 baseEnd_3609458 := by
    simpa [prefixWord, tailWord_3609458, baseEnd_3609458] using wordTrace_append hprefix tailTrace_3609458
  have hstable : (prefixWord ++ tailWord_3609458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609458).length < 2 ^ (prefixWord ++ tailWord_3609458).sum := by decide
  have hdescent : baseEnd_3609458 < baseStart_3609458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609511 : List Nat := [1, 1, 6, 1, 4, 1, 1, 1, 3, 3]
def baseStart_3609511 : Nat := 118140960795 + 3609511 * 2 ^ 59
def prefixEnd_3609511 : Nat := 4983230072969 + 3 ^ 40 * 3609511 * 2
def baseEnd_3609511 : Nat := 1235609380460621670208445

theorem tailTrace_3609511 : CollatzResearch.WordTrace tailWord_3609511 prefixEnd_3609511 1235609380460621670208445 := by
  unfold tailWord_3609511
  simp only [CollatzResearch.WordTrace]
  refine ⟨131649681626365577245388387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87766454417577051496925591 131649681626365577245388387)
  ·
    refine ⟨197474522439548365868082581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131649681626365577245388387 197474522439548365868082581)
    ·
      refine ⟨9256618239353829650066371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 197474522439548365868082581 9256618239353829650066371)
      ·
        refine ⟨13884927359030744475099557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9256618239353829650066371 13884927359030744475099557)
        ·
          refine ⟨2603423879818264589081167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13884927359030744475099557 2603423879818264589081167)
          ·
            refine ⟨3905135819727396883621751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2603423879818264589081167 3905135819727396883621751)
            ·
              refine ⟨5857703729591095325432627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3905135819727396883621751 5857703729591095325432627)
              ·
                refine ⟨8786555594386642988148941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5857703729591095325432627 8786555594386642988148941)
                ·
                  refine ⟨3294958347894991120555853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8786555594386642988148941 3294958347894991120555853)
                  ·
                    refine ⟨1235609380460621670208445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3294958347894991120555853 1235609380460621670208445)
                    ·
                      rfl

theorem cell22_3609511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_3609511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3609511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3609511 prefixEnd_3609511 := by exact prefixLift 3609511
  have htrace : WordTrace (prefixWord ++ tailWord_3609511) baseStart_3609511 baseEnd_3609511 := by
    simpa [prefixWord, tailWord_3609511, baseEnd_3609511] using wordTrace_append hprefix tailTrace_3609511
  have hstable : (prefixWord ++ tailWord_3609511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609511).length < 2 ^ (prefixWord ++ tailWord_3609511).sum := by decide
  have hdescent : baseEnd_3609511 < baseStart_3609511 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609524 : List Nat := [2, 5, 2, 1, 1, 2, 1, 3, 5]
def baseStart_3609524 : Nat := 118140960795 + 3609524 * 2 ^ 59
def prefixEnd_3609524 : Nat := 4983230072969 + 3 ^ 40 * 3609524 * 2
def baseEnd_3609524 : Nat := 411871276875431323211135

theorem tailTrace_3609524 : CollatzResearch.WordTrace tailWord_3609524 prefixEnd_3609524 411871276875431323211135 := by
  unfold tailWord_3609524
  simp only [CollatzResearch.WordTrace]
  refine ⟨65825077887659240232805813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87766770516878986977074417 65825077887659240232805813)
  ·
    refine ⟨6171101051968053771825545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65825077887659240232805813 6171101051968053771825545)
    ·
      refine ⟨4628325788976040328869159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6171101051968053771825545 4628325788976040328869159)
      ·
        refine ⟨6942488683464060493303739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4628325788976040328869159 6942488683464060493303739)
        ·
          refine ⟨10413733025196090739955609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6942488683464060493303739 10413733025196090739955609)
          ·
            refine ⟨7810299768897068054966707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10413733025196090739955609 7810299768897068054966707)
            ·
              refine ⟨11715449653345602082450061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7810299768897068054966707 11715449653345602082450061)
              ·
                refine ⟨4393293620004600780918773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11715449653345602082450061 4393293620004600780918773)
                ·
                  refine ⟨411871276875431323211135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4393293620004600780918773 411871276875431323211135)
                  ·
                    rfl

theorem cell22_3609524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_3609524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3609524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3609524 prefixEnd_3609524 := by exact prefixLift 3609524
  have htrace : WordTrace (prefixWord ++ tailWord_3609524) baseStart_3609524 baseEnd_3609524 := by
    simpa [prefixWord, tailWord_3609524, baseEnd_3609524] using wordTrace_append hprefix tailTrace_3609524
  have hstable : (prefixWord ++ tailWord_3609524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609524).length < 2 ^ (prefixWord ++ tailWord_3609524).sum := by decide
  have hdescent : baseEnd_3609524 < baseStart_3609524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609550 : List Nat := [4, 1, 1, 1, 2, 3, 1, 1, 3, 5]
def baseStart_3609550 : Nat := 118140960795 + 3609550 * 2 ^ 59
def prefixEnd_3609550 : Nat := 4983230072969 + 3 ^ 40 * 3609550 * 2
def baseEnd_3609550 : Nat := 1235622730957638568483325

theorem tailTrace_3609550 : CollatzResearch.WordTrace tailWord_3609550 prefixEnd_3609550 1235622730957638568483325 := by
  unfold tailWord_3609550
  simp only [CollatzResearch.WordTrace]
  refine ⟨16456388009153035863257263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87767402715482857937372069 16456388009153035863257263)
  ·
    refine ⟨24684582013729553794885895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16456388009153035863257263 24684582013729553794885895)
    ·
      refine ⟨37026873020594330692328843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24684582013729553794885895 37026873020594330692328843)
      ·
        refine ⟨55540309530891496038493265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37026873020594330692328843 55540309530891496038493265)
        ·
          refine ⟨41655232148168622028869949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55540309530891496038493265 41655232148168622028869949)
          ·
            refine ⟨15620712055563233260826231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41655232148168622028869949 15620712055563233260826231)
            ·
              refine ⟨23431068083344849891239347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15620712055563233260826231 23431068083344849891239347)
              ·
                refine ⟨35146602125017274836859021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23431068083344849891239347 35146602125017274836859021)
                ·
                  refine ⟨13179975796881478063822133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35146602125017274836859021 13179975796881478063822133)
                  ·
                    refine ⟨1235622730957638568483325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13179975796881478063822133 1235622730957638568483325)
                    ·
                      rfl

theorem cell22_3609550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 3, 5].length) (baseStart_3609550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3609550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3609550 prefixEnd_3609550 := by exact prefixLift 3609550
  have htrace : WordTrace (prefixWord ++ tailWord_3609550) baseStart_3609550 baseEnd_3609550 := by
    simpa [prefixWord, tailWord_3609550, baseEnd_3609550] using wordTrace_append hprefix tailTrace_3609550
  have hstable : (prefixWord ++ tailWord_3609550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609550).length < 2 ^ (prefixWord ++ tailWord_3609550).sum := by decide
  have hdescent : baseEnd_3609550 < baseStart_3609550 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609618 : List Nat := [3, 2, 5, 1, 1, 1, 1, 1, 4, 3]
def baseStart_3609618 : Nat := 118140960795 + 3609618 * 2 ^ 59
def prefixEnd_3609618 : Nat := 4983230072969 + 3 ^ 40 * 3609618 * 2
def baseEnd_3609618 : Nat := 1235646008747309057783117

theorem tailTrace_3609618 : CollatzResearch.WordTrace tailWord_3609618 prefixEnd_3609618 1235646008747309057783117 := by
  unfold tailWord_3609618
  simp only [CollatzResearch.WordTrace]
  refine ⟨32913396059244483629883377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87769056157985289679689005 32913396059244483629883377)
  ·
    refine ⟨24685047044433362722412533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32913396059244483629883377 24685047044433362722412533)
    ·
      refine ⟨2314223160415627755226175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24685047044433362722412533 2314223160415627755226175)
      ·
        refine ⟨3471334740623441632839263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2314223160415627755226175 3471334740623441632839263)
        ·
          refine ⟨5207002110935162449258895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3471334740623441632839263 5207002110935162449258895)
          ·
            refine ⟨7810503166402743673888343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5207002110935162449258895 7810503166402743673888343)
            ·
              refine ⟨11715754749604115510832515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7810503166402743673888343 11715754749604115510832515)
              ·
                refine ⟨17573632124406173266248773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11715754749604115510832515 17573632124406173266248773)
                ·
                  refine ⟨3295056023326157487421645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17573632124406173266248773 3295056023326157487421645)
                  ·
                    refine ⟨1235646008747309057783117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3295056023326157487421645 1235646008747309057783117)
                    ·
                      rfl

theorem cell22_3609618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_3609618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3609618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3609618 prefixEnd_3609618 := by exact prefixLift 3609618
  have htrace : WordTrace (prefixWord ++ tailWord_3609618) baseStart_3609618 baseEnd_3609618 := by
    simpa [prefixWord, tailWord_3609618, baseEnd_3609618] using wordTrace_append hprefix tailTrace_3609618
  have hstable : (prefixWord ++ tailWord_3609618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609618).length < 2 ^ (prefixWord ++ tailWord_3609618).sum := by decide
  have hdescent : baseEnd_3609618 < baseStart_3609618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609672 : List Nat := [2, 1, 3, 1, 1, 1, 3, 5, 1, 4]
def baseStart_3609672 : Nat := 118140960795 + 3609672 * 2 ^ 59
def prefixEnd_3609672 : Nat := 4983230072969 + 3 ^ 40 * 3609672 * 2
def baseEnd_3609672 : Nat := 1235664494050870916932951

theorem tailTrace_3609672 : CollatzResearch.WordTrace tailWord_3609672 prefixEnd_3609672 1235664494050870916932951 := by
  unfold tailWord_3609672
  simp only [CollatzResearch.WordTrace]
  refine ⟨65827776889391150870999635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87770369185854867827999513 65827776889391150870999635)
  ·
    refine ⟨98741665334086726306499453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65827776889391150870999635 98741665334086726306499453)
    ·
      refine ⟨37028124500282522364937295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98741665334086726306499453 37028124500282522364937295)
      ·
        refine ⟨55542186750423783547405943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37028124500282522364937295 55542186750423783547405943)
        ·
          refine ⟨83313280125635675321108915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55542186750423783547405943 83313280125635675321108915)
          ·
            refine ⟨124969920188453512981663373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83313280125635675321108915 124969920188453512981663373)
            ·
              refine ⟨46863720070670067368123765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124969920188453512981663373 46863720070670067368123765)
              ·
                refine ⟨4393473756625318815761603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46863720070670067368123765 4393473756625318815761603)
                ·
                  refine ⟨6590210634937978223642405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4393473756625318815761603 6590210634937978223642405)
                  ·
                    refine ⟨1235664494050870916932951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6590210634937978223642405 1235664494050870916932951)
                    ·
                      rfl

theorem cell22_3609672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 5, 1, 4].length) (baseStart_3609672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3609672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3609672 prefixEnd_3609672 := by exact prefixLift 3609672
  have htrace : WordTrace (prefixWord ++ tailWord_3609672) baseStart_3609672 baseEnd_3609672 := by
    simpa [prefixWord, tailWord_3609672, baseEnd_3609672] using wordTrace_append hprefix tailTrace_3609672
  have hstable : (prefixWord ++ tailWord_3609672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609672).length < 2 ^ (prefixWord ++ tailWord_3609672).sum := by decide
  have hdescent : baseEnd_3609672 < baseStart_3609672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609693 : List Nat := [1, 4, 4, 1, 2, 2, 2, 1, 5]
def baseStart_3609693 : Nat := 118140960795 + 3609693 * 2 ^ 59
def prefixEnd_3609693 : Nat := 4983230072969 + 3 ^ 40 * 3609693 * 2
def baseEnd_3609693 : Nat := 411890560926677954052629

theorem tailTrace_3609693 : CollatzResearch.WordTrace tailWord_3609693 prefixEnd_3609693 411890560926677954052629 := by
  unfold tailWord_3609693
  simp only [CollatzResearch.WordTrace]
  refine ⟨131656319711706222328513733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87770879807804148219009155 131656319711706222328513733)
  ·
    refine ⟨24685559945944916686596325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131656319711706222328513733 24685559945944916686596325)
    ·
      refine ⟨4628542489864671878736811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24685559945944916686596325 4628542489864671878736811)
      ·
        refine ⟨6942813734797007818105217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4628542489864671878736811 6942813734797007818105217)
        ·
          refine ⟨5207110301097755863578913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6942813734797007818105217 5207110301097755863578913)
          ·
            refine ⟨3905332725823316897684185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5207110301097755863578913 3905332725823316897684185)
            ·
              refine ⟨2928999544367487673263139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3905332725823316897684185 2928999544367487673263139)
              ·
                refine ⟨4393499316551231509894709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2928999544367487673263139 4393499316551231509894709)
                ·
                  refine ⟨411890560926677954052629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4393499316551231509894709 411890560926677954052629)
                  ·
                    rfl

theorem cell22_3609693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 2, 1, 5].length) (baseStart_3609693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3609693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3609693 prefixEnd_3609693 := by exact prefixLift 3609693
  have htrace : WordTrace (prefixWord ++ tailWord_3609693) baseStart_3609693 baseEnd_3609693 := by
    simpa [prefixWord, tailWord_3609693, baseEnd_3609693] using wordTrace_append hprefix tailTrace_3609693
  have hstable : (prefixWord ++ tailWord_3609693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609693).length < 2 ^ (prefixWord ++ tailWord_3609693).sum := by decide
  have hdescent : baseEnd_3609693 < baseStart_3609693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609706 : List Nat := [3, 1, 3, 2, 2, 3, 1, 2, 1, 4]
def baseStart_3609706 : Nat := 118140960795 + 3609706 * 2 ^ 59
def prefixEnd_3609706 : Nat := 4983230072969 + 3 ^ 40 * 3609706 * 2
def baseEnd_3609706 : Nat := 1235676132945706161582847

theorem tailTrace_3609706 : CollatzResearch.WordTrace tailWord_3609706 prefixEnd_3609706 1235676132945706161582847 := by
  unfold tailWord_3609706
  simp only [CollatzResearch.WordTrace]
  refine ⟨32914198465164781387184243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87771195907106083699157981 32914198465164781387184243)
  ·
    refine ⟨49371297697747172080776365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32914198465164781387184243 49371297697747172080776365)
    ·
      refine ⟨18514236636655189530291137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49371297697747172080776365 18514236636655189530291137)
      ·
        refine ⟨13885677477491392147718353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18514236636655189530291137 13885677477491392147718353)
        ·
          refine ⟨10414258108118544110788765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13885677477491392147718353 10414258108118544110788765)
          ·
            refine ⟨3905346790544454041545787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10414258108118544110788765 3905346790544454041545787)
            ·
              refine ⟨5858020185816681062318681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3905346790544454041545787 5858020185816681062318681)
              ·
                refine ⟨4393515139362510796739011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5858020185816681062318681 4393515139362510796739011)
                ·
                  refine ⟨6590272709043766195108517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4393515139362510796739011 6590272709043766195108517)
                  ·
                    refine ⟨1235676132945706161582847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6590272709043766195108517 1235676132945706161582847)
                    ·
                      rfl

theorem cell22_3609706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 2, 1, 4].length) (baseStart_3609706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3609706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3609706 prefixEnd_3609706 := by exact prefixLift 3609706
  have htrace : WordTrace (prefixWord ++ tailWord_3609706) baseStart_3609706 baseEnd_3609706 := by
    simpa [prefixWord, tailWord_3609706, baseEnd_3609706] using wordTrace_append hprefix tailTrace_3609706
  have hstable : (prefixWord ++ tailWord_3609706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609706).length < 2 ^ (prefixWord ++ tailWord_3609706).sum := by decide
  have hdescent : baseEnd_3609706 < baseStart_3609706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609764 : List Nat := [2, 3, 1, 2, 3, 1, 1, 1, 5, 3]
def baseStart_3609764 : Nat := 118140960795 + 3609764 * 2 ^ 59
def prefixEnd_3609764 : Nat := 4983230072969 + 3 ^ 40 * 3609764 * 2
def baseEnd_3609764 : Nat := 1235695987531013343632669

theorem tailTrace_3609764 : CollatzResearch.WordTrace tailWord_3609764 prefixEnd_3609764 1235695987531013343632669 := by
  unfold tailWord_3609764
  simp only [CollatzResearch.WordTrace]
  refine ⟨65829454647224500727174173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87772606196299334302898897 65829454647224500727174173)
  ·
    refine ⟨24686045492709187772690315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65829454647224500727174173 24686045492709187772690315)
    ·
      refine ⟨37029068239063781659035473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24686045492709187772690315 37029068239063781659035473)
      ·
        refine ⟨27771801179297836244276605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37029068239063781659035473 27771801179297836244276605)
        ·
          refine ⟨10414425442236688591603727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27771801179297836244276605 10414425442236688591603727)
          ·
            refine ⟨15621638163355032887405591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10414425442236688591603727 15621638163355032887405591)
            ·
              refine ⟨23432457245032549331108387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15621638163355032887405591 23432457245032549331108387)
              ·
                refine ⟨35148685867548823996662581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23432457245032549331108387 35148685867548823996662581)
                ·
                  refine ⟨3295189300082702249687117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35148685867548823996662581 3295189300082702249687117)
                  ·
                    refine ⟨1235695987531013343632669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3295189300082702249687117 1235695987531013343632669)
                    ·
                      rfl

theorem cell22_3609764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 5, 3].length) (baseStart_3609764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3609764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3609764 prefixEnd_3609764 := by exact prefixLift 3609764
  have htrace : WordTrace (prefixWord ++ tailWord_3609764) baseStart_3609764 baseEnd_3609764 := by
    simpa [prefixWord, tailWord_3609764, baseEnd_3609764] using wordTrace_append hprefix tailTrace_3609764
  have hstable : (prefixWord ++ tailWord_3609764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609764).length < 2 ^ (prefixWord ++ tailWord_3609764).sum := by decide
  have hdescent : baseEnd_3609764 < baseStart_3609764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609807 : List Nat := [1, 1, 2, 1, 1, 3, 2, 4, 3, 4]
def baseStart_3609807 : Nat := 118140960795 + 3609807 * 2 ^ 59
def prefixEnd_3609807 : Nat := 4983230072969 + 3 ^ 40 * 3609807 * 2
def baseEnd_3609807 : Nat := 1235710707309775564807537

theorem tailTrace_3609807 : CollatzResearch.WordTrace tailWord_3609807 prefixEnd_3609807 1235710707309775564807537 := by
  unfold tailWord_3609807
  simp only [CollatzResearch.WordTrace]
  refine ⟨131660477633293219798163675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87773651755528813198775783 131660477633293219798163675)
  ·
    refine ⟨197490716449939829697245513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131660477633293219798163675 197490716449939829697245513)
    ·
      refine ⟨148118037337454872272934135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197490716449939829697245513 148118037337454872272934135)
      ·
        refine ⟨222177056006182308409401203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148118037337454872272934135 222177056006182308409401203)
        ·
          refine ⟨333265584009273462614101805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222177056006182308409401203 333265584009273462614101805)
          ·
            refine ⟨124974594003477548480288177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 333265584009273462614101805 124974594003477548480288177)
            ·
              refine ⟨93730945502608161360216133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124974594003477548480288177 93730945502608161360216133)
              ·
                refine ⟨17574552281739030255040525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93730945502608161360216133 17574552281739030255040525)
                ·
                  refine ⟨6590457105652136345640197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17574552281739030255040525 6590457105652136345640197)
                  ·
                    refine ⟨1235710707309775564807537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6590457105652136345640197 1235710707309775564807537)
                    ·
                      rfl

theorem cell22_3609807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 3, 4].length) (baseStart_3609807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3609807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3609807 prefixEnd_3609807 := by exact prefixLift 3609807
  have htrace : WordTrace (prefixWord ++ tailWord_3609807) baseStart_3609807 baseEnd_3609807 := by
    simpa [prefixWord, tailWord_3609807, baseEnd_3609807] using wordTrace_append hprefix tailTrace_3609807
  have hstable : (prefixWord ++ tailWord_3609807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609807).length < 2 ^ (prefixWord ++ tailWord_3609807).sum := by decide
  have hdescent : baseEnd_3609807 < baseStart_3609807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609824 : List Nat := [2, 1, 1, 3, 1, 4, 1, 4, 1, 4]
def baseStart_3609824 : Nat := 118140960795 + 3609824 * 2 ^ 59
def prefixEnd_3609824 : Nat := 4983230072969 + 3 ^ 40 * 3609824 * 2
def baseEnd_3609824 : Nat := 1235716526757193187132485

theorem tailTrace_3609824 : CollatzResearch.WordTrace tailWord_3609824 prefixEnd_3609824 1235716526757193187132485 := by
  unfold tailWord_3609824
  simp only [CollatzResearch.WordTrace]
  refine ⟨65830548837115815850766263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87774065116154421134355017 65830548837115815850766263)
  ·
    refine ⟨98745823255673723776149395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65830548837115815850766263 98745823255673723776149395)
    ·
      refine ⟨148118734883510585664224093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98745823255673723776149395 148118734883510585664224093)
      ·
        refine ⟨55544525581316469624084035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148118734883510585664224093 55544525581316469624084035)
        ·
          refine ⟨83316788371974704436126053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55544525581316469624084035 83316788371974704436126053)
          ·
            refine ⟨15621897819745257081773635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83316788371974704436126053 15621897819745257081773635)
            ·
              refine ⟨23432846729617885622660453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15621897819745257081773635 23432846729617885622660453)
              ·
                refine ⟨4393658761803353554248835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23432846729617885622660453 4393658761803353554248835)
                ·
                  refine ⟨6590488142705030331373253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4393658761803353554248835 6590488142705030331373253)
                  ·
                    refine ⟨1235716526757193187132485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6590488142705030331373253 1235716526757193187132485)
                    ·
                      rfl

theorem cell22_3609824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 4, 1, 4].length) (baseStart_3609824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3609824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3609824 prefixEnd_3609824 := by exact prefixLift 3609824
  have htrace : WordTrace (prefixWord ++ tailWord_3609824) baseStart_3609824 baseEnd_3609824 := by
    simpa [prefixWord, tailWord_3609824, baseEnd_3609824] using wordTrace_append hprefix tailTrace_3609824
  have hstable : (prefixWord ++ tailWord_3609824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609824).length < 2 ^ (prefixWord ++ tailWord_3609824).sum := by decide
  have hdescent : baseEnd_3609824 < baseStart_3609824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609867 : List Nat := [1, 1, 1, 1, 5, 3, 1, 9]
def baseStart_3609867 : Nat := 118140960795 + 3609867 * 2 ^ 59
def prefixEnd_3609867 : Nat := 4983230072969 + 3 ^ 40 * 3609867 * 2
def baseEnd_3609867 : Nat := 137303471837328378700817

theorem tailTrace_3609867 : CollatzResearch.WordTrace tailWord_3609867 prefixEnd_3609867 137303471837328378700817 := by
  unfold tailWord_3609867
  simp only [CollatzResearch.WordTrace]
  refine ⟨131662666013075850045347855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87775110675383900030231903 131662666013075850045347855)
  ·
    refine ⟨197493999019613775068021783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131662666013075850045347855 197493999019613775068021783)
    ·
      refine ⟨296240998529420662602032675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197493999019613775068021783 296240998529420662602032675)
      ·
        refine ⟨444361497794130993903049013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296240998529420662602032675 444361497794130993903049013)
        ·
          refine ⟨41658890418199780678410845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 444361497794130993903049013 41658890418199780678410845)
          ·
            refine ⟨15622083906824917754404067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41658890418199780678410845 15622083906824917754404067)
            ·
              refine ⟨23433125860237376631606101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15622083906824917754404067 23433125860237376631606101)
              ·
                refine ⟨137303471837328378700817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23433125860237376631606101 137303471837328378700817)
                ·
                  rfl

theorem cell22_3609867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 9].length) (baseStart_3609867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3609867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3609867 prefixEnd_3609867 := by exact prefixLift 3609867
  have htrace : WordTrace (prefixWord ++ tailWord_3609867) baseStart_3609867 baseEnd_3609867 := by
    simpa [prefixWord, tailWord_3609867, baseEnd_3609867] using wordTrace_append hprefix tailTrace_3609867
  have hstable : (prefixWord ++ tailWord_3609867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609867).length < 2 ^ (prefixWord ++ tailWord_3609867).sum := by decide
  have hdescent : baseEnd_3609867 < baseStart_3609867 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609929 : List Nat := [1, 2, 1, 1, 2, 3, 4, 3, 5]
def baseStart_3609929 : Nat := 118140960795 + 3609929 * 2 ^ 59
def prefixEnd_3609929 : Nat := 4983230072969 + 3 ^ 40 * 3609929 * 2
def baseEnd_3609929 : Nat := 411917490134335971085721

theorem tailTrace_3609929 : CollatzResearch.WordTrace tailWord_3609929 prefixEnd_3609929 411917490134335971085721 := by
  unfold tailWord_3609929
  simp only [CollatzResearch.WordTrace]
  refine ⟨131664927338851234634104841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87776618225900823089403227 131664927338851234634104841)
  ·
    refine ⟨98748695504138425975578631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131664927338851234634104841 98748695504138425975578631)
    ·
      refine ⟨148123043256207638963367947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98748695504138425975578631 148123043256207638963367947)
      ·
        refine ⟨222184564884311458445051921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148123043256207638963367947 222184564884311458445051921)
        ·
          refine ⟨166638423663233593833788941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222184564884311458445051921 166638423663233593833788941)
          ·
            refine ⟨62489408873712597687670853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166638423663233593833788941 62489408873712597687670853)
            ·
              refine ⟨11716764163821112066438285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62489408873712597687670853 11716764163821112066438285)
              ·
                refine ⟨4393786561432917024914357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11716764163821112066438285 4393786561432917024914357)
                ·
                  refine ⟨411917490134335971085721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4393786561432917024914357 411917490134335971085721)
                  ·
                    rfl

theorem cell22_3609929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 3, 5].length) (baseStart_3609929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3609929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3609929 prefixEnd_3609929 := by exact prefixLift 3609929
  have htrace : WordTrace (prefixWord ++ tailWord_3609929) baseStart_3609929 baseEnd_3609929 := by
    simpa [prefixWord, tailWord_3609929, baseEnd_3609929] using wordTrace_append hprefix tailTrace_3609929
  have hstable : (prefixWord ++ tailWord_3609929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609929).length < 2 ^ (prefixWord ++ tailWord_3609929).sum := by decide
  have hdescent : baseEnd_3609929 < baseStart_3609929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609993 : List Nat := [1, 2, 1, 1, 7, 1, 2, 2, 1, 4]
def baseStart_3609993 : Nat := 118140960795 + 3609993 * 2 ^ 59
def prefixEnd_3609993 : Nat := 4983230072969 + 3 ^ 40 * 3609993 * 2
def baseEnd_3609993 : Nat := 1235774378910933079656967

theorem tailTrace_3609993 : CollatzResearch.WordTrace tailWord_3609993 prefixEnd_3609993 1235774378910933079656967 := by
  unfold tailWord_3609993
  simp only [CollatzResearch.WordTrace]
  refine ⟨131667261610619373564434633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87778174407079582376289755 131667261610619373564434633)
  ·
    refine ⟨98750446207964530173325975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131667261610619373564434633 98750446207964530173325975)
    ·
      refine ⟨148125669311946795259988963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98750446207964530173325975 148125669311946795259988963)
      ·
        refine ⟨222188503967920192889983445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148125669311946795259988963 222188503967920192889983445)
        ·
          refine ⟨5207543061748129520858987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 222188503967920192889983445 5207543061748129520858987)
          ·
            refine ⟨7811314592622194281288481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5207543061748129520858987 7811314592622194281288481)
            ·
              refine ⟨5858485944466645710966361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7811314592622194281288481 5858485944466645710966361)
              ·
                refine ⟨4393864458349984283224771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5858485944466645710966361 4393864458349984283224771)
                ·
                  refine ⟨6590796687524976424837157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4393864458349984283224771 6590796687524976424837157)
                  ·
                    refine ⟨1235774378910933079656967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6590796687524976424837157 1235774378910933079656967)
                    ·
                      rfl

theorem cell22_3609993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 2, 1, 4].length) (baseStart_3609993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3609993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3609993 prefixEnd_3609993 := by exact prefixLift 3609993
  have htrace : WordTrace (prefixWord ++ tailWord_3609993) baseStart_3609993 baseEnd_3609993 := by
    simpa [prefixWord, tailWord_3609993, baseEnd_3609993] using wordTrace_append hprefix tailTrace_3609993
  have hstable : (prefixWord ++ tailWord_3609993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609993).length < 2 ^ (prefixWord ++ tailWord_3609993).sum := by decide
  have hdescent : baseEnd_3609993 < baseStart_3609993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610023 : List Nat := [1, 1, 6, 1, 1, 1, 2, 4, 2, 3]
def baseStart_3610023 : Nat := 118140960795 + 3610023 * 2 ^ 59
def prefixEnd_3610023 : Nat := 4983230072969 + 3 ^ 40 * 3610023 * 2
def baseEnd_3610023 : Nat := 1235784648524023001406875

theorem tailTrace_3610023 : CollatzResearch.WordTrace tailWord_3610023 prefixEnd_3610023 1235784648524023001406875 := by
  unfold tailWord_3610023
  simp only [CollatzResearch.WordTrace]
  refine ⟨131668355800510688688026723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87778903867007125792017815 131668355800510688688026723)
  ·
    refine ⟨197502533700766033032040085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131668355800510688688026723 197502533700766033032040085)
    ·
      refine ⟨9257931267223407798376879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 197502533700766033032040085 9257931267223407798376879)
      ·
        refine ⟨13886896900835111697565319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9257931267223407798376879 13886896900835111697565319)
        ·
          refine ⟨20830345351252667546347979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13886896900835111697565319 20830345351252667546347979)
          ·
            refine ⟨31245518026879001319521969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20830345351252667546347979 31245518026879001319521969)
            ·
              refine ⟨23434138520159250989641477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31245518026879001319521969 23434138520159250989641477)
              ·
                refine ⟨4393900972529859560557777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23434138520159250989641477 4393900972529859560557777)
                ·
                  refine ⟨3295425729397394670418333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4393900972529859560557777 3295425729397394670418333)
                  ·
                    refine ⟨1235784648524023001406875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3295425729397394670418333 1235784648524023001406875)
                    ·
                      rfl

theorem cell22_3610023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_3610023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3610023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3610023 prefixEnd_3610023 := by exact prefixLift 3610023
  have htrace : WordTrace (prefixWord ++ tailWord_3610023) baseStart_3610023 baseEnd_3610023 := by
    simpa [prefixWord, tailWord_3610023, baseEnd_3610023] using wordTrace_append hprefix tailTrace_3610023
  have hstable : (prefixWord ++ tailWord_3610023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610023).length < 2 ^ (prefixWord ++ tailWord_3610023).sum := by decide
  have hdescent : baseEnd_3610023 < baseStart_3610023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610034 : List Nat := [3, 2, 1, 1, 1, 1, 2, 2, 2, 7]
def baseStart_3610034 : Nat := 118140960795 + 3610034 * 2 ^ 59
def prefixEnd_3610034 : Nat := 4983230072969 + 3 ^ 40 * 3610034 * 2
def baseEnd_3610034 : Nat := 1235788414048822639381841

theorem tailTrace_3610034 : CollatzResearch.WordTrace tailWord_3610034 prefixEnd_3610034 1235788414048822639381841 := by
  unfold tailWord_3610034
  simp only [CollatzResearch.WordTrace]
  refine ⟨32917189250867709391669289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87779171335647225044451437 32917189250867709391669289)
  ·
    refine ⟨24687891938150782043751967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32917189250867709391669289 24687891938150782043751967)
    ·
      refine ⟨37031837907226173065627951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24687891938150782043751967 37031837907226173065627951)
      ·
        refine ⟨55547756860839259598441927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37031837907226173065627951 55547756860839259598441927)
        ·
          refine ⟨83321635291258889397662891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55547756860839259598441927 83321635291258889397662891)
          ·
            refine ⟨124982452936888334096494337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83321635291258889397662891 124982452936888334096494337)
            ·
              refine ⟨93736839702666250572370753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124982452936888334096494337 93736839702666250572370753)
              ·
                refine ⟨70302629776999687929278065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93736839702666250572370753 70302629776999687929278065)
                ·
                  refine ⟨52726972332749765946958549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70302629776999687929278065 52726972332749765946958549)
                  ·
                    refine ⟨1235788414048822639381841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52726972332749765946958549 1235788414048822639381841)
                    ·
                      rfl

theorem cell22_3610034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_3610034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3610034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3610034 prefixEnd_3610034 := by exact prefixLift 3610034
  have htrace : WordTrace (prefixWord ++ tailWord_3610034) baseStart_3610034 baseEnd_3610034 := by
    simpa [prefixWord, tailWord_3610034, baseEnd_3610034] using wordTrace_append hprefix tailTrace_3610034
  have hstable : (prefixWord ++ tailWord_3610034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610034).length < 2 ^ (prefixWord ++ tailWord_3610034).sum := by decide
  have hdescent : baseEnd_3610034 < baseStart_3610034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610051 : List Nat := [1, 1, 1, 3, 1, 1, 4, 4, 3, 3]
def baseStart_3610051 : Nat := 118140960795 + 3610051 * 2 ^ 59
def prefixEnd_3610051 : Nat := 4983230072969 + 3 ^ 40 * 3610051 * 2
def baseEnd_3610051 : Nat := 1235794233496240261706789

theorem tailTrace_3610051 : CollatzResearch.WordTrace tailWord_3610051 prefixEnd_3610051 1235794233496240261706789 := by
  unfold tailWord_3610051
  simp only [CollatzResearch.WordTrace]
  refine ⟨131669377044409249470046007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87779584696272832980030671 131669377044409249470046007)
  ·
    refine ⟨197504065566613874205069011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131669377044409249470046007 197504065566613874205069011)
    ·
      refine ⟨296256098349920811307603517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197504065566613874205069011 296256098349920811307603517)
      ·
        refine ⟨111096036881220304240351319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 296256098349920811307603517 111096036881220304240351319)
        ·
          refine ⟨166644055321830456360526979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111096036881220304240351319 166644055321830456360526979)
          ·
            refine ⟨249966082982745684540790469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166644055321830456360526979 249966082982745684540790469)
            ·
              refine ⟨46868640559264815851398213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 249966082982745684540790469 46868640559264815851398213)
              ·
                refine ⟨8787870104862152972137165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46868640559264815851398213 8787870104862152972137165)
                ·
                  refine ⟨3295451289323307364551437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8787870104862152972137165 3295451289323307364551437)
                  ·
                    refine ⟨1235794233496240261706789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3295451289323307364551437 1235794233496240261706789)
                    ·
                      rfl

theorem cell22_3610051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 4, 3, 3].length) (baseStart_3610051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3610051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3610051 prefixEnd_3610051 := by exact prefixLift 3610051
  have htrace : WordTrace (prefixWord ++ tailWord_3610051) baseStart_3610051 baseEnd_3610051 := by
    simpa [prefixWord, tailWord_3610051, baseEnd_3610051] using wordTrace_append hprefix tailTrace_3610051
  have hstable : (prefixWord ++ tailWord_3610051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610051).length < 2 ^ (prefixWord ++ tailWord_3610051).sum := by decide
  have hdescent : baseEnd_3610051 < baseStart_3610051 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610081 : List Nat := [1, 2, 3, 1, 2, 3, 1, 4, 5]
def baseStart_3610081 : Nat := 118140960795 + 3610081 * 2 ^ 59
def prefixEnd_3610081 : Nat := 4983230072969 + 3 ^ 40 * 3610081 * 2
def baseEnd_3610081 : Nat := 411934834369776727818899

theorem tailTrace_3610081 : CollatzResearch.WordTrace tailWord_3610081 prefixEnd_3610081 411934834369776727818899 := by
  unfold tailWord_3610081
  simp only [CollatzResearch.WordTrace]
  refine ⟨131670471234300564593638097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87780314156200376395758731 131670471234300564593638097)
  ·
    refine ⟨98752853425725423445228573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131670471234300564593638097 98752853425725423445228573)
    ·
      refine ⟨37032320034647033791960715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98752853425725423445228573 37032320034647033791960715)
      ·
        refine ⟨55548480051970550687941073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37032320034647033791960715 55548480051970550687941073)
        ·
          refine ⟨41661360038977913015955805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55548480051970550687941073 41661360038977913015955805)
          ·
            refine ⟨15623010014616717380983427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41661360038977913015955805 15623010014616717380983427)
            ·
              refine ⟨23434515021925076071475141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15623010014616717380983427 23434515021925076071475141)
              ·
                refine ⟨4393971566610951763401589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23434515021925076071475141 4393971566610951763401589)
                ·
                  refine ⟨411934834369776727818899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4393971566610951763401589 411934834369776727818899)
                  ·
                    rfl

theorem cell22_3610081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 4, 5].length) (baseStart_3610081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3610081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3610081 prefixEnd_3610081 := by exact prefixLift 3610081
  have htrace : WordTrace (prefixWord ++ tailWord_3610081) baseStart_3610081 baseEnd_3610081 := by
    simpa [prefixWord, tailWord_3610081, baseEnd_3610081] using wordTrace_append hprefix tailTrace_3610081
  have hstable : (prefixWord ++ tailWord_3610081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610081).length < 2 ^ (prefixWord ++ tailWord_3610081).sum := by decide
  have hdescent : baseEnd_3610081 < baseStart_3610081 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610096 : List Nat := [2, 1, 1, 1, 3, 5, 1, 1, 2, 5]
def baseStart_3610096 : Nat := 118140960795 + 3610096 * 2 ^ 59
def prefixEnd_3610096 : Nat := 4983230072969 + 3 ^ 40 * 3610096 * 2
def baseEnd_3610096 : Nat := 1235809637915875144331651

theorem tailTrace_3610096 : CollatzResearch.WordTrace tailWord_3610096 prefixEnd_3610096 1235809637915875144331651 := by
  unfold tailWord_3610096
  simp only [CollatzResearch.WordTrace]
  refine ⟨65835509164623111077717071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87780678886164148103622761 65835509164623111077717071)
  ·
    refine ⟨98753263746934666616575607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65835509164623111077717071 98753263746934666616575607)
    ·
      refine ⟨148129895620401999924863411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98753263746934666616575607 148129895620401999924863411)
      ·
        refine ⟨222194843430602999887295117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148129895620401999924863411 222194843430602999887295117)
        ·
          refine ⟨83323066286476124957735669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 222194843430602999887295117 83323066286476124957735669)
          ·
            refine ⟨7811537464357136714787719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 83323066286476124957735669 7811537464357136714787719)
            ·
              refine ⟨11717306196535705072181579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7811537464357136714787719 11717306196535705072181579)
              ·
                refine ⟨17575959294803557608272369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11717306196535705072181579 17575959294803557608272369)
                ·
                  refine ⟨13181969471102668206204277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17575959294803557608272369 13181969471102668206204277)
                  ·
                    refine ⟨1235809637915875144331651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13181969471102668206204277 1235809637915875144331651)
                    ·
                      rfl

theorem cell22_3610096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 2, 5].length) (baseStart_3610096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3610096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3610096 prefixEnd_3610096 := by exact prefixLift 3610096
  have htrace : WordTrace (prefixWord ++ tailWord_3610096) baseStart_3610096 baseEnd_3610096 := by
    simpa [prefixWord, tailWord_3610096, baseEnd_3610096] using wordTrace_append hprefix tailTrace_3610096
  have hstable : (prefixWord ++ tailWord_3610096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610096).length < 2 ^ (prefixWord ++ tailWord_3610096).sum := by decide
  have hdescent : baseEnd_3610096 < baseStart_3610096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610098 : List Nat := [3, 2, 1, 4, 1, 1, 2, 3, 5]
def baseStart_3610098 : Nat := 118140960795 + 3610098 * 2 ^ 59
def prefixEnd_3610098 : Nat := 4983230072969 + 3 ^ 40 * 3610098 * 2
def baseEnd_3610098 : Nat := 411936774185582601927215

theorem tailTrace_3610098 : CollatzResearch.WordTrace tailWord_3610098 prefixEnd_3610098 411936774185582601927215 := by
  unfold tailWord_3610098
  simp only [CollatzResearch.WordTrace]
  refine ⟨32917772818809744124251737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87780727516825984331337965 32917772818809744124251737)
  ·
    refine ⟨24688329614107308093188803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32917772818809744124251737 24688329614107308093188803)
    ·
      refine ⟨37032494421160962139783205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24688329614107308093188803 37032494421160962139783205)
      ·
        refine ⟨6943592703967680401209351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37032494421160962139783205 6943592703967680401209351)
        ·
          refine ⟨10415389055951520601814027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6943592703967680401209351 10415389055951520601814027)
          ·
            refine ⟨15623083583927280902721041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10415389055951520601814027 15623083583927280902721041)
            ·
              refine ⟨11717312687945460677040781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15623083583927280902721041 11717312687945460677040781)
              ·
                refine ⟨4393992257979547753890293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11717312687945460677040781 4393992257979547753890293)
                ·
                  refine ⟨411936774185582601927215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4393992257979547753890293 411936774185582601927215)
                  ·
                    rfl

theorem cell22_3610098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 3, 5].length) (baseStart_3610098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3610098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3610098 prefixEnd_3610098 := by exact prefixLift 3610098
  have htrace : WordTrace (prefixWord ++ tailWord_3610098) baseStart_3610098 baseEnd_3610098 := by
    simpa [prefixWord, tailWord_3610098, baseEnd_3610098] using wordTrace_append hprefix tailTrace_3610098
  have hstable : (prefixWord ++ tailWord_3610098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610098).length < 2 ^ (prefixWord ++ tailWord_3610098).sum := by decide
  have hdescent : baseEnd_3610098 < baseStart_3610098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610132 : List Nat := [2, 4, 3, 1, 2, 2, 1, 2, 5]
def baseStart_3610132 : Nat := 118140960795 + 3610132 * 2 ^ 59
def prefixEnd_3610132 : Nat := 4983230072969 + 3 ^ 40 * 3610132 * 2
def baseEnd_3610132 : Nat := 411940653817194350143847

theorem tailTrace_3610132 : CollatzResearch.WordTrace tailWord_3610132 prefixEnd_3610132 411940653817194350143847 := by
  unfold tailWord_3610132
  simp only [CollatzResearch.WordTrace]
  refine ⟨65836165678557900151872325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87781554238077200202496433 65836165678557900151872325)
  ·
    refine ⟨12344281064729606278476061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65836165678557900151872325 12344281064729606278476061)
    ·
      refine ⟨4629105399273602354428523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12344281064729606278476061 4629105399273602354428523)
      ·
        refine ⟨6943658098910403531642785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4629105399273602354428523 6943658098910403531642785)
        ·
          refine ⟨5207743574182802648732089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6943658098910403531642785 5207743574182802648732089)
          ·
            refine ⟨3905807680637101986549067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5207743574182802648732089 3905807680637101986549067)
            ·
              refine ⟨5858711520955652979823601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3905807680637101986549067 5858711520955652979823601)
              ·
                refine ⟨4394033640716739734867701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5858711520955652979823601 4394033640716739734867701)
                ·
                  refine ⟨411940653817194350143847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4394033640716739734867701 411940653817194350143847)
                  ·
                    rfl

theorem cell22_3610132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 2, 5].length) (baseStart_3610132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3610132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3610132 prefixEnd_3610132 := by exact prefixLift 3610132
  have htrace : WordTrace (prefixWord ++ tailWord_3610132) baseStart_3610132 baseEnd_3610132 := by
    simpa [prefixWord, tailWord_3610132, baseEnd_3610132] using wordTrace_append hprefix tailTrace_3610132
  have hstable : (prefixWord ++ tailWord_3610132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610132).length < 2 ^ (prefixWord ++ tailWord_3610132).sum := by decide
  have hdescent : baseEnd_3610132 < baseStart_3610132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610143 : List Nat := [1, 1, 2, 4, 1, 1, 4, 4, 4]
def baseStart_3610143 : Nat := 118140960795 + 3610143 * 2 ^ 59
def prefixEnd_3610143 : Nat := 4983230072969 + 3 ^ 40 * 3610143 * 2
def baseEnd_3610143 : Nat := 411941908992127562802169

theorem tailTrace_3610143 : CollatzResearch.WordTrace tailWord_3610143 prefixEnd_3610143 411941908992127562802169 := by
  unfold tailWord_3610143
  simp only [CollatzResearch.WordTrace]
  refine ⟨131672732560075949182395083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87781821706717299454930055 131672732560075949182395083)
  ·
    refine ⟨197509098840113923773592625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131672732560075949182395083 197509098840113923773592625)
    ·
      refine ⟨148131824130085442830194469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197509098840113923773592625 148131824130085442830194469)
      ·
        refine ⟨27774717024391020530661463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148131824130085442830194469 27774717024391020530661463)
        ·
          refine ⟨41662075536586530795992195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27774717024391020530661463 41662075536586530795992195)
          ·
            refine ⟨62493113304879796193988293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41662075536586530795992195 62493113304879796193988293)
            ·
              refine ⟨11717458744664961786372805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62493113304879796193988293 11717458744664961786372805)
              ·
                refine ⟨2197023514624680334944901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11717458744664961786372805 2197023514624680334944901)
                ·
                  refine ⟨411941908992127562802169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2197023514624680334944901 411941908992127562802169)
                  ·
                    rfl

theorem cell22_3610143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 4, 4].length) (baseStart_3610143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3610143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3610143 prefixEnd_3610143 := by exact prefixLift 3610143
  have htrace : WordTrace (prefixWord ++ tailWord_3610143) baseStart_3610143 baseEnd_3610143 := by
    simpa [prefixWord, tailWord_3610143, baseEnd_3610143] using wordTrace_append hprefix tailTrace_3610143
  have hstable : (prefixWord ++ tailWord_3610143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610143).length < 2 ^ (prefixWord ++ tailWord_3610143).sum := by decide
  have hdescent : baseEnd_3610143 < baseStart_3610143 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610231 : List Nat := [1, 1, 3, 1, 1, 3, 1, 2, 4, 5]
def baseStart_3610231 : Nat := 118140960795 + 3610231 * 2 ^ 59
def prefixEnd_3610231 : Nat := 4983230072969 + 3 ^ 40 * 3610231 * 2
def baseEnd_3610231 : Nat := 1235855851174779792206237

theorem tailTrace_3610231 : CollatzResearch.WordTrace tailWord_3610231 prefixEnd_3610231 1235855851174779792206237 := by
  unfold tailWord_3610231
  simp only [CollatzResearch.WordTrace]
  refine ⟨131675942183757140211598547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87783961455838093474399031 131675942183757140211598547)
  ·
    refine ⟨197513913275635710317397821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131675942183757140211598547 197513913275635710317397821)
    ·
      refine ⟨74067717478363391369024183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197513913275635710317397821 74067717478363391369024183)
      ·
        refine ⟨111101576217545087053536275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74067717478363391369024183 111101576217545087053536275)
        ·
          refine ⟨166652364326317630580304413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111101576217545087053536275 166652364326317630580304413)
          ·
            refine ⟨62494636622369111467614155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166652364326317630580304413 62494636622369111467614155)
            ·
              refine ⟨93741954933553667201421233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62494636622369111467614155 93741954933553667201421233)
              ·
                refine ⟨70306466200165250401065925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93741954933553667201421233 70306466200165250401065925)
                ·
                  refine ⟨13182462412530984450199861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70306466200165250401065925 13182462412530984450199861)
                  ·
                    refine ⟨1235855851174779792206237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13182462412530984450199861 1235855851174779792206237)
                    ·
                      rfl

theorem cell22_3610231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 4, 5].length) (baseStart_3610231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3610231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3610231 prefixEnd_3610231 := by exact prefixLift 3610231
  have htrace : WordTrace (prefixWord ++ tailWord_3610231) baseStart_3610231 baseEnd_3610231 := by
    simpa [prefixWord, tailWord_3610231, baseEnd_3610231] using wordTrace_append hprefix tailTrace_3610231
  have hstable : (prefixWord ++ tailWord_3610231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610231).length < 2 ^ (prefixWord ++ tailWord_3610231).sum := by decide
  have hdescent : baseEnd_3610231 < baseStart_3610231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610250 : List Nat := [3, 1, 2, 3, 2, 2, 2, 2, 5]
def baseStart_3610250 : Nat := 118140960795 + 3610250 * 2 ^ 59
def prefixEnd_3610250 : Nat := 4983230072969 + 3 ^ 40 * 3610250 * 2
def baseEnd_3610250 : Nat := 411954118421023358660393

theorem tailTrace_3610250 : CollatzResearch.WordTrace tailWord_3610250 prefixEnd_3610250 411954118421023358660393 := by
  unfold tailWord_3610250
  simp only [CollatzResearch.WordTrace]
  refine ⟨32919158792672076614135051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87784423447125537637693469 32919158792672076614135051)
  ·
    refine ⟨49378738189008114921202577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32919158792672076614135051 49378738189008114921202577)
    ·
      refine ⟨37034053641756086190901933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49378738189008114921202577 37034053641756086190901933)
      ·
        refine ⟨13887770115658532321588225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37034053641756086190901933 13887770115658532321588225)
        ·
          refine ⟨10415827586743899241191169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13887770115658532321588225 10415827586743899241191169)
          ·
            refine ⟨7811870690057924430893377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10415827586743899241191169 7811870690057924430893377)
            ·
              refine ⟨5858903017543443323170033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7811870690057924430893377 5858903017543443323170033)
              ·
                refine ⟨4394177263157582492377525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5858903017543443323170033 4394177263157582492377525)
                ·
                  refine ⟨411954118421023358660393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4394177263157582492377525 411954118421023358660393)
                  ·
                    rfl

theorem cell22_3610250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 2, 5].length) (baseStart_3610250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3610250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3610250 prefixEnd_3610250 := by exact prefixLift 3610250
  have htrace : WordTrace (prefixWord ++ tailWord_3610250) baseStart_3610250 baseEnd_3610250 := by
    simpa [prefixWord, tailWord_3610250, baseEnd_3610250] using wordTrace_append hprefix tailTrace_3610250
  have hstable : (prefixWord ++ tailWord_3610250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610250).length < 2 ^ (prefixWord ++ tailWord_3610250).sum := by decide
  have hdescent : baseEnd_3610250 < baseStart_3610250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610254 : List Nat := [4, 1, 1, 3, 1, 2, 4, 2, 1, 3]
def baseStart_3610254 : Nat := 118140960795 + 3610254 * 2 ^ 59
def prefixEnd_3610254 : Nat := 4983230072969 + 3 ^ 40 * 3610254 * 2
def baseEnd_3610254 : Nat := 1235863724544815398881167

theorem tailTrace_3610254 : CollatzResearch.WordTrace tailWord_3610254 prefixEnd_3610254 1235863724544815398881167 := by
  unfold tailWord_3610254
  simp only [CollatzResearch.WordTrace]
  refine ⟨16459597632834226892460727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87784520708449210093123877 16459597632834226892460727)
  ·
    refine ⟨24689396449251340338691091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16459597632834226892460727 24689396449251340338691091)
    ·
      refine ⟨37034094673877010508036637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24689396449251340338691091 37034094673877010508036637)
      ·
        refine ⟨13887785502703878940513739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37034094673877010508036637 13887785502703878940513739)
        ·
          refine ⟨20831678254055818410770609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13887785502703878940513739 20831678254055818410770609)
          ·
            refine ⟨15623758690541863808077957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20831678254055818410770609 15623758690541863808077957)
            ·
              refine ⟨2929454754476599464014617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15623758690541863808077957 2929454754476599464014617)
              ·
                refine ⟨2197091065857449598010963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2929454754476599464014617 2197091065857449598010963)
                ·
                  refine ⟨3295636598786174397016445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2197091065857449598010963 3295636598786174397016445)
                  ·
                    refine ⟨1235863724544815398881167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3295636598786174397016445 1235863724544815398881167)
                    ·
                      rfl

theorem cell22_3610254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 4, 2, 1, 3].length) (baseStart_3610254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3610254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3610254 prefixEnd_3610254 := by exact prefixLift 3610254
  have htrace : WordTrace (prefixWord ++ tailWord_3610254) baseStart_3610254 baseEnd_3610254 := by
    simpa [prefixWord, tailWord_3610254, baseEnd_3610254] using wordTrace_append hprefix tailTrace_3610254
  have hstable : (prefixWord ++ tailWord_3610254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610254).length < 2 ^ (prefixWord ++ tailWord_3610254).sum := by decide
  have hdescent : baseEnd_3610254 < baseStart_3610254 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610261 : List Nat := [1, 3, 2, 1, 1, 1, 1, 2, 10]
def baseStart_3610261 : Nat := 118140960795 + 3610261 * 2 ^ 59
def prefixEnd_3610261 : Nat := 4983230072969 + 3 ^ 40 * 3610261 * 2
def baseEnd_3610261 : Nat := 411955373595956571318715

theorem tailTrace_3610261 : CollatzResearch.WordTrace tailWord_3610261 prefixEnd_3610261 411955373595956571318715 := by
  unfold tailWord_3610261
  simp only [CollatzResearch.WordTrace]
  refine ⟨131677036373648455335190637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87784690915765636890127091 131677036373648455335190637)
  ·
    refine ⟨49378888640118170750696489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131677036373648455335190637 49378888640118170750696489)
    ·
      refine ⟨37034166480088628063022367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49378888640118170750696489 37034166480088628063022367)
      ·
        refine ⟨55551249720132942094533551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37034166480088628063022367 55551249720132942094533551)
        ·
          refine ⟨83326874580199413141800327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55551249720132942094533551 83326874580199413141800327)
          ·
            refine ⟨124990311870299119712700491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83326874580199413141800327 124990311870299119712700491)
            ·
              refine ⟨187485467805448679569050737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124990311870299119712700491 187485467805448679569050737)
              ·
                refine ⟨140614100854086509676788053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 187485467805448679569050737 140614100854086509676788053)
                ·
                  refine ⟨411955373595956571318715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 140614100854086509676788053 411955373595956571318715)
                  ·
                    rfl

theorem cell22_3610261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 10].length) (baseStart_3610261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3610261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3610261 prefixEnd_3610261 := by exact prefixLift 3610261
  have htrace : WordTrace (prefixWord ++ tailWord_3610261) baseStart_3610261 baseEnd_3610261 := by
    simpa [prefixWord, tailWord_3610261, baseEnd_3610261] using wordTrace_append hprefix tailTrace_3610261
  have hstable : (prefixWord ++ tailWord_3610261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610261).length < 2 ^ (prefixWord ++ tailWord_3610261).sum := by decide
  have hdescent : baseEnd_3610261 < baseStart_3610261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610263 : List Nat := [1, 1, 3, 3, 2, 2, 1, 2, 3, 4]
def baseStart_3610263 : Nat := 118140960795 + 3610263 * 2 ^ 59
def prefixEnd_3610263 : Nat := 4983230072969 + 3 ^ 40 * 3610263 * 2
def baseEnd_3610263 : Nat := 1235866805428742375406139

theorem tailTrace_3610263 : CollatzResearch.WordTrace tailWord_3610263 prefixEnd_3610263 1235866805428742375406139 := by
  unfold tailWord_3610263
  simp only [CollatzResearch.WordTrace]
  refine ⟨131677109319641209676763443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87784739546427473117842295 131677109319641209676763443)
  ·
    refine ⟨197515663979461814515145165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131677109319641209676763443 197515663979461814515145165)
    ·
      refine ⟨74068373992298180443179437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197515663979461814515145165 74068373992298180443179437)
      ·
        refine ⟨27775640247111817666192289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74068373992298180443179437 27775640247111817666192289)
        ·
          refine ⟨20831730185333863249644217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27775640247111817666192289 20831730185333863249644217)
          ·
            refine ⟨15623797639000397437233163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20831730185333863249644217 15623797639000397437233163)
            ·
              refine ⟨23435696458500596155849745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15623797639000397437233163 23435696458500596155849745)
              ·
                refine ⟨17576772343875447116887309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23435696458500596155849745 17576772343875447116887309)
                ·
                  refine ⟨6591289628953292668832741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17576772343875447116887309 6591289628953292668832741)
                  ·
                    refine ⟨1235866805428742375406139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6591289628953292668832741 1235866805428742375406139)
                    ·
                      rfl

theorem cell22_3610263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 3, 4].length) (baseStart_3610263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3610263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3610263 prefixEnd_3610263 := by exact prefixLift 3610263
  have htrace : WordTrace (prefixWord ++ tailWord_3610263) baseStart_3610263 baseEnd_3610263 := by
    simpa [prefixWord, tailWord_3610263, baseEnd_3610263] using wordTrace_append hprefix tailTrace_3610263
  have hstable : (prefixWord ++ tailWord_3610263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610263).length < 2 ^ (prefixWord ++ tailWord_3610263).sum := by decide
  have hdescent : baseEnd_3610263 < baseStart_3610263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610295 : List Nat := [1, 1, 3, 1, 5, 1, 1, 5, 4]
def baseStart_3610295 : Nat := 118140960795 + 3610295 * 2 ^ 59
def prefixEnd_3610295 : Nat := 4983230072969 + 3 ^ 40 * 3610295 * 2
def baseEnd_3610295 : Nat := 411959253227568319535347

theorem tailTrace_3610295 : CollatzResearch.WordTrace tailWord_3610295 prefixEnd_3610295 411959253227568319535347 := by
  unfold tailWord_3610295
  simp only [CollatzResearch.WordTrace]
  refine ⟨131678276455525279141928339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87785517637016852761285559 131678276455525279141928339)
  ·
    refine ⟨197517414683287918712892509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131678276455525279141928339 197517414683287918712892509)
    ·
      refine ⟨74069030506232969517334691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197517414683287918712892509 74069030506232969517334691)
      ·
        refine ⟨111103545759349454276002037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74069030506232969517334691 111103545759349454276002037)
        ·
          refine ⟨10415957414939011338375191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 111103545759349454276002037 10415957414939011338375191)
          ·
            refine ⟨15623936122408517007562787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10415957414939011338375191 15623936122408517007562787)
            ·
              refine ⟨23435904183612775511344181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15623936122408517007562787 23435904183612775511344181)
              ·
                refine ⟨2197116017213697704188517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23435904183612775511344181 2197116017213697704188517)
                ·
                  refine ⟨411959253227568319535347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2197116017213697704188517 411959253227568319535347)
                  ·
                    rfl

theorem cell22_3610295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 5, 4].length) (baseStart_3610295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3610295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3610295 prefixEnd_3610295 := by exact prefixLift 3610295
  have htrace : WordTrace (prefixWord ++ tailWord_3610295) baseStart_3610295 baseEnd_3610295 := by
    simpa [prefixWord, tailWord_3610295, baseEnd_3610295] using wordTrace_append hprefix tailTrace_3610295
  have hstable : (prefixWord ++ tailWord_3610295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610295).length < 2 ^ (prefixWord ++ tailWord_3610295).sum := by decide
  have hdescent : baseEnd_3610295 < baseStart_3610295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610327 : List Nat := [1, 1, 3, 2, 1, 3, 5, 1, 2, 3]
def baseStart_3610327 : Nat := 118140960795 + 3610327 * 2 ^ 59
def prefixEnd_3610327 : Nat := 4983230072969 + 3 ^ 40 * 3610327 * 2
def baseEnd_3610327 : Nat := 1235888713936667541805943

theorem tailTrace_3610327 : CollatzResearch.WordTrace tailWord_3610327 prefixEnd_3610327 1235888713936667541805943 := by
  unfold tailWord_3610327
  simp only [CollatzResearch.WordTrace]
  refine ⟨131679443591409348607093235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87786295727606232404728823 131679443591409348607093235)
  ·
    refine ⟨197519165387114022910639853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131679443591409348607093235 197519165387114022910639853)
    ·
      refine ⟨74069687020167758591489945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197519165387114022910639853 74069687020167758591489945)
      ·
        refine ⟨55552265265125818943617459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74069687020167758591489945 55552265265125818943617459)
        ·
          refine ⟨83328397897688728415426189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55552265265125818943617459 83328397897688728415426189)
          ·
            refine ⟨31248149211633273155784821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83328397897688728415426189 31248149211633273155784821)
            ·
              refine ⟨2929513988590619358354827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31248149211633273155784821 2929513988590619358354827)
              ·
                refine ⟨4394270982885929037532241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2929513988590619358354827 4394270982885929037532241)
                ·
                  refine ⟨3295703237164446778149181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4394270982885929037532241 3295703237164446778149181)
                  ·
                    refine ⟨1235888713936667541805943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3295703237164446778149181 1235888713936667541805943)
                    ·
                      rfl

theorem cell22_3610327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 5, 1, 2, 3].length) (baseStart_3610327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3610327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3610327 prefixEnd_3610327 := by exact prefixLift 3610327
  have htrace : WordTrace (prefixWord ++ tailWord_3610327) baseStart_3610327 baseEnd_3610327 := by
    simpa [prefixWord, tailWord_3610327, baseEnd_3610327] using wordTrace_append hprefix tailTrace_3610327
  have hstable : (prefixWord ++ tailWord_3610327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610327).length < 2 ^ (prefixWord ++ tailWord_3610327).sum := by decide
  have hdescent : baseEnd_3610327 < baseStart_3610327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610370 : List Nat := [3, 4, 1, 1, 1, 1, 2, 1, 2, 6]
def baseStart_3610370 : Nat := 118140960795 + 3610370 * 2 ^ 59
def prefixEnd_3610370 : Nat := 4983230072969 + 3 ^ 40 * 3610370 * 2
def baseEnd_3610370 : Nat := 1235903433715429762980811

theorem tailTrace_3610370 : CollatzResearch.WordTrace tailWord_3610370 prefixEnd_3610370 1235903433715429762980811 := by
  unfold tailWord_3610370
  simp only [CollatzResearch.WordTrace]
  refine ⟨32920252982563391737727141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87787341286835711300605709 32920252982563391737727141)
  ·
    refine ⟨6172547434230635950823839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32920252982563391737727141 6172547434230635950823839)
    ·
      refine ⟨9258821151345953926235759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6172547434230635950823839 9258821151345953926235759)
      ·
        refine ⟨13888231727018930889353639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9258821151345953926235759 13888231727018930889353639)
        ·
          refine ⟨20832347590528396334030459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13888231727018930889353639 20832347590528396334030459)
          ·
            refine ⟨31248521385792594501045689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20832347590528396334030459 31248521385792594501045689)
            ·
              refine ⟨23436391039344445875784267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31248521385792594501045689 23436391039344445875784267)
              ·
                refine ⟨35154586559016668813676401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23436391039344445875784267 35154586559016668813676401)
                ·
                  refine ⟨26365939919262501610257301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35154586559016668813676401 26365939919262501610257301)
                  ·
                    refine ⟨1235903433715429762980811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26365939919262501610257301 1235903433715429762980811)
                    ·
                      rfl

theorem cell22_3610370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_3610370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3610370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3610370 prefixEnd_3610370 := by exact prefixLift 3610370
  have htrace : WordTrace (prefixWord ++ tailWord_3610370) baseStart_3610370 baseEnd_3610370 := by
    simpa [prefixWord, tailWord_3610370, baseEnd_3610370] using wordTrace_append hprefix tailTrace_3610370
  have hstable : (prefixWord ++ tailWord_3610370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610370).length < 2 ^ (prefixWord ++ tailWord_3610370).sum := by decide
  have hdescent : baseEnd_3610370 < baseStart_3610370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610372 : List Nat := [2, 3, 2, 2, 1, 2, 3, 1, 3, 3]
def baseStart_3610372 : Nat := 118140960795 + 3610372 * 2 ^ 59
def prefixEnd_3610372 : Nat := 4983230072969 + 3 ^ 40 * 3610372 * 2
def baseEnd_3610372 : Nat := 1235904118356302424430805

theorem tailTrace_3610372 : CollatzResearch.WordTrace tailWord_3610372 prefixEnd_3610372 1235904118356302424430805 := by
  unfold tailWord_3610372
  simp only [CollatzResearch.WordTrace]
  refine ⟨65840542438123160646240685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87787389917497547528320913 65840542438123160646240685)
  ·
    refine ⟨24690203414296185242340257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65840542438123160646240685 24690203414296185242340257)
    ·
      refine ⟨18517652560722138931755193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24690203414296185242340257 18517652560722138931755193)
      ·
        refine ⟨13888239420541604198816395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18517652560722138931755193 13888239420541604198816395)
        ·
          refine ⟨20832359130812406298224593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13888239420541604198816395 20832359130812406298224593)
          ·
            refine ⟨15624269348109304723668445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20832359130812406298224593 15624269348109304723668445)
            ·
              refine ⟨5859101005540989271375667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15624269348109304723668445 5859101005540989271375667)
              ·
                refine ⟨8788651508311483907063501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5859101005540989271375667 8788651508311483907063501)
                ·
                  refine ⟨3295744315616806465148813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8788651508311483907063501 3295744315616806465148813)
                  ·
                    refine ⟨1235904118356302424430805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3295744315616806465148813 1235904118356302424430805)
                    ·
                      rfl

theorem cell22_3610372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 1, 3, 3].length) (baseStart_3610372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3610372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3610372 prefixEnd_3610372 := by exact prefixLift 3610372
  have htrace : WordTrace (prefixWord ++ tailWord_3610372) baseStart_3610372 baseEnd_3610372 := by
    simpa [prefixWord, tailWord_3610372, baseEnd_3610372] using wordTrace_append hprefix tailTrace_3610372
  have hstable : (prefixWord ++ tailWord_3610372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610372).length < 2 ^ (prefixWord ++ tailWord_3610372).sum := by decide
  have hdescent : baseEnd_3610372 < baseStart_3610372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610466 : List Nat := [3, 3, 2, 1, 2, 3, 2, 1, 1, 4]
def baseStart_3610466 : Nat := 118140960795 + 3610466 * 2 ^ 59
def prefixEnd_3610466 : Nat := 4983230072969 + 3 ^ 40 * 3610466 * 2
def baseEnd_3610466 : Nat := 1235936296477317512580517

theorem tailTrace_3610466 : CollatzResearch.WordTrace tailWord_3610466 prefixEnd_3610466 1235936296477317512580517 := by
  unfold tailWord_3610466
  simp only [CollatzResearch.WordTrace]
  refine ⟨32921128334476443836600813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87789675558603850230935501 32921128334476443836600813)
  ·
    refine ⟨12345423125428666438725305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32921128334476443836600813 12345423125428666438725305)
    ·
      refine ⟨9259067344071499829043979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12345423125428666438725305 9259067344071499829043979)
      ·
        refine ⟨13888601016107249743565969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9259067344071499829043979 13888601016107249743565969)
        ·
          refine ⟨10416450762080437307674477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13888601016107249743565969 10416450762080437307674477)
          ·
            refine ⟨3906169035780163990377929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10416450762080437307674477 3906169035780163990377929)
            ·
              refine ⟨2929626776835122992783447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3906169035780163990377929 2929626776835122992783447)
              ·
                refine ⟨4394440165252684489175171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2929626776835122992783447 4394440165252684489175171)
                ·
                  refine ⟨6591660247879026733762757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4394440165252684489175171 6591660247879026733762757)
                  ·
                    refine ⟨1235936296477317512580517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6591660247879026733762757 1235936296477317512580517)
                    ·
                      rfl

theorem cell22_3610466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_3610466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3610466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3610466 prefixEnd_3610466 := by exact prefixLift 3610466
  have htrace : WordTrace (prefixWord ++ tailWord_3610466) baseStart_3610466 baseEnd_3610466 := by
    simpa [prefixWord, tailWord_3610466, baseEnd_3610466] using wordTrace_append hprefix tailTrace_3610466
  have hstable : (prefixWord ++ tailWord_3610466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610466).length < 2 ^ (prefixWord ++ tailWord_3610466).sum := by decide
  have hdescent : baseEnd_3610466 < baseStart_3610466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610473 : List Nat := [1, 2, 1, 1, 1, 3, 1, 2, 1, 9]
def baseStart_3610473 : Nat := 118140960795 + 3610473 * 2 ^ 59
def prefixEnd_3610473 : Nat := 4983230072969 + 3 ^ 40 * 3610473 * 2
def baseEnd_3610473 : Nat := 1235938692720371827655495

theorem tailTrace_3610473 : CollatzResearch.WordTrace tailWord_3610473 prefixEnd_3610473 1235938692720371827655495 := by
  unfold tailWord_3610473
  simp only [CollatzResearch.WordTrace]
  refine ⟨131684768648880415541908073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87789845765920277027938715 131684768648880415541908073)
  ·
    refine ⟨98763576486660311656431055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131684768648880415541908073 98763576486660311656431055)
    ·
      refine ⟨148145364729990467484646583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98763576486660311656431055 148145364729990467484646583)
      ·
        refine ⟨222218047094985701226969875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148145364729990467484646583 222218047094985701226969875)
        ·
          refine ⟨333327070642478551840454813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222218047094985701226969875 333327070642478551840454813)
          ·
            refine ⟨124997651490929456940170555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 333327070642478551840454813 124997651490929456940170555)
            ·
              refine ⟨187496477236394185410255833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124997651490929456940170555 187496477236394185410255833)
              ·
                refine ⟨140622357927295639057691875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 187496477236394185410255833 140622357927295639057691875)
                ·
                  refine ⟨210933536890943458586537813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 140622357927295639057691875 210933536890943458586537813)
                  ·
                    refine ⟨1235938692720371827655495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 210933536890943458586537813 1235938692720371827655495)
                    ·
                      rfl

theorem cell22_3610473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 9].length) (baseStart_3610473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3610473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3610473 prefixEnd_3610473 := by exact prefixLift 3610473
  have htrace : WordTrace (prefixWord ++ tailWord_3610473) baseStart_3610473 baseEnd_3610473 := by
    simpa [prefixWord, tailWord_3610473, baseEnd_3610473] using wordTrace_append hprefix tailTrace_3610473
  have hstable : (prefixWord ++ tailWord_3610473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610473).length < 2 ^ (prefixWord ++ tailWord_3610473).sum := by decide
  have hdescent : baseEnd_3610473 < baseStart_3610473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610526 : List Nat := [4, 3, 1, 3, 2, 1, 8]
def baseStart_3610526 : Nat := 118140960795 + 3610526 * 2 ^ 59
def prefixEnd_3610526 : Nat := 4983230072969 + 3 ^ 40 * 3610526 * 2
def baseEnd_3610526 : Nat := 45776179100129531706679

theorem tailTrace_3610526 : CollatzResearch.WordTrace tailWord_3610526 prefixEnd_3610526 45776179100129531706679 := by
  unfold tailWord_3610526
  simp only [CollatzResearch.WordTrace]
  refine ⟨16460837714711050699198429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87791134478458937062391621 16460837714711050699198429)
  ·
    refine ⟨6172814143016644012199411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16460837714711050699198429 6172814143016644012199411)
    ·
      refine ⟨9259221214524966018299117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6172814143016644012199411 9259221214524966018299117)
      ·
        refine ⟨3472207955446862256862169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9259221214524966018299117 3472207955446862256862169)
        ·
          refine ⟨2604155966585146692646627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3472207955446862256862169 2604155966585146692646627)
          ·
            refine ⟨3906233949877720038969941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2604155966585146692646627 3906233949877720038969941)
            ·
              refine ⟨45776179100129531706679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3906233949877720038969941 45776179100129531706679)
              ·
                rfl

theorem cell22_3610526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 8].length) (baseStart_3610526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3610526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3610526 prefixEnd_3610526 := by exact prefixLift 3610526
  have htrace : WordTrace (prefixWord ++ tailWord_3610526) baseStart_3610526 baseEnd_3610526 := by
    simpa [prefixWord, tailWord_3610526, baseEnd_3610526] using wordTrace_append hprefix tailTrace_3610526
  have hstable : (prefixWord ++ tailWord_3610526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610526).length < 2 ^ (prefixWord ++ tailWord_3610526).sum := by decide
  have hdescent : baseEnd_3610526 < baseStart_3610526 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610584 : List Nat := [2, 1, 2, 2, 2, 2, 5, 1, 1, 4]
def baseStart_3610584 : Nat := 118140960795 + 3610584 * 2 ^ 59
def prefixEnd_3610584 : Nat := 4983230072969 + 3 ^ 40 * 3610584 * 2
def baseEnd_3610584 : Nat := 1235976690288804538130155

theorem tailTrace_3610584 : CollatzResearch.WordTrace tailWord_3610584 prefixEnd_3610584 1235976690288804538130155 := by
  unfold tailWord_3610584
  simp only [CollatzResearch.WordTrace]
  refine ⟨65844408575739140749599403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87792544767652187666132537 65844408575739140749599403)
  ·
    refine ⟨98766612863608711124399105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65844408575739140749599403 98766612863608711124399105)
    ·
      refine ⟨74074959647706533343299329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98766612863608711124399105 74074959647706533343299329)
      ·
        refine ⟨55556219735779900007474497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74074959647706533343299329 55556219735779900007474497)
        ·
          refine ⟨41667164801834925005605873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55556219735779900007474497 41667164801834925005605873)
          ·
            refine ⟨31250373601376193754204405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41667164801834925005605873 31250373601376193754204405)
            ·
              refine ⟨2929722525129018164456663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31250373601376193754204405 2929722525129018164456663)
              ·
                refine ⟨4394583787693527246684995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2929722525129018164456663 4394583787693527246684995)
                ·
                  refine ⟨6591875681540290870027493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4394583787693527246684995 6591875681540290870027493)
                  ·
                    refine ⟨1235976690288804538130155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6591875681540290870027493 1235976690288804538130155)
                    ·
                      rfl

theorem cell22_3610584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 5, 1, 1, 4].length) (baseStart_3610584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3610584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3610584 prefixEnd_3610584 := by exact prefixLift 3610584
  have htrace : WordTrace (prefixWord ++ tailWord_3610584) baseStart_3610584 baseEnd_3610584 := by
    simpa [prefixWord, tailWord_3610584, baseEnd_3610584] using wordTrace_append hprefix tailTrace_3610584
  have hstable : (prefixWord ++ tailWord_3610584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610584).length < 2 ^ (prefixWord ++ tailWord_3610584).sum := by decide
  have hdescent : baseEnd_3610584 < baseStart_3610584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610588 : List Nat := [2, 2, 6, 1, 1, 1, 2, 2, 5]
def baseStart_3610588 : Nat := 118140960795 + 3610588 * 2 ^ 59
def prefixEnd_3610588 : Nat := 4983230072969 + 3 ^ 40 * 3610588 * 2
def baseEnd_3610588 : Nat := 411992686523516620343381

theorem tailTrace_3610588 : CollatzResearch.WordTrace tailWord_3610588 prefixEnd_3610588 411992686523516620343381 := by
  unfold tailWord_3610588
  simp only [CollatzResearch.WordTrace]
  refine ⟨65844481521731895091172209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87792642028975860121562945 65844481521731895091172209)
  ·
    refine ⟨49383361141298921318379157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65844481521731895091172209 49383361141298921318379157)
    ·
      refine ⟨2314845053498386936799023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 49383361141298921318379157 2314845053498386936799023)
      ·
        refine ⟨3472267580247580405198535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2314845053498386936799023 3472267580247580405198535)
        ·
          refine ⟨5208401370371370607797803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3472267580247580405198535 5208401370371370607797803)
          ·
            refine ⟨7812602055557055911696705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5208401370371370607797803 7812602055557055911696705)
            ·
              refine ⟨5859451541667791933772529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7812602055557055911696705 5859451541667791933772529)
              ·
                refine ⟨4394588656250843950329397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5859451541667791933772529 4394588656250843950329397)
                ·
                  refine ⟨411992686523516620343381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4394588656250843950329397 411992686523516620343381)
                  ·
                    rfl

theorem cell22_3610588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 2, 5].length) (baseStart_3610588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3610588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3610588 prefixEnd_3610588 := by exact prefixLift 3610588
  have htrace : WordTrace (prefixWord ++ tailWord_3610588) baseStart_3610588 baseEnd_3610588 := by
    simpa [prefixWord, tailWord_3610588, baseEnd_3610588] using wordTrace_append hprefix tailTrace_3610588
  have hstable : (prefixWord ++ tailWord_3610588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610588).length < 2 ^ (prefixWord ++ tailWord_3610588).sum := by decide
  have hdescent : baseEnd_3610588 < baseStart_3610588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610629 : List Nat := [1, 3, 1, 1, 2, 6, 1, 1, 2, 4]
def baseStart_3610629 : Nat := 118140960795 + 3610629 * 2 ^ 59
def prefixEnd_3610629 : Nat := 4983230072969 + 3 ^ 40 * 3610629 * 2
def baseEnd_3610629 : Nat := 1235992094708439420755017

theorem tailTrace_3610629 : CollatzResearch.WordTrace tailWord_3610629 prefixEnd_3610629 1235992094708439420755017 := by
  unfold tailWord_3610629
  simp only [CollatzResearch.WordTrace]
  refine ⟨131690458436315254184586941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87793638957543502789724627 131690458436315254184586941)
  ·
    refine ⟨49383921913618220319220103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131690458436315254184586941 49383921913618220319220103)
    ·
      refine ⟨74075882870427330478830155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49383921913618220319220103 74075882870427330478830155)
      ·
        refine ⟨111113824305640995718245233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74075882870427330478830155 111113824305640995718245233)
        ·
          refine ⟨83335368229230746788683925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111113824305640995718245233 83335368229230746788683925)
          ·
            refine ⟨3906345385745191255719559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 83335368229230746788683925 3906345385745191255719559)
            ·
              refine ⟨5859518078617786883579339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3906345385745191255719559 5859518078617786883579339)
              ·
                refine ⟨8789277117926680325369009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5859518078617786883579339 8789277117926680325369009)
                ·
                  refine ⟨6591957838445010244026757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8789277117926680325369009 6591957838445010244026757)
                  ·
                    refine ⟨1235992094708439420755017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6591957838445010244026757 1235992094708439420755017)
                    ·
                      rfl

theorem cell22_3610629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 1, 2, 4].length) (baseStart_3610629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3610629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3610629 prefixEnd_3610629 := by exact prefixLift 3610629
  have htrace : WordTrace (prefixWord ++ tailWord_3610629) baseStart_3610629 baseEnd_3610629 := by
    simpa [prefixWord, tailWord_3610629, baseEnd_3610629] using wordTrace_append hprefix tailTrace_3610629
  have hstable : (prefixWord ++ tailWord_3610629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610629).length < 2 ^ (prefixWord ++ tailWord_3610629).sum := by decide
  have hdescent : baseEnd_3610629 < baseStart_3610629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610640 : List Nat := [2, 1, 1, 1, 1, 1, 1, 4, 4, 6]
def baseStart_3610640 : Nat := 118140960795 + 3610640 * 2 ^ 59
def prefixEnd_3610640 : Nat := 4983230072969 + 3 ^ 40 * 3610640 * 2
def baseEnd_3610640 : Nat := 1235995860233239058729983

theorem tailTrace_3610640 : CollatzResearch.WordTrace tailWord_3610640 prefixEnd_3610640 1235995860233239058729983 := by
  unfold tailWord_3610640
  simp only [CollatzResearch.WordTrace]
  refine ⟨65845429819637701531618687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87793906426183602042158249 65845429819637701531618687)
  ·
    refine ⟨98768144729456552297428031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65845429819637701531618687 98768144729456552297428031)
    ·
      refine ⟨148152217094184828446142047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98768144729456552297428031 148152217094184828446142047)
      ·
        refine ⟨222228325641277242669213071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148152217094184828446142047 222228325641277242669213071)
        ·
          refine ⟨333342488461915864003819607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222228325641277242669213071 333342488461915864003819607)
          ·
            refine ⟨500013732692873796005729411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333342488461915864003819607 500013732692873796005729411)
            ·
              refine ⟨750020599039310694008594117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 500013732692873796005729411 750020599039310694008594117)
              ·
                refine ⟨140628862319870755126611397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 750020599039310694008594117 140628862319870755126611397)
                ·
                  refine ⟨26367911684975766586239637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 140628862319870755126611397 26367911684975766586239637)
                  ·
                    refine ⟨1235995860233239058729983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26367911684975766586239637 1235995860233239058729983)
                    ·
                      rfl

theorem cell22_3610640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 4, 6].length) (baseStart_3610640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3610640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3610640 prefixEnd_3610640 := by exact prefixLift 3610640
  have htrace : WordTrace (prefixWord ++ tailWord_3610640) baseStart_3610640 baseEnd_3610640 := by
    simpa [prefixWord, tailWord_3610640, baseEnd_3610640] using wordTrace_append hprefix tailTrace_3610640
  have hstable : (prefixWord ++ tailWord_3610640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610640).length < 2 ^ (prefixWord ++ tailWord_3610640).sum := by decide
  have hdescent : baseEnd_3610640 < baseStart_3610640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610659 : List Nat := [1, 1, 1, 4, 3, 1, 4, 1, 3, 3]
def baseStart_3610659 : Nat := 118140960795 + 3610659 * 2 ^ 59
def prefixEnd_3610659 : Nat := 4983230072969 + 3 ^ 40 * 3610659 * 2
def baseEnd_3610659 : Nat := 1236002364321529342504925

theorem tailTrace_3610659 : CollatzResearch.WordTrace tailWord_3610659 prefixEnd_3610659 1236002364321529342504925 := by
  unfold tailWord_3610659
  simp only [CollatzResearch.WordTrace]
  refine ⟨131691552626206569308179031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87794368417471046205452687 131691552626206569308179031)
  ·
    refine ⟨197537328939309853962268547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131691552626206569308179031 197537328939309853962268547)
    ·
      refine ⟨296305993408964780943402821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197537328939309853962268547 296305993408964780943402821)
      ·
        refine ⟨55557373764180896426888029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 296305993408964780943402821 55557373764180896426888029)
        ·
          refine ⟨20834015161567836160083011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55557373764180896426888029 20834015161567836160083011)
          ·
            refine ⟨31251022742351754240124517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20834015161567836160083011 31251022742351754240124517)
            ·
              refine ⟨5859566764190953920023347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31251022742351754240124517 5859566764190953920023347)
              ·
                refine ⟨8789350146286430880035021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5859566764190953920023347 8789350146286430880035021)
                ·
                  refine ⟨3296006304857411580013133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8789350146286430880035021 3296006304857411580013133)
                  ·
                    refine ⟨1236002364321529342504925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3296006304857411580013133 1236002364321529342504925)
                    ·
                      rfl

theorem cell22_3610659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 1, 3, 3].length) (baseStart_3610659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3610659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3610659 prefixEnd_3610659 := by exact prefixLift 3610659
  have htrace : WordTrace (prefixWord ++ tailWord_3610659) baseStart_3610659 baseEnd_3610659 := by
    simpa [prefixWord, tailWord_3610659, baseEnd_3610659] using wordTrace_append hprefix tailTrace_3610659
  have hstable : (prefixWord ++ tailWord_3610659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610659).length < 2 ^ (prefixWord ++ tailWord_3610659).sum := by decide
  have hdescent : baseEnd_3610659 < baseStart_3610659 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610710 : List Nat := [5, 2, 2, 1, 1, 3, 1, 1, 3, 3]
def baseStart_3610710 : Nat := 118140960795 + 3610710 * 2 ^ 59
def prefixEnd_3610710 : Nat := 4983230072969 + 3 ^ 40 * 3610710 * 2
def baseEnd_3610710 : Nat := 1236019822663782209479769

theorem tailTrace_3610710 : CollatzResearch.WordTrace tailWord_3610710 prefixEnd_3610710 1236019822663782209479769 := by
  unfold tailWord_3610710
  simp only [CollatzResearch.WordTrace]
  refine ⟨8230838296813862813642849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87795608499347870012190389 8230838296813862813642849)
  ·
    refine ⟨6173128722610397110232137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8230838296813862813642849 6173128722610397110232137)
    ·
      refine ⟨4629846541957797832674103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6173128722610397110232137 4629846541957797832674103)
      ·
        refine ⟨6944769812936696749011155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4629846541957797832674103 6944769812936696749011155)
        ·
          refine ⟨10417154719405045123516733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6944769812936696749011155 10417154719405045123516733)
          ·
            refine ⟨3906433019776891921318775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10417154719405045123516733 3906433019776891921318775)
            ·
              refine ⟨5859649529665337881978163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3906433019776891921318775 5859649529665337881978163)
              ·
                refine ⟨8789474294498006822967245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5859649529665337881978163 8789474294498006822967245)
                ·
                  refine ⟨3296052860436752558612717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8789474294498006822967245 3296052860436752558612717)
                  ·
                    refine ⟨1236019822663782209479769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3296052860436752558612717 1236019822663782209479769)
                    ·
                      rfl

theorem cell22_3610710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_3610710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3610710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3610710 prefixEnd_3610710 := by exact prefixLift 3610710
  have htrace : WordTrace (prefixWord ++ tailWord_3610710) baseStart_3610710 baseEnd_3610710 := by
    simpa [prefixWord, tailWord_3610710, baseEnd_3610710] using wordTrace_append hprefix tailTrace_3610710
  have hstable : (prefixWord ++ tailWord_3610710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610710).length < 2 ^ (prefixWord ++ tailWord_3610710).sum := by decide
  have hdescent : baseEnd_3610710 < baseStart_3610710 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610736 : List Nat := [2, 1, 1, 1, 5, 4, 1, 2, 1, 4]
def baseStart_3610736 : Nat := 118140960795 + 3610736 * 2 ^ 59
def prefixEnd_3610736 : Nat := 4983230072969 + 3 ^ 40 * 3610736 * 2
def baseEnd_3610736 : Nat := 1236028722995126808329689

theorem tailTrace_3610736 : CollatzResearch.WordTrace tailWord_3610736 prefixEnd_3610736 1236028722995126808329689 := by
  unfold tailWord_3610736
  simp only [CollatzResearch.WordTrace]
  refine ⟨65847180523463805729366031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87796240697951740972488041 65847180523463805729366031)
  ·
    refine ⟨98770770785195708594049047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65847180523463805729366031 98770770785195708594049047)
    ·
      refine ⟨148156156177793562891073571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98770770785195708594049047 148156156177793562891073571)
      ·
        refine ⟨222234234266690344336610357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148156156177793562891073571 222234234266690344336610357)
        ·
          refine ⟨20834459462502219781557221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 222234234266690344336610357 20834459462502219781557221)
          ·
            refine ⟨3906461149219166209041979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20834459462502219781557221 3906461149219166209041979)
            ·
              refine ⟨5859691723828749313562969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3906461149219166209041979 5859691723828749313562969)
              ·
                refine ⟨4394768792871561985172227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5859691723828749313562969 4394768792871561985172227)
                ·
                  refine ⟨6592153189307342977758341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4394768792871561985172227 6592153189307342977758341)
                  ·
                    refine ⟨1236028722995126808329689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6592153189307342977758341 1236028722995126808329689)
                    ·
                      rfl

theorem cell22_3610736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 2, 1, 4].length) (baseStart_3610736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3610736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3610736 prefixEnd_3610736 := by exact prefixLift 3610736
  have htrace : WordTrace (prefixWord ++ tailWord_3610736) baseStart_3610736 baseEnd_3610736 := by
    simpa [prefixWord, tailWord_3610736, baseEnd_3610736] using wordTrace_append hprefix tailTrace_3610736
  have hstable : (prefixWord ++ tailWord_3610736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610736).length < 2 ^ (prefixWord ++ tailWord_3610736).sum := by decide
  have hdescent : baseEnd_3610736 < baseStart_3610736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610749 : List Nat := [1, 4, 1, 1, 3, 3, 1, 2, 1, 5]
def baseStart_3610749 : Nat := 118140960795 + 3610749 * 2 ^ 59
def prefixEnd_3610749 : Nat := 4983230072969 + 3 ^ 40 * 3610749 * 2
def baseEnd_3610749 : Nat := 1236033173160799107754649

theorem tailTrace_3610749 : CollatzResearch.WordTrace tailWord_3610749 prefixEnd_3610749 1236033173160799107754649 := by
  unfold tailWord_3610749
  simp only [CollatzResearch.WordTrace]
  refine ⟨131694835195880514678955301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87796556797253676452636867 131694835195880514678955301)
  ·
    refine ⟨24692781599227596502304119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131694835195880514678955301 24692781599227596502304119)
    ·
      refine ⟨37039172398841394753456179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24692781599227596502304119 37039172398841394753456179)
      ·
        refine ⟨55558758598262092130184269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37039172398841394753456179 55558758598262092130184269)
        ·
          refine ⟨20834534474348284548819101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55558758598262092130184269 20834534474348284548819101)
          ·
            refine ⟨7812950427880606705807163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20834534474348284548819101 7812950427880606705807163)
            ·
              refine ⟨11719425641820910058710745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7812950427880606705807163 11719425641820910058710745)
              ·
                refine ⟨8789569231365682544033059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11719425641820910058710745 8789569231365682544033059)
                ·
                  refine ⟨13184353847048523816049589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8789569231365682544033059 13184353847048523816049589)
                  ·
                    refine ⟨1236033173160799107754649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13184353847048523816049589 1236033173160799107754649)
                    ·
                      rfl

theorem cell22_3610749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 2, 1, 5].length) (baseStart_3610749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3610749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3610749 prefixEnd_3610749 := by exact prefixLift 3610749
  have htrace : WordTrace (prefixWord ++ tailWord_3610749) baseStart_3610749 baseEnd_3610749 := by
    simpa [prefixWord, tailWord_3610749, baseEnd_3610749] using wordTrace_append hprefix tailTrace_3610749
  have hstable : (prefixWord ++ tailWord_3610749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610749).length < 2 ^ (prefixWord ++ tailWord_3610749).sum := by decide
  have hdescent : baseEnd_3610749 < baseStart_3610749 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610753 : List Nat := [1, 2, 4, 2, 3, 1, 3, 1, 1, 4]
def baseStart_3610753 : Nat := 118140960795 + 3610753 * 2 ^ 59
def prefixEnd_3610753 : Nat := 4983230072969 + 3 ^ 40 * 3610753 * 2
def baseEnd_3610753 : Nat := 1236034542442544430654637

theorem tailTrace_3610753 : CollatzResearch.WordTrace tailWord_3610753 prefixEnd_3610753 1236034542442544430654637 := by
  unfold tailWord_3610753
  simp only [CollatzResearch.WordTrace]
  refine ⟨131694981087866023362100913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87796654058577348908067275 131694981087866023362100913)
  ·
    refine ⟨98771235815899517521575685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131694981087866023362100913 98771235815899517521575685)
    ·
      refine ⟨18519606715481159535295441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98771235815899517521575685 18519606715481159535295441)
      ·
        refine ⟨13889705036610869651471581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18519606715481159535295441 13889705036610869651471581)
        ·
          refine ⟨5208639388729076119301843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13889705036610869651471581 5208639388729076119301843)
          ·
            refine ⟨7812959083093614178952765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5208639388729076119301843 7812959083093614178952765)
            ·
              refine ⟨2929859656160105317107287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7812959083093614178952765 2929859656160105317107287)
              ·
                refine ⟨4394789484240157975660931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2929859656160105317107287 4394789484240157975660931)
                ·
                  refine ⟨6592184226360236963491397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4394789484240157975660931 6592184226360236963491397)
                  ·
                    refine ⟨1236034542442544430654637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6592184226360236963491397 1236034542442544430654637)
                    ·
                      rfl

theorem cell22_3610753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 3, 1, 1, 4].length) (baseStart_3610753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3610753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3610753 prefixEnd_3610753 := by exact prefixLift 3610753
  have htrace : WordTrace (prefixWord ++ tailWord_3610753) baseStart_3610753 baseEnd_3610753 := by
    simpa [prefixWord, tailWord_3610753, baseEnd_3610753] using wordTrace_append hprefix tailTrace_3610753
  have hstable : (prefixWord ++ tailWord_3610753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610753).length < 2 ^ (prefixWord ++ tailWord_3610753).sum := by decide
  have hdescent : baseEnd_3610753 < baseStart_3610753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610762 : List Nat := [3, 1, 2, 3, 1, 12]
def baseStart_3610762 : Nat := 118140960795 + 3610762 * 2 ^ 59
def prefixEnd_3610762 : Nat := 4983230072969 + 3 ^ 40 * 3610762 * 2
def baseEnd_3610762 : Nat := 15259723744771251940489

theorem tailTrace_3610762 : CollatzResearch.WordTrace tailWord_3610762 prefixEnd_3610762 15259723744771251940489 := by
  unfold tailWord_3610762
  simp only [CollatzResearch.WordTrace]
  refine ⟨32923827336208354474794635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87796872896555611932785693 32923827336208354474794635)
  ·
    refine ⟨49385741004312531712191953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32923827336208354474794635 49385741004312531712191953)
    ·
      refine ⟨37039305753234398784143965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49385741004312531712191953 37039305753234398784143965)
      ·
        refine ⟨13889739657462899544053987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37039305753234398784143965 13889739657462899544053987)
        ·
          refine ⟨20834609486194349316080981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13889739657462899544053987 20834609486194349316080981)
          ·
            refine ⟨15259723744771251940489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 20834609486194349316080981 15259723744771251940489)
            ·
              rfl

theorem cell22_3610762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 12].length) (baseStart_3610762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3610762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3610762 prefixEnd_3610762 := by exact prefixLift 3610762
  have htrace : WordTrace (prefixWord ++ tailWord_3610762) baseStart_3610762 baseEnd_3610762 := by
    simpa [prefixWord, tailWord_3610762, baseEnd_3610762] using wordTrace_append hprefix tailTrace_3610762
  have hstable : (prefixWord ++ tailWord_3610762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610762).length < 2 ^ (prefixWord ++ tailWord_3610762).sum := by decide
  have hdescent : baseEnd_3610762 < baseStart_3610762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610798 : List Nat := [4, 1, 4, 2, 1, 1, 1, 1, 1, 6]
def baseStart_3610798 : Nat := 118140960795 + 3610798 * 2 ^ 59
def prefixEnd_3610798 : Nat := 4983230072969 + 3 ^ 40 * 3610798 * 2
def baseEnd_3610798 : Nat := 1236049946862179313279499

theorem tailTrace_3610798 : CollatzResearch.WordTrace tailWord_3610798 prefixEnd_3610798 1236049946862179313279499 := by
  unfold tailWord_3610798
  simp only [CollatzResearch.WordTrace]
  refine ⟨16462077796587874505936131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87797748248468664031659365 16462077796587874505936131)
  ·
    refine ⟨24693116694881811758904197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16462077796587874505936131 24693116694881811758904197)
    ·
      refine ⟨4629959380290339704794537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24693116694881811758904197 4629959380290339704794537)
      ·
        refine ⟨3472469535217754778595903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4629959380290339704794537 3472469535217754778595903)
        ·
          refine ⟨5208704302826632167893855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3472469535217754778595903 5208704302826632167893855)
          ·
            refine ⟨7813056454239948251840783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5208704302826632167893855 7813056454239948251840783)
            ·
              refine ⟨11719584681359922377761175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7813056454239948251840783 11719584681359922377761175)
              ·
                refine ⟨17579377022039883566641763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11719584681359922377761175 17579377022039883566641763)
                ·
                  refine ⟨26369065533059825349962645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17579377022039883566641763 26369065533059825349962645)
                  ·
                    refine ⟨1236049946862179313279499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26369065533059825349962645 1236049946862179313279499)
                    ·
                      rfl

theorem cell22_3610798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_3610798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3610798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3610798 prefixEnd_3610798 := by exact prefixLift 3610798
  have htrace : WordTrace (prefixWord ++ tailWord_3610798) baseStart_3610798 baseEnd_3610798 := by
    simpa [prefixWord, tailWord_3610798, baseEnd_3610798] using wordTrace_append hprefix tailTrace_3610798
  have hstable : (prefixWord ++ tailWord_3610798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610798).length < 2 ^ (prefixWord ++ tailWord_3610798).sum := by decide
  have hdescent : baseEnd_3610798 < baseStart_3610798 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610804 : List Nat := [2, 5, 3, 1, 1, 2, 2, 1, 1, 4]
def baseStart_3610804 : Nat := 118140960795 + 3610804 * 2 ^ 59
def prefixEnd_3610804 : Nat := 4983230072969 + 3 ^ 40 * 3610804 * 2
def baseEnd_3610804 : Nat := 1236052000784797297629481

theorem tailTrace_3610804 : CollatzResearch.WordTrace tailWord_3610804 prefixEnd_3610804 1236052000784797297629481 := by
  unfold tailWord_3610804
  simp only [CollatzResearch.WordTrace]
  refine ⟨65848420605340629536103733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87797894140454172714804977 65848420605340629536103733)
  ·
    refine ⟨6173289431750684019009725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65848420605340629536103733 6173289431750684019009725)
    ·
      refine ⟨2314983536906506507128647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6173289431750684019009725 2314983536906506507128647)
      ·
        refine ⟨3472475305359759760692971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2314983536906506507128647 3472475305359759760692971)
        ·
          refine ⟨5208712958039639641039457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3472475305359759760692971 5208712958039639641039457)
          ·
            refine ⟨3906534718529729730779593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5208712958039639641039457 3906534718529729730779593)
            ·
              refine ⟨2929901038897297298084695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3906534718529729730779593 2929901038897297298084695)
              ·
                refine ⟨4394851558345945947127043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2929901038897297298084695 4394851558345945947127043)
                ·
                  refine ⟨6592277337518918920690565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4394851558345945947127043 6592277337518918920690565)
                  ·
                    refine ⟨1236052000784797297629481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6592277337518918920690565 1236052000784797297629481)
                    ·
                      rfl

theorem cell22_3610804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_3610804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3610804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3610804 prefixEnd_3610804 := by exact prefixLift 3610804
  have htrace : WordTrace (prefixWord ++ tailWord_3610804) baseStart_3610804 baseEnd_3610804 := by
    simpa [prefixWord, tailWord_3610804, baseEnd_3610804] using wordTrace_append hprefix tailTrace_3610804
  have hstable : (prefixWord ++ tailWord_3610804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610804).length < 2 ^ (prefixWord ++ tailWord_3610804).sum := by decide
  have hdescent : baseEnd_3610804 < baseStart_3610804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610817 : List Nat := [1, 2, 6, 1, 3, 1, 1, 2, 2, 3]
def baseStart_3610817 : Nat := 118140960795 + 3610817 * 2 ^ 59
def prefixEnd_3610817 : Nat := 4983230072969 + 3 ^ 40 * 3610817 * 2
def baseEnd_3610817 : Nat := 1236056450950469597054441

theorem tailTrace_3610817 : CollatzResearch.WordTrace tailWord_3610817 prefixEnd_3610817 1236056450950469597054441 := by
  unfold tailWord_3610817
  simp only [CollatzResearch.WordTrace]
  refine ⟨131697315359634162292430705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87798210239756108194953803 131697315359634162292430705)
  ·
    refine ⟨98772986519725621719323029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131697315359634162292430705 98772986519725621719323029)
    ·
      refine ⟨4629983743112138518093267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 98772986519725621719323029 4629983743112138518093267)
      ·
        refine ⟨6944975614668207777139901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4629983743112138518093267 6944975614668207777139901)
        ·
          refine ⟨2604365855500577916427463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6944975614668207777139901 2604365855500577916427463)
          ·
            refine ⟨3906548783250866874641195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2604365855500577916427463 3906548783250866874641195)
            ·
              refine ⟨5859823174876300311961793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3906548783250866874641195 5859823174876300311961793)
              ·
                refine ⟨4394867381157225233971345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5859823174876300311961793 4394867381157225233971345)
                ·
                  refine ⟨3296150535867918925478509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4394867381157225233971345 3296150535867918925478509)
                  ·
                    refine ⟨1236056450950469597054441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3296150535867918925478509 1236056450950469597054441)
                    ·
                      rfl

theorem cell22_3610817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_3610817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3610817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3610817 prefixEnd_3610817 := by exact prefixLift 3610817
  have htrace : WordTrace (prefixWord ++ tailWord_3610817) baseStart_3610817 baseEnd_3610817 := by
    simpa [prefixWord, tailWord_3610817, baseEnd_3610817] using wordTrace_append hprefix tailTrace_3610817
  have hstable : (prefixWord ++ tailWord_3610817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610817).length < 2 ^ (prefixWord ++ tailWord_3610817).sum := by decide
  have hdescent : baseEnd_3610817 < baseStart_3610817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610916 : List Nat := [2, 3, 1, 3, 1, 2, 1, 3, 2, 4]
def baseStart_3610916 : Nat := 118140960795 + 3610916 * 2 ^ 59
def prefixEnd_3610916 : Nat := 4983230072969 + 3 ^ 40 * 3610916 * 2
def baseEnd_3610916 : Nat := 1236090340673666338829137

theorem tailTrace_3610916 : CollatzResearch.WordTrace tailWord_3610916 prefixEnd_3610916 1236090340673666338829137 := by
  unfold tailWord_3610916
  simp only [CollatzResearch.WordTrace]
  refine ⟨65850463093137751100142301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87800617457517001466856401 65850463093137751100142301)
  ·
    refine ⟨24693923659926656662553363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65850463093137751100142301 24693923659926656662553363)
    ·
      refine ⟨37040885489889984993830045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24693923659926656662553363 37040885489889984993830045)
      ·
        refine ⟨13890332058708744372686267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37040885489889984993830045 13890332058708744372686267)
        ·
          refine ⟨20835498088063116559029401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13890332058708744372686267 20835498088063116559029401)
          ·
            refine ⟨15626623566047337419272051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20835498088063116559029401 15626623566047337419272051)
            ·
              refine ⟨23439935349071006128908077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15626623566047337419272051 23439935349071006128908077)
              ·
                refine ⟨8789975755901627298340529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23439935349071006128908077 8789975755901627298340529)
                ·
                  refine ⟨6592481816926220473755397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8789975755901627298340529 6592481816926220473755397)
                  ·
                    refine ⟨1236090340673666338829137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6592481816926220473755397 1236090340673666338829137)
                    ·
                      rfl

theorem cell22_3610916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 3, 2, 4].length) (baseStart_3610916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3610916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3610916 prefixEnd_3610916 := by exact prefixLift 3610916
  have htrace : WordTrace (prefixWord ++ tailWord_3610916) baseStart_3610916 baseEnd_3610916 := by
    simpa [prefixWord, tailWord_3610916, baseEnd_3610916] using wordTrace_append hprefix tailTrace_3610916
  have hstable : (prefixWord ++ tailWord_3610916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610916).length < 2 ^ (prefixWord ++ tailWord_3610916).sum := by decide
  have hdescent : baseEnd_3610916 < baseStart_3610916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610980 : List Nat := [2, 3, 1, 1, 3, 1, 4, 3, 1, 3]
def baseStart_3610980 : Nat := 118140960795 + 3610980 * 2 ^ 59
def prefixEnd_3610980 : Nat := 4983230072969 + 3 ^ 40 * 3610980 * 2
def baseEnd_3610980 : Nat := 1236112249181591505228941

theorem tailTrace_3610980 : CollatzResearch.WordTrace tailWord_3610980 prefixEnd_3610980 1236112249181591505228941 := by
  unfold tailWord_3610980
  simp only [CollatzResearch.WordTrace]
  refine ⟨65851630229021820565307197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87802173638695760753742929 65851630229021820565307197)
  ·
    refine ⟨24694361335883182711990199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65851630229021820565307197 24694361335883182711990199)
    ·
      refine ⟨37041542003824774067985299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24694361335883182711990199 37041542003824774067985299)
      ·
        refine ⟨55562313005737161101977949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37041542003824774067985299 55562313005737161101977949)
        ·
          refine ⟨20835867377151435413241731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55562313005737161101977949 20835867377151435413241731)
          ·
            refine ⟨31253801065727153119862597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20835867377151435413241731 31253801065727153119862597)
            ·
              refine ⟨5860087699823841209974237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31253801065727153119862597 5860087699823841209974237)
              ·
                refine ⟨2197532887433940453740339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5860087699823841209974237 2197532887433940453740339)
                ·
                  refine ⟨3296299331150910680610509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2197532887433940453740339 3296299331150910680610509)
                  ·
                    refine ⟨1236112249181591505228941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3296299331150910680610509 1236112249181591505228941)
                    ·
                      rfl

theorem cell22_3610980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 3, 1, 3].length) (baseStart_3610980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3610980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3610980 prefixEnd_3610980 := by exact prefixLift 3610980
  have htrace : WordTrace (prefixWord ++ tailWord_3610980) baseStart_3610980 baseEnd_3610980 := by
    simpa [prefixWord, tailWord_3610980, baseEnd_3610980] using wordTrace_append hprefix tailTrace_3610980
  have hstable : (prefixWord ++ tailWord_3610980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610980).length < 2 ^ (prefixWord ++ tailWord_3610980).sum := by decide
  have hdescent : baseEnd_3610980 < baseStart_3610980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611106 : List Nat := [3, 3, 3, 2, 1, 2, 2, 2, 4]
def baseStart_3611106 : Nat := 118140960795 + 3611106 * 2 ^ 59
def prefixEnd_3611106 : Nat := 4983230072969 + 3 ^ 40 * 3611106 * 2
def baseEnd_3611106 : Nat := 412051793852189725526185

theorem tailTrace_3611106 : CollatzResearch.WordTrace tailWord_3611106 prefixEnd_3611106 412051793852189725526185 := by
  unfold tailWord_3611106
  simp only [CollatzResearch.WordTrace]
  refine ⟨32926964013896791162425293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87805237370391443099800781 32926964013896791162425293)
  ·
    refine ⟨12347611505211296685909485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32926964013896791162425293 12347611505211296685909485)
    ·
      refine ⟨4630354314454236257216057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12347611505211296685909485 4630354314454236257216057)
      ·
        refine ⟨3472765735840677192912043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4630354314454236257216057 3472765735840677192912043)
        ·
          refine ⟨5209148603761015789368065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3472765735840677192912043 5209148603761015789368065)
          ·
            refine ⟨3906861452820761842026049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5209148603761015789368065 3906861452820761842026049)
            ·
              refine ⟨2930146089615571381519537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3906861452820761842026049 2930146089615571381519537)
              ·
                refine ⟨2197609567211678536139653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2930146089615571381519537 2197609567211678536139653)
                ·
                  refine ⟨412051793852189725526185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2197609567211678536139653 412051793852189725526185)
                  ·
                    rfl

theorem cell22_3611106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 2, 2, 4].length) (baseStart_3611106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3611106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3611106 prefixEnd_3611106 := by exact prefixLift 3611106
  have htrace : WordTrace (prefixWord ++ tailWord_3611106) baseStart_3611106 baseEnd_3611106 := by
    simpa [prefixWord, tailWord_3611106, baseEnd_3611106] using wordTrace_append hprefix tailTrace_3611106
  have hstable : (prefixWord ++ tailWord_3611106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611106).length < 2 ^ (prefixWord ++ tailWord_3611106).sum := by decide
  have hdescent : baseEnd_3611106 < baseStart_3611106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611115 : List Nat := [1, 1, 1, 1, 2, 3, 5, 4, 1, 3]
def baseStart_3611115 : Nat := 118140960795 + 3611115 * 2 ^ 59
def prefixEnd_3611115 : Nat := 4983230072969 + 3 ^ 40 * 3611115 * 2
def baseEnd_3611115 : Nat := 1236158462440496153103527

theorem tailTrace_3611115 : CollatzResearch.WordTrace tailWord_3611115 prefixEnd_3611115 1236158462440496153103527 := by
  unfold tailWord_3611115
  simp only [CollatzResearch.WordTrace]
  refine ⟨131708184312554559186778799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87805456208369706124519199 131708184312554559186778799)
  ·
    refine ⟨197562276468831838780168199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131708184312554559186778799 197562276468831838780168199)
    ·
      refine ⟨296343414703247758170252299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197562276468831838780168199 296343414703247758170252299)
      ·
        refine ⟨444515122054871637255378449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296343414703247758170252299 444515122054871637255378449)
        ·
          refine ⟨333386341541153727941533837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 444515122054871637255378449 333386341541153727941533837)
          ·
            refine ⟨125019878077932647978075189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 333386341541153727941533837 125019878077932647978075189)
            ·
              refine ⟨11720613569806185747944549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 125019878077932647978075189 11720613569806185747944549)
              ·
                refine ⟨2197615044338659827739603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11720613569806185747944549 2197615044338659827739603)
                ·
                  refine ⟨3296422566507989741609405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2197615044338659827739603 3296422566507989741609405)
                  ·
                    refine ⟨1236158462440496153103527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3296422566507989741609405 1236158462440496153103527)
                    ·
                      rfl

theorem cell22_3611115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 4, 1, 3].length) (baseStart_3611115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3611115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3611115 prefixEnd_3611115 := by exact prefixLift 3611115
  have htrace : WordTrace (prefixWord ++ tailWord_3611115) baseStart_3611115 baseEnd_3611115 := by
    simpa [prefixWord, tailWord_3611115, baseEnd_3611115] using wordTrace_append hprefix tailTrace_3611115
  have hstable : (prefixWord ++ tailWord_3611115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611115).length < 2 ^ (prefixWord ++ tailWord_3611115).sum := by decide
  have hdescent : baseEnd_3611115 < baseStart_3611115 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611190 : List Nat := [5, 1, 2, 1, 2, 1, 2, 2, 6]
def baseStart_3611190 : Nat := 118140960795 + 3611190 * 2 ^ 59
def prefixEnd_3611190 : Nat := 4983230072969 + 3 ^ 40 * 3611190 * 2
def baseEnd_3611190 : Nat := 412061378824406985826099

theorem tailTrace_3611190 : CollatzResearch.WordTrace tailWord_3611190 prefixEnd_3611190 412061378824406985826099 := by
  unfold tailWord_3611190
  simp only [CollatzResearch.WordTrace]
  refine ⟨8231932486705177937234939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87807279858188564663839349 8231932486705177937234939)
  ·
    refine ⟨12347898730057766905852409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8231932486705177937234939 12347898730057766905852409)
    ·
      refine ⟨9260924047543325179389307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12347898730057766905852409 9260924047543325179389307)
      ·
        refine ⟨13891386071314987769083961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9260924047543325179389307 13891386071314987769083961)
        ·
          refine ⟨10418539553486240826812971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13891386071314987769083961 10418539553486240826812971)
          ·
            refine ⟨15627809330229361240219457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10418539553486240826812971 15627809330229361240219457)
            ·
              refine ⟨11720856997672020930164593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15627809330229361240219457 11720856997672020930164593)
              ·
                refine ⟨8790642748254015697623445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11720856997672020930164593 8790642748254015697623445)
                ·
                  refine ⟨412061378824406985826099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8790642748254015697623445 412061378824406985826099)
                  ·
                    rfl

theorem cell22_3611190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_3611190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3611190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3611190 prefixEnd_3611190 := by exact prefixLift 3611190
  have htrace : WordTrace (prefixWord ++ tailWord_3611190) baseStart_3611190 baseEnd_3611190 := by
    simpa [prefixWord, tailWord_3611190, baseEnd_3611190] using wordTrace_append hprefix tailTrace_3611190
  have hstable : (prefixWord ++ tailWord_3611190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611190).length < 2 ^ (prefixWord ++ tailWord_3611190).sum := by decide
  have hdescent : baseEnd_3611190 < baseStart_3611190 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611207 : List Nat := [1, 1, 4, 1, 4, 3, 1, 3, 4]
def baseStart_3611207 : Nat := 118140960795 + 3611207 * 2 ^ 59
def prefixEnd_3611207 : Nat := 4983230072969 + 3 ^ 40 * 3611207 * 2
def baseEnd_3611207 : Nat := 412063318640212859934415

theorem tailTrace_3611207 : CollatzResearch.WordTrace tailWord_3611207 prefixEnd_3611207 412063318640212859934415 := by
  unfold tailWord_3611207
  simp only [CollatzResearch.WordTrace]
  refine ⟨131711539828221258899127875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87807693218814172599418583 131711539828221258899127875)
  ·
    refine ⟨197567309742331888348691813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131711539828221258899127875 197567309742331888348691813)
    ·
      refine ⟨37043870576687229065379715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 197567309742331888348691813 37043870576687229065379715)
      ·
        refine ⟨55565805865030843598069573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37043870576687229065379715 55565805865030843598069573)
        ·
          refine ⟨10418588599693283174638045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55565805865030843598069573 10418588599693283174638045)
          ·
            refine ⟨3906970724884981190489267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10418588599693283174638045 3906970724884981190489267)
            ·
              refine ⟨5860456087327471785733901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3906970724884981190489267 5860456087327471785733901)
              ·
                refine ⟨2197671032747801919650213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5860456087327471785733901 2197671032747801919650213)
                ·
                  refine ⟨412063318640212859934415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2197671032747801919650213 412063318640212859934415)
                  ·
                    rfl

theorem cell22_3611207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 3, 4].length) (baseStart_3611207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3611207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3611207 prefixEnd_3611207 := by exact prefixLift 3611207
  have htrace : WordTrace (prefixWord ++ tailWord_3611207) baseStart_3611207 baseEnd_3611207 := by
    simpa [prefixWord, tailWord_3611207, baseEnd_3611207] using wordTrace_append hprefix tailTrace_3611207
  have hstable : (prefixWord ++ tailWord_3611207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611207).length < 2 ^ (prefixWord ++ tailWord_3611207).sum := by decide
  have hdescent : baseEnd_3611207 < baseStart_3611207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611220 : List Nat := [2, 4, 1, 1, 1, 4, 1, 2, 2, 4]
def baseStart_3611220 : Nat := 118140960795 + 3611220 * 2 ^ 59
def prefixEnd_3611220 : Nat := 4983230072969 + 3 ^ 40 * 3611220 * 2
def baseEnd_3611220 : Nat := 1236194406086310879228205

theorem tailTrace_3611220 : CollatzResearch.WordTrace tailWord_3611220 prefixEnd_3611220 1236194406086310879228205 := by
  unfold tailWord_3611220
  simp only [CollatzResearch.WordTrace]
  refine ⟨65856006988587081059675557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87808009318116108079567409 65856006988587081059675557)
  ·
    refine ⟨12348001310360077698689167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65856006988587081059675557 12348001310360077698689167)
    ·
      refine ⟨18522001965540116548033751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12348001310360077698689167 18522001965540116548033751)
      ·
        refine ⟨27783002948310174822050627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18522001965540116548033751 27783002948310174822050627)
        ·
          refine ⟨41674504422465262233075941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27783002948310174822050627 41674504422465262233075941)
          ·
            refine ⟨7813969579212236668701739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41674504422465262233075941 7813969579212236668701739)
            ·
              refine ⟨11720954368818355003052609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7813969579212236668701739 11720954368818355003052609)
              ·
                refine ⟨8790715776613766252289457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11720954368818355003052609 8790715776613766252289457)
                ·
                  refine ⟨6593036832460324689217093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8790715776613766252289457 6593036832460324689217093)
                  ·
                    refine ⟨1236194406086310879228205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6593036832460324689217093 1236194406086310879228205)
                    ·
                      rfl

theorem cell22_3611220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_3611220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3611220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3611220 prefixEnd_3611220 := by exact prefixLift 3611220
  have htrace : WordTrace (prefixWord ++ tailWord_3611220) baseStart_3611220 baseEnd_3611220 := by
    simpa [prefixWord, tailWord_3611220, baseEnd_3611220] using wordTrace_append hprefix tailTrace_3611220
  have hstable : (prefixWord ++ tailWord_3611220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611220).length < 2 ^ (prefixWord ++ tailWord_3611220).sum := by decide
  have hdescent : baseEnd_3611220 < baseStart_3611220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611318 : List Nat := [5, 1, 3, 1, 2, 1, 2, 3, 1, 3]
def baseStart_3611318 : Nat := 118140960795 + 3611318 * 2 ^ 59
def prefixEnd_3611318 : Nat := 4983230072969 + 3 ^ 40 * 3611318 * 2
def baseEnd_3611318 : Nat := 1236227953489071290277905

theorem tailTrace_3611318 : CollatzResearch.WordTrace tailWord_3611318 prefixEnd_3611318 1236227953489071290277905 := by
  unfold tailWord_3611318
  simp only [CollatzResearch.WordTrace]
  refine ⟨8232224270676195303526163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87810392220546083237612405 8232224270676195303526163)
  ·
    refine ⟨12348336406014292955289245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8232224270676195303526163 12348336406014292955289245)
    ·
      refine ⟨4630626152255359858233467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12348336406014292955289245 4630626152255359858233467)
      ·
        refine ⟨6945939228383039787350201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4630626152255359858233467 6945939228383039787350201)
        ·
          refine ⟨5209454421287279840512651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6945939228383039787350201 5209454421287279840512651)
          ·
            refine ⟨7814181631930919760768977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5209454421287279840512651 7814181631930919760768977)
            ·
              refine ⟨5860636223948189820576733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7814181631930919760768977 5860636223948189820576733)
              ·
                refine ⟨2197738583980571182716275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5860636223948189820576733 2197738583980571182716275)
                ·
                  refine ⟨3296607875970856774074413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2197738583980571182716275 3296607875970856774074413)
                  ·
                    refine ⟨1236227953489071290277905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3296607875970856774074413 1236227953489071290277905)
                    ·
                      rfl

theorem cell22_3611318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_3611318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3611318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3611318 prefixEnd_3611318 := by exact prefixLift 3611318
  have htrace : WordTrace (prefixWord ++ tailWord_3611318) baseStart_3611318 baseEnd_3611318 := by
    simpa [prefixWord, tailWord_3611318, baseEnd_3611318] using wordTrace_append hprefix tailTrace_3611318
  have hstable : (prefixWord ++ tailWord_3611318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611318).length < 2 ^ (prefixWord ++ tailWord_3611318).sum := by decide
  have hdescent : baseEnd_3611318 < baseStart_3611318 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611327 : List Nat := [1, 1, 2, 2, 2, 4, 4, 1, 1, 4]
def baseStart_3611327 : Nat := 118140960795 + 3611327 * 2 ^ 59
def prefixEnd_3611327 : Nat := 4983230072969 + 3 ^ 40 * 3611327 * 2
def baseEnd_3611327 : Nat := 1236231034372998266802877

theorem tailTrace_3611327 : CollatzResearch.WordTrace tailWord_3611327 prefixEnd_3611327 1236231034372998266802877 := by
  unfold tailWord_3611327
  simp only [CollatzResearch.WordTrace]
  refine ⟨131715916587786519393496235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87810611058524346262330823 131715916587786519393496235)
  ·
    refine ⟨197573874881679779090244353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131715916587786519393496235 197573874881679779090244353)
    ·
      refine ⟨148180406161259834317683265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197573874881679779090244353 148180406161259834317683265)
      ·
        refine ⟨111135304620944875738262449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148180406161259834317683265 111135304620944875738262449)
        ·
          refine ⟨83351478465708656803696837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111135304620944875738262449 83351478465708656803696837)
          ·
            refine ⟨15628402212320373150693157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83351478465708656803696837 15628402212320373150693157)
            ·
              refine ⟨2930325414810069965754967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15628402212320373150693157 2930325414810069965754967)
              ·
                refine ⟨4395488122215104948632451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2930325414810069965754967 4395488122215104948632451)
                ·
                  refine ⟨6593232183322657422948677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4395488122215104948632451 6593232183322657422948677)
                  ·
                    refine ⟨1236231034372998266802877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6593232183322657422948677 1236231034372998266802877)
                    ·
                      rfl

theorem cell22_3611327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 4, 1, 1, 4].length) (baseStart_3611327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3611327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3611327 prefixEnd_3611327 := by exact prefixLift 3611327
  have htrace : WordTrace (prefixWord ++ tailWord_3611327) baseStart_3611327 baseEnd_3611327 := by
    simpa [prefixWord, tailWord_3611327, baseEnd_3611327] using wordTrace_append hprefix tailTrace_3611327
  have hstable : (prefixWord ++ tailWord_3611327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611327).length < 2 ^ (prefixWord ++ tailWord_3611327).sum := by decide
  have hdescent : baseEnd_3611327 < baseStart_3611327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611342 : List Nat := [4, 1, 1, 1, 3, 2, 2, 4, 4]
def baseStart_3611342 : Nat := 118140960795 + 3611342 * 2 ^ 59
def prefixEnd_3611342 : Nat := 4983230072969 + 3 ^ 40 * 3611342 * 2
def baseEnd_3611342 : Nat := 412078723059847742559277

theorem tailTrace_3611342 : CollatzResearch.WordTrace tailWord_3611342 prefixEnd_3611342 412078723059847742559277 := by
  unfold tailWord_3611342
  simp only [CollatzResearch.WordTrace]
  refine ⟨16464557960341522119411535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87810975788488117970194853 16464557960341522119411535)
  ·
    refine ⟨24696836940512283179117303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16464557960341522119411535 24696836940512283179117303)
    ·
      refine ⟨37045255410768424768675955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24696836940512283179117303 37045255410768424768675955)
      ·
        refine ⟨55567883116152637153013933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37045255410768424768675955 55567883116152637153013933)
        ·
          refine ⟨20837956168557238932380225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55567883116152637153013933 20837956168557238932380225)
          ·
            refine ⟨15628467126417929199285169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20837956168557238932380225 15628467126417929199285169)
            ·
              refine ⟨11721350344813446899463877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15628467126417929199285169 11721350344813446899463877)
              ·
                refine ⟨2197753189652521293649477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11721350344813446899463877 2197753189652521293649477)
                ·
                  refine ⟨412078723059847742559277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2197753189652521293649477 412078723059847742559277)
                  ·
                    rfl

theorem cell22_3611342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 4, 4].length) (baseStart_3611342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3611342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3611342 prefixEnd_3611342 := by exact prefixLift 3611342
  have htrace : WordTrace (prefixWord ++ tailWord_3611342) baseStart_3611342 baseEnd_3611342 := by
    simpa [prefixWord, tailWord_3611342, baseEnd_3611342] using wordTrace_append hprefix tailTrace_3611342
  have hstable : (prefixWord ++ tailWord_3611342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611342).length < 2 ^ (prefixWord ++ tailWord_3611342).sum := by decide
  have hdescent : baseEnd_3611342 < baseStart_3611342 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611353 : List Nat := [1, 2, 1, 2, 3, 2, 2, 9]
def baseStart_3611353 : Nat := 118140960795 + 3611353 * 2 ^ 59
def prefixEnd_3611353 : Nat := 4983230072969 + 3 ^ 40 * 3611353 * 2
def baseEnd_3611353 : Nat := 137359992744926985072533

theorem tailTrace_3611353 : CollatzResearch.WordTrace tailWord_3611353 prefixEnd_3611353 137359992744926985072533 := by
  unfold tailWord_3611353
  simp only [CollatzResearch.WordTrace]
  refine ⟨131716864885692325833942713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87811243257128217222628475 131716864885692325833942713)
  ·
    refine ⟨98787648664269244375457035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131716864885692325833942713 98787648664269244375457035)
    ·
      refine ⟨148181472996403866563185553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98787648664269244375457035 148181472996403866563185553)
      ·
        refine ⟨111136104747302899922389165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148181472996403866563185553 111136104747302899922389165)
        ·
          refine ⟨41676039280238587470895937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111136104747302899922389165 41676039280238587470895937)
          ·
            refine ⟨31257029460178940603171953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41676039280238587470895937 31257029460178940603171953)
            ·
              refine ⟨23442772095134205452378965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31257029460178940603171953 23442772095134205452378965)
              ·
                refine ⟨137359992744926985072533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23442772095134205452378965 137359992744926985072533)
                ·
                  rfl

theorem cell22_3611353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 9].length) (baseStart_3611353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3611353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3611353 prefixEnd_3611353 := by exact prefixLift 3611353
  have htrace : WordTrace (prefixWord ++ tailWord_3611353) baseStart_3611353 baseEnd_3611353 := by
    simpa [prefixWord, tailWord_3611353, baseEnd_3611353] using wordTrace_append hprefix tailTrace_3611353
  have hstable : (prefixWord ++ tailWord_3611353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611353).length < 2 ^ (prefixWord ++ tailWord_3611353).sum := by decide
  have hdescent : baseEnd_3611353 < baseStart_3611353 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611383 : List Nat := [1, 1, 3, 1, 1, 1, 3, 2, 1, 8]
def baseStart_3611383 : Nat := 118140960795 + 3611383 * 2 ^ 59
def prefixEnd_3611383 : Nat := 4983230072969 + 3 ^ 40 * 3611383 * 2
def baseEnd_3611383 : Nat := 1236250204317432787402705

theorem tailTrace_3611383 : CollatzResearch.WordTrace tailWord_3611383 prefixEnd_3611383 1236250204317432787402705 := by
  unfold tailWord_3611383
  simp only [CollatzResearch.WordTrace]
  refine ⟨131717959075583640957534803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87811972717055760638356535 131717959075583640957534803)
  ·
    refine ⟨197576938613375461436302205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131717959075583640957534803 197576938613375461436302205)
    ·
      refine ⟨74091351980015798038613327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197576938613375461436302205 74091351980015798038613327)
      ·
        refine ⟨111137027970023697057919991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74091351980015798038613327 111137027970023697057919991)
        ·
          refine ⟨166705541955035545586879987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111137027970023697057919991 166705541955035545586879987)
          ·
            refine ⟨250058312932553318380319981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166705541955035545586879987 250058312932553318380319981)
            ·
              refine ⟨93771867349707494392619993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 250058312932553318380319981 93771867349707494392619993)
              ·
                refine ⟨70328900512280620794464995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93771867349707494392619993 70328900512280620794464995)
                ·
                  refine ⟨105493350768420931191697493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70328900512280620794464995 105493350768420931191697493)
                  ·
                    refine ⟨1236250204317432787402705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 105493350768420931191697493 1236250204317432787402705)
                    ·
                      rfl

theorem cell22_3611383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 8].length) (baseStart_3611383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3611383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3611383 prefixEnd_3611383 := by exact prefixLift 3611383
  have htrace : WordTrace (prefixWord ++ tailWord_3611383) baseStart_3611383 baseEnd_3611383 := by
    simpa [prefixWord, tailWord_3611383, baseEnd_3611383] using wordTrace_append hprefix tailTrace_3611383
  have hstable : (prefixWord ++ tailWord_3611383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611383).length < 2 ^ (prefixWord ++ tailWord_3611383).sum := by decide
  have hdescent : baseEnd_3611383 < baseStart_3611383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611385 : List Nat := [1, 2, 1, 3, 1, 1, 1, 4, 5, 3]
def baseStart_3611385 : Nat := 118140960795 + 3611385 * 2 ^ 59
def prefixEnd_3611385 : Nat := 4983230072969 + 3 ^ 40 * 3611385 * 2
def baseEnd_3611385 : Nat := 1236250888958305448852699

theorem tailTrace_3611385 : CollatzResearch.WordTrace tailWord_3611385 prefixEnd_3611385 1236250888958305448852699 := by
  unfold tailWord_3611385
  simp only [CollatzResearch.WordTrace]
  refine ⟨131718032021576395299107609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87812021347717596866071739 131718032021576395299107609)
  ·
    refine ⟨98788524016182296474330707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131718032021576395299107609 98788524016182296474330707)
    ·
      refine ⟨148182786024273444711496061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98788524016182296474330707 148182786024273444711496061)
      ·
        refine ⟨55568544759102541766811023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148182786024273444711496061 55568544759102541766811023)
        ·
          refine ⟨83352817138653812650216535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55568544759102541766811023 83352817138653812650216535)
          ·
            refine ⟨125029225707980718975324803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83352817138653812650216535 125029225707980718975324803)
            ·
              refine ⟨187543838561971078462987205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125029225707980718975324803 187543838561971078462987205)
              ·
                refine ⟨35164469730369577211810101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 187543838561971078462987205 35164469730369577211810101)
                ·
                  refine ⟨3296669037222147863607197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35164469730369577211810101 3296669037222147863607197)
                  ·
                    refine ⟨1236250888958305448852699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3296669037222147863607197 1236250888958305448852699)
                    ·
                      rfl

theorem cell22_3611385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 5, 3].length) (baseStart_3611385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3611385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3611385 prefixEnd_3611385 := by exact prefixLift 3611385
  have htrace : WordTrace (prefixWord ++ tailWord_3611385) baseStart_3611385 baseEnd_3611385 := by
    simpa [prefixWord, tailWord_3611385, baseEnd_3611385] using wordTrace_append hprefix tailTrace_3611385
  have hstable : (prefixWord ++ tailWord_3611385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611385).length < 2 ^ (prefixWord ++ tailWord_3611385).sum := by decide
  have hdescent : baseEnd_3611385 < baseStart_3611385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611492 : List Nat := [2, 3, 1, 1, 4, 1, 2, 2, 1, 5]
def baseStart_3611492 : Nat := 118140960795 + 3611492 * 2 ^ 59
def prefixEnd_3611492 : Nat := 4983230072969 + 3 ^ 40 * 3611492 * 2
def baseEnd_3611492 : Nat := 1236287517244992836427371

theorem tailTrace_3611492 : CollatzResearch.WordTrace tailWord_3611492 prefixEnd_3611492 1236287517244992836427371 := by
  unfold tailWord_3611492
  simp only [CollatzResearch.WordTrace]
  refine ⟨65860967316094376286626365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87814623088125835048835153 65860967316094376286626365)
  ·
    refine ⟨24697862743535391107484887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65860967316094376286626365 24697862743535391107484887)
    ·
      refine ⟨37046794115303086661227331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24697862743535391107484887 37046794115303086661227331)
      ·
        refine ⟨55570191172954629991840997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37046794115303086661227331 55570191172954629991840997)
        ·
          refine ⟨10419410844928993123470187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55570191172954629991840997 10419410844928993123470187)
          ·
            refine ⟨15629116267393489685205281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10419410844928993123470187 15629116267393489685205281)
            ·
              refine ⟨11721837200545117263903961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15629116267393489685205281 11721837200545117263903961)
              ·
                refine ⟨8791377900408837947927971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11721837200545117263903961 8791377900408837947927971)
                ·
                  refine ⟨13187066850613256921891957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8791377900408837947927971 13187066850613256921891957)
                  ·
                    refine ⟨1236287517244992836427371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13187066850613256921891957 1236287517244992836427371)
                    ·
                      rfl

theorem cell22_3611492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 2, 1, 5].length) (baseStart_3611492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3611492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3611492 prefixEnd_3611492 := by exact prefixLift 3611492
  have htrace : WordTrace (prefixWord ++ tailWord_3611492) baseStart_3611492 baseEnd_3611492 := by
    simpa [prefixWord, tailWord_3611492, baseEnd_3611492] using wordTrace_append hprefix tailTrace_3611492
  have hstable : (prefixWord ++ tailWord_3611492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611492).length < 2 ^ (prefixWord ++ tailWord_3611492).sum := by decide
  have hdescent : baseEnd_3611492 < baseStart_3611492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611496 : List Nat := [2, 1, 4, 2, 1, 4, 2, 1, 1, 4]
def baseStart_3611496 : Nat := 118140960795 + 3611496 * 2 ^ 59
def prefixEnd_3611496 : Nat := 4983230072969 + 3 ^ 40 * 3611496 * 2
def baseEnd_3611496 : Nat := 1236288886526738159327359

theorem tailTrace_3611496 : CollatzResearch.WordTrace tailWord_3611496 prefixEnd_3611496 1236288886526738159327359 := by
  unfold tailWord_3611496
  simp only [CollatzResearch.WordTrace]
  refine ⟨65861040262087130628199171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87814720349449507504265561 65861040262087130628199171)
  ·
    refine ⟨98791560393130695942298757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65861040262087130628199171 98791560393130695942298757)
    ·
      refine ⟨18523417573712005489181017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98791560393130695942298757 18523417573712005489181017)
      ·
        refine ⟨13892563180284004116885763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18523417573712005489181017 13892563180284004116885763)
        ·
          refine ⟨20838844770426006175328645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13892563180284004116885763 20838844770426006175328645)
          ·
            refine ⟨3907283394454876157874121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20838844770426006175328645 3907283394454876157874121)
            ·
              refine ⟨2930462545841157118405591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3907283394454876157874121 2930462545841157118405591)
              ·
                refine ⟨4395693818761735677608387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2930462545841157118405591 4395693818761735677608387)
                ·
                  refine ⟨6593540728142603516412581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4395693818761735677608387 6593540728142603516412581)
                  ·
                    refine ⟨1236288886526738159327359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6593540728142603516412581 1236288886526738159327359)
                    ·
                      rfl

theorem cell22_3611496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 2, 1, 1, 4].length) (baseStart_3611496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3611496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3611496 prefixEnd_3611496 := by exact prefixLift 3611496
  have htrace : WordTrace (prefixWord ++ tailWord_3611496) baseStart_3611496 baseEnd_3611496 := by
    simpa [prefixWord, tailWord_3611496, baseEnd_3611496] using wordTrace_append hprefix tailTrace_3611496
  have hstable : (prefixWord ++ tailWord_3611496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611496).length < 2 ^ (prefixWord ++ tailWord_3611496).sum := by decide
  have hdescent : baseEnd_3611496 < baseStart_3611496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611505 : List Nat := [1, 2, 2, 2, 1, 5, 9]
def baseStart_3611505 : Nat := 118140960795 + 3611505 * 2 ^ 59
def prefixEnd_3611505 : Nat := 4983230072969 + 3 ^ 40 * 3611505 * 2
def baseEnd_3611505 : Nat := 45788591385580190216753

theorem tailTrace_3611505 : CollatzResearch.WordTrace tailWord_3611505 prefixEnd_3611505 45788591385580190216753 := by
  unfold tailWord_3611505
  simp only [CollatzResearch.WordTrace]
  refine ⟨131722408781141655793475969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87814939187427770528983979 131722408781141655793475969)
  ·
    refine ⟨98791806585856241845106977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131722408781141655793475969 98791806585856241845106977)
    ·
      refine ⟨74093854939392181383830233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98791806585856241845106977 74093854939392181383830233)
      ·
        refine ⟨55570391204544136037872675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74093854939392181383830233 55570391204544136037872675)
        ·
          refine ⟨83355586806816204056809013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55570391204544136037872675 83355586806816204056809013)
          ·
            refine ⟨7814586263139019130325845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 83355586806816204056809013 7814586263139019130325845)
            ·
              refine ⟨45788591385580190216753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7814586263139019130325845 45788591385580190216753)
              ·
                rfl

theorem cell22_3611505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 9].length) (baseStart_3611505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3611505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3611505 prefixEnd_3611505 := by exact prefixLift 3611505
  have htrace : WordTrace (prefixWord ++ tailWord_3611505) baseStart_3611505 baseEnd_3611505 := by
    simpa [prefixWord, tailWord_3611505, baseEnd_3611505] using wordTrace_append hprefix tailTrace_3611505
  have hstable : (prefixWord ++ tailWord_3611505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611505).length < 2 ^ (prefixWord ++ tailWord_3611505).sum := by decide
  have hdescent : baseEnd_3611505 < baseStart_3611505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611509 : List Nat := [1, 3, 4, 1, 1, 3, 1, 1, 4, 3]
def baseStart_3611509 : Nat := 118140960795 + 3611509 * 2 ^ 59
def prefixEnd_3611509 : Nat := 4983230072969 + 3 ^ 40 * 3611509 * 2
def baseEnd_3611509 : Nat := 1236293336692410458752319

theorem tailTrace_3611509 : CollatzResearch.WordTrace tailWord_3611509 prefixEnd_3611509 1236293336692410458752319 := by
  unfold tailWord_3611509
  simp only [CollatzResearch.WordTrace]
  refine ⟨131722554673127164476621581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87815036448751442984414387 131722554673127164476621581)
  ·
    refine ⟨49395958002422686678733093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131722554673127164476621581 49395958002422686678733093)
    ·
      refine ⟨9261742125454253752262455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49395958002422686678733093 9261742125454253752262455)
      ·
        refine ⟨13892613188181380628393683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9261742125454253752262455 13892613188181380628393683)
        ·
          refine ⟨20838919782272070942590525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13892613188181380628393683 20838919782272070942590525)
          ·
            refine ⟨7814594918352026603471447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20838919782272070942590525 7814594918352026603471447)
            ·
              refine ⟨11721892377528039905207171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7814594918352026603471447 11721892377528039905207171)
              ·
                refine ⟨17582838566292059857810757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11721892377528039905207171 17582838566292059857810757)
                ·
                  refine ⟨3296782231179761223339517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17582838566292059857810757 3296782231179761223339517)
                  ·
                    refine ⟨1236293336692410458752319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3296782231179761223339517 1236293336692410458752319)
                    ·
                      rfl

theorem cell22_3611509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_3611509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3611509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3611509 prefixEnd_3611509 := by exact prefixLift 3611509
  have htrace : WordTrace (prefixWord ++ tailWord_3611509) baseStart_3611509 baseEnd_3611509 := by
    simpa [prefixWord, tailWord_3611509, baseEnd_3611509] using wordTrace_append hprefix tailTrace_3611509
  have hstable : (prefixWord ++ tailWord_3611509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611509).length < 2 ^ (prefixWord ++ tailWord_3611509).sum := by decide
  have hdescent : baseEnd_3611509 < baseStart_3611509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611582 : List Nat := [4, 2, 1, 1, 1, 2, 2, 1, 1, 7]
def baseStart_3611582 : Nat := 118140960795 + 3611582 * 2 ^ 59
def prefixEnd_3611582 : Nat := 4983230072969 + 3 ^ 40 * 3611582 * 2
def baseEnd_3611582 : Nat := 1236318326084262601677095

theorem tailTrace_3611582 : CollatzResearch.WordTrace tailWord_3611582 prefixEnd_3611582 1236318326084262601677095 := by
  unfold tailWord_3611582
  simp only [CollatzResearch.WordTrace]
  refine ⟨16465652150232837243003625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87816811467908465296019333 16465652150232837243003625)
  ·
    refine ⟨12349239112674627932252719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16465652150232837243003625 12349239112674627932252719)
    ·
      refine ⟨18523858669011941898379079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12349239112674627932252719 18523858669011941898379079)
      ·
        refine ⟨27785788003517912847568619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18523858669011941898379079 27785788003517912847568619)
        ·
          refine ⟨41678682005276869271352929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27785788003517912847568619 41678682005276869271352929)
          ·
            refine ⟨31259011503957651953514697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41678682005276869271352929 31259011503957651953514697)
            ·
              refine ⟨23444258627968238965136023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31259011503957651953514697 23444258627968238965136023)
              ·
                refine ⟨35166387941952358447704035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23444258627968238965136023 35166387941952358447704035)
                ·
                  refine ⟨52749581912928537671556053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35166387941952358447704035 52749581912928537671556053)
                  ·
                    refine ⟨1236318326084262601677095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52749581912928537671556053 1236318326084262601677095)
                    ·
                      rfl

theorem cell22_3611582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_3611582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3611582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3611582 prefixEnd_3611582 := by exact prefixLift 3611582
  have htrace : WordTrace (prefixWord ++ tailWord_3611582) baseStart_3611582 baseEnd_3611582 := by
    simpa [prefixWord, tailWord_3611582, baseEnd_3611582] using wordTrace_append hprefix tailTrace_3611582
  have hstable : (prefixWord ++ tailWord_3611582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611582).length < 2 ^ (prefixWord ++ tailWord_3611582).sum := by decide
  have hdescent : baseEnd_3611582 < baseStart_3611582 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611584 : List Nat := [2, 1, 1, 2, 3, 3, 4, 1, 5]
def baseStart_3611584 : Nat := 118140960795 + 3611584 * 2 ^ 59
def prefixEnd_3611584 : Nat := 4983230072969 + 3 ^ 40 * 3611584 * 2
def baseEnd_3611584 : Nat := 412106336908378421042363

theorem tailTrace_3611584 : CollatzResearch.WordTrace tailWord_3611584 prefixEnd_3611584 412106336908378421042363 := by
  unfold tailWord_3611584
  simp only [CollatzResearch.WordTrace]
  refine ⟨65862645073927726142800903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87816860098570301523734537 65862645073927726142800903)
  ·
    refine ⟨98793967610891589214201355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65862645073927726142800903 98793967610891589214201355)
    ·
      refine ⟨148190951416337383821302033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98793967610891589214201355 148190951416337383821302033)
      ·
        refine ⟨111143213562253037865976525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148190951416337383821302033 111143213562253037865976525)
        ·
          refine ⟨41678705085844889199741197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111143213562253037865976525 41678705085844889199741197)
          ·
            refine ⟨15629514407191833449902949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41678705085844889199741197 15629514407191833449902949)
            ·
              refine ⟨2930533951348468771856803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15629514407191833449902949 2930533951348468771856803)
              ·
                refine ⟨4395800927022703157785205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2930533951348468771856803 4395800927022703157785205)
                ·
                  refine ⟨412106336908378421042363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4395800927022703157785205 412106336908378421042363)
                  ·
                    rfl

theorem cell22_3611584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 4, 1, 5].length) (baseStart_3611584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3611584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3611584 prefixEnd_3611584 := by exact prefixLift 3611584
  have htrace : WordTrace (prefixWord ++ tailWord_3611584) baseStart_3611584 baseEnd_3611584 := by
    simpa [prefixWord, tailWord_3611584, baseEnd_3611584] using wordTrace_append hprefix tailTrace_3611584
  have hstable : (prefixWord ++ tailWord_3611584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611584).length < 2 ^ (prefixWord ++ tailWord_3611584).sum := by decide
  have hdescent : baseEnd_3611584 < baseStart_3611584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611642 : List Nat := [3, 1, 1, 1, 1, 2, 1, 4, 4, 4]
def baseStart_3611642 : Nat := 118140960795 + 3611642 * 2 ^ 59
def prefixEnd_3611642 : Nat := 4983230072969 + 3 ^ 40 * 3611642 * 2
def baseEnd_3611642 : Nat := 1236338865310442445176911

theorem tailTrace_3611642 : CollatzResearch.WordTrace tailWord_3611642 prefixEnd_3611642 1236338865310442445176911 := by
  unfold tailWord_3611642
  simp only [CollatzResearch.WordTrace]
  refine ⟨32931851395411332047803295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87818270387763552127475453 32931851395411332047803295)
  ·
    refine ⟨49397777093116998071704943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32931851395411332047803295 49397777093116998071704943)
    ·
      refine ⟨74096665639675497107557415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49397777093116998071704943 74096665639675497107557415)
      ·
        refine ⟨111144998459513245661336123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74096665639675497107557415 111144998459513245661336123)
        ·
          refine ⟨166717497689269868492004185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111144998459513245661336123 166717497689269868492004185)
          ·
            refine ⟨125038123266952401369003139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166717497689269868492004185 125038123266952401369003139)
            ·
              refine ⟨187557184900428602053504709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125038123266952401369003139 187557184900428602053504709)
              ·
                refine ⟨35166972168830362885032133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 187557184900428602053504709 35166972168830362885032133)
                ·
                  refine ⟨6593807281655693040943525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35166972168830362885032133 6593807281655693040943525)
                  ·
                    refine ⟨1236338865310442445176911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6593807281655693040943525 1236338865310442445176911)
                    ·
                      rfl

theorem cell22_3611642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 4, 4].length) (baseStart_3611642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3611642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3611642 prefixEnd_3611642 := by exact prefixLift 3611642
  have htrace : WordTrace (prefixWord ++ tailWord_3611642) baseStart_3611642 baseEnd_3611642 := by
    simpa [prefixWord, tailWord_3611642, baseEnd_3611642] using wordTrace_append hprefix tailTrace_3611642
  have hstable : (prefixWord ++ tailWord_3611642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611642).length < 2 ^ (prefixWord ++ tailWord_3611642).sum := by decide
  have hdescent : baseEnd_3611642 < baseStart_3611642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611644 : List Nat := [2, 2, 2, 1, 2, 4, 2, 1, 1, 5]
def baseStart_3611644 : Nat := 118140960795 + 3611644 * 2 ^ 59
def prefixEnd_3611644 : Nat := 4983230072969 + 3 ^ 40 * 3611644 * 2
def baseEnd_3611644 : Nat := 1236339549951315106626905

theorem tailTrace_3611644 : CollatzResearch.WordTrace tailWord_3611644 prefixEnd_3611644 1236339549951315106626905 := by
  unfold tailWord_3611644
  simp only [CollatzResearch.WordTrace]
  refine ⟨65863739263819041266392993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87818319018425388355190657 65863739263819041266392993)
  ·
    refine ⟨49397804447864280949794745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65863739263819041266392993 49397804447864280949794745)
    ·
      refine ⟨37048353335898210712346059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49397804447864280949794745 37048353335898210712346059)
      ·
        refine ⟨55572530003847316068519089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37048353335898210712346059 55572530003847316068519089)
        ·
          refine ⟨41679397502885487051389317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55572530003847316068519089 41679397502885487051389317)
          ·
            refine ⟨7814887031791028822135497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41679397502885487051389317 7814887031791028822135497)
            ·
              refine ⟨5861165273843271616601623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7814887031791028822135497 5861165273843271616601623)
              ·
                refine ⟨8791747910764907424902435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5861165273843271616601623 8791747910764907424902435)
                ·
                  refine ⟨13187621866147361137353653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8791747910764907424902435 13187621866147361137353653)
                  ·
                    refine ⟨1236339549951315106626905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13187621866147361137353653 1236339549951315106626905)
                    ·
                      rfl

theorem cell22_3611644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 1, 1, 5].length) (baseStart_3611644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3611644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3611644 prefixEnd_3611644 := by exact prefixLift 3611644
  have htrace : WordTrace (prefixWord ++ tailWord_3611644) baseStart_3611644 baseEnd_3611644 := by
    simpa [prefixWord, tailWord_3611644, baseEnd_3611644] using wordTrace_append hprefix tailTrace_3611644
  have hstable : (prefixWord ++ tailWord_3611644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611644).length < 2 ^ (prefixWord ++ tailWord_3611644).sum := by decide
  have hdescent : baseEnd_3611644 < baseStart_3611644 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611646 : List Nat := [4, 2, 2, 2, 2, 1, 1, 2, 6]
def baseStart_3611646 : Nat := 118140960795 + 3611646 * 2 ^ 59
def prefixEnd_3611646 : Nat := 4983230072969 + 3 ^ 40 * 3611646 * 2
def baseEnd_3611646 : Nat := 412113411530729256025633

theorem tailTrace_3611646 : CollatzResearch.WordTrace tailWord_3611646 prefixEnd_3611646 412113411530729256025633 := by
  unfold tailWord_3611646
  simp only [CollatzResearch.WordTrace]
  refine ⟨16465943934203854609294849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87818367649087224582905861 16465943934203854609294849)
  ·
    refine ⟨12349457950652890956971137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16465943934203854609294849 12349457950652890956971137)
    ·
      refine ⟨9262093462989668217728353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12349457950652890956971137 9262093462989668217728353)
      ·
        refine ⟨6946570097242251163296265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9262093462989668217728353 6946570097242251163296265)
        ·
          refine ⟨5209927572931688372472199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6946570097242251163296265 5209927572931688372472199)
          ·
            refine ⟨7814891359397532558708299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5209927572931688372472199 7814891359397532558708299)
            ·
              refine ⟨11722337039096298838062449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7814891359397532558708299 11722337039096298838062449)
              ·
                refine ⟨8791752779322224128546837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11722337039096298838062449 8791752779322224128546837)
                ·
                  refine ⟨412113411530729256025633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8791752779322224128546837 412113411530729256025633)
                  ·
                    rfl

theorem cell22_3611646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 2, 6].length) (baseStart_3611646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3611646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3611646 prefixEnd_3611646 := by exact prefixLift 3611646
  have htrace : WordTrace (prefixWord ++ tailWord_3611646) baseStart_3611646 baseEnd_3611646 := by
    simpa [prefixWord, tailWord_3611646, baseEnd_3611646] using wordTrace_append hprefix tailTrace_3611646
  have hstable : (prefixWord ++ tailWord_3611646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611646).length < 2 ^ (prefixWord ++ tailWord_3611646).sum := by decide
  have hdescent : baseEnd_3611646 < baseStart_3611646 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611659 : List Nat := [1, 1, 1, 1, 6, 2, 3, 1, 2, 4]
def baseStart_3611659 : Nat := 118140960795 + 3611659 * 2 ^ 59
def prefixEnd_3611659 : Nat := 4983230072969 + 3 ^ 40 * 3611659 * 2
def baseEnd_3611659 : Nat := 1236344684757860067501859

theorem tailTrace_3611659 : CollatzResearch.WordTrace tailWord_3611659 prefixEnd_3611659 1236344684757860067501859 := by
  unfold tailWord_3611659
  simp only [CollatzResearch.WordTrace]
  refine ⟨131728025622583740094582031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87818683748389160063054687 131728025622583740094582031)
  ·
    refine ⟨197592038433875610141873047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131728025622583740094582031 197592038433875610141873047)
    ·
      refine ⟨296388057650813415212809571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197592038433875610141873047 296388057650813415212809571)
      ·
        refine ⟨444582086476220122819214357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296388057650813415212809571 444582086476220122819214357)
        ·
          refine ⟨20839785303572818257150673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 444582086476220122819214357 20839785303572818257150673)
          ·
            refine ⟨15629838977679613692863005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20839785303572818257150673 15629838977679613692863005)
            ·
              refine ⟨5861189616629855134823627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15629838977679613692863005 5861189616629855134823627)
              ·
                refine ⟨8791784424944782702235441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5861189616629855134823627 8791784424944782702235441)
                ·
                  refine ⟨6593838318708587026676581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8791784424944782702235441 6593838318708587026676581)
                  ·
                    refine ⟨1236344684757860067501859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6593838318708587026676581 1236344684757860067501859)
                    ·
                      rfl

theorem cell22_3611659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 1, 2, 4].length) (baseStart_3611659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3611659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3611659 prefixEnd_3611659 := by exact prefixLift 3611659
  have htrace : WordTrace (prefixWord ++ tailWord_3611659) baseStart_3611659 baseEnd_3611659 := by
    simpa [prefixWord, tailWord_3611659, baseEnd_3611659] using wordTrace_append hprefix tailTrace_3611659
  have hstable : (prefixWord ++ tailWord_3611659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611659).length < 2 ^ (prefixWord ++ tailWord_3611659).sum := by decide
  have hdescent : baseEnd_3611659 < baseStart_3611659 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611717 : List Nat := [1, 3, 1, 1, 1, 3, 2, 2, 1, 7]
def baseStart_3611717 : Nat := 118140960795 + 3611717 * 2 ^ 59
def prefixEnd_3611717 : Nat := 4983230072969 + 3 ^ 40 * 3611717 * 2
def baseEnd_3611717 : Nat := 1236364539343167249551681

theorem tailTrace_3611717 : CollatzResearch.WordTrace tailWord_3611717 prefixEnd_3611717 1236364539343167249551681 := by
  unfold tailWord_3611717
  simp only [CollatzResearch.WordTrace]
  refine ⟨131730141056373616000193405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87820094037582410666795603 131730141056373616000193405)
  ·
    refine ⟨49398802896140106000072527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131730141056373616000193405 49398802896140106000072527)
    ·
      refine ⟨74098204344210159000108791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49398802896140106000072527 74098204344210159000108791)
      ·
        refine ⟨111147306516315238500163187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74098204344210159000108791 111147306516315238500163187)
        ·
          refine ⟨166720959774472857750244781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111147306516315238500163187 166720959774472857750244781)
          ·
            refine ⟨62520359915427321656341793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166720959774472857750244781 62520359915427321656341793)
            ·
              refine ⟨46890269936570491242256345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62520359915427321656341793 46890269936570491242256345)
              ·
                refine ⟨35167702452427868431692259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46890269936570491242256345 35167702452427868431692259)
                ·
                  refine ⟨52751553678641802647538389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35167702452427868431692259 52751553678641802647538389)
                  ·
                    refine ⟨1236364539343167249551681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52751553678641802647538389 1236364539343167249551681)
                    ·
                      rfl

theorem cell22_3611717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 7].length) (baseStart_3611717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3611717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3611717 prefixEnd_3611717 := by exact prefixLift 3611717
  have htrace : WordTrace (prefixWord ++ tailWord_3611717) baseStart_3611717 baseEnd_3611717 := by
    simpa [prefixWord, tailWord_3611717, baseEnd_3611717] using wordTrace_append hprefix tailTrace_3611717
  have hstable : (prefixWord ++ tailWord_3611717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611717).length < 2 ^ (prefixWord ++ tailWord_3611717).sum := by decide
  have hdescent : baseEnd_3611717 < baseStart_3611717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611740 : List Nat := [2, 2, 4, 1, 1, 1, 5, 2, 1, 3]
def baseStart_3611740 : Nat := 118140960795 + 3611740 * 2 ^ 59
def prefixEnd_3611740 : Nat := 4983230072969 + 3 ^ 40 * 3611740 * 2
def baseEnd_3611740 : Nat := 1236372412713202856226611

theorem tailTrace_3611740 : CollatzResearch.WordTrace tailWord_3611740 prefixEnd_3611740 1236372412713202856226611 := by
  unfold tailWord_3611740
  simp only [CollatzResearch.WordTrace]
  refine ⟨65865489967645145464140337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87820653290193527285520449 65865489967645145464140337)
  ·
    refine ⟨49399117475733859098105253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65865489967645145464140337 49399117475733859098105253)
    ·
      refine ⟨9262334526700098580894735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49399117475733859098105253 9262334526700098580894735)
      ·
        refine ⟨13893501790050147871342103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9262334526700098580894735 13893501790050147871342103)
        ·
          refine ⟨20840252685075221807013155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13893501790050147871342103 20840252685075221807013155)
          ·
            refine ⟨31260379027612832710519733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20840252685075221807013155 31260379027612832710519733)
            ·
              refine ⟨2930660533838703066611225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31260379027612832710519733 2930660533838703066611225)
              ·
                refine ⟨2197995400379027299958419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2930660533838703066611225 2197995400379027299958419)
                ·
                  refine ⟨3296993100568540949937629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2197995400379027299958419 3296993100568540949937629)
                  ·
                    refine ⟨1236372412713202856226611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3296993100568540949937629 1236372412713202856226611)
                    ·
                      rfl

theorem cell22_3611740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_3611740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3611740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3611740 prefixEnd_3611740 := by exact prefixLift 3611740
  have htrace : WordTrace (prefixWord ++ tailWord_3611740) baseStart_3611740 baseEnd_3611740 := by
    simpa [prefixWord, tailWord_3611740, baseEnd_3611740] using wordTrace_append hprefix tailTrace_3611740
  have hstable : (prefixWord ++ tailWord_3611740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611740).length < 2 ^ (prefixWord ++ tailWord_3611740).sum := by decide
  have hdescent : baseEnd_3611740 < baseStart_3611740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611749 : List Nat := [1, 3, 1, 3, 2, 1, 2, 2, 3, 4]
def baseStart_3611749 : Nat := 118140960795 + 3611749 * 2 ^ 59
def prefixEnd_3611749 : Nat := 4983230072969 + 3 ^ 40 * 3611749 * 2
def baseEnd_3611749 : Nat := 1236375493597129832751583

theorem tailTrace_3611749 : CollatzResearch.WordTrace tailWord_3611749 prefixEnd_3611749 1236375493597129832751583 := by
  unfold tailWord_3611749
  simp only [CollatzResearch.WordTrace]
  refine ⟨131731308192257685465358301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87820872128171790310238867 131731308192257685465358301)
  ·
    refine ⟨49399240572096632049509363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131731308192257685465358301 49399240572096632049509363)
    ·
      refine ⟨74098860858144948074264045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49399240572096632049509363 74098860858144948074264045)
      ·
        refine ⟨27787072821804355527849017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74098860858144948074264045 27787072821804355527849017)
        ·
          refine ⟨20840304616353266645886763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27787072821804355527849017 20840304616353266645886763)
          ·
            refine ⟨31260456924529899968830145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20840304616353266645886763 31260456924529899968830145)
            ·
              refine ⟨23445342693397424976622609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31260456924529899968830145 23445342693397424976622609)
              ·
                refine ⟨17584007020048068732466957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23445342693397424976622609 17584007020048068732466957)
                ·
                  refine ⟨6594002632518025774675109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17584007020048068732466957 6594002632518025774675109)
                  ·
                    refine ⟨1236375493597129832751583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6594002632518025774675109 1236375493597129832751583)
                    ·
                      rfl

theorem cell22_3611749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 3, 4].length) (baseStart_3611749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3611749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3611749 prefixEnd_3611749 := by exact prefixLift 3611749
  have htrace : WordTrace (prefixWord ++ tailWord_3611749) baseStart_3611749 baseEnd_3611749 := by
    simpa [prefixWord, tailWord_3611749, baseEnd_3611749] using wordTrace_append hprefix tailTrace_3611749
  have hstable : (prefixWord ++ tailWord_3611749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611749).length < 2 ^ (prefixWord ++ tailWord_3611749).sum := by decide
  have hdescent : baseEnd_3611749 < baseStart_3611749 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611766 : List Nat := [5, 1, 1, 2, 1, 1, 3, 1, 3, 4]
def baseStart_3611766 : Nat := 118140960795 + 3611766 * 2 ^ 59
def prefixEnd_3611766 : Nat := 4983230072969 + 3 ^ 40 * 3611766 * 2
def baseEnd_3611766 : Nat := 1236381313044547455076531

theorem tailTrace_3611766 : CollatzResearch.WordTrace tailWord_3611766 prefixEnd_3611766 1236381313044547455076531 := by
  unfold tailWord_3611766
  simp only [CollatzResearch.WordTrace]
  refine ⟨8233245514574756085545447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87821285488797398245818101 8233245514574756085545447)
  ·
    refine ⟨12349868271862134128318171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8233245514574756085545447 12349868271862134128318171)
    ·
      refine ⟨18524802407793201192477257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12349868271862134128318171 18524802407793201192477257)
      ·
        refine ⟨13893601805844900894357943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18524802407793201192477257 13893601805844900894357943)
        ·
          refine ⟨20840402708767351341536915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13893601805844900894357943 20840402708767351341536915)
          ·
            refine ⟨31260604063151027012305373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20840402708767351341536915 31260604063151027012305373)
            ·
              refine ⟨11722726523681635129614515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31260604063151027012305373 11722726523681635129614515)
              ·
                refine ⟨17584089785522452694421773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11722726523681635129614515 17584089785522452694421773)
                ·
                  refine ⟨6594033669570919760408165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17584089785522452694421773 6594033669570919760408165)
                  ·
                    refine ⟨1236381313044547455076531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6594033669570919760408165 1236381313044547455076531)
                    ·
                      rfl

theorem cell22_3611766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_3611766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3611766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3611766 prefixEnd_3611766 := by exact prefixLift 3611766
  have htrace : WordTrace (prefixWord ++ tailWord_3611766) baseStart_3611766 baseEnd_3611766 := by
    simpa [prefixWord, tailWord_3611766, baseEnd_3611766] using wordTrace_append hprefix tailTrace_3611766
  have hstable : (prefixWord ++ tailWord_3611766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611766).length < 2 ^ (prefixWord ++ tailWord_3611766).sum := by decide
  have hdescent : baseEnd_3611766 < baseStart_3611766 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611779 : List Nat := [1, 1, 1, 3, 3, 2, 3, 2, 1, 5]
def baseStart_3611779 : Nat := 118140960795 + 3611779 * 2 ^ 59
def prefixEnd_3611779 : Nat := 4983230072969 + 3 ^ 40 * 3611779 * 2
def baseEnd_3611779 : Nat := 1236385763210219754501491

theorem tailTrace_3611779 : CollatzResearch.WordTrace tailWord_3611779 prefixEnd_3611779 1236385763210219754501491 := by
  unfold tailWord_3611779
  simp only [CollatzResearch.WordTrace]
  refine ⟨131732402382149000588950391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87821601588099333725966927 131732402382149000588950391)
  ·
    refine ⟨197598603573223500883425587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131732402382149000588950391 197598603573223500883425587)
    ·
      refine ⟨296397905359835251325138381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197598603573223500883425587 296397905359835251325138381)
      ·
        refine ⟨111149214509938219246926893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 296397905359835251325138381 111149214509938219246926893)
        ·
          refine ⟨41680955441226832217597585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111149214509938219246926893 41680955441226832217597585)
          ·
            refine ⟨31260716580920124163198189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41680955441226832217597585 31260716580920124163198189)
            ·
              refine ⟨11722768717845046561199321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31260716580920124163198189 11722768717845046561199321)
              ·
                refine ⟨8792076538383784920899491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11722768717845046561199321 8792076538383784920899491)
                ·
                  refine ⟨13188114807575677381349237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8792076538383784920899491 13188114807575677381349237)
                  ·
                    refine ⟨1236385763210219754501491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13188114807575677381349237 1236385763210219754501491)
                    ·
                      rfl

theorem cell22_3611779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 2, 1, 5].length) (baseStart_3611779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3611779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3611779 prefixEnd_3611779 := by exact prefixLift 3611779
  have htrace : WordTrace (prefixWord ++ tailWord_3611779) baseStart_3611779 baseEnd_3611779 := by
    simpa [prefixWord, tailWord_3611779, baseEnd_3611779] using wordTrace_append hprefix tailTrace_3611779
  have hstable : (prefixWord ++ tailWord_3611779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611779).length < 2 ^ (prefixWord ++ tailWord_3611779).sum := by decide
  have hdescent : baseEnd_3611779 < baseStart_3611779 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611826 : List Nat := [3, 2, 1, 1, 1, 5, 3, 6]
def baseStart_3611826 : Nat := 118140960795 + 3611826 * 2 ^ 59
def prefixEnd_3611826 : Nat := 4983230072969 + 3 ^ 40 * 3611826 * 2
def baseEnd_3611826 : Nat := 137377983585636366508483

theorem tailTrace_3611826 : CollatzResearch.WordTrace tailWord_3611826 prefixEnd_3611826 137377983585636366508483 := by
  unfold tailWord_3611826
  simp only [CollatzResearch.WordTrace]
  refine ⟨32933529153244681903977833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87822744408652485077274221 32933529153244681903977833)
  ·
    refine ⟨24700146864933511427983375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32933529153244681903977833 24700146864933511427983375)
    ·
      refine ⟨37050220297400267141975063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24700146864933511427983375 37050220297400267141975063)
      ·
        refine ⟨55575330446100400712962595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37050220297400267141975063 55575330446100400712962595)
        ·
          refine ⟨83362995669150601069443893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55575330446100400712962595 83362995669150601069443893)
          ·
            refine ⟨7815280843982868850260365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 83362995669150601069443893 7815280843982868850260365)
            ·
              refine ⟨2930730316493575818847637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7815280843982868850260365 2930730316493575818847637)
              ·
                refine ⟨137377983585636366508483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2930730316493575818847637 137377983585636366508483)
                ·
                  rfl

theorem cell22_3611826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 3, 6].length) (baseStart_3611826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3611826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3611826 prefixEnd_3611826 := by exact prefixLift 3611826
  have htrace : WordTrace (prefixWord ++ tailWord_3611826) baseStart_3611826 baseEnd_3611826 := by
    simpa [prefixWord, tailWord_3611826, baseEnd_3611826] using wordTrace_append hprefix tailTrace_3611826
  have hstable : (prefixWord ++ tailWord_3611826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611826).length < 2 ^ (prefixWord ++ tailWord_3611826).sum := by decide
  have hdescent : baseEnd_3611826 < baseStart_3611826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611858 : List Nat := [3, 2, 2, 2, 1, 1, 4, 1, 3, 3]
def baseStart_3611858 : Nat := 118140960795 + 3611858 * 2 ^ 59
def prefixEnd_3611858 : Nat := 4983230072969 + 3 ^ 40 * 3611858 * 2
def baseEnd_3611858 : Nat := 1236412806524689881776249

theorem tailTrace_3611858 : CollatzResearch.WordTrace tailWord_3611858 prefixEnd_3611858 1236412806524689881776249 := by
  unfold tailWord_3611858
  simp only [CollatzResearch.WordTrace]
  refine ⟨32933820937215699270269057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87823522499241864720717485 32933820937215699270269057)
  ·
    refine ⟨24700365702911774452701793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32933820937215699270269057 24700365702911774452701793)
    ·
      refine ⟨18525274277183830839526345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24700365702911774452701793 18525274277183830839526345)
      ·
        refine ⟨13893955707887873129644759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18525274277183830839526345 13893955707887873129644759)
        ·
          refine ⟨20840933561831809694467139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13893955707887873129644759 20840933561831809694467139)
          ·
            refine ⟨31261400342747714541700709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20840933561831809694467139 31261400342747714541700709)
            ·
              refine ⟨5861512564265196476568883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31261400342747714541700709 5861512564265196476568883)
              ·
                refine ⟨8792268846397794714853325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5861512564265196476568883 8792268846397794714853325)
                ·
                  refine ⟨3297100817399173018069997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8792268846397794714853325 3297100817399173018069997)
                  ·
                    refine ⟨1236412806524689881776249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3297100817399173018069997 1236412806524689881776249)
                    ·
                      rfl

theorem cell22_3611858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 1, 3, 3].length) (baseStart_3611858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3611858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3611858 prefixEnd_3611858 := by exact prefixLift 3611858
  have htrace : WordTrace (prefixWord ++ tailWord_3611858) baseStart_3611858 baseEnd_3611858 := by
    simpa [prefixWord, tailWord_3611858, baseEnd_3611858] using wordTrace_append hprefix tailTrace_3611858
  have hstable : (prefixWord ++ tailWord_3611858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611858).length < 2 ^ (prefixWord ++ tailWord_3611858).sum := by decide
  have hdescent : baseEnd_3611858 < baseStart_3611858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611916 : List Nat := [2, 2, 1, 2, 2, 3, 3, 1, 6]
def baseStart_3611916 : Nat := 118140960795 + 3611916 * 2 ^ 59
def prefixEnd_3611916 : Nat := 4983230072969 + 3 ^ 40 * 3611916 * 2
def baseEnd_3611916 : Nat := 412144220369999021275357

theorem tailTrace_3611916 : CollatzResearch.WordTrace tailWord_3611916 prefixEnd_3611916 412144220369999021275357 := by
  unfold tailWord_3611916
  simp only [CollatzResearch.WordTrace]
  refine ⟨65868699591326336493343801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87824932788435115324458401 65868699591326336493343801)
  ·
    refine ⟨49401524693494752370007851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65868699591326336493343801 49401524693494752370007851)
    ·
      refine ⟨74102287040242128555011777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49401524693494752370007851 74102287040242128555011777)
      ·
        refine ⟨55576715280181596416258833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74102287040242128555011777 55576715280181596416258833)
        ·
          refine ⟨41682536460136197312194125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55576715280181596416258833 41682536460136197312194125)
          ·
            refine ⟨15630951172551073992072797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41682536460136197312194125 15630951172551073992072797)
            ·
              refine ⟨5861606689706652747027299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15630951172551073992072797 5861606689706652747027299)
              ·
                refine ⟨8792410034559979120540949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5861606689706652747027299 8792410034559979120540949)
                ·
                  refine ⟨412144220369999021275357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8792410034559979120540949 412144220369999021275357)
                  ·
                    rfl

theorem cell22_3611916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 1, 6].length) (baseStart_3611916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3611916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3611916 prefixEnd_3611916 := by exact prefixLift 3611916
  have htrace : WordTrace (prefixWord ++ tailWord_3611916) baseStart_3611916 baseEnd_3611916 := by
    simpa [prefixWord, tailWord_3611916, baseEnd_3611916] using wordTrace_append hprefix tailTrace_3611916
  have hstable : (prefixWord ++ tailWord_3611916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611916).length < 2 ^ (prefixWord ++ tailWord_3611916).sum := by decide
  have hdescent : baseEnd_3611916 < baseStart_3611916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611935 : List Nat := [1, 1, 2, 4, 4, 2, 1, 2, 1, 4]
def baseStart_3611935 : Nat := 118140960795 + 3611935 * 2 ^ 59
def prefixEnd_3611935 : Nat := 4983230072969 + 3 ^ 40 * 3611935 * 2
def baseEnd_3611935 : Nat := 1236439165198287347601013

theorem tailTrace_3611935 : CollatzResearch.WordTrace tailWord_3611935 prefixEnd_3611935 1236439165198287347601013 := by
  unfold tailWord_3611935
  simp only [CollatzResearch.WordTrace]
  refine ⟨131738092169583839231629259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87825394779722559487752839 131738092169583839231629259)
  ·
    refine ⟨197607138254375758847443889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131738092169583839231629259 197607138254375758847443889)
    ·
      refine ⟨148205353690781819135582917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197607138254375758847443889 148205353690781819135582917)
      ·
        refine ⟨27788503817021591087921797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148205353690781819135582917 27788503817021591087921797)
        ·
          refine ⟨5210344465691548328985337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27788503817021591087921797 5210344465691548328985337)
          ·
            refine ⟨3907758349268661246739003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5210344465691548328985337 3907758349268661246739003)
            ·
              refine ⟨5861637523902991870108505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3907758349268661246739003 5861637523902991870108505)
              ·
                refine ⟨4396228142927243902581379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5861637523902991870108505 4396228142927243902581379)
                ·
                  refine ⟨6594342214390865853872069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4396228142927243902581379 6594342214390865853872069)
                  ·
                    refine ⟨1236439165198287347601013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6594342214390865853872069 1236439165198287347601013)
                    ·
                      rfl

theorem cell22_3611935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 2, 1, 4].length) (baseStart_3611935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3611935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3611935 prefixEnd_3611935 := by exact prefixLift 3611935
  have htrace : WordTrace (prefixWord ++ tailWord_3611935) baseStart_3611935 baseEnd_3611935 := by
    simpa [prefixWord, tailWord_3611935, baseEnd_3611935] using wordTrace_append hprefix tailTrace_3611935
  have hstable : (prefixWord ++ tailWord_3611935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611935).length < 2 ^ (prefixWord ++ tailWord_3611935).sum := by decide
  have hdescent : baseEnd_3611935 < baseStart_3611935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611961 : List Nat := [1, 2, 1, 6, 2, 10]
def baseStart_3611961 : Nat := 118140960795 + 3611961 * 2 ^ 59
def prefixEnd_3611961 : Nat := 4983230072969 + 3 ^ 40 * 3611961 * 2
def baseEnd_3611961 : Nat := 15264790932464591931493

theorem tailTrace_3611961 : CollatzResearch.WordTrace tailWord_3611961 prefixEnd_3611961 15264790932464591931493 := by
  unfold tailWord_3611961
  simp only [CollatzResearch.WordTrace]
  refine ⟨131739040467489645672075737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87826026978326430448050491 131739040467489645672075737)
  ·
    refine ⟨98804280350617234254056803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131739040467489645672075737 98804280350617234254056803)
    ·
      refine ⟨148206420525925851381085205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98804280350617234254056803 148206420525925851381085205)
      ·
        refine ⟨6947175962152774283488369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 148206420525925851381085205 6947175962152774283488369)
        ·
          refine ⟨5210381971614580712616277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6947175962152774283488369 5210381971614580712616277)
          ·
            refine ⟨15264790932464591931493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5210381971614580712616277 15264790932464591931493)
            ·
              rfl

theorem cell22_3611961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 10].length) (baseStart_3611961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3611961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3611961 prefixEnd_3611961 := by exact prefixLift 3611961
  have htrace : WordTrace (prefixWord ++ tailWord_3611961) baseStart_3611961 baseEnd_3611961 := by
    simpa [prefixWord, tailWord_3611961, baseEnd_3611961] using wordTrace_append hprefix tailTrace_3611961
  have hstable : (prefixWord ++ tailWord_3611961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611961).length < 2 ^ (prefixWord ++ tailWord_3611961).sum := by decide
  have hdescent : baseEnd_3611961 < baseStart_3611961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611997 : List Nat := [1, 4, 5, 1, 1, 1, 1, 1, 1, 6]
def baseStart_3611997 : Nat := 118140960795 + 3611997 * 2 ^ 59
def prefixEnd_3611997 : Nat := 4983230072969 + 3 ^ 40 * 3611997 * 2
def baseEnd_3611997 : Nat := 1236460389065339852550823

theorem tailTrace_3611997 : CollatzResearch.WordTrace tailWord_3611997 prefixEnd_3611997 1236460389065339852550823 := by
  unfold tailWord_3611997
  simp only [CollatzResearch.WordTrace]
  refine ⟨131740353495359223820386245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87826902330239482546924163 131740353495359223820386245)
  ·
    refine ⟨24701316280379854466322421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131740353495359223820386245 24701316280379854466322421)
    ·
      refine ⟨2315748401285611356217727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24701316280379854466322421 2315748401285611356217727)
      ·
        refine ⟨3473622601928417034326591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2315748401285611356217727 3473622601928417034326591)
        ·
          refine ⟨5210433902892625551489887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3473622601928417034326591 5210433902892625551489887)
          ·
            refine ⟨7815650854338938327234831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5210433902892625551489887 7815650854338938327234831)
            ·
              refine ⟨11723476281508407490852247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7815650854338938327234831 11723476281508407490852247)
              ·
                refine ⟨17585214422262611236278371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11723476281508407490852247 17585214422262611236278371)
                ·
                  refine ⟨26377821633393916854417557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17585214422262611236278371 26377821633393916854417557)
                  ·
                    refine ⟨1236460389065339852550823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26377821633393916854417557 1236460389065339852550823)
                    ·
                      rfl

theorem cell22_3611997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_3611997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3611997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3611997 prefixEnd_3611997 := by exact prefixLift 3611997
  have htrace : WordTrace (prefixWord ++ tailWord_3611997) baseStart_3611997 baseEnd_3611997 := by
    simpa [prefixWord, tailWord_3611997, baseEnd_3611997] using wordTrace_append hprefix tailTrace_3611997
  have hstable : (prefixWord ++ tailWord_3611997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611997).length < 2 ^ (prefixWord ++ tailWord_3611997).sum := by decide
  have hdescent : baseEnd_3611997 < baseStart_3611997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3612040 : List Nat := [2, 1, 3, 3, 1, 3, 3, 1, 5]
def baseStart_3612040 : Nat := 118140960795 + 3612040 * 2 ^ 59
def prefixEnd_3612040 : Nat := 4983230072969 + 3 ^ 40 * 3612040 * 2
def baseEnd_3612040 : Nat := 412158369614700691241897

theorem tailTrace_3612040 : CollatzResearch.WordTrace tailWord_3612040 prefixEnd_3612040 412158369614700691241897 := by
  unfold tailWord_3612040
  simp only [CollatzResearch.WordTrace]
  refine ⟨65870960917101721082100787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87827947889468961442801049 65870960917101721082100787)
  ·
    refine ⟨98806441375652581623151181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65870960917101721082100787 98806441375652581623151181)
    ·
      refine ⟨37052415515869718108681693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98806441375652581623151181 37052415515869718108681693)
      ·
        refine ⟨13894655818451144290755635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37052415515869718108681693 13894655818451144290755635)
        ·
          refine ⟨20841983727676716436133453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13894655818451144290755635 20841983727676716436133453)
          ·
            refine ⟨7815743897878768663550045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20841983727676716436133453 7815743897878768663550045)
            ·
              refine ⟨2930903961704538248831267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7815743897878768663550045 2930903961704538248831267)
              ·
                refine ⟨4396355942556807373246901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2930903961704538248831267 4396355942556807373246901)
                ·
                  refine ⟨412158369614700691241897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4396355942556807373246901 412158369614700691241897)
                  ·
                    rfl

theorem cell22_3612040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 3, 1, 5].length) (baseStart_3612040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3612040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3612040 prefixEnd_3612040 := by exact prefixLift 3612040
  have htrace : WordTrace (prefixWord ++ tailWord_3612040) baseStart_3612040 baseEnd_3612040 := by
    simpa [prefixWord, tailWord_3612040, baseEnd_3612040] using wordTrace_append hprefix tailTrace_3612040
  have hstable : (prefixWord ++ tailWord_3612040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612040).length < 2 ^ (prefixWord ++ tailWord_3612040).sum := by decide
  have hdescent : baseEnd_3612040 < baseStart_3612040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3612053 : List Nat := [1, 3, 2, 1, 1, 2, 3, 4, 1, 4]
def baseStart_3612053 : Nat := 118140960795 + 3612053 * 2 ^ 59
def prefixEnd_3612053 : Nat := 4983230072969 + 3 ^ 40 * 3612053 * 2
def baseEnd_3612053 : Nat := 1236479559009774373150651

theorem tailTrace_3612053 : CollatzResearch.WordTrace tailWord_3612053 prefixEnd_3612053 1236479559009774373150651 := by
  unfold tailWord_3612053
  simp only [CollatzResearch.WordTrace]
  refine ⟨131742395983156345384424813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87828263988770896922949875 131742395983156345384424813)
  ·
    refine ⟨49403398493683629519159305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131742395983156345384424813 49403398493683629519159305)
    ·
      refine ⟨37052548870262722139369479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49403398493683629519159305 37052548870262722139369479)
      ·
        refine ⟨55578823305394083209054219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37052548870262722139369479 55578823305394083209054219)
        ·
          refine ⟨83368234958091124813581329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55578823305394083209054219 83368234958091124813581329)
          ·
            refine ⟨62526176218568343610185997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83368234958091124813581329 62526176218568343610185997)
            ·
              refine ⟨23447316081963128853819749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62526176218568343610185997 23447316081963128853819749)
              ·
                refine ⟨4396371765368086660091203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23447316081963128853819749 4396371765368086660091203)
                ·
                  refine ⟨6594557648052129990136805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4396371765368086660091203 6594557648052129990136805)
                  ·
                    refine ⟨1236479559009774373150651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6594557648052129990136805 1236479559009774373150651)
                    ·
                      rfl

theorem cell22_3612053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 4, 1, 4].length) (baseStart_3612053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3612053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3612053 prefixEnd_3612053 := by exact prefixLift 3612053
  have htrace : WordTrace (prefixWord ++ tailWord_3612053) baseStart_3612053 baseEnd_3612053 := by
    simpa [prefixWord, tailWord_3612053, baseEnd_3612053] using wordTrace_append hprefix tailTrace_3612053
  have hstable : (prefixWord ++ tailWord_3612053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612053).length < 2 ^ (prefixWord ++ tailWord_3612053).sum := by decide
  have hdescent : baseEnd_3612053 < baseStart_3612053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3612085 : List Nat := [1, 3, 3, 2, 2, 3, 1, 1, 6]
def baseStart_3612085 : Nat := 118140960795 + 3612085 * 2 ^ 59
def prefixEnd_3612085 : Nat := 4983230072969 + 3 ^ 40 * 3612085 * 2
def baseEnd_3612085 : Nat := 412163504421245652116851

theorem tailTrace_3612085 : CollatzResearch.WordTrace tailWord_3612085 prefixEnd_3612085 412163504421245652116851 := by
  unfold tailWord_3612085
  simp only [CollatzResearch.WordTrace]
  refine ⟨131743563119040414849589709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87829042079360276566393139 131743563119040414849589709)
  ·
    refine ⟨49403836169640155568596141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131743563119040414849589709 49403836169640155568596141)
    ·
      refine ⟨18526438563615058338223553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49403836169640155568596141 18526438563615058338223553)
      ·
        refine ⟨13894828922711293753667665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18526438563615058338223553 13894828922711293753667665)
        ·
          refine ⟨10421121692033470315250749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13894828922711293753667665 10421121692033470315250749)
          ·
            refine ⟨3907920634512551368219031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10421121692033470315250749 3907920634512551368219031)
            ·
              refine ⟨5861880951768827052328547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3907920634512551368219031 5861880951768827052328547)
              ·
                refine ⟨8792821427653240578492821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5861880951768827052328547 8792821427653240578492821)
                ·
                  refine ⟨412163504421245652116851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8792821427653240578492821 412163504421245652116851)
                  ·
                    rfl

theorem cell22_3612085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 1, 6].length) (baseStart_3612085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3612085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3612085 prefixEnd_3612085 := by exact prefixLift 3612085
  have htrace : WordTrace (prefixWord ++ tailWord_3612085) baseStart_3612085 baseEnd_3612085 := by
    simpa [prefixWord, tailWord_3612085, baseEnd_3612085] using wordTrace_append hprefix tailTrace_3612085
  have hstable : (prefixWord ++ tailWord_3612085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612085).length < 2 ^ (prefixWord ++ tailWord_3612085).sum := by decide
  have hdescent : baseEnd_3612085 < baseStart_3612085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3612096 : List Nat := [2, 1, 1, 2, 3, 1, 3, 9]
def baseStart_3612096 : Nat := 118140960795 + 3612096 * 2 ^ 59
def prefixEnd_3612096 : Nat := 4983230072969 + 3 ^ 40 * 3612096 * 2
def baseEnd_3612096 : Nat := 137388253198726288258391

theorem tailTrace_3612096 : CollatzResearch.WordTrace tailWord_3612096 prefixEnd_3612096 137388253198726288258391 := by
  unfold tailWord_3612096
  simp only [CollatzResearch.WordTrace]
  refine ⟨65871982161000281864120071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87829309548000375818826761 65871982161000281864120071)
  ·
    refine ⟨98807973241500422796180107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65871982161000281864120071 98807973241500422796180107)
    ·
      refine ⟨148211959862250634194270161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98807973241500422796180107 148211959862250634194270161)
      ·
        refine ⟨111158969896687975645702621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148211959862250634194270161 111158969896687975645702621)
        ·
          refine ⟨41684613711257990867138483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111158969896687975645702621 41684613711257990867138483)
          ·
            refine ⟨62526920566886986300707725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41684613711257990867138483 62526920566886986300707725)
            ·
              refine ⟨23447595212582619862765397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62526920566886986300707725 23447595212582619862765397)
              ·
                refine ⟨137388253198726288258391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23447595212582619862765397 137388253198726288258391)
                ·
                  rfl

theorem cell22_3612096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 9].length) (baseStart_3612096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3612096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3612096 prefixEnd_3612096 := by exact prefixLift 3612096
  have htrace : WordTrace (prefixWord ++ tailWord_3612096) baseStart_3612096 baseEnd_3612096 := by
    simpa [prefixWord, tailWord_3612096, baseEnd_3612096] using wordTrace_append hprefix tailTrace_3612096
  have hstable : (prefixWord ++ tailWord_3612096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612096).length < 2 ^ (prefixWord ++ tailWord_3612096).sum := by decide
  have hdescent : baseEnd_3612096 < baseStart_3612096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3612111 : List Nat := [1, 1, 2, 1, 1, 4, 2, 1, 2, 7]
def baseStart_3612111 : Nat := 118140960795 + 3612111 * 2 ^ 59
def prefixEnd_3612111 : Nat := 4983230072969 + 3 ^ 40 * 3612111 * 2
def baseEnd_3612111 : Nat := 1236499413595081555200473

theorem tailTrace_3612111 : CollatzResearch.WordTrace tailWord_3612111 prefixEnd_3612111 1236499413595081555200473 := by
  unfold tailWord_3612111
  simp only [CollatzResearch.WordTrace]
  refine ⟨131744511416946221290036187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87829674277964147526690791 131744511416946221290036187)
  ·
    refine ⟨197616767125419331935054281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131744511416946221290036187 197616767125419331935054281)
    ·
      refine ⟨148212575344064498951290711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197616767125419331935054281 148212575344064498951290711)
      ·
        refine ⟨222318863016096748426936067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148212575344064498951290711 222318863016096748426936067)
        ·
          refine ⟨333478294524145122640404101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222318863016096748426936067 333478294524145122640404101)
          ·
            refine ⟨62527180223277210495075769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 333478294524145122640404101 62527180223277210495075769)
            ·
              refine ⟨46895385167457907871306827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62527180223277210495075769 46895385167457907871306827)
              ·
                refine ⟨70343077751186861806960241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46895385167457907871306827 70343077751186861806960241)
                ·
                  refine ⟨52757308313390146355220181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70343077751186861806960241 52757308313390146355220181)
                  ·
                    refine ⟨1236499413595081555200473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52757308313390146355220181 1236499413595081555200473)
                    ·
                      rfl

theorem cell22_3612111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 7].length) (baseStart_3612111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3612111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3612111 prefixEnd_3612111 := by exact prefixLift 3612111
  have htrace : WordTrace (prefixWord ++ tailWord_3612111) baseStart_3612111 baseEnd_3612111 := by
    simpa [prefixWord, tailWord_3612111, baseEnd_3612111] using wordTrace_append hprefix tailTrace_3612111
  have hstable : (prefixWord ++ tailWord_3612111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612111).length < 2 ^ (prefixWord ++ tailWord_3612111).sum := by decide
  have hdescent : baseEnd_3612111 < baseStart_3612111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3612128 : List Nat := [2, 1, 1, 3, 1, 1, 2, 1, 7, 3]
def baseStart_3612128 : Nat := 118140960795 + 3612128 * 2 ^ 59
def prefixEnd_3612128 : Nat := 4983230072969 + 3 ^ 40 * 3612128 * 2
def baseEnd_3612128 : Nat := 1236505233042499177525421

theorem tailTrace_3612128 : CollatzResearch.WordTrace tailWord_3612128 prefixEnd_3612128 1236505233042499177525421 := by
  unfold tailWord_3612128
  simp only [CollatzResearch.WordTrace]
  refine ⟨65872565728942316596702519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87830087638589755462270025 65872565728942316596702519)
  ·
    refine ⟨98808848593413474895053779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65872565728942316596702519 98808848593413474895053779)
    ·
      refine ⟨148213272890120212342580669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98808848593413474895053779 148213272890120212342580669)
      ·
        refine ⟨55579977333795079628467751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148213272890120212342580669 55579977333795079628467751)
        ·
          refine ⟨83369966000692619442701627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55579977333795079628467751 83369966000692619442701627)
          ·
            refine ⟨125054949001038929164052441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83369966000692619442701627 125054949001038929164052441)
            ·
              refine ⟨93791211750779196873039331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125054949001038929164052441 93791211750779196873039331)
              ·
                refine ⟨140686817626168795309558997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93791211750779196873039331 140686817626168795309558997)
                ·
                  refine ⟨3297347288113331140067789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 140686817626168795309558997 3297347288113331140067789)
                  ·
                    refine ⟨1236505233042499177525421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3297347288113331140067789 1236505233042499177525421)
                    ·
                      rfl

theorem cell22_3612128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 7, 3].length) (baseStart_3612128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3612128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3612128 prefixEnd_3612128 := by exact prefixLift 3612128
  have htrace : WordTrace (prefixWord ++ tailWord_3612128) baseStart_3612128 baseEnd_3612128 := by
    simpa [prefixWord, tailWord_3612128, baseEnd_3612128] using wordTrace_append hprefix tailTrace_3612128
  have hstable : (prefixWord ++ tailWord_3612128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612128).length < 2 ^ (prefixWord ++ tailWord_3612128).sum := by decide
  have hdescent : baseEnd_3612128 < baseStart_3612128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3612162 : List Nat := [3, 4, 1, 2, 1, 1, 1, 1, 5, 3]
def baseStart_3612162 : Nat := 118140960795 + 3612162 * 2 ^ 59
def prefixEnd_3612162 : Nat := 4983230072969 + 3 ^ 40 * 3612162 * 2
def baseEnd_3612162 : Nat := 1236516871937334422175317

theorem tailTrace_3612162 : CollatzResearch.WordTrace tailWord_3612162 prefixEnd_3612162 1236516871937334422175317 := by
  unfold tailWord_3612162
  simp only [CollatzResearch.WordTrace]
  refine ⟨32936592884940364250035685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87830914359840971333428493 32936592884940364250035685)
  ·
    refine ⟨6175611165926318296881691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32936592884940364250035685 6175611165926318296881691)
    ·
      refine ⟨9263416748889477445322537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6175611165926318296881691 9263416748889477445322537)
      ·
        refine ⟨6947562561667108083991903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9263416748889477445322537 6947562561667108083991903)
        ·
          refine ⟨10421343842500662125987855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6947562561667108083991903 10421343842500662125987855)
          ·
            refine ⟨15632015763750993188981783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10421343842500662125987855 15632015763750993188981783)
            ·
              refine ⟨23448023645626489783472675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15632015763750993188981783 23448023645626489783472675)
              ·
                refine ⟨35172035468439734675209013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23448023645626489783472675 35172035468439734675209013)
                ·
                  refine ⟨3297378325166225125800845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35172035468439734675209013 3297378325166225125800845)
                  ·
                    refine ⟨1236516871937334422175317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3297378325166225125800845 1236516871937334422175317)
                    ·
                      rfl

theorem cell22_3612162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_3612162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3612162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3612162 prefixEnd_3612162 := by exact prefixLift 3612162
  have htrace : WordTrace (prefixWord ++ tailWord_3612162) baseStart_3612162 baseEnd_3612162 := by
    simpa [prefixWord, tailWord_3612162, baseEnd_3612162] using wordTrace_append hprefix tailTrace_3612162
  have hstable : (prefixWord ++ tailWord_3612162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612162).length < 2 ^ (prefixWord ++ tailWord_3612162).sum := by decide
  have hdescent : baseEnd_3612162 < baseStart_3612162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3612192 : List Nat := [2, 1, 1, 6, 1, 3, 1, 2, 5]
def baseStart_3612192 : Nat := 118140960795 + 3612192 * 2 ^ 59
def prefixEnd_3612192 : Nat := 4983230072969 + 3 ^ 40 * 3612192 * 2
def baseEnd_3612192 : Nat := 412175713850141447975075

theorem tailTrace_3612192 : CollatzResearch.WordTrace tailWord_3612192 prefixEnd_3612192 412175713850141447975075 := by
  unfold tailWord_3612192
  simp only [CollatzResearch.WordTrace]
  refine ⟨65873732864826386061867415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87831643819768514749156553 65873732864826386061867415)
  ·
    refine ⟨98810599297239579092801123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65873732864826386061867415 98810599297239579092801123)
    ·
      refine ⟨148215898945859368639201685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98810599297239579092801123 148215898945859368639201685)
      ·
        refine ⟨6947620263087157904962579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 148215898945859368639201685 6947620263087157904962579)
        ·
          refine ⟨10421430394630736857443869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6947620263087157904962579 10421430394630736857443869)
          ·
            refine ⟨3908036397986526321541451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10421430394630736857443869 3908036397986526321541451)
            ·
              refine ⟨5862054596979789482312177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3908036397986526321541451 5862054596979789482312177)
              ·
                refine ⟨4396540947734842111734133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5862054596979789482312177 4396540947734842111734133)
                ·
                  refine ⟨412175713850141447975075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4396540947734842111734133 412175713850141447975075)
                  ·
                    rfl

theorem cell22_3612192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 2, 5].length) (baseStart_3612192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3612192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3612192 prefixEnd_3612192 := by exact prefixLift 3612192
  have htrace : WordTrace (prefixWord ++ tailWord_3612192) baseStart_3612192 baseEnd_3612192 := by
    simpa [prefixWord, tailWord_3612192, baseEnd_3612192] using wordTrace_append hprefix tailTrace_3612192
  have hstable : (prefixWord ++ tailWord_3612192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612192).length < 2 ^ (prefixWord ++ tailWord_3612192).sum := by decide
  have hdescent : baseEnd_3612192 < baseStart_3612192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3612230 : List Nat := [6, 1, 1, 1, 4, 1, 1, 3, 1, 3]
def baseStart_3612230 : Nat := 118140960795 + 3612230 * 2 ^ 59
def prefixEnd_3612230 : Nat := 4983230072969 + 3 ^ 40 * 3612230 * 2
def baseEnd_3612230 : Nat := 1236540149727004911475109

theorem tailTrace_3612230 : CollatzResearch.WordTrace tailWord_3612230 prefixEnd_3612230 1236540149727004911475109 := by
  unfold tailWord_3612230
  simp only [CollatzResearch.WordTrace]
  refine ⟨4117151615734847019175567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 87832567802343403075745429 4117151615734847019175567)
  ·
    refine ⟨6175727423602270528763351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4117151615734847019175567 6175727423602270528763351)
    ·
      refine ⟨9263591135403405793145027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6175727423602270528763351 9263591135403405793145027)
      ·
        refine ⟨13895386703105108689717541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9263591135403405793145027 13895386703105108689717541)
        ·
          refine ⟨2605385006832207879322039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13895386703105108689717541 2605385006832207879322039)
          ·
            refine ⟨3908077510248311818983059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2605385006832207879322039 3908077510248311818983059)
            ·
              refine ⟨5862116265372467728474589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3908077510248311818983059 5862116265372467728474589)
              ·
                refine ⟨2198293599514675398177971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5862116265372467728474589 2198293599514675398177971)
                ·
                  refine ⟨3297440399272013097266957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2198293599514675398177971 3297440399272013097266957)
                  ·
                    refine ⟨1236540149727004911475109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3297440399272013097266957 1236540149727004911475109)
                    ·
                      rfl

theorem cell22_3612230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_3612230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3612230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3612230 prefixEnd_3612230 := by exact prefixLift 3612230
  have htrace : WordTrace (prefixWord ++ tailWord_3612230) baseStart_3612230 baseEnd_3612230 := by
    simpa [prefixWord, tailWord_3612230, baseEnd_3612230] using wordTrace_append hprefix tailTrace_3612230
  have hstable : (prefixWord ++ tailWord_3612230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612230).length < 2 ^ (prefixWord ++ tailWord_3612230).sum := by decide
  have hdescent : baseEnd_3612230 < baseStart_3612230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3612233 : List Nat := [1, 2, 1, 1, 2, 2, 1, 2, 6, 4]
def baseStart_3612233 : Nat := 118140960795 + 3612233 * 2 ^ 59
def prefixEnd_3612233 : Nat := 4983230072969 + 3 ^ 40 * 3612233 * 2
def baseEnd_3612233 : Nat := 1236541176688313903650099

theorem tailTrace_3612233 : CollatzResearch.WordTrace tailWord_3612233 prefixEnd_3612233 1236541176688313903650099 := by
  unfold tailWord_3612233
  simp only [CollatzResearch.WordTrace]
  refine ⟨131748961122504236125977353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87832640748336157417318235 131748961122504236125977353)
  ·
    refine ⟨98811720841878177094483015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131748961122504236125977353 98811720841878177094483015)
    ·
      refine ⟨148217581262817265641724523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98811720841878177094483015 148217581262817265641724523)
      ·
        refine ⟨222326371894225898462586785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148217581262817265641724523 222326371894225898462586785)
        ·
          refine ⟨166744778920669423846940089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222326371894225898462586785 166744778920669423846940089)
          ·
            refine ⟨125058584190502067885205067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166744778920669423846940089 125058584190502067885205067)
            ·
              refine ⟨187587876285753101827807601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125058584190502067885205067 187587876285753101827807601)
              ·
                refine ⟨140690907214314826370855701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 187587876285753101827807601 140690907214314826370855701)
                ·
                  refine ⟨6594886275671007486133861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 140690907214314826370855701 6594886275671007486133861)
                  ·
                    refine ⟨1236541176688313903650099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6594886275671007486133861 1236541176688313903650099)
                    ·
                      rfl

theorem cell22_3612233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 6, 4].length) (baseStart_3612233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3612233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3612233 prefixEnd_3612233 := by exact prefixLift 3612233
  have htrace : WordTrace (prefixWord ++ tailWord_3612233) baseStart_3612233 baseEnd_3612233 := by
    simpa [prefixWord, tailWord_3612233, baseEnd_3612233] using wordTrace_append hprefix tailTrace_3612233
  have hstable : (prefixWord ++ tailWord_3612233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612233).length < 2 ^ (prefixWord ++ tailWord_3612233).sum := by decide
  have hdescent : baseEnd_3612233 < baseStart_3612233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3612252 : List Nat := [2, 2, 4, 1, 2, 1, 2, 1, 4, 3]
def baseStart_3612252 : Nat := 118140960795 + 3612252 * 2 ^ 59
def prefixEnd_3612252 : Nat := 4983230072969 + 3 ^ 40 * 3612252 * 2
def baseEnd_3612252 : Nat := 1236547680776604187425041

theorem tailTrace_3612252 : CollatzResearch.WordTrace tailWord_3612252 prefixEnd_3612252 1236547680776604187425041 := by
  unfold tailWord_3612252
  simp only [CollatzResearch.WordTrace]
  refine ⟨65874827054717701185459505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87833102739623601580612673 65874827054717701185459505)
  ·
    refine ⟨49406120291038275889094629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65874827054717701185459505 49406120291038275889094629)
    ·
      refine ⟨9263647554569676729205243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49406120291038275889094629 9263647554569676729205243)
      ·
        refine ⟨13895471331854515093807865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9263647554569676729205243 13895471331854515093807865)
        ·
          refine ⟨10421603498890886320355899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13895471331854515093807865 10421603498890886320355899)
          ·
            refine ⟨15632405248336329480533849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10421603498890886320355899 15632405248336329480533849)
            ·
              refine ⟨11724303936252247110400387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15632405248336329480533849 11724303936252247110400387)
              ·
                refine ⟨17586455904378370665600581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11724303936252247110400387 17586455904378370665600581)
                ·
                  refine ⟨3297460482070944499800109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17586455904378370665600581 3297460482070944499800109)
                  ·
                    refine ⟨1236547680776604187425041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3297460482070944499800109 1236547680776604187425041)
                    ·
                      rfl

theorem cell22_3612252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_3612252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3612252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3612252 prefixEnd_3612252 := by exact prefixLift 3612252
  have htrace : WordTrace (prefixWord ++ tailWord_3612252) baseStart_3612252 baseEnd_3612252 := by
    simpa [prefixWord, tailWord_3612252, baseEnd_3612252] using wordTrace_append hprefix tailTrace_3612252
  have hstable : (prefixWord ++ tailWord_3612252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612252).length < 2 ^ (prefixWord ++ tailWord_3612252).sum := by decide
  have hdescent : baseEnd_3612252 < baseStart_3612252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3612269 : List Nat := [1, 5, 1, 1, 4, 1, 1, 3, 2, 3]
def baseStart_3612269 : Nat := 118140960795 + 3612269 * 2 ^ 59
def prefixEnd_3612269 : Nat := 4983230072969 + 3 ^ 40 * 3612269 * 2
def baseEnd_3612269 : Nat := 1236553500224021809749989

theorem tailTrace_3612269 : CollatzResearch.WordTrace tailWord_3612269 prefixEnd_3612269 1236553500224021809749989 := by
  unfold tailWord_3612269
  simp only [CollatzResearch.WordTrace]
  refine ⟨131750274150373814274287861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87833516100249209516191907 131750274150373814274287861)
  ·
    refine ⟨12351588201597545088214487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 131750274150373814274287861 12351588201597545088214487)
    ·
      refine ⟨18527382302396317632321731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12351588201597545088214487 18527382302396317632321731)
      ·
        refine ⟨27791073453594476448482597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18527382302396317632321731 27791073453594476448482597)
        ·
          refine ⟨5210826272548964334090487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27791073453594476448482597 5210826272548964334090487)
          ·
            refine ⟨7816239408823446501135731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5210826272548964334090487 7816239408823446501135731)
            ·
              refine ⟨11724359113235169751703597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7816239408823446501135731 11724359113235169751703597)
              ·
                refine ⟨4396634667463188656888849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11724359113235169751703597 4396634667463188656888849)
                ·
                  refine ⟨3297476000597391492666637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4396634667463188656888849 3297476000597391492666637)
                  ·
                    refine ⟨1236553500224021809749989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3297476000597391492666637 1236553500224021809749989)
                    ·
                      rfl

theorem cell22_3612269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 3, 2, 3].length) (baseStart_3612269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3612269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3612269 prefixEnd_3612269 := by exact prefixLift 3612269
  have htrace : WordTrace (prefixWord ++ tailWord_3612269) baseStart_3612269 baseEnd_3612269 := by
    simpa [prefixWord, tailWord_3612269, baseEnd_3612269] using wordTrace_append hprefix tailTrace_3612269
  have hstable : (prefixWord ++ tailWord_3612269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612269).length < 2 ^ (prefixWord ++ tailWord_3612269).sum := by decide
  have hdescent : baseEnd_3612269 < baseStart_3612269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3612372 : List Nat := [2, 4, 1, 3, 1, 1, 1, 3, 6]
def baseStart_3612372 : Nat := 118140960795 + 3612372 * 2 ^ 59
def prefixEnd_3612372 : Nat := 4983230072969 + 3 ^ 40 * 3612372 * 2
def baseEnd_3612372 : Nat := 412196253076321291474891

theorem tailTrace_3612372 : CollatzResearch.WordTrace tailWord_3612372 prefixEnd_3612372 412196253076321291474891 := by
  unfold tailWord_3612372
  simp only [CollatzResearch.WordTrace]
  refine ⟨65877015434500331432643685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87836020579333775243524913 65877015434500331432643685)
  ·
    refine ⟨12351940393968812143620691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65877015434500331432643685 12351940393968812143620691)
    ·
      refine ⟨18527910590953218215431037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12351940393968812143620691 18527910590953218215431037)
      ·
        refine ⟨6947966471607456830786639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18527910590953218215431037 6947966471607456830786639)
        ·
          refine ⟨10421949707411185246179959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6947966471607456830786639 10421949707411185246179959)
          ·
            refine ⟨15632924561116777869269939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10421949707411185246179959 15632924561116777869269939)
            ·
              refine ⟨23449386841675166803904909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15632924561116777869269939 23449386841675166803904909)
              ·
                refine ⟨8793520065628187551464341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23449386841675166803904909 8793520065628187551464341)
                ·
                  refine ⟨412196253076321291474891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8793520065628187551464341 412196253076321291474891)
                  ·
                    rfl

theorem cell22_3612372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_3612372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3612372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3612372 prefixEnd_3612372 := by exact prefixLift 3612372
  have htrace : WordTrace (prefixWord ++ tailWord_3612372) baseStart_3612372 baseEnd_3612372 := by
    simpa [prefixWord, tailWord_3612372, baseEnd_3612372] using wordTrace_append hprefix tailTrace_3612372
  have hstable : (prefixWord ++ tailWord_3612372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612372).length < 2 ^ (prefixWord ++ tailWord_3612372).sum := by decide
  have hdescent : baseEnd_3612372 < baseStart_3612372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3612391 : List Nat := [1, 1, 5, 4, 1, 1, 2, 2, 1, 4]
def baseStart_3612391 : Nat := 118140960795 + 3612391 * 2 ^ 59
def prefixEnd_3612391 : Nat := 4983230072969 + 3 ^ 40 * 3612391 * 2
def baseEnd_3612391 : Nat := 1236595263317254158199615

theorem tailTrace_3612391 : CollatzResearch.WordTrace tailWord_3612391 prefixEnd_3612391 1236595263317254158199615 := by
  unfold tailWord_3612391
  simp only [CollatzResearch.WordTrace]
  refine ⟨131754723855931829110229027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87836482570621219406819351 131754723855931829110229027)
  ·
    refine ⟨197632085783897743665343541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131754723855931829110229027 197632085783897743665343541)
    ·
      refine ⟨18528008042240413468625957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 197632085783897743665343541 18528008042240413468625957)
      ·
        refine ⟨3474001507920077525367367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18528008042240413468625957 3474001507920077525367367)
        ·
          refine ⟨5211002261880116288051051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3474001507920077525367367 5211002261880116288051051)
          ·
            refine ⟨7816503392820174432076577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5211002261880116288051051 7816503392820174432076577)
            ·
              refine ⟨5862377544615130824057433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7816503392820174432076577 5862377544615130824057433)
              ·
                refine ⟨4396783158461348118043075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5862377544615130824057433 4396783158461348118043075)
                ·
                  refine ⟨6595174737692022177064613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4396783158461348118043075 6595174737692022177064613)
                  ·
                    refine ⟨1236595263317254158199615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6595174737692022177064613 1236595263317254158199615)
                    ·
                      rfl

theorem cell22_3612391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 2, 1, 4].length) (baseStart_3612391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3612391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3612391 prefixEnd_3612391 := by exact prefixLift 3612391
  have htrace : WordTrace (prefixWord ++ tailWord_3612391) baseStart_3612391 baseEnd_3612391 := by
    simpa [prefixWord, tailWord_3612391, baseEnd_3612391] using wordTrace_append hprefix tailTrace_3612391
  have hstable : (prefixWord ++ tailWord_3612391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612391).length < 2 ^ (prefixWord ++ tailWord_3612391).sum := by decide
  have hdescent : baseEnd_3612391 < baseStart_3612391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3612402 : List Nat := [3, 2, 1, 3, 1, 1, 2, 3, 2, 4]
def baseStart_3612402 : Nat := 118140960795 + 3612402 * 2 ^ 59
def prefixEnd_3612402 : Nat := 4983230072969 + 3 ^ 40 * 3612402 * 2
def baseEnd_3612402 : Nat := 1236599028842053796174581

theorem tailTrace_3612402 : CollatzResearch.WordTrace tailWord_3612402 prefixEnd_3612402 1236599028842053796174581 := by
  unfold tailWord_3612402
  simp only [CollatzResearch.WordTrace]
  refine ⟨32938781264722994497219865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87836750039261318659252973 32938781264722994497219865)
  ·
    refine ⟨24704085948542245872914899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32938781264722994497219865 24704085948542245872914899)
    ·
      refine ⟨37056128922813368809372349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24704085948542245872914899 37056128922813368809372349)
      ·
        refine ⟨13896048346055013303514631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37056128922813368809372349 13896048346055013303514631)
        ·
          refine ⟨20844072519082519955271947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13896048346055013303514631 20844072519082519955271947)
          ·
            refine ⟨31266108778623779932907921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20844072519082519955271947 31266108778623779932907921)
            ·
              refine ⟨23449581583967834949680941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31266108778623779932907921 23449581583967834949680941)
              ·
                refine ⟨8793593093987938106130353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23449581583967834949680941 8793593093987938106130353)
                ·
                  refine ⟨6595194820490953579597765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8793593093987938106130353 6595194820490953579597765)
                  ·
                    refine ⟨1236599028842053796174581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6595194820490953579597765 1236599028842053796174581)
                    ·
                      rfl

theorem cell22_3612402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 3, 2, 4].length) (baseStart_3612402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3612402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3612402 prefixEnd_3612402 := by exact prefixLift 3612402
  have htrace : WordTrace (prefixWord ++ tailWord_3612402) baseStart_3612402 baseEnd_3612402 := by
    simpa [prefixWord, tailWord_3612402, baseEnd_3612402] using wordTrace_append hprefix tailTrace_3612402
  have hstable : (prefixWord ++ tailWord_3612402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612402).length < 2 ^ (prefixWord ++ tailWord_3612402).sum := by decide
  have hdescent : baseEnd_3612402 < baseStart_3612402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3612406 : List Nat := [5, 1, 1, 1, 1, 5, 1, 3, 4]
def baseStart_3612406 : Nat := 118140960795 + 3612406 * 2 ^ 59
def prefixEnd_3612406 : Nat := 4983230072969 + 3 ^ 40 * 3612406 * 2
def baseEnd_3612406 : Nat := 412200132707933039691523

theorem tailTrace_3612406 : CollatzResearch.WordTrace tailWord_3612406 prefixEnd_3612406 412200132707933039691523 := by
  unfold tailWord_3612406
  simp only [CollatzResearch.WordTrace]
  refine ⟨8234704434429842917001567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87836847300584991114683381 8234704434429842917001567)
  ·
    refine ⟨12352056651644764375502351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8234704434429842917001567 12352056651644764375502351)
    ·
      refine ⟨18528084977467146563253527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12352056651644764375502351 18528084977467146563253527)
      ·
        refine ⟨27792127466200719844880291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18528084977467146563253527 27792127466200719844880291)
        ·
          refine ⟨41688191199301079767320437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27792127466200719844880291 41688191199301079767320437)
          ·
            refine ⟨3908267924934476228186291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41688191199301079767320437 3908267924934476228186291)
            ·
              refine ⟨5862401887401714342279437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3908267924934476228186291 5862401887401714342279437)
              ·
                refine ⟨2198400707775642878354789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5862401887401714342279437 2198400707775642878354789)
                ·
                  refine ⟨412200132707933039691523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2198400707775642878354789 412200132707933039691523)
                  ·
                    rfl

theorem cell22_3612406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 3, 4].length) (baseStart_3612406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3612406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3612406 prefixEnd_3612406 := by exact prefixLift 3612406
  have htrace : WordTrace (prefixWord ++ tailWord_3612406) baseStart_3612406 baseEnd_3612406 := by
    simpa [prefixWord, tailWord_3612406, baseEnd_3612406] using wordTrace_append hprefix tailTrace_3612406
  have hstable : (prefixWord ++ tailWord_3612406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612406).length < 2 ^ (prefixWord ++ tailWord_3612406).sum := by decide
  have hdescent : baseEnd_3612406 < baseStart_3612406 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3612434 : List Nat := [3, 2, 4, 1, 1, 2, 2, 7]
def baseStart_3612434 : Nat := 118140960795 + 3612434 * 2 ^ 59
def prefixEnd_3612434 : Nat := 4983230072969 + 3 ^ 40 * 3612434 * 2
def baseEnd_3612434 : Nat := 137401109232890708819387

theorem tailTrace_3612434 : CollatzResearch.WordTrace tailWord_3612434 prefixEnd_3612434 137401109232890708819387 := by
  unfold tailWord_3612434
  simp only [CollatzResearch.WordTrace]
  refine ⟨32939073048694011863511089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87837528129850698302696237 32939073048694011863511089)
  ·
    refine ⟨24704304786520508897633317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32939073048694011863511089 24704304786520508897633317)
    ·
      refine ⟨4632057147472595418306247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24704304786520508897633317 4632057147472595418306247)
      ·
        refine ⟨6948085721208893127459371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4632057147472595418306247 6948085721208893127459371)
        ·
          refine ⟨10422128581813339691189057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6948085721208893127459371 10422128581813339691189057)
          ·
            refine ⟨7816596436360004768391793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10422128581813339691189057 7816596436360004768391793)
            ·
              refine ⟨5862447327270003576293845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7816596436360004768391793 5862447327270003576293845)
              ·
                refine ⟨137401109232890708819387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5862447327270003576293845 137401109232890708819387)
                ·
                  rfl

theorem cell22_3612434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 7].length) (baseStart_3612434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3612434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3612434 prefixEnd_3612434 := by exact prefixLift 3612434
  have htrace : WordTrace (prefixWord ++ tailWord_3612434) baseStart_3612434 baseEnd_3612434 := by
    simpa [prefixWord, tailWord_3612434, baseEnd_3612434] using wordTrace_append hprefix tailTrace_3612434
  have hstable : (prefixWord ++ tailWord_3612434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612434).length < 2 ^ (prefixWord ++ tailWord_3612434).sum := by decide
  have hdescent : baseEnd_3612434 < baseStart_3612434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3612479 : List Nat := [1, 1, 2, 2, 6, 1, 2, 2, 5]
def baseStart_3612479 : Nat := 118140960795 + 3612479 * 2 ^ 59
def prefixEnd_3612479 : Nat := 4983230072969 + 3 ^ 40 * 3612479 * 2
def baseEnd_3612479 : Nat := 412208462505217087333115

theorem tailTrace_3612479 : CollatzResearch.WordTrace tailWord_3612479 prefixEnd_3612479 412208462505217087333115 := by
  unfold tailWord_3612479
  simp only [CollatzResearch.WordTrace]
  refine ⟨131757933479613020139432491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87838622319742013426288327 131757933479613020139432491)
  ·
    refine ⟨197636900219419530209148737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131757933479613020139432491 197636900219419530209148737)
    ·
      refine ⟨148227675164564647656861553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197636900219419530209148737 148227675164564647656861553)
      ·
        refine ⟨111170756373423485742646165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148227675164564647656861553 111170756373423485742646165)
        ·
          refine ⟨5211129205004225894186539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 111170756373423485742646165 5211129205004225894186539)
          ·
            refine ⟨7816693807506338841279809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5211129205004225894186539 7816693807506338841279809)
            ·
              refine ⟨5862520355629754130959857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7816693807506338841279809 5862520355629754130959857)
              ·
                refine ⟨4396890266722315598219893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5862520355629754130959857 4396890266722315598219893)
                ·
                  refine ⟨412208462505217087333115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4396890266722315598219893 412208462505217087333115)
                  ·
                    rfl

theorem cell22_3612479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 2, 5].length) (baseStart_3612479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3612479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3612479 prefixEnd_3612479 := by exact prefixLift 3612479
  have htrace : WordTrace (prefixWord ++ tailWord_3612479) baseStart_3612479 baseEnd_3612479 := by
    simpa [prefixWord, tailWord_3612479, baseEnd_3612479] using wordTrace_append hprefix tailTrace_3612479
  have hstable : (prefixWord ++ tailWord_3612479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612479).length < 2 ^ (prefixWord ++ tailWord_3612479).sum := by decide
  have hdescent : baseEnd_3612479 < baseStart_3612479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3612483 : List Nat := [1, 1, 1, 3, 1, 7, 2, 2, 1, 3]
def baseStart_3612483 : Nat := 118140960795 + 3612483 * 2 ^ 59
def prefixEnd_3612483 : Nat := 4983230072969 + 3 ^ 40 * 3612483 * 2
def baseEnd_3612483 : Nat := 1236626756797396584899333

theorem tailTrace_3612483 : CollatzResearch.WordTrace tailWord_3612483 prefixEnd_3612483 1236626756797396584899333 := by
  unfold tailWord_3612483
  simp only [CollatzResearch.WordTrace]
  refine ⟨131758079371598528822578103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87838719581065685881718735 131758079371598528822578103)
  ·
    refine ⟨197637119057397793233867155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131758079371598528822578103 197637119057397793233867155)
    ·
      refine ⟨296455678586096689850800733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197637119057397793233867155 296455678586096689850800733)
      ·
        refine ⟨111170879469786258694050275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 296455678586096689850800733 111170879469786258694050275)
        ·
          refine ⟨166756319204679388041075413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111170879469786258694050275 166756319204679388041075413)
          ·
            refine ⟨3908351231359673157212705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 166756319204679388041075413 3908351231359673157212705)
            ·
              refine ⟨2931263423519754867909529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3908351231359673157212705 2931263423519754867909529)
              ·
                refine ⟨2198447567639816150932147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2931263423519754867909529 2198447567639816150932147)
                ·
                  refine ⟨3297671351459724226398221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2198447567639816150932147 3297671351459724226398221)
                  ·
                    refine ⟨1236626756797396584899333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3297671351459724226398221 1236626756797396584899333)
                    ·
                      rfl

theorem cell22_3612483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 2, 2, 1, 3].length) (baseStart_3612483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3612483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3612483 prefixEnd_3612483 := by exact prefixLift 3612483
  have htrace : WordTrace (prefixWord ++ tailWord_3612483) baseStart_3612483 baseEnd_3612483 := by
    simpa [prefixWord, tailWord_3612483, baseEnd_3612483] using wordTrace_append hprefix tailTrace_3612483
  have hstable : (prefixWord ++ tailWord_3612483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612483).length < 2 ^ (prefixWord ++ tailWord_3612483).sum := by decide
  have hdescent : baseEnd_3612483 < baseStart_3612483 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3612524 : List Nat := [2, 2, 1, 1, 4, 2, 1, 5, 4]
def baseStart_3612524 : Nat := 118140960795 + 3612524 * 2 ^ 59
def prefixEnd_3612524 : Nat := 4983230072969 + 3 ^ 40 * 3612524 * 2
def baseEnd_3612524 : Nat := 412213597311762048208069

theorem tailTrace_3612524 : CollatzResearch.WordTrace tailWord_3612524 prefixEnd_3612524 412213597311762048208069 := by
  unfold tailWord_3612524
  simp only [CollatzResearch.WordTrace]
  refine ⟨65879787382224996412410313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87839716509633328549880417 65879787382224996412410313)
  ·
    refine ⟨49409840536668747309307735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65879787382224996412410313 49409840536668747309307735)
    ·
      refine ⟨74114760805003120963961603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49409840536668747309307735 74114760805003120963961603)
      ·
        refine ⟨111172141207504681445942405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74114760805003120963961603 111172141207504681445942405)
        ·
          refine ⟨20844776476407127771114201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111172141207504681445942405 20844776476407127771114201)
          ·
            refine ⟨15633582357305345828335651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20844776476407127771114201 15633582357305345828335651)
            ·
              refine ⟨23450373535958018742503477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15633582357305345828335651 23450373535958018742503477)
              ·
                refine ⟨2198472518996064257109701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23450373535958018742503477 2198472518996064257109701)
                ·
                  refine ⟨412213597311762048208069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2198472518996064257109701 412213597311762048208069)
                  ·
                    rfl

theorem cell22_3612524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 5, 4].length) (baseStart_3612524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3612524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3612524 prefixEnd_3612524 := by exact prefixLift 3612524
  have htrace : WordTrace (prefixWord ++ tailWord_3612524) baseStart_3612524 baseEnd_3612524 := by
    simpa [prefixWord, tailWord_3612524, baseEnd_3612524] using wordTrace_append hprefix tailTrace_3612524
  have hstable : (prefixWord ++ tailWord_3612524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612524).length < 2 ^ (prefixWord ++ tailWord_3612524).sum := by decide
  have hdescent : baseEnd_3612524 < baseStart_3612524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3612526 : List Nat := [4, 1, 2, 3, 1, 2, 1, 3, 1, 4]
def baseStart_3612526 : Nat := 118140960795 + 3612526 * 2 ^ 59
def prefixEnd_3612526 : Nat := 4983230072969 + 3 ^ 40 * 3612526 * 2
def baseEnd_3612526 : Nat := 1236641476576158806074201

theorem tailTrace_3612526 : CollatzResearch.WordTrace tailWord_3612526 prefixEnd_3612526 1236641476576158806074201 := by
  unfold tailWord_3612526
  simp only [CollatzResearch.WordTrace]
  refine ⟨16469955963805343395799179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87839765140295164777595621 16469955963805343395799179)
  ·
    refine ⟨24704933945708015093698769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16469955963805343395799179 24704933945708015093698769)
    ·
      refine ⟨18528700459281011320274077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24704933945708015093698769 18528700459281011320274077)
      ·
        refine ⟨6948262672230379245102779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18528700459281011320274077 6948262672230379245102779)
        ·
          refine ⟨10422394008345568867654169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6948262672230379245102779 10422394008345568867654169)
          ·
            refine ⟨7816795506259176650740627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10422394008345568867654169 7816795506259176650740627)
            ·
              refine ⟨11725193259388764976110941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7816795506259176650740627 11725193259388764976110941)
              ·
                refine ⟨4396947472270786866041603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11725193259388764976110941 4396947472270786866041603)
                ·
                  refine ⟨6595421208406180299062405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4396947472270786866041603 6595421208406180299062405)
                  ·
                    refine ⟨1236641476576158806074201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6595421208406180299062405 1236641476576158806074201)
                    ·
                      rfl

theorem cell22_3612526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_3612526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3612526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3612526 prefixEnd_3612526 := by exact prefixLift 3612526
  have htrace : WordTrace (prefixWord ++ tailWord_3612526) baseStart_3612526 baseEnd_3612526 := by
    simpa [prefixWord, tailWord_3612526, baseEnd_3612526] using wordTrace_append hprefix tailTrace_3612526
  have hstable : (prefixWord ++ tailWord_3612526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612526).length < 2 ^ (prefixWord ++ tailWord_3612526).sum := by decide
  have hdescent : baseEnd_3612526 < baseStart_3612526 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3612537 : List Nat := [1, 2, 1, 3, 2, 2, 2, 1, 4, 4]
def baseStart_3612537 : Nat := 118140960795 + 3612537 * 2 ^ 59
def prefixEnd_3612537 : Nat := 4983230072969 + 3 ^ 40 * 3612537 * 2
def baseEnd_3612537 : Nat := 1236645242100958444049167

theorem tailTrace_3612537 : CollatzResearch.WordTrace tailWord_3612537 prefixEnd_3612537 1236645242100958444049167 := by
  unfold tailWord_3612537
  simp only [CollatzResearch.WordTrace]
  refine ⟨131760048913402896045043865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87840032608935264030029243 131760048913402896045043865)
  ·
    refine ⟨98820036685052172033782899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131760048913402896045043865 98820036685052172033782899)
    ·
      refine ⟨148230055027578258050674349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98820036685052172033782899 148230055027578258050674349)
      ·
        refine ⟨55586270635341846769002881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148230055027578258050674349 55586270635341846769002881)
        ·
          refine ⟨41689702976506385076752161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55586270635341846769002881 41689702976506385076752161)
          ·
            refine ⟨31267277232379788807564121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41689702976506385076752161 31267277232379788807564121)
            ·
              refine ⟨23450457924284841605673091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31267277232379788807564121 23450457924284841605673091)
              ·
                refine ⟨35175686886427262408509637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23450457924284841605673091 35175686886427262408509637)
                ·
                  refine ⟨6595441291205111701595557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35175686886427262408509637 6595441291205111701595557)
                  ·
                    refine ⟨1236645242100958444049167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6595441291205111701595557 1236645242100958444049167)
                    ·
                      rfl

theorem cell22_3612537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 4, 4].length) (baseStart_3612537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3612537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3612537 prefixEnd_3612537 := by exact prefixLift 3612537
  have htrace : WordTrace (prefixWord ++ tailWord_3612537) baseStart_3612537 baseEnd_3612537 := by
    simpa [prefixWord, tailWord_3612537, baseEnd_3612537] using wordTrace_append hprefix tailTrace_3612537
  have hstable : (prefixWord ++ tailWord_3612537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612537).length < 2 ^ (prefixWord ++ tailWord_3612537).sum := by decide
  have hdescent : baseEnd_3612537 < baseStart_3612537 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3612693 : List Nat := [1, 3, 2, 1, 5, 1, 2, 3, 4]
def baseStart_3612693 : Nat := 118140960795 + 3612693 * 2 ^ 59
def prefixEnd_3612693 : Nat := 4983230072969 + 3 ^ 40 * 3612693 * 2
def baseEnd_3612693 : Nat := 412232881363008679049563

theorem tailTrace_3612693 : CollatzResearch.WordTrace tailWord_3612693 prefixEnd_3612693 412232881363008679049563 := by
  unfold tailWord_3612693
  simp only [CollatzResearch.WordTrace]
  refine ⟨131765738700837734687722733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87843825800558489791815155 131765738700837734687722733)
  ·
    refine ⟨49412152012814150507896025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131765738700837734687722733 49412152012814150507896025)
    ·
      refine ⟨37059114009610612880922019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49412152012814150507896025 37059114009610612880922019)
      ·
        refine ⟨55588671014415919321383029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37059114009610612880922019 55588671014415919321383029)
        ·
          refine ⟨5211437907601492436379659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55588671014415919321383029 5211437907601492436379659)
          ·
            refine ⟨7817156861402238654569489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5211437907601492436379659 7817156861402238654569489)
            ·
              refine ⟨5862867646051678990927117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7817156861402238654569489 5862867646051678990927117)
              ·
                refine ⟨2198575367269379621597669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5862867646051678990927117 2198575367269379621597669)
                ·
                  refine ⟨412232881363008679049563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2198575367269379621597669 412232881363008679049563)
                  ·
                    rfl

theorem cell22_3612693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 3, 4].length) (baseStart_3612693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3612693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3612693 prefixEnd_3612693 := by exact prefixLift 3612693
  have htrace : WordTrace (prefixWord ++ tailWord_3612693) baseStart_3612693 baseEnd_3612693 := by
    simpa [prefixWord, tailWord_3612693, baseEnd_3612693] using wordTrace_append hprefix tailTrace_3612693
  have hstable : (prefixWord ++ tailWord_3612693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612693).length < 2 ^ (prefixWord ++ tailWord_3612693).sum := by decide
  have hdescent : baseEnd_3612693 < baseStart_3612693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3612695 : List Nat := [1, 1, 3, 5, 2, 2, 2, 1, 1, 4]
def baseStart_3612695 : Nat := 118140960795 + 3612695 * 2 ^ 59
def prefixEnd_3612695 : Nat := 4983230072969 + 3 ^ 40 * 3612695 * 2
def baseEnd_3612695 : Nat := 1236699328729898698598683

theorem tailTrace_3612695 : CollatzResearch.WordTrace tailWord_3612695 prefixEnd_3612695 1236699328729898698598683 := by
  unfold tailWord_3612695
  simp only [CollatzResearch.WordTrace]
  refine ⟨131765811646830489029295539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87843874431220326019530359 131765811646830489029295539)
  ·
    refine ⟨197648717470245733543943309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131765811646830489029295539 197648717470245733543943309)
    ·
      refine ⟨74118269051342150078978741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197648717470245733543943309 74118269051342150078978741)
      ·
        refine ⟨6948587723563326569904257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74118269051342150078978741 6948587723563326569904257)
        ·
          refine ⟨5211440792672494927428193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6948587723563326569904257 5211440792672494927428193)
          ·
            refine ⟨3908580594504371195571145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5211440792672494927428193 3908580594504371195571145)
            ·
              refine ⟨2931435445878278396678359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3908580594504371195571145 2931435445878278396678359)
              ·
                refine ⟨4397153168817417595017539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2931435445878278396678359 4397153168817417595017539)
                ·
                  refine ⟨6595729753226126392526309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4397153168817417595017539 6595729753226126392526309)
                  ·
                    refine ⟨1236699328729898698598683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6595729753226126392526309 1236699328729898698598683)
                    ·
                      rfl

theorem cell22_3612695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 2, 1, 1, 4].length) (baseStart_3612695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3612695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3612695 prefixEnd_3612695 := by exact prefixLift 3612695
  have htrace : WordTrace (prefixWord ++ tailWord_3612695) baseStart_3612695 baseEnd_3612695 := by
    simpa [prefixWord, tailWord_3612695, baseEnd_3612695] using wordTrace_append hprefix tailTrace_3612695
  have hstable : (prefixWord ++ tailWord_3612695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612695).length < 2 ^ (prefixWord ++ tailWord_3612695).sum := by decide
  have hdescent : baseEnd_3612695 < baseStart_3612695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3612708 : List Nat := [2, 3, 1, 4, 2, 1, 1, 1, 4, 3]
def baseStart_3612708 : Nat := 118140960795 + 3612708 * 2 ^ 59
def prefixEnd_3612708 : Nat := 4983230072969 + 3 ^ 40 * 3612708 * 2
def baseEnd_3612708 : Nat := 1236703778895570998023643

theorem tailTrace_3612708 : CollatzResearch.WordTrace tailWord_3612708 prefixEnd_3612708 1236703778895570998023643 := by
  unfold tailWord_3612708
  simp only [CollatzResearch.WordTrace]
  refine ⟨65883142897891696124759389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87844190530522261499679185 65883142897891696124759389)
  ·
    refine ⟨24706178586709386046784771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65883142897891696124759389 24706178586709386046784771)
    ·
      refine ⟨37059267880064079070177157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24706178586709386046784771 37059267880064079070177157)
      ·
        refine ⟨6948612727512014825658217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37059267880064079070177157 6948612727512014825658217)
        ·
          refine ⟨5211459545634011119243663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6948612727512014825658217 5211459545634011119243663)
          ·
            refine ⟨7817189318451016678865495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5211459545634011119243663 7817189318451016678865495)
            ·
              refine ⟨11725783977676525018298243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7817189318451016678865495 11725783977676525018298243)
              ·
                refine ⟨17588675966514787527447365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11725783977676525018298243 17588675966514787527447365)
                ·
                  refine ⟨3297876743721522661396381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17588675966514787527447365 3297876743721522661396381)
                  ·
                    refine ⟨1236703778895570998023643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3297876743721522661396381 1236703778895570998023643)
                    ·
                      rfl

theorem cell22_3612708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 4, 3].length) (baseStart_3612708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3612708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3612708 prefixEnd_3612708 := by exact prefixLift 3612708
  have htrace : WordTrace (prefixWord ++ tailWord_3612708) baseStart_3612708 baseEnd_3612708 := by
    simpa [prefixWord, tailWord_3612708, baseEnd_3612708] using wordTrace_append hprefix tailTrace_3612708
  have hstable : (prefixWord ++ tailWord_3612708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612708).length < 2 ^ (prefixWord ++ tailWord_3612708).sum := by decide
  have hdescent : baseEnd_3612708 < baseStart_3612708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3612736 : List Nat := [2, 1, 1, 2, 2, 4, 2, 2, 3, 3]
def baseStart_3612736 : Nat := 118140960795 + 3612736 * 2 ^ 59
def prefixEnd_3612736 : Nat := 4983230072969 + 3 ^ 40 * 3612736 * 2
def baseEnd_3612736 : Nat := 1236713363867788258323557

theorem tailTrace_3612736 : CollatzResearch.WordTrace tailWord_3612736 prefixEnd_3612736 1236713363867788258323557 := by
  unfold tailWord_3612736
  simp only [CollatzResearch.WordTrace]
  refine ⟨65883653519840976515769031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87844871359787968687692041 65883653519840976515769031)
  ·
    refine ⟨98825480279761464773653547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65883653519840976515769031 98825480279761464773653547)
    ·
      refine ⟨148238220419642197160480321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98825480279761464773653547 148238220419642197160480321)
      ·
        refine ⟨111178665314731647870360241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148238220419642197160480321 111178665314731647870360241)
        ·
          refine ⟨83383998986048735902770181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111178665314731647870360241 83383998986048735902770181)
          ·
            refine ⟨15634499809884137981769409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83383998986048735902770181 15634499809884137981769409)
            ·
              refine ⟨11725874857413103486327057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15634499809884137981769409 11725874857413103486327057)
              ·
                refine ⟨8794406143059827614745293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11725874857413103486327057 8794406143059827614745293)
                ·
                  refine ⟨3297902303647435355529485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8794406143059827614745293 3297902303647435355529485)
                  ·
                    refine ⟨1236713363867788258323557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3297902303647435355529485 1236713363867788258323557)
                    ·
                      rfl

theorem cell22_3612736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 2, 3, 3].length) (baseStart_3612736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3612736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3612736 prefixEnd_3612736 := by exact prefixLift 3612736
  have htrace : WordTrace (prefixWord ++ tailWord_3612736) baseStart_3612736 baseEnd_3612736 := by
    simpa [prefixWord, tailWord_3612736, baseEnd_3612736] using wordTrace_append hprefix tailTrace_3612736
  have hstable : (prefixWord ++ tailWord_3612736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612736).length < 2 ^ (prefixWord ++ tailWord_3612736).sum := by decide
  have hdescent : baseEnd_3612736 < baseStart_3612736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
