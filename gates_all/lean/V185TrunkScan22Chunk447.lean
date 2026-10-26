import V185TrunkScan22Chunk446

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3984039 : List Nat := [1, 1, 6, 3, 1, 2, 1, 1, 2, 4]
def baseStart_3984039 : Nat := 118140960795 + 3984039 * 2 ^ 59
def prefixEnd_3984039 : Nat := 4983230072969 + 3 ^ 40 * 3984039 * 2
def baseEnd_3984039 : Nat := 1363817968838695441860163

theorem tailTrace_3984039 : CollatzResearch.WordTrace tailWord_3984039 prefixEnd_3984039 1363817968838695441860163 := by
  unfold tailWord_3984039
  simp only [CollatzResearch.WordTrace]
  refine ⟨145309840013514597535331171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96873226675676398356887447 145309840013514597535331171)
  ·
    refine ⟨217964760020271896302996757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145309840013514597535331171 217964760020271896302996757)
    ·
      refine ⟨10217098125950245139202973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 217964760020271896302996757 10217098125950245139202973)
      ·
        refine ⟨3831411797231341927201115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10217098125950245139202973 3831411797231341927201115)
        ·
          refine ⟨5747117695847012890801673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3831411797231341927201115 5747117695847012890801673)
          ·
            refine ⟨4310338271885259668101255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5747117695847012890801673 4310338271885259668101255)
            ·
              refine ⟨6465507407827889502151883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4310338271885259668101255 6465507407827889502151883)
              ·
                refine ⟨9698261111741834253227825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6465507407827889502151883 9698261111741834253227825)
                ·
                  refine ⟨7273695833806375689920869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9698261111741834253227825 7273695833806375689920869)
                  ·
                    refine ⟨1363817968838695441860163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7273695833806375689920869 1363817968838695441860163)
                    ·
                      rfl

theorem cell22_3984039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_3984039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3984039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3984039 prefixEnd_3984039 := by exact prefixLift 3984039
  have htrace : WordTrace (prefixWord ++ tailWord_3984039) baseStart_3984039 baseEnd_3984039 := by
    simpa [prefixWord, tailWord_3984039, baseEnd_3984039] using wordTrace_append hprefix tailTrace_3984039
  have hstable : (prefixWord ++ tailWord_3984039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984039).length < 2 ^ (prefixWord ++ tailWord_3984039).sum := by decide
  have hdescent : baseEnd_3984039 < baseStart_3984039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984063 : List Nat := [1, 1, 2, 2, 2, 4, 1, 2, 2, 5]
def baseStart_3984063 : Nat := 118140960795 + 3984063 * 2 ^ 59
def prefixEnd_3984063 : Nat := 4983230072969 + 3 ^ 40 * 3984063 * 2
def baseEnd_3984063 : Nat := 1363826184529167379260089

theorem tailTrace_3984063 : CollatzResearch.WordTrace tailWord_3984063 prefixEnd_3984063 1363826184529167379260089 := by
  unfold tailWord_3984063
  simp only [CollatzResearch.WordTrace]
  refine ⟨145310715365427649634204843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96873810243618433089469895 145310715365427649634204843)
  ·
    refine ⟨217966073048141474451307265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145310715365427649634204843 217966073048141474451307265)
    ·
      refine ⟨163474554786106105838480449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217966073048141474451307265 163474554786106105838480449)
      ·
        refine ⟨122605916089579579378860337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163474554786106105838480449 122605916089579579378860337)
        ·
          refine ⟨91954437067184684534145253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122605916089579579378860337 91954437067184684534145253)
          ·
            refine ⟨17241456950097128350152235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91954437067184684534145253 17241456950097128350152235)
            ·
              refine ⟨25862185425145692525228353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17241456950097128350152235 25862185425145692525228353)
              ·
                refine ⟨19396639068859269393921265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25862185425145692525228353 19396639068859269393921265)
                ·
                  refine ⟨14547479301644452045440949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19396639068859269393921265 14547479301644452045440949)
                  ·
                    refine ⟨1363826184529167379260089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14547479301644452045440949 1363826184529167379260089)
                    ·
                      rfl

theorem cell22_3984063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 2, 5].length) (baseStart_3984063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3984063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3984063 prefixEnd_3984063 := by exact prefixLift 3984063
  have htrace : WordTrace (prefixWord ++ tailWord_3984063) baseStart_3984063 baseEnd_3984063 := by
    simpa [prefixWord, tailWord_3984063, baseEnd_3984063] using wordTrace_append hprefix tailTrace_3984063
  have hstable : (prefixWord ++ tailWord_3984063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984063).length < 2 ^ (prefixWord ++ tailWord_3984063).sum := by decide
  have hdescent : baseEnd_3984063 < baseStart_3984063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984095 : List Nat := [1, 1, 2, 3, 2, 3, 1, 4, 1, 4]
def baseStart_3984095 : Nat := 118140960795 + 3984095 * 2 ^ 59
def prefixEnd_3984095 : Nat := 4983230072969 + 3 ^ 40 * 3984095 * 2
def baseEnd_3984095 : Nat := 1363837138783129962459991

theorem tailTrace_3984095 : CollatzResearch.WordTrace tailWord_3984095 prefixEnd_3984095 1363837138783129962459991 := by
  unfold tailWord_3984095
  simp only [CollatzResearch.WordTrace]
  refine ⟨145311882501311719099369739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96874588334207812732913159 145311882501311719099369739)
  ·
    refine ⟨217967823751967578649054609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145311882501311719099369739 217967823751967578649054609)
    ·
      refine ⟨163475867813975683986790957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217967823751967578649054609 163475867813975683986790957)
      ·
        refine ⟨61303450430240881495046609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163475867813975683986790957 61303450430240881495046609)
        ·
          refine ⟨45977587822680661121284957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61303450430240881495046609 45977587822680661121284957)
          ·
            refine ⟨17241595433505247920481859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45977587822680661121284957 17241595433505247920481859)
            ·
              refine ⟨25862393150257871880722789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17241595433505247920481859 25862393150257871880722789)
              ·
                refine ⟨4849198715673350977635523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25862393150257871880722789 4849198715673350977635523)
                ·
                  refine ⟨7273798073510026466453285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4849198715673350977635523 7273798073510026466453285)
                  ·
                    refine ⟨1363837138783129962459991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7273798073510026466453285 1363837138783129962459991)
                    ·
                      rfl

theorem cell22_3984095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 4, 1, 4].length) (baseStart_3984095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3984095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3984095 prefixEnd_3984095 := by exact prefixLift 3984095
  have htrace : WordTrace (prefixWord ++ tailWord_3984095) baseStart_3984095 baseEnd_3984095 := by
    simpa [prefixWord, tailWord_3984095, baseEnd_3984095] using wordTrace_append hprefix tailTrace_3984095
  have hstable : (prefixWord ++ tailWord_3984095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984095).length < 2 ^ (prefixWord ++ tailWord_3984095).sum := by decide
  have hdescent : baseEnd_3984095 < baseStart_3984095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984108 : List Nat := [2, 2, 1, 1, 2, 2, 1, 3, 3, 5]
def baseStart_3984108 : Nat := 118140960795 + 3984108 * 2 ^ 59
def prefixEnd_3984108 : Nat := 4983230072969 + 3 ^ 40 * 3984108 * 2
def baseEnd_3984108 : Nat := 1363841588948802261884951

theorem tailTrace_3984108 : CollatzResearch.WordTrace tailWord_3984108 prefixEnd_3984108 1363841588948802261884951 := by
  unfold tailWord_3984108
  simp only [CollatzResearch.WordTrace]
  refine ⟨72656178325132311159796489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96874904433509748213061985 72656178325132311159796489)
  ·
    refine ⟨54492133743849233369847367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72656178325132311159796489 54492133743849233369847367)
    ·
      refine ⟨81738200615773850054771051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54492133743849233369847367 81738200615773850054771051)
      ·
        refine ⟨122607300923660775082156577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81738200615773850054771051 122607300923660775082156577)
        ·
          refine ⟨91955475692745581311617433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122607300923660775082156577 91955475692745581311617433)
          ·
            refine ⟨68966606769559185983713075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91955475692745581311617433 68966606769559185983713075)
            ·
              refine ⟨103449910154338778975569613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68966606769559185983713075 103449910154338778975569613)
              ·
                refine ⟨38793716307877042115838605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103449910154338778975569613 38793716307877042115838605)
                ·
                  refine ⟨14547643615453890793439477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38793716307877042115838605 14547643615453890793439477)
                  ·
                    refine ⟨1363841588948802261884951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14547643615453890793439477 1363841588948802261884951)
                    ·
                      rfl

theorem cell22_3984108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 5].length) (baseStart_3984108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3984108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3984108 prefixEnd_3984108 := by exact prefixLift 3984108
  have htrace : WordTrace (prefixWord ++ tailWord_3984108) baseStart_3984108 baseEnd_3984108 := by
    simpa [prefixWord, tailWord_3984108, baseEnd_3984108] using wordTrace_append hprefix tailTrace_3984108
  have hstable : (prefixWord ++ tailWord_3984108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984108).length < 2 ^ (prefixWord ++ tailWord_3984108).sum := by decide
  have hdescent : baseEnd_3984108 < baseStart_3984108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984125 : List Nat := [1, 4, 1, 1, 1, 1, 3, 3, 4, 3]
def baseStart_3984125 : Nat := 118140960795 + 3984125 * 2 ^ 59
def prefixEnd_3984125 : Nat := 4983230072969 + 3 ^ 40 * 3984125 * 2
def baseEnd_3984125 : Nat := 1363847408396219884209899

theorem tailTrace_3984125 : CollatzResearch.WordTrace tailWord_3984125 prefixEnd_3984125 1363847408396219884209899 := by
  unfold tailWord_3984125
  simp only [CollatzResearch.WordTrace]
  refine ⟨145312976691203034222961829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96875317794135356148641219 145312976691203034222961829)
  ·
    refine ⟨27246183129600568916805343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145312976691203034222961829 27246183129600568916805343)
    ·
      refine ⟨40869274694400853375208015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27246183129600568916805343 40869274694400853375208015)
      ·
        refine ⟨61303912041601280062812023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40869274694400853375208015 61303912041601280062812023)
        ·
          refine ⟨91955868062401920094218035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61303912041601280062812023 91955868062401920094218035)
          ·
            refine ⟨137933802093602880141327053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91955868062401920094218035 137933802093602880141327053)
            ·
              refine ⟨51725175785101080052997645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137933802093602880141327053 51725175785101080052997645)
              ·
                refine ⟨19396940919412905019874117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51725175785101080052997645 19396940919412905019874117)
                ·
                  refine ⟨3636926422389919691226397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19396940919412905019874117 3636926422389919691226397)
                  ·
                    refine ⟨1363847408396219884209899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3636926422389919691226397 1363847408396219884209899)
                    ·
                      rfl

theorem cell22_3984125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 4, 3].length) (baseStart_3984125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3984125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3984125 prefixEnd_3984125 := by exact prefixLift 3984125
  have htrace : WordTrace (prefixWord ++ tailWord_3984125) baseStart_3984125 baseEnd_3984125 := by
    simpa [prefixWord, tailWord_3984125, baseEnd_3984125] using wordTrace_append hprefix tailTrace_3984125
  have hstable : (prefixWord ++ tailWord_3984125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984125).length < 2 ^ (prefixWord ++ tailWord_3984125).sum := by decide
  have hdescent : baseEnd_3984125 < baseStart_3984125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984146 : List Nat := [3, 2, 4, 1, 2, 2, 1, 2, 1, 4]
def baseStart_3984146 : Nat := 118140960795 + 3984146 * 2 ^ 59
def prefixEnd_3984146 : Nat := 4983230072969 + 3 ^ 40 * 3984146 * 2
def baseEnd_3984146 : Nat := 1363854597125382829434835

theorem tailTrace_3984146 : CollatzResearch.WordTrace tailWord_3984146 prefixEnd_3984146 1363854597125382829434835 := by
  unfold tailWord_3984146
  simp only [CollatzResearch.WordTrace]
  refine ⟨36328435656031738702369073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96875828416084636539650861 36328435656031738702369073)
  ·
    refine ⟨27246326742023804026776805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36328435656031738702369073 27246326742023804026776805)
    ·
      refine ⟨5108686264129463255020651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27246326742023804026776805 5108686264129463255020651)
      ·
        refine ⟨7663029396194194882530977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5108686264129463255020651 7663029396194194882530977)
        ·
          refine ⟨5747272047145646161898233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7663029396194194882530977 5747272047145646161898233)
          ·
            refine ⟨4310454035359234621423675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5747272047145646161898233 4310454035359234621423675)
            ·
              refine ⟨6465681053038851932135513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4310454035359234621423675 6465681053038851932135513)
              ·
                refine ⟨4849260789779138949101635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6465681053038851932135513 4849260789779138949101635)
                ·
                  refine ⟨7273891184668708423652453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4849260789779138949101635 7273891184668708423652453)
                  ·
                    refine ⟨1363854597125382829434835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7273891184668708423652453 1363854597125382829434835)
                    ·
                      rfl

theorem cell22_3984146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_3984146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3984146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3984146 prefixEnd_3984146 := by exact prefixLift 3984146
  have htrace : WordTrace (prefixWord ++ tailWord_3984146) baseStart_3984146 baseEnd_3984146 := by
    simpa [prefixWord, tailWord_3984146, baseEnd_3984146] using wordTrace_append hprefix tailTrace_3984146
  have hstable : (prefixWord ++ tailWord_3984146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984146).length < 2 ^ (prefixWord ++ tailWord_3984146).sum := by decide
  have hdescent : baseEnd_3984146 < baseStart_3984146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984189 : List Nat := [1, 4, 1, 4, 3, 1, 1, 7]
def baseStart_3984189 : Nat := 118140960795 + 3984189 * 2 ^ 59
def prefixEnd_3984189 : Nat := 4983230072969 + 3 ^ 40 * 3984189 * 2
def baseEnd_3984189 : Nat := 151541035211571672289967

theorem tailTrace_3984189 : CollatzResearch.WordTrace tailWord_3984189 prefixEnd_3984189 151541035211571672289967 := by
  unfold tailWord_3984189
  simp only [CollatzResearch.WordTrace]
  refine ⟨145315310962971173153291621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96876873975314115435527747 145315310962971173153291621)
  ·
    refine ⟨27246620805557094966242179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145315310962971173153291621 27246620805557094966242179)
    ·
      refine ⟨40869931208335642449363269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27246620805557094966242179 40869931208335642449363269)
      ·
        refine ⟨7663112101562932959255613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40869931208335642449363269 7663112101562932959255613)
        ·
          refine ⟨2873667038086099859720855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7663112101562932959255613 2873667038086099859720855)
          ·
            refine ⟨4310500557129149789581283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2873667038086099859720855 4310500557129149789581283)
            ·
              refine ⟨6465750835693724684371925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4310500557129149789581283 6465750835693724684371925)
              ·
                refine ⟨151541035211571672289967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6465750835693724684371925 151541035211571672289967)
                ·
                  rfl

theorem cell22_3984189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 7].length) (baseStart_3984189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3984189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3984189 prefixEnd_3984189 := by exact prefixLift 3984189
  have htrace : WordTrace (prefixWord ++ tailWord_3984189) baseStart_3984189 baseEnd_3984189 := by
    simpa [prefixWord, tailWord_3984189, baseEnd_3984189] using wordTrace_append hprefix tailTrace_3984189
  have hstable : (prefixWord ++ tailWord_3984189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984189).length < 2 ^ (prefixWord ++ tailWord_3984189).sum := by decide
  have hdescent : baseEnd_3984189 < baseStart_3984189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984200 : List Nat := [2, 1, 3, 1, 1, 3, 1, 5, 5]
def baseStart_3984200 : Nat := 118140960795 + 3984200 * 2 ^ 59
def prefixEnd_3984200 : Nat := 4983230072969 + 3 ^ 40 * 3984200 * 2
def baseEnd_3984200 : Nat := 454624360809648229528223

theorem tailTrace_3984200 : CollatzResearch.WordTrace tailWord_3984200 prefixEnd_3984200 454624360809648229528223 := by
  unfold tailWord_3984200
  simp only [CollatzResearch.WordTrace]
  refine ⟨72657856082965661015971027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96877141443954214687961369 72657856082965661015971027)
  ·
    refine ⟨108986784124448491523956541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72657856082965661015971027 108986784124448491523956541)
    ·
      refine ⟨40870044046668184321483703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108986784124448491523956541 40870044046668184321483703)
      ·
        refine ⟨61305066070002276482225555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40870044046668184321483703 61305066070002276482225555)
        ·
          refine ⟨91957599105003414723338333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61305066070002276482225555 91957599105003414723338333)
          ·
            refine ⟨34484099664376280521251875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91957599105003414723338333 34484099664376280521251875)
            ·
              refine ⟨51726149496564420781877813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34484099664376280521251875 51726149496564420781877813)
              ·
                refine ⟨4849326515302914448301045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51726149496564420781877813 4849326515302914448301045)
                ·
                  refine ⟨454624360809648229528223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4849326515302914448301045 454624360809648229528223)
                  ·
                    rfl

theorem cell22_3984200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 5, 5].length) (baseStart_3984200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3984200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3984200 prefixEnd_3984200 := by exact prefixLift 3984200
  have htrace : WordTrace (prefixWord ++ tailWord_3984200) baseStart_3984200 baseEnd_3984200 := by
    simpa [prefixWord, tailWord_3984200, baseEnd_3984200] using wordTrace_append hprefix tailTrace_3984200
  have hstable : (prefixWord ++ tailWord_3984200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984200).length < 2 ^ (prefixWord ++ tailWord_3984200).sum := by decide
  have hdescent : baseEnd_3984200 < baseStart_3984200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984264 : List Nat := [2, 1, 3, 3, 2, 2, 2, 2, 1, 4]
def baseStart_3984264 : Nat := 118140960795 + 3984264 * 2 ^ 59
def prefixEnd_3984264 : Nat := 4983230072969 + 3 ^ 40 * 3984264 * 2
def baseEnd_3984264 : Nat := 1363894990936869854984473

theorem tailTrace_3984264 : CollatzResearch.WordTrace tailWord_3984264 prefixEnd_3984264 1363894990936869854984473 := by
  unfold tailWord_3984264
  simp only [CollatzResearch.WordTrace]
  refine ⟨72659023218849730481135923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96878697625132973974847897 72659023218849730481135923)
  ·
    refine ⟨108988534828274595721703885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72659023218849730481135923 108988534828274595721703885)
    ·
      refine ⟨40870700560602973395638957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108988534828274595721703885 40870700560602973395638957)
      ·
        refine ⟨15326512710226115023364609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40870700560602973395638957 15326512710226115023364609)
        ·
          refine ⟨11494884532669586267523457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15326512710226115023364609 11494884532669586267523457)
          ·
            refine ⟨8621163399502189700642593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11494884532669586267523457 8621163399502189700642593)
            ·
              refine ⟨6465872549626642275481945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8621163399502189700642593 6465872549626642275481945)
              ·
                refine ⟨4849404412219981706611459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6465872549626642275481945 4849404412219981706611459)
                ·
                  refine ⟨7274106618329972559917189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4849404412219981706611459 7274106618329972559917189)
                  ·
                    refine ⟨1363894990936869854984473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7274106618329972559917189 1363894990936869854984473)
                    ·
                      rfl

theorem cell22_3984264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 2, 1, 4].length) (baseStart_3984264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3984264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3984264 prefixEnd_3984264 := by exact prefixLift 3984264
  have htrace : WordTrace (prefixWord ++ tailWord_3984264) baseStart_3984264 baseEnd_3984264 := by
    simpa [prefixWord, tailWord_3984264, baseEnd_3984264] using wordTrace_append hprefix tailTrace_3984264
  have hstable : (prefixWord ++ tailWord_3984264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984264).length < 2 ^ (prefixWord ++ tailWord_3984264).sum := by decide
  have hdescent : baseEnd_3984264 < baseStart_3984264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984277 : List Nat := [1, 3, 2, 1, 1, 4, 1, 2, 4, 3]
def baseStart_3984277 : Nat := 118140960795 + 3984277 * 2 ^ 59
def prefixEnd_3984277 : Nat := 4983230072969 + 3 ^ 40 * 3984277 * 2
def baseEnd_3984277 : Nat := 1363899441102542154409433

theorem tailTrace_3984277 : CollatzResearch.WordTrace tailWord_3984277 prefixEnd_3984277 1363899441102542154409433 := by
  unfold tailWord_3984277
  simp only [CollatzResearch.WordTrace]
  refine ⟨145318520586652364182495085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96879013724434909454996723 145318520586652364182495085)
  ·
    refine ⟨54494445219994636568435657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145318520586652364182495085 54494445219994636568435657)
    ·
      refine ⟨40870833914995977426326743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54494445219994636568435657 40870833914995977426326743)
      ·
        refine ⟨61306250872493966139490115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40870833914995977426326743 61306250872493966139490115)
        ·
          refine ⟨91959376308740949209235173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61306250872493966139490115 91959376308740949209235173)
          ·
            refine ⟨17242383057888927976731595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91959376308740949209235173 17242383057888927976731595)
            ·
              refine ⟨25863574586833391965097393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17242383057888927976731595 25863574586833391965097393)
              ·
                refine ⟨19397680940125043973823045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25863574586833391965097393 19397680940125043973823045)
                ·
                  refine ⟨3637065176273445745091821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19397680940125043973823045 3637065176273445745091821)
                  ·
                    refine ⟨1363899441102542154409433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3637065176273445745091821 1363899441102542154409433)
                    ·
                      rfl

theorem cell22_3984277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 4, 3].length) (baseStart_3984277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3984277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3984277 prefixEnd_3984277 := by exact prefixLift 3984277
  have htrace : WordTrace (prefixWord ++ tailWord_3984277) baseStart_3984277 baseEnd_3984277 := by
    simpa [prefixWord, tailWord_3984277, baseEnd_3984277] using wordTrace_append hprefix tailTrace_3984277
  have hstable : (prefixWord ++ tailWord_3984277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984277).length < 2 ^ (prefixWord ++ tailWord_3984277).sum := by decide
  have hdescent : baseEnd_3984277 < baseStart_3984277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984292 : List Nat := [2, 3, 1, 2, 1, 2, 3, 2, 2, 4]
def baseStart_3984292 : Nat := 118140960795 + 3984292 * 2 ^ 59
def prefixEnd_3984292 : Nat := 4983230072969 + 3 ^ 40 * 3984292 * 2
def baseEnd_3984292 : Nat := 1363904575909087115284387

theorem tailTrace_3984292 : CollatzResearch.WordTrace tailWord_3984292 prefixEnd_3984292 1363904575909087115284387 := by
  unfold tailWord_3984292
  simp only [CollatzResearch.WordTrace]
  refine ⟨72659533840799010872145565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96879378454398681162860753 72659533840799010872145565)
  ·
    refine ⟨27247325190299629077054587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72659533840799010872145565 27247325190299629077054587)
    ·
      refine ⟨40870987785449443615581881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27247325190299629077054587 40870987785449443615581881)
      ·
        refine ⟨30653240839087082711686411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40870987785449443615581881 30653240839087082711686411)
        ·
          refine ⟨45979861258630624067529617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30653240839087082711686411 45979861258630624067529617)
          ·
            refine ⟨34484895943972968050647213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45979861258630624067529617 34484895943972968050647213)
            ·
              refine ⟨12931835978989863018992705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34484895943972968050647213 12931835978989863018992705)
              ·
                refine ⟨9698876984242397264244529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12931835978989863018992705 9698876984242397264244529)
                ·
                  refine ⟨7274157738181797948183397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9698876984242397264244529 7274157738181797948183397)
                  ·
                    refine ⟨1363904575909087115284387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7274157738181797948183397 1363904575909087115284387)
                    ·
                      rfl

theorem cell22_3984292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 2, 2, 4].length) (baseStart_3984292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3984292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3984292 prefixEnd_3984292 := by exact prefixLift 3984292
  have htrace : WordTrace (prefixWord ++ tailWord_3984292) baseStart_3984292 baseEnd_3984292 := by
    simpa [prefixWord, tailWord_3984292, baseEnd_3984292] using wordTrace_append hprefix tailTrace_3984292
  have hstable : (prefixWord ++ tailWord_3984292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984292).length < 2 ^ (prefixWord ++ tailWord_3984292).sum := by decide
  have hdescent : baseEnd_3984292 < baseStart_3984292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984354 : List Nat := [3, 3, 3, 1, 1, 1, 1, 1, 2, 6]
def baseStart_3984354 : Nat := 118140960795 + 3984354 * 2 ^ 59
def prefixEnd_3984354 : Nat := 4983230072969 + 3 ^ 40 * 3984354 * 2
def baseEnd_3984354 : Nat := 1363925799776139620234197

theorem tailTrace_3984354 : CollatzResearch.WordTrace tailWord_3984354 prefixEnd_3984354 1363925799776139620234197 := by
  unfold tailWord_3984354
  simp only [CollatzResearch.WordTrace]
  refine ⟨36330332251843351583262029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96880886004915604222032077 36330332251843351583262029)
  ·
    refine ⟨13623874594441256843723261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36330332251843351583262029 13623874594441256843723261)
    ·
      refine ⟨5108952972915471316396223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13623874594441256843723261 5108952972915471316396223)
      ·
        refine ⟨7663429459373206974594335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5108952972915471316396223 7663429459373206974594335)
        ·
          refine ⟨11495144189059810461891503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7663429459373206974594335 11495144189059810461891503)
          ·
            refine ⟨17242716283589715692837255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11495144189059810461891503 17242716283589715692837255)
            ·
              refine ⟨25864074425384573539255883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17242716283589715692837255 25864074425384573539255883)
              ·
                refine ⟨38796111638076860308883825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25864074425384573539255883 38796111638076860308883825)
                ·
                  refine ⟨29097083728557645231662869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38796111638076860308883825 29097083728557645231662869)
                  ·
                    refine ⟨1363925799776139620234197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29097083728557645231662869 1363925799776139620234197)
                    ·
                      rfl

theorem cell22_3984354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_3984354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3984354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3984354 prefixEnd_3984354 := by exact prefixLift 3984354
  have htrace : WordTrace (prefixWord ++ tailWord_3984354) baseStart_3984354 baseEnd_3984354 := by
    simpa [prefixWord, tailWord_3984354, baseEnd_3984354] using wordTrace_append hprefix tailTrace_3984354
  have hstable : (prefixWord ++ tailWord_3984354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984354).length < 2 ^ (prefixWord ++ tailWord_3984354).sum := by decide
  have hdescent : baseEnd_3984354 < baseStart_3984354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984367 : List Nat := [1, 1, 2, 1, 4, 4, 1, 1, 2, 5]
def baseStart_3984367 : Nat := 118140960795 + 3984367 * 2 ^ 59
def prefixEnd_3984367 : Nat := 4983230072969 + 3 ^ 40 * 3984367 * 2
def baseEnd_3984367 : Nat := 1363930249941811919659157

theorem tailTrace_3984367 : CollatzResearch.WordTrace tailWord_3984367 prefixEnd_3984367 1363930249941811919659157 := by
  unfold tailWord_3984367
  simp only [CollatzResearch.WordTrace]
  refine ⟨145321803156326309553271355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96881202104217539702180903 145321803156326309553271355)
  ·
    refine ⟨217982704734489464329907033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145321803156326309553271355 217982704734489464329907033)
    ·
      refine ⟨163487028550867098247430275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217982704734489464329907033 163487028550867098247430275)
      ·
        refine ⟨245230542826300647371145413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163487028550867098247430275 245230542826300647371145413)
        ·
          refine ⟨45980726779931371382089765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 245230542826300647371145413 45980726779931371382089765)
          ·
            refine ⟨8621386271237132134141831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45980726779931371382089765 8621386271237132134141831)
            ·
              refine ⟨12932079406855698201212747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8621386271237132134141831 12932079406855698201212747)
              ·
                refine ⟨19398119110283547301819121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12932079406855698201212747 19398119110283547301819121)
                ·
                  refine ⟨14548589332712660476364341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19398119110283547301819121 14548589332712660476364341)
                  ·
                    refine ⟨1363930249941811919659157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14548589332712660476364341 1363930249941811919659157)
                    ·
                      rfl

theorem cell22_3984367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 2, 5].length) (baseStart_3984367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3984367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3984367 prefixEnd_3984367 := by exact prefixLift 3984367
  have htrace : WordTrace (prefixWord ++ tailWord_3984367) baseStart_3984367 baseEnd_3984367 := by
    simpa [prefixWord, tailWord_3984367, baseEnd_3984367] using wordTrace_append hprefix tailTrace_3984367
  have hstable : (prefixWord ++ tailWord_3984367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984367).length < 2 ^ (prefixWord ++ tailWord_3984367).sum := by decide
  have hdescent : baseEnd_3984367 < baseStart_3984367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984373 : List Nat := [1, 3, 5, 2, 1, 1, 1, 2, 3, 3]
def baseStart_3984373 : Nat := 118140960795 + 3984373 * 2 ^ 59
def prefixEnd_3984373 : Nat := 4983230072969 + 3 ^ 40 * 3984373 * 2
def baseEnd_3984373 : Nat := 1363932303864429904009139

theorem tailTrace_3984373 : CollatzResearch.WordTrace tailWord_3984373 prefixEnd_3984373 1363932303864429904009139 := by
  unfold tailWord_3984373
  simp only [CollatzResearch.WordTrace]
  refine ⟨145322021994304572577989773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96881347996203048385326515 145322021994304572577989773)
  ·
    refine ⟨54495758247864214716746165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145322021994304572577989773 54495758247864214716746165)
    ·
      refine ⟨5108977335737270129694953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54495758247864214716746165 5108977335737270129694953)
      ·
        refine ⟨3831733001802952597271215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5108977335737270129694953 3831733001802952597271215)
        ·
          refine ⟨5747599502704428895906823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3831733001802952597271215 5747599502704428895906823)
          ·
            refine ⟨8621399254056643343860235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5747599502704428895906823 8621399254056643343860235)
            ·
              refine ⟨12932098881084965015790353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8621399254056643343860235 12932098881084965015790353)
              ·
                refine ⟨9699074160813723761842765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12932098881084965015790353 9699074160813723761842765)
                ·
                  refine ⟨3637152810305146410691037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9699074160813723761842765 3637152810305146410691037)
                  ·
                    refine ⟨1363932303864429904009139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3637152810305146410691037 1363932303864429904009139)
                    ·
                      rfl

theorem cell22_3984373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_3984373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3984373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3984373 prefixEnd_3984373 := by exact prefixLift 3984373
  have htrace : WordTrace (prefixWord ++ tailWord_3984373) baseStart_3984373 baseEnd_3984373 := by
    simpa [prefixWord, tailWord_3984373, baseEnd_3984373] using wordTrace_append hprefix tailTrace_3984373
  have hstable : (prefixWord ++ tailWord_3984373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984373).length < 2 ^ (prefixWord ++ tailWord_3984373).sum := by decide
  have hdescent : baseEnd_3984373 < baseStart_3984373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984446 : List Nat := [4, 2, 1, 3, 1, 1, 1, 2, 4, 3]
def baseStart_3984446 : Nat := 118140960795 + 3984446 * 2 ^ 59
def prefixEnd_3984446 : Nat := 4983230072969 + 3 ^ 40 * 3984446 * 2
def baseEnd_3984446 : Nat := 1363957293256282046933915

theorem tailTrace_3984446 : CollatzResearch.WordTrace tailWord_3984446 prefixEnd_3984446 1363957293256282046933915 := by
  unfold tailWord_3984446
  simp only [CollatzResearch.WordTrace]
  refine ⟨18165585565380013255674649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96883123015360070696931461 18165585565380013255674649)
  ·
    refine ⟨13624189174035009941755987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18165585565380013255674649 13624189174035009941755987)
    ·
      refine ⟨20436283761052514912633981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13624189174035009941755987 20436283761052514912633981)
      ·
        refine ⟨7663606410394693092237743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20436283761052514912633981 7663606410394693092237743)
        ·
          refine ⟨11495409615592039638356615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7663606410394693092237743 11495409615592039638356615)
          ·
            refine ⟨17243114423388059457534923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11495409615592039638356615 17243114423388059457534923)
            ·
              refine ⟨25864671635082089186302385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17243114423388059457534923 25864671635082089186302385)
              ·
                refine ⟨19398503726311566889726789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25864671635082089186302385 19398503726311566889726789)
                ·
                  refine ⟨3637219448683418791823773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19398503726311566889726789 3637219448683418791823773)
                  ·
                    refine ⟨1363957293256282046933915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3637219448683418791823773 1363957293256282046933915)
                    ·
                      rfl

theorem cell22_3984446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 4, 3].length) (baseStart_3984446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3984446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3984446 prefixEnd_3984446 := by exact prefixLift 3984446
  have htrace : WordTrace (prefixWord ++ tailWord_3984446) baseStart_3984446 baseEnd_3984446 := by
    simpa [prefixWord, tailWord_3984446, baseEnd_3984446] using wordTrace_append hprefix tailTrace_3984446
  have hstable : (prefixWord ++ tailWord_3984446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984446).length < 2 ^ (prefixWord ++ tailWord_3984446).sum := by decide
  have hdescent : baseEnd_3984446 < baseStart_3984446 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984461 : List Nat := [1, 6, 1, 1, 1, 3, 1, 2, 2, 4]
def baseStart_3984461 : Nat := 118140960795 + 3984461 * 2 ^ 59
def prefixEnd_3984461 : Nat := 4983230072969 + 3 ^ 40 * 3984461 * 2
def baseEnd_3984461 : Nat := 1363962428062827007808869

theorem tailTrace_3984461 : CollatzResearch.WordTrace tailWord_3984461 prefixEnd_3984461 1363962428062827007808869 := by
  unfold tailWord_3984461
  simp only [CollatzResearch.WordTrace]
  refine ⟨145325231617985763607193237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96883487745323842404795491 145325231617985763607193237)
  ·
    refine ⟨6812120232093082669087183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 145325231617985763607193237 6812120232093082669087183)
    ·
      refine ⟨10218180348139624003630775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6812120232093082669087183 10218180348139624003630775)
      ·
        refine ⟨15327270522209436005446163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10218180348139624003630775 15327270522209436005446163)
        ·
          refine ⟨22990905783314154008169245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15327270522209436005446163 22990905783314154008169245)
          ·
            refine ⟨8621589668742807753063467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22990905783314154008169245 8621589668742807753063467)
            ·
              refine ⟨12932384503114211629595201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8621589668742807753063467 12932384503114211629595201)
              ·
                refine ⟨9699288377335658722196401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12932384503114211629595201 9699288377335658722196401)
                ·
                  refine ⟨7274466283001744041647301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9699288377335658722196401 7274466283001744041647301)
                  ·
                    refine ⟨1363962428062827007808869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7274466283001744041647301 1363962428062827007808869)
                    ·
                      rfl

theorem cell22_3984461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_3984461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3984461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3984461 prefixEnd_3984461 := by exact prefixLift 3984461
  have htrace : WordTrace (prefixWord ++ tailWord_3984461) baseStart_3984461 baseEnd_3984461 := by
    simpa [prefixWord, tailWord_3984461, baseEnd_3984461] using wordTrace_append hprefix tailTrace_3984461
  have hstable : (prefixWord ++ tailWord_3984461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984461).length < 2 ^ (prefixWord ++ tailWord_3984461).sum := by decide
  have hdescent : baseEnd_3984461 < baseStart_3984461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984472 : List Nat := [2, 1, 2, 2, 1, 3, 2, 1, 2, 6]
def baseStart_3984472 : Nat := 118140960795 + 3984472 * 2 ^ 59
def prefixEnd_3984472 : Nat := 4983230072969 + 3 ^ 40 * 3984472 * 2
def baseEnd_3984472 : Nat := 1363966193587626645783835

theorem tailTrace_3984472 : CollatzResearch.WordTrace tailWord_3984472 prefixEnd_3984472 1363966193587626645783835 := by
  unfold tailWord_3984472
  simp only [CollatzResearch.WordTrace]
  refine ⟨72662816410472956242921835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96883755213963941657229113 72662816410472956242921835)
  ·
    refine ⟨108994224615709434364382753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72662816410472956242921835 108994224615709434364382753)
    ·
      refine ⟨81745668461782075773287065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108994224615709434364382753 81745668461782075773287065)
      ·
        refine ⟨61309251346336556829965299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81745668461782075773287065 61309251346336556829965299)
        ·
          refine ⟨91963877019504835244947949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61309251346336556829965299 91963877019504835244947949)
          ·
            refine ⟨34486453882314313216855481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91963877019504835244947949 34486453882314313216855481)
            ·
              refine ⟨25864840411735734912641611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34486453882314313216855481 25864840411735734912641611)
              ·
                refine ⟨38797260617603602368962417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25864840411735734912641611 38797260617603602368962417)
                ·
                  refine ⟨29097945463202701776721813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38797260617603602368962417 29097945463202701776721813)
                  ·
                    refine ⟨1363966193587626645783835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29097945463202701776721813 1363966193587626645783835)
                    ·
                      rfl

theorem cell22_3984472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 2, 6].length) (baseStart_3984472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3984472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3984472 prefixEnd_3984472 := by exact prefixLift 3984472
  have htrace : WordTrace (prefixWord ++ tailWord_3984472) baseStart_3984472 baseEnd_3984472 := by
    simpa [prefixWord, tailWord_3984472, baseEnd_3984472] using wordTrace_append hprefix tailTrace_3984472
  have hstable : (prefixWord ++ tailWord_3984472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984472).length < 2 ^ (prefixWord ++ tailWord_3984472).sum := by decide
  have hdescent : baseEnd_3984472 < baseStart_3984472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984474 : List Nat := [3, 1, 1, 2, 1, 1, 2, 5, 3, 3]
def baseStart_3984474 : Nat := 118140960795 + 3984474 * 2 ^ 59
def prefixEnd_3984474 : Nat := 4983230072969 + 3 ^ 40 * 3984474 * 2
def baseEnd_3984474 : Nat := 1363966878228499307233829

theorem tailTrace_3984474 : CollatzResearch.WordTrace tailWord_3984474 prefixEnd_3984474 1363966878228499307233829 := by
  unfold tailWord_3984474
  simp only [CollatzResearch.WordTrace]
  refine ⟨36331426441734666706854119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96883803844625777884944317 36331426441734666706854119)
  ·
    refine ⟨54497139662602000060281179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36331426441734666706854119 54497139662602000060281179)
    ·
      refine ⟨81745709493903000090421769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54497139662602000060281179 81745709493903000090421769)
      ·
        refine ⟨61309282120427250067816327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81745709493903000090421769 61309282120427250067816327)
        ·
          refine ⟨91963923180640875101724491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61309282120427250067816327 91963923180640875101724491)
          ·
            refine ⟨137945884770961312652586737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91963923180640875101724491 137945884770961312652586737)
            ·
              refine ⟨103459413578220984489440053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137945884770961312652586737 103459413578220984489440053)
              ·
                refine ⟨9699320022958217295885005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103459413578220984489440053 9699320022958217295885005)
                ·
                  refine ⟨3637245008609331485956877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9699320022958217295885005 3637245008609331485956877)
                  ·
                    refine ⟨1363966878228499307233829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3637245008609331485956877 1363966878228499307233829)
                    ·
                      rfl

theorem cell22_3984474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 5, 3, 3].length) (baseStart_3984474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3984474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3984474 prefixEnd_3984474 := by exact prefixLift 3984474
  have htrace : WordTrace (prefixWord ++ tailWord_3984474) baseStart_3984474 baseEnd_3984474 := by
    simpa [prefixWord, tailWord_3984474, baseEnd_3984474] using wordTrace_append hprefix tailTrace_3984474
  have hstable : (prefixWord ++ tailWord_3984474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984474).length < 2 ^ (prefixWord ++ tailWord_3984474).sum := by decide
  have hdescent : baseEnd_3984474 < baseStart_3984474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984549 : List Nat := [1, 3, 1, 2, 1, 5, 1, 2, 6]
def baseStart_3984549 : Nat := 118140960795 + 3984549 * 2 ^ 59
def prefixEnd_3984549 : Nat := 4983230072969 + 3 ^ 40 * 3984549 * 2
def baseEnd_3984549 : Nat := 454664184087074703869533

theorem tailTrace_3984549 : CollatzResearch.WordTrace tailWord_3984549 prefixEnd_3984549 454664184087074703869533 := by
  unfold tailWord_3984549
  simp only [CollatzResearch.WordTrace]
  refine ⟨145328441241666954636396701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96885627494444636424264467 145328441241666954636396701)
  ·
    refine ⟨54498165465625107988648763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145328441241666954636396701 54498165465625107988648763)
    ·
      refine ⟨81747248198437661982973145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54498165465625107988648763 81747248198437661982973145)
      ·
        refine ⟨61310436148828246487229859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81747248198437661982973145 61310436148828246487229859)
        ·
          refine ⟨91965654223242369730844789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61310436148828246487229859 91965654223242369730844789)
          ·
            refine ⟨8621780083428972162266699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91965654223242369730844789 8621780083428972162266699)
            ·
              refine ⟨12932670125143458243400049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8621780083428972162266699 12932670125143458243400049)
              ·
                refine ⟨9699502593857593682550037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12932670125143458243400049 9699502593857593682550037)
                ·
                  refine ⟨454664184087074703869533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9699502593857593682550037 454664184087074703869533)
                  ·
                    rfl

theorem cell22_3984549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 2, 6].length) (baseStart_3984549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3984549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3984549 prefixEnd_3984549 := by exact prefixLift 3984549
  have htrace : WordTrace (prefixWord ++ tailWord_3984549) baseStart_3984549 baseEnd_3984549 := by
    simpa [prefixWord, tailWord_3984549, baseEnd_3984549] using wordTrace_append hprefix tailTrace_3984549
  have hstable : (prefixWord ++ tailWord_3984549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984549).length < 2 ^ (prefixWord ++ tailWord_3984549).sum := by decide
  have hdescent : baseEnd_3984549 < baseStart_3984549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984551 : List Nat := [1, 1, 6, 2, 1, 1, 2, 1, 3, 4]
def baseStart_3984551 : Nat := 118140960795 + 3984551 * 2 ^ 59
def prefixEnd_3984551 : Nat := 4983230072969 + 3 ^ 40 * 3984551 * 2
def baseEnd_3984551 : Nat := 1363993236902096773058593

theorem tailTrace_3984551 : CollatzResearch.WordTrace tailWord_3984551 prefixEnd_3984551 1363993236902096773058593 := by
  unfold tailWord_3984551
  simp only [CollatzResearch.WordTrace]
  refine ⟨145328514187659708977969507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96885676125106472651979671 145328514187659708977969507)
  ·
    refine ⟨217992771281489563466954261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145328514187659708977969507 217992771281489563466954261)
    ·
      refine ⟨10218411153819823287513481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 217992771281489563466954261 10218411153819823287513481)
      ·
        refine ⟨7663808365364867465635111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10218411153819823287513481 7663808365364867465635111)
        ·
          refine ⟨11495712548047301198452667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7663808365364867465635111 11495712548047301198452667)
          ·
            refine ⟨17243568822070951797679001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11495712548047301198452667 17243568822070951797679001)
            ·
              refine ⟨12932676616553213848259251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17243568822070951797679001 12932676616553213848259251)
              ·
                refine ⟨19399014924829820772388877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12932676616553213848259251 19399014924829820772388877)
                ·
                  refine ⟨7274630596811182789645829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19399014924829820772388877 7274630596811182789645829)
                  ·
                    refine ⟨1363993236902096773058593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7274630596811182789645829 1363993236902096773058593)
                    ·
                      rfl

theorem cell22_3984551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_3984551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3984551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3984551 prefixEnd_3984551 := by exact prefixLift 3984551
  have htrace : WordTrace (prefixWord ++ tailWord_3984551) baseStart_3984551 baseEnd_3984551 := by
    simpa [prefixWord, tailWord_3984551, baseEnd_3984551] using wordTrace_append hprefix tailTrace_3984551
  have hstable : (prefixWord ++ tailWord_3984551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984551).length < 2 ^ (prefixWord ++ tailWord_3984551).sum := by decide
  have hdescent : baseEnd_3984551 < baseStart_3984551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984594 : List Nat := [3, 2, 2, 2, 1, 1, 2, 9]
def baseStart_3984594 : Nat := 118140960795 + 3984594 * 2 ^ 59
def prefixEnd_3984594 : Nat := 4983230072969 + 3 ^ 40 * 3984594 * 2
def baseEnd_3984594 : Nat := 151556439631206554914829

theorem tailTrace_3984594 : CollatzResearch.WordTrace tailWord_3984594 prefixEnd_3984594 151556439631206554914829 := by
  unfold tailWord_3984594
  simp only [CollatzResearch.WordTrace]
  refine ⟨36332520631625981830446209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96886721684335951547856557 36332520631625981830446209)
  ·
    refine ⟨27249390473719486372834657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36332520631625981830446209 27249390473719486372834657)
    ·
      refine ⟨20437042855289614779625993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27249390473719486372834657 20437042855289614779625993)
      ·
        refine ⟨15327782141467211084719495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20437042855289614779625993 15327782141467211084719495)
        ·
          refine ⟨22991673212200816627079243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15327782141467211084719495 22991673212200816627079243)
          ·
            refine ⟨34487509818301224940618865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22991673212200816627079243 34487509818301224940618865)
            ·
              refine ⟨25865632363725918705464149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34487509818301224940618865 25865632363725918705464149)
              ·
                refine ⟨151556439631206554914829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25865632363725918705464149 151556439631206554914829)
                ·
                  rfl

theorem cell22_3984594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 9].length) (baseStart_3984594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3984594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3984594 prefixEnd_3984594 := by exact prefixLift 3984594
  have htrace : WordTrace (prefixWord ++ tailWord_3984594) baseStart_3984594 baseEnd_3984594 := by
    simpa [prefixWord, tailWord_3984594, baseEnd_3984594] using wordTrace_append hprefix tailTrace_3984594
  have hstable : (prefixWord ++ tailWord_3984594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984594).length < 2 ^ (prefixWord ++ tailWord_3984594).sum := by decide
  have hdescent : baseEnd_3984594 < baseStart_3984594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984639 : List Nat := [1, 1, 2, 2, 1, 5, 2, 1, 7]
def baseStart_3984639 : Nat := 118140960795 + 3984639 * 2 ^ 59
def prefixEnd_3984639 : Nat := 4983230072969 + 3 ^ 40 * 3984639 * 2
def baseEnd_3984639 : Nat := 454674453700164625619441

theorem tailTrace_3984639 : CollatzResearch.WordTrace tailWord_3984639 prefixEnd_3984639 454674453700164625619441 := by
  unfold tailWord_3984639
  simp only [CollatzResearch.WordTrace]
  refine ⟨145331723811340900007172971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96887815874227266671448647 145331723811340900007172971)
  ·
    refine ⟨217997585717011350010759457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145331723811340900007172971 217997585717011350010759457)
    ·
      refine ⟨163498189287758512508069593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217997585717011350010759457 163498189287758512508069593)
      ·
        refine ⟨122623641965818884381052195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163498189287758512508069593 122623641965818884381052195)
        ·
          refine ⟨183935462948728326571578293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122623641965818884381052195 183935462948728326571578293)
          ·
            refine ⟨17243949651443280616085465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 183935462948728326571578293 17243949651443280616085465)
            ·
              refine ⟨12932962238582460462064099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17243949651443280616085465 12932962238582460462064099)
              ·
                refine ⟨19399443357873690693096149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12932962238582460462064099 19399443357873690693096149)
                ·
                  refine ⟨454674453700164625619441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19399443357873690693096149 454674453700164625619441)
                  ·
                    rfl

theorem cell22_3984639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 7].length) (baseStart_3984639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3984639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3984639 prefixEnd_3984639 := by exact prefixLift 3984639
  have htrace : WordTrace (prefixWord ++ tailWord_3984639) baseStart_3984639 baseEnd_3984639 := by
    simpa [prefixWord, tailWord_3984639, baseEnd_3984639] using wordTrace_append hprefix tailTrace_3984639
  have hstable : (prefixWord ++ tailWord_3984639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984639).length < 2 ^ (prefixWord ++ tailWord_3984639).sum := by decide
  have hdescent : baseEnd_3984639 < baseStart_3984639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984643 : List Nat := [1, 1, 1, 3, 2, 6, 1, 1, 3, 3]
def baseStart_3984643 : Nat := 118140960795 + 3984643 * 2 ^ 59
def prefixEnd_3984643 : Nat := 4983230072969 + 3 ^ 40 * 3984643 * 2
def baseEnd_3984643 : Nat := 1364024730382239199758311

theorem tailTrace_3984643 : CollatzResearch.WordTrace tailWord_3984643 prefixEnd_3984643 1364024730382239199758311 := by
  unfold tailWord_3984643
  simp only [CollatzResearch.WordTrace]
  refine ⟨145331869703326408690318583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96887913135550939126879055 145331869703326408690318583)
  ·
    refine ⟨217997804554989613035477875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145331869703326408690318583 217997804554989613035477875)
    ·
      refine ⟨326996706832484419553216813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217997804554989613035477875 326996706832484419553216813)
      ·
        refine ⟨122623765062181657332456305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 326996706832484419553216813 122623765062181657332456305)
        ·
          refine ⟨91967823796636242999342229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122623765062181657332456305 91967823796636242999342229)
          ·
            refine ⟨4310991740467323890594167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 91967823796636242999342229 4310991740467323890594167)
            ·
              refine ⟨6466487610700985835891251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4310991740467323890594167 6466487610700985835891251)
              ·
                refine ⟨9699731416051478753836877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6466487610700985835891251 9699731416051478753836877)
                ·
                  refine ⟨3637399281019304532688829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9699731416051478753836877 3637399281019304532688829)
                  ·
                    refine ⟨1364024730382239199758311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3637399281019304532688829 1364024730382239199758311)
                    ·
                      rfl

theorem cell22_3984643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 1, 3, 3].length) (baseStart_3984643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3984643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3984643 prefixEnd_3984643 := by exact prefixLift 3984643
  have htrace : WordTrace (prefixWord ++ tailWord_3984643) baseStart_3984643 baseEnd_3984643 := by
    simpa [prefixWord, tailWord_3984643, baseEnd_3984643] using wordTrace_append hprefix tailTrace_3984643
  have hstable : (prefixWord ++ tailWord_3984643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984643).length < 2 ^ (prefixWord ++ tailWord_3984643).sum := by decide
  have hdescent : baseEnd_3984643 < baseStart_3984643 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984694 : List Nat := [5, 1, 2, 3, 1, 1, 1, 4, 1, 3]
def baseStart_3984694 : Nat := 118140960795 + 3984694 * 2 ^ 59
def prefixEnd_3984694 : Nat := 4983230072969 + 3 ^ 40 * 3984694 * 2
def baseEnd_3984694 : Nat := 1364042188724492066733155

theorem tailTrace_3984694 : CollatzResearch.WordTrace tailWord_3984694 prefixEnd_3984694 1364042188724492066733155 := by
  unfold tailWord_3984694
  simp only [CollatzResearch.WordTrace]
  refine ⟨9083358114133852775026571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96889153217427762933616757 9083358114133852775026571)
  ·
    refine ⟨13625037171200779162539857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9083358114133852775026571 13625037171200779162539857)
    ·
      refine ⟨10218777878400584371904893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13625037171200779162539857 10218777878400584371904893)
      ·
        refine ⟨3832041704400219139464335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10218777878400584371904893 3832041704400219139464335)
        ·
          refine ⟨5748062556600328709196503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3832041704400219139464335 5748062556600328709196503)
          ·
            refine ⟨8622093834900493063794755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5748062556600328709196503 8622093834900493063794755)
            ·
              refine ⟨12933140752350739595692133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8622093834900493063794755 12933140752350739595692133)
              ·
                refine ⟨2424963891065763674192275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12933140752350739595692133 2424963891065763674192275)
                ·
                  refine ⟨3637445836598645511288413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2424963891065763674192275 3637445836598645511288413)
                  ·
                    refine ⟨1364042188724492066733155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3637445836598645511288413 1364042188724492066733155)
                    ·
                      rfl

theorem cell22_3984694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_3984694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3984694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3984694 prefixEnd_3984694 := by exact prefixLift 3984694
  have htrace : WordTrace (prefixWord ++ tailWord_3984694) baseStart_3984694 baseEnd_3984694 := by
    simpa [prefixWord, tailWord_3984694, baseEnd_3984694] using wordTrace_append hprefix tailTrace_3984694
  have hstable : (prefixWord ++ tailWord_3984694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984694).length < 2 ^ (prefixWord ++ tailWord_3984694).sum := by decide
  have hdescent : baseEnd_3984694 < baseStart_3984694 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984716 : List Nat := [2, 2, 1, 3, 2, 2, 1, 3, 1, 5]
def baseStart_3984716 : Nat := 118140960795 + 3984716 * 2 ^ 59
def prefixEnd_3984716 : Nat := 4983230072969 + 3 ^ 40 * 3984716 * 2
def baseEnd_3984716 : Nat := 1364049719774091342683087

theorem tailTrace_3984716 : CollatzResearch.WordTrace tailWord_3984716 prefixEnd_3984716 1364049719774091342683087 := by
  unfold tailWord_3984716
  simp only [CollatzResearch.WordTrace]
  refine ⟨72667266116030971078863001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96889688154707961438484001 72667266116030971078863001)
  ·
    refine ⟨54500449587023228309147251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72667266116030971078863001 54500449587023228309147251)
    ·
      refine ⟨81750674380534842463720877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54500449587023228309147251 81750674380534842463720877)
      ·
        refine ⟨30656502892700565923895329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81750674380534842463720877 30656502892700565923895329)
        ·
          refine ⟨22992377169525424442921497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30656502892700565923895329 22992377169525424442921497)
          ·
            refine ⟨17244282877144068332191123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22992377169525424442921497 17244282877144068332191123)
            ·
              refine ⟨25866424315716102498286685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17244282877144068332191123 25866424315716102498286685)
              ·
                refine ⟨9699909118393538436857507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25866424315716102498286685 9699909118393538436857507)
                ·
                  refine ⟨14549863677590307655286261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9699909118393538436857507 14549863677590307655286261)
                  ·
                    refine ⟨1364049719774091342683087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14549863677590307655286261 1364049719774091342683087)
                    ·
                      rfl

theorem cell22_3984716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 3, 1, 5].length) (baseStart_3984716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3984716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3984716 prefixEnd_3984716 := by exact prefixLift 3984716
  have htrace : WordTrace (prefixWord ++ tailWord_3984716) baseStart_3984716 baseEnd_3984716 := by
    simpa [prefixWord, tailWord_3984716, baseEnd_3984716] using wordTrace_append hprefix tailTrace_3984716
  have hstable : (prefixWord ++ tailWord_3984716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984716).length < 2 ^ (prefixWord ++ tailWord_3984716).sum := by decide
  have hdescent : baseEnd_3984716 < baseStart_3984716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984729 : List Nat := [1, 2, 1, 2, 2, 2, 2, 10]
def baseStart_3984729 : Nat := 118140960795 + 3984729 * 2 ^ 59
def prefixEnd_3984729 : Nat := 4983230072969 + 3 ^ 40 * 3984729 * 2
def baseEnd_3984729 : Nat := 151561574437751515789783

theorem tailTrace_3984729 : CollatzResearch.WordTrace tailWord_3984729 prefixEnd_3984729 151561574437751515789783 := by
  unfold tailWord_3984729
  simp only [CollatzResearch.WordTrace]
  refine ⟨145335006381014845377949241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96890004254009896918632827 145335006381014845377949241)
  ·
    refine ⟨109001254785761134033461931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145335006381014845377949241 109001254785761134033461931)
    ·
      refine ⟨163501882178641701050192897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109001254785761134033461931 163501882178641701050192897)
      ·
        refine ⟨122626411633981275787644673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163501882178641701050192897 122626411633981275787644673)
        ·
          refine ⟨91969808725485956840733505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122626411633981275787644673 91969808725485956840733505)
          ·
            refine ⟨68977356544114467630550129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91969808725485956840733505 68977356544114467630550129)
            ·
              refine ⟨51733017408085850722912597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68977356544114467630550129 51733017408085850722912597)
              ·
                refine ⟨151561574437751515789783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 51733017408085850722912597 151561574437751515789783)
                ·
                  rfl

theorem cell22_3984729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 10].length) (baseStart_3984729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3984729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3984729 prefixEnd_3984729 := by exact prefixLift 3984729
  have htrace : WordTrace (prefixWord ++ tailWord_3984729) baseStart_3984729 baseEnd_3984729 := by
    simpa [prefixWord, tailWord_3984729, baseEnd_3984729] using wordTrace_append hprefix tailTrace_3984729
  have hstable : (prefixWord ++ tailWord_3984729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984729).length < 2 ^ (prefixWord ++ tailWord_3984729).sum := by decide
  have hdescent : baseEnd_3984729 < baseStart_3984729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984868 : List Nat := [2, 3, 1, 1, 1, 1, 1, 5, 4, 3]
def baseStart_3984868 : Nat := 118140960795 + 3984868 * 2 ^ 59
def prefixEnd_3984868 : Nat := 4983230072969 + 3 ^ 40 * 3984868 * 2
def baseEnd_3984868 : Nat := 1364101752480413612882621

theorem tailTrace_3984868 : CollatzResearch.WordTrace tailWord_3984868 prefixEnd_3984868 1364101752480413612882621 := by
  unfold tailWord_3984868
  simp only [CollatzResearch.WordTrace]
  refine ⟨72670038063755636058629629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96893384085007514744839505 72670038063755636058629629)
  ·
    refine ⟨27251264273908363521986111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72670038063755636058629629 27251264273908363521986111)
    ·
      refine ⟨40876896410862545282979167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27251264273908363521986111 40876896410862545282979167)
      ·
        refine ⟨61315344616293817924468751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40876896410862545282979167 61315344616293817924468751)
        ·
          refine ⟨91973016924440726886703127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61315344616293817924468751 91973016924440726886703127)
          ·
            refine ⟨137959525386661090330054691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91973016924440726886703127 137959525386661090330054691)
            ·
              refine ⟨206939288079991635495082037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137959525386661090330054691 206939288079991635495082037)
              ·
                refine ⟨19400558257499215827663941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 206939288079991635495082037 19400558257499215827663941)
                ·
                  refine ⟨3637604673281102967686989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19400558257499215827663941 3637604673281102967686989)
                  ·
                    refine ⟨1364101752480413612882621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3637604673281102967686989 1364101752480413612882621)
                    ·
                      rfl

theorem cell22_3984868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 4, 3].length) (baseStart_3984868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3984868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3984868 prefixEnd_3984868 := by exact prefixLift 3984868
  have htrace : WordTrace (prefixWord ++ tailWord_3984868) baseStart_3984868 baseEnd_3984868 := by
    simpa [prefixWord, tailWord_3984868, baseEnd_3984868] using wordTrace_append hprefix tailTrace_3984868
  have hstable : (prefixWord ++ tailWord_3984868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984868).length < 2 ^ (prefixWord ++ tailWord_3984868).sum := by decide
  have hdescent : baseEnd_3984868 < baseStart_3984868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984885 : List Nat := [1, 3, 5, 1, 1, 1, 1, 3, 1, 5]
def baseStart_3984885 : Nat := 118140960795 + 3984885 * 2 ^ 59
def prefixEnd_3984885 : Nat := 4983230072969 + 3 ^ 40 * 3984885 * 2
def baseEnd_3984885 : Nat := 1364107571927831235207569

theorem tailTrace_3984885 : CollatzResearch.WordTrace tailWord_3984885 prefixEnd_3984885 1364107571927831235207569 := by
  unfold tailWord_3984885
  simp only [CollatzResearch.WordTrace]
  refine ⟨145340696168449684020628109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96893797445633122680418739 145340696168449684020628109)
  ·
    refine ⟨54502761063168631507735541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145340696168449684020628109 54502761063168631507735541)
    ·
      refine ⟨5109633849672059203850207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54502761063168631507735541 5109633849672059203850207)
      ·
        refine ⟨7664450774508088805775311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5109633849672059203850207 7664450774508088805775311)
        ·
          refine ⟨11496676161762133208662967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7664450774508088805775311 11496676161762133208662967)
          ·
            refine ⟨17245014242643199812994451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11496676161762133208662967 17245014242643199812994451)
            ·
              refine ⟨25867521363964799719491677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17245014242643199812994451 25867521363964799719491677)
              ·
                refine ⟨9700320511486799894809379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25867521363964799719491677 9700320511486799894809379)
                ·
                  refine ⟨14550480767230199842214069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9700320511486799894809379 14550480767230199842214069)
                  ·
                    refine ⟨1364107571927831235207569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14550480767230199842214069 1364107571927831235207569)
                    ·
                      rfl

theorem cell22_3984885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_3984885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3984885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3984885 prefixEnd_3984885 := by exact prefixLift 3984885
  have htrace : WordTrace (prefixWord ++ tailWord_3984885) baseStart_3984885 baseEnd_3984885 := by
    simpa [prefixWord, tailWord_3984885, baseEnd_3984885] using wordTrace_append hprefix tailTrace_3984885
  have hstable : (prefixWord ++ tailWord_3984885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984885).length < 2 ^ (prefixWord ++ tailWord_3984885).sum := by decide
  have hdescent : baseEnd_3984885 < baseStart_3984885 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984900 : List Nat := [2, 3, 2, 3, 2, 1, 1, 1, 1, 6]
def baseStart_3984900 : Nat := 118140960795 + 3984900 * 2 ^ 59
def prefixEnd_3984900 : Nat := 4983230072969 + 3 ^ 40 * 3984900 * 2
def baseEnd_3984900 : Nat := 1364112706734376196082523

theorem tailTrace_3984900 : CollatzResearch.WordTrace tailWord_3984900 prefixEnd_3984900 1364112706734376196082523 := by
  unfold tailWord_3984900
  simp only [CollatzResearch.WordTrace]
  refine ⟨72670621631697670791212077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96894162175596894388282769 72670621631697670791212077)
  ·
    refine ⟨27251483111886626546704529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72670621631697670791212077 27251483111886626546704529)
    ·
      refine ⟨20438612333914969910028397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27251483111886626546704529 20438612333914969910028397)
      ·
        refine ⟨7664479625218113716260649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20438612333914969910028397 7664479625218113716260649)
        ·
          refine ⟨5748359718913585287195487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7664479625218113716260649 5748359718913585287195487)
          ·
            refine ⟨8622539578370377930793231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5748359718913585287195487 8622539578370377930793231)
            ·
              refine ⟨12933809367555566896189847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8622539578370377930793231 12933809367555566896189847)
              ·
                refine ⟨19400714051333350344284771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12933809367555566896189847 19400714051333350344284771)
                ·
                  refine ⟨29101071077000025516427157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19400714051333350344284771 29101071077000025516427157)
                  ·
                    refine ⟨1364112706734376196082523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29101071077000025516427157 1364112706734376196082523)
                    ·
                      rfl

theorem cell22_3984900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_3984900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3984900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3984900 prefixEnd_3984900 := by exact prefixLift 3984900
  have htrace : WordTrace (prefixWord ++ tailWord_3984900) baseStart_3984900 baseEnd_3984900 := by
    simpa [prefixWord, tailWord_3984900, baseEnd_3984900] using wordTrace_append hprefix tailTrace_3984900
  have hstable : (prefixWord ++ tailWord_3984900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984900).length < 2 ^ (prefixWord ++ tailWord_3984900).sum := by decide
  have hdescent : baseEnd_3984900 < baseStart_3984900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984913 : List Nat := [1, 2, 2, 1, 1, 2, 3, 2, 5, 3]
def baseStart_3984913 : Nat := 118140960795 + 3984913 * 2 ^ 59
def prefixEnd_3984913 : Nat := 4983230072969 + 3 ^ 40 * 3984913 * 2
def baseEnd_3984913 : Nat := 1364117156900048495507483

theorem tailTrace_3984913 : CollatzResearch.WordTrace tailWord_3984913 prefixEnd_3984913 1364117156900048495507483 := by
  unfold tailWord_3984913
  simp only [CollatzResearch.WordTrace]
  refine ⟨145341717412348244802647393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96894478274898829868431595 145341717412348244802647393)
  ·
    refine ⟨109006288059261183601985545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145341717412348244802647393 109006288059261183601985545)
    ·
      refine ⟨81754716044445887701489159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109006288059261183601985545 81754716044445887701489159)
      ·
        refine ⟨122632074066668831552233739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81754716044445887701489159 122632074066668831552233739)
        ·
          refine ⟨183948111100003247328350609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122632074066668831552233739 183948111100003247328350609)
          ·
            refine ⟨137961083325002435496262957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183948111100003247328350609 137961083325002435496262957)
            ·
              refine ⟨51735406246875913311098609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137961083325002435496262957 51735406246875913311098609)
              ·
                refine ⟨38801554685156934983323957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51735406246875913311098609 38801554685156934983323957)
                ·
                  refine ⟨3637645751733462654686621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38801554685156934983323957 3637645751733462654686621)
                  ·
                    refine ⟨1364117156900048495507483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3637645751733462654686621 1364117156900048495507483)
                    ·
                      rfl

theorem cell22_3984913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 5, 3].length) (baseStart_3984913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3984913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3984913 prefixEnd_3984913 := by exact prefixLift 3984913
  have htrace : WordTrace (prefixWord ++ tailWord_3984913) baseStart_3984913 baseEnd_3984913 := by
    simpa [prefixWord, tailWord_3984913, baseEnd_3984913] using wordTrace_append hprefix tailTrace_3984913
  have hstable : (prefixWord ++ tailWord_3984913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984913).length < 2 ^ (prefixWord ++ tailWord_3984913).sum := by decide
  have hdescent : baseEnd_3984913 < baseStart_3984913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3984930 : List Nat := [3, 3, 1, 1, 1, 1, 3, 3, 3, 3]
def baseStart_3984930 : Nat := 118140960795 + 3984930 * 2 ^ 59
def prefixEnd_3984930 : Nat := 4983230072969 + 3 ^ 40 * 3984930 * 2
def baseEnd_3984930 : Nat := 1364122976347466117832431

theorem tailTrace_3984930 : CollatzResearch.WordTrace tailWord_3984930 prefixEnd_3984930 1364122976347466117832431 := by
  unfold tailWord_3984930
  simp only [CollatzResearch.WordTrace]
  refine ⟨36335584363321664176504061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96894891635524437804010829 36335584363321664176504061)
  ·
    refine ⟨13625844136245624066189023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36335584363321664176504061 13625844136245624066189023)
    ·
      refine ⟨20438766204368436099283535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13625844136245624066189023 20438766204368436099283535)
      ·
        refine ⟨30658149306552654148925303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20438766204368436099283535 30658149306552654148925303)
        ·
          refine ⟨45987223959828981223387955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30658149306552654148925303 45987223959828981223387955)
          ·
            refine ⟨68980835939743471835081933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45987223959828981223387955 68980835939743471835081933)
            ·
              refine ⟨25867813477403801938155725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68980835939743471835081933 25867813477403801938155725)
              ·
                refine ⟨9700430054026425726808397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25867813477403801938155725 9700430054026425726808397)
                ·
                  refine ⟨3637661270259909647553149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9700430054026425726808397 3637661270259909647553149)
                  ·
                    refine ⟨1364122976347466117832431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3637661270259909647553149 1364122976347466117832431)
                    ·
                      rfl

theorem cell22_3984930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 3, 3, 3].length) (baseStart_3984930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3984930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3984930 prefixEnd_3984930 := by exact prefixLift 3984930
  have htrace : WordTrace (prefixWord ++ tailWord_3984930) baseStart_3984930 baseEnd_3984930 := by
    simpa [prefixWord, tailWord_3984930, baseEnd_3984930] using wordTrace_append hprefix tailTrace_3984930
  have hstable : (prefixWord ++ tailWord_3984930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3984930).length < 2 ^ (prefixWord ++ tailWord_3984930).sum := by decide
  have hdescent : baseEnd_3984930 < baseStart_3984930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3984930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985054 : List Nat := [4, 3, 1, 1, 1, 2, 2, 3, 2, 3]
def baseStart_3985054 : Nat := 118140960795 + 3985054 * 2 ^ 59
def prefixEnd_3985054 : Nat := 4983230072969 + 3 ^ 40 * 3985054 * 2
def baseEnd_3985054 : Nat := 1364165424081571127732051

theorem tailTrace_3985054 : CollatzResearch.WordTrace tailWord_3985054 prefixEnd_3985054 1364165424081571127732051 := by
  unfold tailWord_3985054
  simp only [CollatzResearch.WordTrace]
  refine ⟨18168357513104678235441277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96897906736558283922353477 18168357513104678235441277)
  ·
    refine ⟨6813134067414254338290479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18168357513104678235441277 6813134067414254338290479)
    ·
      refine ⟨10219701101121381507435719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6813134067414254338290479 10219701101121381507435719)
      ·
        refine ⟨15329551651682072261153579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10219701101121381507435719 15329551651682072261153579)
        ·
          refine ⟨22994327477523108391730369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15329551651682072261153579 22994327477523108391730369)
          ·
            refine ⟨17245745608142331293797777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22994327477523108391730369 17245745608142331293797777)
            ·
              refine ⟨12934309206106748470348333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17245745608142331293797777 12934309206106748470348333)
              ·
                refine ⟨4850365952290030676380625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12934309206106748470348333 4850365952290030676380625)
                ·
                  refine ⟨3637774464217523007285469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4850365952290030676380625 3637774464217523007285469)
                  ·
                    refine ⟨1364165424081571127732051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3637774464217523007285469 1364165424081571127732051)
                    ·
                      rfl

theorem cell22_3985054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_3985054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3985054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3985054 prefixEnd_3985054 := by exact prefixLift 3985054
  have htrace : WordTrace (prefixWord ++ tailWord_3985054) baseStart_3985054 baseEnd_3985054 := by
    simpa [prefixWord, tailWord_3985054, baseEnd_3985054] using wordTrace_append hprefix tailTrace_3985054
  have hstable : (prefixWord ++ tailWord_3985054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985054).length < 2 ^ (prefixWord ++ tailWord_3985054).sum := by decide
  have hdescent : baseEnd_3985054 < baseStart_3985054 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985093 : List Nat := [1, 3, 1, 1, 1, 1, 2, 2, 3, 7]
def baseStart_3985093 : Nat := 118140960795 + 3985093 * 2 ^ 59
def prefixEnd_3985093 : Nat := 4983230072969 + 3 ^ 40 * 3985093 * 2
def baseEnd_3985093 : Nat := 1364178774578588026006931

theorem tailTrace_3985093 : CollatzResearch.WordTrace tailWord_3985093 prefixEnd_3985093 1364178774578588026006931 := by
  unfold tailWord_3985093
  simp only [CollatzResearch.WordTrace]
  refine ⟨145348282551696135544199933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96898855034464090362799955 145348282551696135544199933)
  ·
    refine ⟨54505605956886050829074975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145348282551696135544199933 54505605956886050829074975)
    ·
      refine ⟨81758408935329076243612463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54505605956886050829074975 81758408935329076243612463)
      ·
        refine ⟨122637613402993614365418695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81758408935329076243612463 122637613402993614365418695)
        ·
          refine ⟨183956420104490421548128043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122637613402993614365418695 183956420104490421548128043)
          ·
            refine ⟨275934630156735632322192065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183956420104490421548128043 275934630156735632322192065)
            ·
              refine ⟨206950972617551724241644049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 275934630156735632322192065 206950972617551724241644049)
              ·
                refine ⟨155213229463163793181233037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 206950972617551724241644049 155213229463163793181233037)
                ·
                  refine ⟨58204961048686422442962389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 155213229463163793181233037 58204961048686422442962389)
                  ·
                    refine ⟨1364178774578588026006931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58204961048686422442962389 1364178774578588026006931)
                    ·
                      rfl

theorem cell22_3985093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 7].length) (baseStart_3985093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3985093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3985093 prefixEnd_3985093 := by exact prefixLift 3985093
  have htrace : WordTrace (prefixWord ++ tailWord_3985093) baseStart_3985093 baseEnd_3985093 := by
    simpa [prefixWord, tailWord_3985093, baseEnd_3985093] using wordTrace_append hprefix tailTrace_3985093
  have hstable : (prefixWord ++ tailWord_3985093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985093).length < 2 ^ (prefixWord ++ tailWord_3985093).sum := by decide
  have hdescent : baseEnd_3985093 < baseStart_3985093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985112 : List Nat := [2, 1, 2, 2, 3, 1, 5, 1, 5]
def baseStart_3985112 : Nat := 118140960795 + 3985112 * 2 ^ 59
def prefixEnd_3985112 : Nat := 4983230072969 + 3 ^ 40 * 3985112 * 2
def baseEnd_3985112 : Nat := 454728426222292769927291

theorem tailTrace_3985112 : CollatzResearch.WordTrace tailWord_3985112 prefixEnd_3985112 454728426222292769927291 := by
  unfold tailWord_3985112
  simp only [CollatzResearch.WordTrace]
  refine ⟨72674487769313650894570795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96899317025751534526094393 72674487769313650894570795)
  ·
    refine ⟨109011731653970476341856193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72674487769313650894570795 109011731653970476341856193)
    ·
      refine ⟨81758798740477857256392145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109011731653970476341856193 81758798740477857256392145)
      ·
        refine ⟨61319099055358392942294109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81758798740477857256392145 61319099055358392942294109)
        ·
          refine ⟨22994662145759397353360291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61319099055358392942294109 22994662145759397353360291)
          ·
            refine ⟨34491993218639096030040437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22994662145759397353360291 34491993218639096030040437)
            ·
              refine ⟨3233624364247415252816291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34491993218639096030040437 3233624364247415252816291)
              ·
                refine ⟨4850436546371122879224437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3233624364247415252816291 4850436546371122879224437)
                ·
                  refine ⟨454728426222292769927291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4850436546371122879224437 454728426222292769927291)
                  ·
                    rfl

theorem cell22_3985112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 5, 1, 5].length) (baseStart_3985112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3985112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3985112 prefixEnd_3985112 := by exact prefixLift 3985112
  have htrace : WordTrace (prefixWord ++ tailWord_3985112) baseStart_3985112 baseEnd_3985112 := by
    simpa [prefixWord, tailWord_3985112, baseEnd_3985112] using wordTrace_append hprefix tailTrace_3985112
  have hstable : (prefixWord ++ tailWord_3985112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985112).length < 2 ^ (prefixWord ++ tailWord_3985112).sum := by decide
  have hdescent : baseEnd_3985112 < baseStart_3985112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985185 : List Nat := [1, 2, 3, 2, 1, 3, 2, 8]
def baseStart_3985185 : Nat := 118140960795 + 3985185 * 2 ^ 59
def prefixEnd_3985185 : Nat := 4983230072969 + 3 ^ 40 * 3985185 * 2
def baseEnd_3985185 : Nat := 151578918673192272522961

theorem tailTrace_3985185 : CollatzResearch.WordTrace tailWord_3985185 prefixEnd_3985185 151578918673192272522961 := by
  unfold tailWord_3985185
  simp only [CollatzResearch.WordTrace]
  refine ⟨145351638067362835256549009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96901092044908556837699339 145351638067362835256549009)
  ·
    refine ⟨109013728550522126442411757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145351638067362835256549009 109013728550522126442411757)
    ·
      refine ⟨40880148206445797415904409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109013728550522126442411757 40880148206445797415904409)
      ·
        refine ⟨30660111154834348061928307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40880148206445797415904409 30660111154834348061928307)
        ·
          refine ⟨45990166732251522092892461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30660111154834348061928307 45990166732251522092892461)
          ·
            refine ⟨17246312524594320784834673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45990166732251522092892461 17246312524594320784834673)
            ·
              refine ⟨12934734393445740588626005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17246312524594320784834673 12934734393445740588626005)
              ·
                refine ⟨151578918673192272522961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12934734393445740588626005 151578918673192272522961)
                ·
                  rfl

theorem cell22_3985185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 8].length) (baseStart_3985185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3985185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3985185 prefixEnd_3985185 := by exact prefixLift 3985185
  have htrace : WordTrace (prefixWord ++ tailWord_3985185) baseStart_3985185 baseEnd_3985185 := by
    simpa [prefixWord, tailWord_3985185, baseEnd_3985185] using wordTrace_append hprefix tailTrace_3985185
  have hstable : (prefixWord ++ tailWord_3985185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985185).length < 2 ^ (prefixWord ++ tailWord_3985185).sum := by decide
  have hdescent : baseEnd_3985185 < baseStart_3985185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985204 : List Nat := [2, 5, 1, 1, 2, 1, 2, 2, 2, 4]
def baseStart_3985204 : Nat := 118140960795 + 3985204 * 2 ^ 59
def prefixEnd_3985204 : Nat := 4983230072969 + 3 ^ 40 * 3985204 * 2
def baseEnd_3985204 : Nat := 1364216772147020736481591

theorem tailTrace_3985204 : CollatzResearch.WordTrace tailWord_3985204 prefixEnd_3985204 1364216772147020736481591 := by
  unfold tailWord_3985204
  simp only [CollatzResearch.WordTrace]
  refine ⟨72676165527147000750745333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96901554036196001000993777 72676165527147000750745333)
  ·
    refine ⟨6813390518170031320382375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72676165527147000750745333 6813390518170031320382375)
    ·
      refine ⟨10220085777255046980573563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6813390518170031320382375 10220085777255046980573563)
      ·
        refine ⟨15330128665882570470860345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10220085777255046980573563 15330128665882570470860345)
        ·
          refine ⟨11497596499411927853145259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15330128665882570470860345 11497596499411927853145259)
          ·
            refine ⟨17246394749117891779717889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11497596499411927853145259 17246394749117891779717889)
            ·
              refine ⟨12934796061838418834788417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17246394749117891779717889 12934796061838418834788417)
              ·
                refine ⟨9701097046378814126091313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12934796061838418834788417 9701097046378814126091313)
                ·
                  refine ⟨7275822784784110594568485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9701097046378814126091313 7275822784784110594568485)
                  ·
                    refine ⟨1364216772147020736481591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7275822784784110594568485 1364216772147020736481591)
                    ·
                      rfl

theorem cell22_3985204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_3985204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3985204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3985204 prefixEnd_3985204 := by exact prefixLift 3985204
  have htrace : WordTrace (prefixWord ++ tailWord_3985204) baseStart_3985204 baseEnd_3985204 := by
    simpa [prefixWord, tailWord_3985204, baseEnd_3985204] using wordTrace_append hprefix tailTrace_3985204
  have hstable : (prefixWord ++ tailWord_3985204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985204).length < 2 ^ (prefixWord ++ tailWord_3985204).sum := by decide
  have hdescent : baseEnd_3985204 < baseStart_3985204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985206 : List Nat := [5, 1, 2, 2, 1, 1, 1, 4, 2, 3]
def baseStart_3985206 : Nat := 118140960795 + 3985206 * 2 ^ 59
def prefixEnd_3985206 : Nat := 4983230072969 + 3 ^ 40 * 3985206 * 2
def baseEnd_3985206 : Nat := 1364217456787893397931585

theorem tailTrace_3985206 : CollatzResearch.WordTrace tailWord_3985206 prefixEnd_3985206 1364217456787893397931585 := by
  unfold tailWord_3985206
  simp only [CollatzResearch.WordTrace]
  refine ⟨9084525250017922240191467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96901602666857837228708981 9084525250017922240191467)
  ·
    refine ⟨13626787875026883360287201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9084525250017922240191467 13626787875026883360287201)
    ·
      refine ⟨10220090906270162520215401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13626787875026883360287201 10220090906270162520215401)
      ·
        refine ⟨7665068179702621890161551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10220090906270162520215401 7665068179702621890161551)
        ·
          refine ⟨11497602269553932835242327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7665068179702621890161551 11497602269553932835242327)
          ·
            refine ⟨17246403404330899252863491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11497602269553932835242327 17246403404330899252863491)
            ·
              refine ⟨25869605106496348879295237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17246403404330899252863491 25869605106496348879295237)
              ·
                refine ⟨4850550957468065414867857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25869605106496348879295237 4850550957468065414867857)
                ·
                  refine ⟨3637913218101049061150893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4850550957468065414867857 3637913218101049061150893)
                  ·
                    refine ⟨1364217456787893397931585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3637913218101049061150893 1364217456787893397931585)
                    ·
                      rfl

theorem cell22_3985206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_3985206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3985206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3985206 prefixEnd_3985206 := by exact prefixLift 3985206
  have htrace : WordTrace (prefixWord ++ tailWord_3985206) baseStart_3985206 baseEnd_3985206 := by
    simpa [prefixWord, tailWord_3985206, baseEnd_3985206] using wordTrace_append hprefix tailTrace_3985206
  have hstable : (prefixWord ++ tailWord_3985206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985206).length < 2 ^ (prefixWord ++ tailWord_3985206).sum := by decide
  have hdescent : baseEnd_3985206 < baseStart_3985206 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985230 : List Nat := [4, 1, 1, 1, 1, 1, 1, 1, 11]
def baseStart_3985230 : Nat := 118140960795 + 3985230 * 2 ^ 59
def prefixEnd_3985230 : Nat := 4983230072969 + 3 ^ 40 * 3985230 * 2
def baseEnd_3985230 : Nat := 454741890826121778443837

theorem tailTrace_3985230 : CollatzResearch.WordTrace tailWord_3985230 prefixEnd_3985230 454741890826121778443837 := by
  unfold tailWord_3985230
  simp only [CollatzResearch.WordTrace]
  refine ⟨18169159919024975992742143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96902186234799871961291429 18169159919024975992742143)
  ·
    refine ⟨27253739878537463989113215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18169159919024975992742143 27253739878537463989113215)
    ·
      refine ⟨40880609817806195983669823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27253739878537463989113215 40880609817806195983669823)
      ·
        refine ⟨61320914726709293975504735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40880609817806195983669823 61320914726709293975504735)
        ·
          refine ⟨91981372090063940963257103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61320914726709293975504735 91981372090063940963257103)
          ·
            refine ⟨137972058135095911444885655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91981372090063940963257103 137972058135095911444885655)
            ·
              refine ⟨206958087202643867167328483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137972058135095911444885655 206958087202643867167328483)
              ·
                refine ⟨310437130803965800750992725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206958087202643867167328483 310437130803965800750992725)
                ·
                  refine ⟨454741890826121778443837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 310437130803965800750992725 454741890826121778443837)
                  ·
                    rfl

theorem cell22_3985230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 11].length) (baseStart_3985230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3985230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3985230 prefixEnd_3985230 := by exact prefixLift 3985230
  have htrace : WordTrace (prefixWord ++ tailWord_3985230) baseStart_3985230 baseEnd_3985230 := by
    simpa [prefixWord, tailWord_3985230, baseEnd_3985230] using wordTrace_append hprefix tailTrace_3985230
  have hstable : (prefixWord ++ tailWord_3985230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985230).length < 2 ^ (prefixWord ++ tailWord_3985230).sum := by decide
  have hdescent : baseEnd_3985230 < baseStart_3985230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985234 : List Nat := [3, 2, 2, 1, 1, 4, 1, 2, 3, 3]
def baseStart_3985234 : Nat := 118140960795 + 3985234 * 2 ^ 59
def prefixEnd_3985234 : Nat := 4983230072969 + 3 ^ 40 * 3985234 * 2
def baseEnd_3985234 : Nat := 1364227041760110658231499

theorem tailTrace_3985234 : CollatzResearch.WordTrace tailWord_3985234 prefixEnd_3985234 1364227041760110658231499 := by
  unfold tailWord_3985234
  simp only [CollatzResearch.WordTrace]
  refine ⟨36338356311046329156270689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96902283496123544416721837 36338356311046329156270689)
  ·
    refine ⟨27253767233284746867203017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36338356311046329156270689 27253767233284746867203017)
    ·
      refine ⟨20440325424963560150402263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27253767233284746867203017 20440325424963560150402263)
      ·
        refine ⟨30660488137445340225603395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20440325424963560150402263 30660488137445340225603395)
        ·
          refine ⟨45990732206168010338405093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30660488137445340225603395 45990732206168010338405093)
          ·
            refine ⟨8623262288656501938450955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45990732206168010338405093 8623262288656501938450955)
            ·
              refine ⟨12934893432984752907676433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8623262288656501938450955 12934893432984752907676433)
              ·
                refine ⟨9701170074738564680757325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12934893432984752907676433 9701170074738564680757325)
                ·
                  refine ⟨3637938778026961755283997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9701170074738564680757325 3637938778026961755283997)
                  ·
                    refine ⟨1364227041760110658231499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3637938778026961755283997 1364227041760110658231499)
                    ·
                      rfl

theorem cell22_3985234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 2, 3, 3].length) (baseStart_3985234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3985234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3985234 prefixEnd_3985234 := by exact prefixLift 3985234
  have htrace : WordTrace (prefixWord ++ tailWord_3985234) baseStart_3985234 baseEnd_3985234 := by
    simpa [prefixWord, tailWord_3985234, baseEnd_3985234] using wordTrace_append hprefix tailTrace_3985234
  have hstable : (prefixWord ++ tailWord_3985234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985234).length < 2 ^ (prefixWord ++ tailWord_3985234).sum := by decide
  have hdescent : baseEnd_3985234 < baseStart_3985234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985337 : List Nat := [1, 2, 1, 4, 2, 1, 4, 7]
def baseStart_3985337 : Nat := 118140960795 + 3985337 * 2 ^ 59
def prefixEnd_3985337 : Nat := 4983230072969 + 3 ^ 40 * 3985337 * 2
def baseEnd_3985337 : Nat := 151584700085005858100687

theorem tailTrace_3985337 : CollatzResearch.WordTrace tailWord_3985337 prefixEnd_3985337 151584700085005858100687 := by
  unfold tailWord_3985337
  simp only [CollatzResearch.WordTrace]
  refine ⟨145357181962812165216082265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96904787975208110144054843 145357181962812165216082265)
  ·
    refine ⟨109017886472109123912061699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145357181962812165216082265 109017886472109123912061699)
    ·
      refine ⟨163526829708163685868092549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109017886472109123912061699 163526829708163685868092549)
      ·
        refine ⟨30661280570280691100267353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163526829708163685868092549 30661280570280691100267353)
        ·
          refine ⟨22995960427710518325200515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30661280570280691100267353 22995960427710518325200515)
          ·
            refine ⟨34493940641565777487800773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22995960427710518325200515 34493940641565777487800773)
            ·
              refine ⟨6467613870293583278962645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34493940641565777487800773 6467613870293583278962645)
              ·
                refine ⟨151584700085005858100687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6467613870293583278962645 151584700085005858100687)
                ·
                  rfl

theorem cell22_3985337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 7].length) (baseStart_3985337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3985337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3985337 prefixEnd_3985337 := by exact prefixLift 3985337
  have htrace : WordTrace (prefixWord ++ tailWord_3985337) baseStart_3985337 baseEnd_3985337 := by
    simpa [prefixWord, tailWord_3985337, baseEnd_3985337] using wordTrace_append hprefix tailTrace_3985337
  have hstable : (prefixWord ++ tailWord_3985337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985337).length < 2 ^ (prefixWord ++ tailWord_3985337).sum := by decide
  have hdescent : baseEnd_3985337 < baseStart_3985337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985341 : List Nat := [1, 4, 1, 2, 3, 2, 1, 3, 2, 3]
def baseStart_3985341 : Nat := 118140960795 + 3985341 * 2 ^ 59
def prefixEnd_3985341 : Nat := 4983230072969 + 3 ^ 40 * 3985341 * 2
def baseEnd_3985341 : Nat := 1364263670046798045806171

theorem tailTrace_3985341 : CollatzResearch.WordTrace tailWord_3985341 prefixEnd_3985341 1364263670046798045806171 := by
  unfold tailWord_3985341
  simp only [CollatzResearch.WordTrace]
  refine ⟨145357327854797673899227877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96904885236531782599485251 145357327854797673899227877)
  ·
    refine ⟨27254498972774563856105227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145357327854797673899227877 27254498972774563856105227)
    ·
      refine ⟨40881748459161845784157841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27254498972774563856105227 40881748459161845784157841)
      ·
        refine ⟨30661311344371384338118381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40881748459161845784157841 30661311344371384338118381)
        ·
          refine ⟨11497991754139269126794393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30661311344371384338118381 11497991754139269126794393)
          ·
            refine ⟨8623493815604451845095795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11497991754139269126794393 8623493815604451845095795)
            ·
              refine ⟨12935240723406677767643693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8623493815604451845095795 12935240723406677767643693)
              ·
                refine ⟨4850715271277504162866385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12935240723406677767643693 4850715271277504162866385)
                ·
                  refine ⟨3638036453458128122149789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4850715271277504162866385 3638036453458128122149789)
                  ·
                    refine ⟨1364263670046798045806171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3638036453458128122149789 1364263670046798045806171)
                    ·
                      rfl

theorem cell22_3985341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 3, 2, 3].length) (baseStart_3985341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3985341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3985341 prefixEnd_3985341 := by exact prefixLift 3985341
  have htrace : WordTrace (prefixWord ++ tailWord_3985341) baseStart_3985341 baseEnd_3985341 := by
    simpa [prefixWord, tailWord_3985341, baseEnd_3985341] using wordTrace_append hprefix tailTrace_3985341
  have hstable : (prefixWord ++ tailWord_3985341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985341).length < 2 ^ (prefixWord ++ tailWord_3985341).sum := by decide
  have hdescent : baseEnd_3985341 < baseStart_3985341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985459 : List Nat := [1, 1, 1, 2, 4, 1, 5, 1, 1, 5]
def baseStart_3985459 : Nat := 118140960795 + 3985459 * 2 ^ 59
def prefixEnd_3985459 : Nat := 4983230072969 + 3 ^ 40 * 3985459 * 2
def baseEnd_3985459 : Nat := 1364304063858285071355809

theorem tailTrace_3985459 : CollatzResearch.WordTrace tailWord_3985459 prefixEnd_3985459 1364304063858285071355809 := by
  unfold tailWord_3985459
  simp only [CollatzResearch.WordTrace]
  refine ⟨145361631668370180052023431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96907754445580120034682287 145361631668370180052023431)
  ·
    refine ⟨218042447502555270078035147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145361631668370180052023431 218042447502555270078035147)
    ·
      refine ⟨327063671253832905117052721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218042447502555270078035147 327063671253832905117052721)
      ·
        refine ⟨245297753440374678837789541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327063671253832905117052721 245297753440374678837789541)
        ·
          refine ⟨45993328770070252282085539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 245297753440374678837789541 45993328770070252282085539)
          ·
            refine ⟨68989993155105378423128309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45993328770070252282085539 68989993155105378423128309)
            ·
              refine ⟨6467811858291129227168279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68989993155105378423128309 6467811858291129227168279)
              ·
                refine ⟨9701717787436693840752419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6467811858291129227168279 9701717787436693840752419)
                ·
                  refine ⟨14552576681155040761128629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9701717787436693840752419 14552576681155040761128629)
                  ·
                    refine ⟨1364304063858285071355809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14552576681155040761128629 1364304063858285071355809)
                    ·
                      rfl

theorem cell22_3985459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 1, 1, 5].length) (baseStart_3985459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3985459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3985459 prefixEnd_3985459 := by exact prefixLift 3985459
  have htrace : WordTrace (prefixWord ++ tailWord_3985459) baseStart_3985459 baseEnd_3985459 := by
    simpa [prefixWord, tailWord_3985459, baseEnd_3985459] using wordTrace_append hprefix tailTrace_3985459
  have hstable : (prefixWord ++ tailWord_3985459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985459).length < 2 ^ (prefixWord ++ tailWord_3985459).sum := by decide
  have hdescent : baseEnd_3985459 < baseStart_3985459 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985487 : List Nat := [1, 1, 2, 1, 1, 2, 2, 2, 1, 9]
def baseStart_3985487 : Nat := 118140960795 + 3985487 * 2 ^ 59
def prefixEnd_3985487 : Nat := 4983230072969 + 3 ^ 40 * 3985487 * 2
def baseEnd_3985487 : Nat := 1364313648830502331655723

theorem tailTrace_3985487 : CollatzResearch.WordTrace tailWord_3985487 prefixEnd_3985487 1364313648830502331655723 := by
  unfold tailWord_3985487
  simp only [CollatzResearch.WordTrace]
  refine ⟨145362652912268740834042715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96908435274845827222695143 145362652912268740834042715)
  ·
    refine ⟨218043979368403111251064073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145362652912268740834042715 218043979368403111251064073)
    ·
      refine ⟨163532984526302333438298055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218043979368403111251064073 163532984526302333438298055)
      ·
        refine ⟨245299476789453500157447083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163532984526302333438298055 245299476789453500157447083)
        ·
          refine ⟨367949215184180250236170625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245299476789453500157447083 367949215184180250236170625)
          ·
            refine ⟨275961911388135187677127969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 367949215184180250236170625 275961911388135187677127969)
            ·
              refine ⟨206971433541101390757845977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 275961911388135187677127969 206971433541101390757845977)
              ·
                refine ⟨155228575155826043068384483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 206971433541101390757845977 155228575155826043068384483)
                ·
                  refine ⟨232842862733739064602576725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 155228575155826043068384483 232842862733739064602576725)
                  ·
                    refine ⟨1364313648830502331655723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 232842862733739064602576725 1364313648830502331655723)
                    ·
                      rfl

theorem cell22_3985487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 9].length) (baseStart_3985487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3985487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3985487 prefixEnd_3985487 := by exact prefixLift 3985487
  have htrace : WordTrace (prefixWord ++ tailWord_3985487) baseStart_3985487 baseEnd_3985487 := by
    simpa [prefixWord, tailWord_3985487, baseEnd_3985487] using wordTrace_append hprefix tailTrace_3985487
  have hstable : (prefixWord ++ tailWord_3985487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985487).length < 2 ^ (prefixWord ++ tailWord_3985487).sum := by decide
  have hdescent : baseEnd_3985487 < baseStart_3985487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985602 : List Nat := [3, 5, 1, 1, 1, 3, 1, 2, 5]
def baseStart_3985602 : Nat := 118140960795 + 3985602 * 2 ^ 59
def prefixEnd_3985602 : Nat := 4983230072969 + 3 ^ 40 * 3985602 * 2
def baseEnd_3985602 : Nat := 454784338560226788343457

theorem tailTrace_3985602 : CollatzResearch.WordTrace tailWord_3985602 prefixEnd_3985602 454784338560226788343457 := by
  unfold tailWord_3985602
  simp only [CollatzResearch.WordTrace]
  refine ⟨36341711826713028868619765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96911231537901410316319373 36341711826713028868619765)
  ·
    refine ⟨3407035483754346456433103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36341711826713028868619765 3407035483754346456433103)
    ·
      refine ⟨5110553225631519684649655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3407035483754346456433103 5110553225631519684649655)
      ·
        refine ⟨7665829838447279526974483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5110553225631519684649655 7665829838447279526974483)
        ·
          refine ⟨11498744757670919290461725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7665829838447279526974483 11498744757670919290461725)
          ·
            refine ⟨4312029284126594733923147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11498744757670919290461725 4312029284126594733923147)
            ·
              refine ⟨6468043926189892100884721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4312029284126594733923147 6468043926189892100884721)
              ·
                refine ⟨4851032944642419075663541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6468043926189892100884721 4851032944642419075663541)
                ·
                  refine ⟨454784338560226788343457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4851032944642419075663541 454784338560226788343457)
                  ·
                    rfl

theorem cell22_3985602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_3985602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3985602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3985602 prefixEnd_3985602 := by exact prefixLift 3985602
  have htrace : WordTrace (prefixWord ++ tailWord_3985602) baseStart_3985602 baseEnd_3985602 := by
    simpa [prefixWord, tailWord_3985602, baseEnd_3985602] using wordTrace_append hprefix tailTrace_3985602
  have hstable : (prefixWord ++ tailWord_3985602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985602).length < 2 ^ (prefixWord ++ tailWord_3985602).sum := by decide
  have hdescent : baseEnd_3985602 < baseStart_3985602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985611 : List Nat := [1, 1, 1, 1, 3, 2, 5, 1, 4, 3]
def baseStart_3985611 : Nat := 118140960795 + 3985611 * 2 ^ 59
def prefixEnd_3985611 : Nat := 4983230072969 + 3 ^ 40 * 3985611 * 2
def baseEnd_3985611 : Nat := 1364356096564607341555343

theorem tailTrace_3985611 : CollatzResearch.WordTrace tailWord_3985611 prefixEnd_3985611 1364356096564607341555343 := by
  unfold tailWord_3985611
  simp only [CollatzResearch.WordTrace]
  refine ⟨145367175563819510011556687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96911450375879673341037791 145367175563819510011556687)
  ·
    refine ⟨218050763345729265017335031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145367175563819510011556687 218050763345729265017335031)
    ·
      refine ⟨327076145018593897526002547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218050763345729265017335031 327076145018593897526002547)
      ·
        refine ⟨490614217527890846289003821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327076145018593897526002547 490614217527890846289003821)
        ·
          refine ⟨183980331572959067358376433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 490614217527890846289003821 183980331572959067358376433)
          ·
            refine ⟨137985248679719300518782325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183980331572959067358376433 137985248679719300518782325)
            ·
              refine ⟨12936117063723684423635843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 137985248679719300518782325 12936117063723684423635843)
              ·
                refine ⟨19404175595585526635453765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12936117063723684423635843 19404175595585526635453765)
                ·
                  refine ⟨3638282924172286244147581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19404175595585526635453765 3638282924172286244147581)
                  ·
                    refine ⟨1364356096564607341555343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3638282924172286244147581 1364356096564607341555343)
                    ·
                      rfl

theorem cell22_3985611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 4, 3].length) (baseStart_3985611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3985611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3985611 prefixEnd_3985611 := by exact prefixLift 3985611
  have htrace : WordTrace (prefixWord ++ tailWord_3985611) baseStart_3985611 baseEnd_3985611 := by
    simpa [prefixWord, tailWord_3985611, baseEnd_3985611] using wordTrace_append hprefix tailTrace_3985611
  have hstable : (prefixWord ++ tailWord_3985611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985611).length < 2 ^ (prefixWord ++ tailWord_3985611).sum := by decide
  have hdescent : baseEnd_3985611 < baseStart_3985611 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985656 : List Nat := [2, 1, 2, 1, 1, 2, 1, 4, 5, 3]
def baseStart_3985656 : Nat := 118140960795 + 3985656 * 2 ^ 59
def prefixEnd_3985656 : Nat := 4983230072969 + 3 ^ 40 * 3985656 * 2
def baseEnd_3985656 : Nat := 1364371500984242224180205

theorem tailTrace_3985656 : CollatzResearch.WordTrace tailWord_3985656 prefixEnd_3985656 1364371500984242224180205 := by
  unfold tailWord_3985656
  simp only [CollatzResearch.WordTrace]
  refine ⟨72684408424328241348472411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96912544565770988464629881 72684408424328241348472411)
  ·
    refine ⟨109026612636492362022708617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72684408424328241348472411 109026612636492362022708617)
    ·
      refine ⟨81769959477369271517031463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109026612636492362022708617 81769959477369271517031463)
      ·
        refine ⟨122654939216053907275547195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81769959477369271517031463 122654939216053907275547195)
        ·
          refine ⟨183982408824080860913320793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122654939216053907275547195 183982408824080860913320793)
          ·
            refine ⟨137986806618060645684990595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183982408824080860913320793 137986806618060645684990595)
            ·
              refine ⟨206980209927090968527485893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137986806618060645684990595 206980209927090968527485893)
              ·
                refine ⟨38808789361329556598903605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 206980209927090968527485893 38808789361329556598903605)
                ·
                  refine ⟨3638324002624645931147213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38808789361329556598903605 3638324002624645931147213)
                  ·
                    refine ⟨1364371500984242224180205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3638324002624645931147213 1364371500984242224180205)
                    ·
                      rfl

theorem cell22_3985656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 5, 3].length) (baseStart_3985656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3985656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3985656 prefixEnd_3985656 := by exact prefixLift 3985656
  have htrace : WordTrace (prefixWord ++ tailWord_3985656) baseStart_3985656 baseEnd_3985656 := by
    simpa [prefixWord, tailWord_3985656, baseEnd_3985656] using wordTrace_append hprefix tailTrace_3985656
  have hstable : (prefixWord ++ tailWord_3985656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985656).length < 2 ^ (prefixWord ++ tailWord_3985656).sum := by decide
  have hdescent : baseEnd_3985656 < baseStart_3985656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985673 : List Nat := [1, 2, 1, 1, 3, 4, 3, 1, 3, 3]
def baseStart_3985673 : Nat := 118140960795 + 3985673 * 2 ^ 59
def prefixEnd_3985673 : Nat := 4983230072969 + 3 ^ 40 * 3985673 * 2
def baseEnd_3985673 : Nat := 1364377320431659846505153

theorem tailTrace_3985673 : CollatzResearch.WordTrace tailWord_3985673 prefixEnd_3985673 1364377320431659846505153 := by
  unfold tailWord_3985673
  simp only [CollatzResearch.WordTrace]
  refine ⟨145369436889594894600313673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96912957926396596400209115 145369436889594894600313673)
  ·
    refine ⟨109027077667196170950235255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145369436889594894600313673 109027077667196170950235255)
    ·
      refine ⟨163540616500794256425352883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109027077667196170950235255 163540616500794256425352883)
      ·
        refine ⟨245310924751191384638029325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163540616500794256425352883 245310924751191384638029325)
        ·
          refine ⟨91991596781696769239260997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 245310924751191384638029325 91991596781696769239260997)
          ·
            refine ⟨17248424396568144232361437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91991596781696769239260997 17248424396568144232361437)
            ·
              refine ⟨6468159148713054087135539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17248424396568144232361437 6468159148713054087135539)
              ·
                refine ⟨9702238723069581130703309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6468159148713054087135539 9702238723069581130703309)
                ·
                  refine ⟨3638339521151092924013741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9702238723069581130703309 3638339521151092924013741)
                  ·
                    refine ⟨1364377320431659846505153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3638339521151092924013741 1364377320431659846505153)
                    ·
                      rfl

theorem cell22_3985673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 1, 3, 3].length) (baseStart_3985673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3985673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3985673 prefixEnd_3985673 := by exact prefixLift 3985673
  have htrace : WordTrace (prefixWord ++ tailWord_3985673) baseStart_3985673 baseEnd_3985673 := by
    simpa [prefixWord, tailWord_3985673, baseEnd_3985673] using wordTrace_append hprefix tailTrace_3985673
  have hstable : (prefixWord ++ tailWord_3985673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985673).length < 2 ^ (prefixWord ++ tailWord_3985673).sum := by decide
  have hdescent : baseEnd_3985673 < baseStart_3985673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985748 : List Nat := [2, 4, 1, 1, 2, 3, 1, 2, 6]
def baseStart_3985748 : Nat := 118140960795 + 3985748 * 2 ^ 59
def prefixEnd_3985748 : Nat := 4983230072969 + 3 ^ 40 * 3985748 * 2
def baseEnd_3985748 : Nat := 454800998154794883626641

theorem tailTrace_3985748 : CollatzResearch.WordTrace tailWord_3985748 prefixEnd_3985748 454800998154794883626641 := by
  unfold tailWord_3985748
  simp only [CollatzResearch.WordTrace]
  refine ⟨72686086182161591204646949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96914781576215454939529265 72686086182161591204646949)
  ·
    refine ⟨13628641159155298350871303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72686086182161591204646949 13628641159155298350871303)
    ·
      refine ⟨20442961738732947526306955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13628641159155298350871303 20442961738732947526306955)
      ·
        refine ⟨30664442608099421289460433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20442961738732947526306955 30664442608099421289460433)
        ·
          refine ⟨22998331956074565967095325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30664442608099421289460433 22998331956074565967095325)
          ·
            refine ⟨8624374483527962237660747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22998331956074565967095325 8624374483527962237660747)
            ·
              refine ⟨12936561725291943356491121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8624374483527962237660747 12936561725291943356491121)
              ·
                refine ⟨9702421293968957517368341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12936561725291943356491121 9702421293968957517368341)
                ·
                  refine ⟨454800998154794883626641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9702421293968957517368341 454800998154794883626641)
                  ·
                    rfl

theorem cell22_3985748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_3985748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3985748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3985748 prefixEnd_3985748 := by exact prefixLift 3985748
  have htrace : WordTrace (prefixWord ++ tailWord_3985748) baseStart_3985748 baseEnd_3985748 := by
    simpa [prefixWord, tailWord_3985748, baseEnd_3985748] using wordTrace_append hprefix tailTrace_3985748
  have hstable : (prefixWord ++ tailWord_3985748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985748).length < 2 ^ (prefixWord ++ tailWord_3985748).sum := by decide
  have hdescent : baseEnd_3985748 < baseStart_3985748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985763 : List Nat := [1, 1, 1, 5, 2, 1, 2, 2, 4, 3]
def baseStart_3985763 : Nat := 118140960795 + 3985763 * 2 ^ 59
def prefixEnd_3985763 : Nat := 4983230072969 + 3 ^ 40 * 3985763 * 2
def baseEnd_3985763 : Nat := 1364408129270929611754877

theorem tailTrace_3985763 : CollatzResearch.WordTrace tailWord_3985763 prefixEnd_3985763 1364408129270929611754877 := by
  unfold tailWord_3985763
  simp only [CollatzResearch.WordTrace]
  refine ⟨145372719459268839971089943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96915146306179226647393295 145372719459268839971089943)
  ·
    refine ⟨218059079188903259956634915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145372719459268839971089943 218059079188903259956634915)
    ·
      refine ⟨327088618783354889934952373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218059079188903259956634915 327088618783354889934952373)
      ·
        refine ⟨30664558010939520931401785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 327088618783354889934952373 30664558010939520931401785)
        ·
          refine ⟨22998418508204640698551339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30664558010939520931401785 22998418508204640698551339)
          ·
            refine ⟨34497627762306961047827009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22998418508204640698551339 34497627762306961047827009)
            ·
              refine ⟨25873220821730220785870257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34497627762306961047827009 25873220821730220785870257)
              ·
                refine ⟨19404915616297665589402693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25873220821730220785870257 19404915616297665589402693)
                ·
                  refine ⟨3638421678055812298013005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19404915616297665589402693 3638421678055812298013005)
                  ·
                    refine ⟨1364408129270929611754877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3638421678055812298013005 1364408129270929611754877)
                    ·
                      rfl

theorem cell22_3985763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 4, 3].length) (baseStart_3985763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3985763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3985763 prefixEnd_3985763 := by exact prefixLift 3985763
  have htrace : WordTrace (prefixWord ++ tailWord_3985763) baseStart_3985763 baseEnd_3985763 := by
    simpa [prefixWord, tailWord_3985763, baseEnd_3985763] using wordTrace_append hprefix tailTrace_3985763
  have hstable : (prefixWord ++ tailWord_3985763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985763).length < 2 ^ (prefixWord ++ tailWord_3985763).sum := by decide
  have hdescent : baseEnd_3985763 < baseStart_3985763 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985765 : List Nat := [1, 3, 1, 3, 1, 4, 2, 3, 4]
def baseStart_3985765 : Nat := 118140960795 + 3985765 * 2 ^ 59
def prefixEnd_3985765 : Nat := 4983230072969 + 3 ^ 40 * 3985765 * 2
def baseEnd_3985765 : Nat := 454802937970600757734957

theorem tailTrace_3985765 : CollatzResearch.WordTrace tailWord_3985765 prefixEnd_3985765 454802937970600757734957 := by
  unfold tailWord_3985765
  simp only [CollatzResearch.WordTrace]
  refine ⟨145372792405261594312662749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96915194936841062875108499 145372792405261594312662749)
  ·
    refine ⟨54514797151973097867248531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145372792405261594312662749 54514797151973097867248531)
    ·
      refine ⟨81772195727959646800872797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54514797151973097867248531 81772195727959646800872797)
      ·
        refine ⟨30664573397984867550327299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81772195727959646800872797 30664573397984867550327299)
        ·
          refine ⟨45996860096977301325490949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30664573397984867550327299 45996860096977301325490949)
          ·
            refine ⟨8624411268183243998529553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45996860096977301325490949 8624411268183243998529553)
            ·
              refine ⟨6468308451137432998897165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8624411268183243998529553 6468308451137432998897165)
              ·
                refine ⟨2425615669176537374586437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6468308451137432998897165 2425615669176537374586437)
                ·
                  refine ⟨454802937970600757734957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2425615669176537374586437 454802937970600757734957)
                  ·
                    rfl

theorem cell22_3985765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 3, 4].length) (baseStart_3985765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3985765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3985765 prefixEnd_3985765 := by exact prefixLift 3985765
  have htrace : WordTrace (prefixWord ++ tailWord_3985765) baseStart_3985765 baseEnd_3985765 := by
    simpa [prefixWord, tailWord_3985765, baseEnd_3985765] using wordTrace_append hprefix tailTrace_3985765
  have hstable : (prefixWord ++ tailWord_3985765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985765).length < 2 ^ (prefixWord ++ tailWord_3985765).sum := by decide
  have hdescent : baseEnd_3985765 < baseStart_3985765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985767 : List Nat := [1, 1, 5, 1, 3, 3, 2, 1, 1, 4]
def baseStart_3985767 : Nat := 118140960795 + 3985767 * 2 ^ 59
def prefixEnd_3985767 : Nat := 4983230072969 + 3 ^ 40 * 3985767 * 2
def baseEnd_3985767 : Nat := 1364409498552674934654865

theorem tailTrace_3985767 : CollatzResearch.WordTrace tailWord_3985767 prefixEnd_3985767 1364409498552674934654865 := by
  unfold tailWord_3985767
  simp only [CollatzResearch.WordTrace]
  refine ⟨145372865351254348654235555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96915243567502899102823703 145372865351254348654235555)
  ·
    refine ⟨218059298026881522981353333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145372865351254348654235555 218059298026881522981353333)
    ·
      refine ⟨20443059190020142779501875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 218059298026881522981353333 20443059190020142779501875)
      ·
        refine ⟨30664588785030214169252813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20443059190020142779501875 30664588785030214169252813)
        ·
          refine ⟨11499220794386330313469805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30664588785030214169252813 11499220794386330313469805)
          ·
            refine ⟨4312207797894873867551177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11499220794386330313469805 4312207797894873867551177)
            ·
              refine ⟨3234155848421155400663383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4312207797894873867551177 3234155848421155400663383)
              ·
                refine ⟨4851233772631733100995075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3234155848421155400663383 4851233772631733100995075)
                ·
                  refine ⟨7276850658947599651492613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4851233772631733100995075 7276850658947599651492613)
                  ·
                    refine ⟨1364409498552674934654865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7276850658947599651492613 1364409498552674934654865)
                    ·
                      rfl

theorem cell22_3985767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 2, 1, 1, 4].length) (baseStart_3985767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3985767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3985767 prefixEnd_3985767 := by exact prefixLift 3985767
  have htrace : WordTrace (prefixWord ++ tailWord_3985767) baseStart_3985767 baseEnd_3985767 := by
    simpa [prefixWord, tailWord_3985767, baseEnd_3985767] using wordTrace_append hprefix tailTrace_3985767
  have hstable : (prefixWord ++ tailWord_3985767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985767).length < 2 ^ (prefixWord ++ tailWord_3985767).sum := by decide
  have hdescent : baseEnd_3985767 < baseStart_3985767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985776 : List Nat := [2, 1, 1, 1, 4, 4, 9]
def baseStart_3985776 : Nat := 118140960795 + 3985776 * 2 ^ 59
def prefixEnd_3985776 : Nat := 4983230072969 + 3 ^ 40 * 3985776 * 2
def baseEnd_3985776 : Nat := 50533799238392663377031

theorem tailTrace_3985776 : CollatzResearch.WordTrace tailWord_3985776 prefixEnd_3985776 50533799238392663377031 := by
  unfold tailWord_3985776
  simp only [CollatzResearch.WordTrace]
  refine ⟨72686596804110871595656591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96915462405481162127542121 72686596804110871595656591)
  ·
    refine ⟨109029895206166307393484887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72686596804110871595656591 109029895206166307393484887)
    ·
      refine ⟨163544842809249461090227331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109029895206166307393484887 163544842809249461090227331)
      ·
        refine ⟨245317264213874191635340997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163544842809249461090227331 245317264213874191635340997)
        ·
          refine ⟨45996987040101410931626437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 245317264213874191635340997 45996987040101410931626437)
          ·
            refine ⟨8624435070019014549679957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45996987040101410931626437 8624435070019014549679957)
            ·
              refine ⟨50533799238392663377031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8624435070019014549679957 50533799238392663377031)
              ·
                rfl

theorem cell22_3985776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 9].length) (baseStart_3985776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3985776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3985776 prefixEnd_3985776 := by exact prefixLift 3985776
  have htrace : WordTrace (prefixWord ++ tailWord_3985776) baseStart_3985776 baseEnd_3985776 := by
    simpa [prefixWord, tailWord_3985776, baseEnd_3985776] using wordTrace_append hprefix tailTrace_3985776
  have hstable : (prefixWord ++ tailWord_3985776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985776).length < 2 ^ (prefixWord ++ tailWord_3985776).sum := by decide
  have hdescent : baseEnd_3985776 < baseStart_3985776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985782 : List Nat := [5, 1, 1, 4, 1, 1, 2, 1, 6]
def baseStart_3985782 : Nat := 118140960795 + 3985782 * 2 ^ 59
def prefixEnd_3985782 : Nat := 4983230072969 + 3 ^ 40 * 3985782 * 2
def baseEnd_3985782 : Nat := 454804877786406631843273

theorem tailTrace_3985782 : CollatzResearch.WordTrace tailWord_3985782 prefixEnd_3985782 454804877786406631843273 := by
  unfold tailWord_3985782
  simp only [CollatzResearch.WordTrace]
  refine ⟨9085838277887500388501975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96915608297466670810687733 9085838277887500388501975)
  ·
    refine ⟨13628757416831250582752963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9085838277887500388501975 13628757416831250582752963)
    ·
      refine ⟨20443136125246875874129445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13628757416831250582752963 20443136125246875874129445)
      ·
        refine ⟨3833088023483789226399271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20443136125246875874129445 3833088023483789226399271)
        ·
          refine ⟨5749632035225683839598907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3833088023483789226399271 5749632035225683839598907)
          ·
            refine ⟨8624448052838525759398361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5749632035225683839598907 8624448052838525759398361)
            ·
              refine ⟨6468336039628894319548771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8624448052838525759398361 6468336039628894319548771)
              ·
                refine ⟨9702504059443341479323157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6468336039628894319548771 9702504059443341479323157)
                ·
                  refine ⟨454804877786406631843273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9702504059443341479323157 454804877786406631843273)
                  ·
                    rfl

theorem cell22_3985782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 1, 6].length) (baseStart_3985782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3985782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3985782 prefixEnd_3985782 := by exact prefixLift 3985782
  have htrace : WordTrace (prefixWord ++ tailWord_3985782) baseStart_3985782 baseEnd_3985782 := by
    simpa [prefixWord, tailWord_3985782, baseEnd_3985782] using wordTrace_append hprefix tailTrace_3985782
  have hstable : (prefixWord ++ tailWord_3985782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985782).length < 2 ^ (prefixWord ++ tailWord_3985782).sum := by decide
  have hdescent : baseEnd_3985782 < baseStart_3985782 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985893 : List Nat := [1, 3, 1, 5, 3, 1, 2, 2, 1, 3]
def baseStart_3985893 : Nat := 118140960795 + 3985893 * 2 ^ 59
def prefixEnd_3985893 : Nat := 4983230072969 + 3 ^ 40 * 3985893 * 2
def baseEnd_3985893 : Nat := 1364452630927652606004479

theorem tailTrace_3985893 : CollatzResearch.WordTrace tailWord_3985893 prefixEnd_3985893 1364452630927652606004479 := by
  unfold tailWord_3985893
  simp only [CollatzResearch.WordTrace]
  refine ⟨145377460948797872173322333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96918307299198581448881555 145377460948797872173322333)
  ·
    refine ⟨54516547855799202064995875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145377460948797872173322333 54516547855799202064995875)
    ·
      refine ⟨81774821783698803097493813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54516547855799202064995875 81774821783698803097493813)
      ·
        refine ⟨7666389542221762790390045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81774821783698803097493813 7666389542221762790390045)
        ·
          refine ⟨2874896078333161046396267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7666389542221762790390045 2874896078333161046396267)
          ·
            refine ⟨4312344117499741569594401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2874896078333161046396267 4312344117499741569594401)
            ·
              refine ⟨3234258088124806177195801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4312344117499741569594401 3234258088124806177195801)
              ·
                refine ⟨2425693566093604632896851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3234258088124806177195801 2425693566093604632896851)
                ·
                  refine ⟨3638540349140406949345277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2425693566093604632896851 3638540349140406949345277)
                  ·
                    refine ⟨1364452630927652606004479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3638540349140406949345277 1364452630927652606004479)
                    ·
                      rfl

theorem cell22_3985893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 2, 2, 1, 3].length) (baseStart_3985893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3985893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3985893 prefixEnd_3985893 := by exact prefixLift 3985893
  have htrace : WordTrace (prefixWord ++ tailWord_3985893) baseStart_3985893 baseEnd_3985893 := by
    simpa [prefixWord, tailWord_3985893, baseEnd_3985893] using wordTrace_append hprefix tailTrace_3985893
  have hstable : (prefixWord ++ tailWord_3985893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985893).length < 2 ^ (prefixWord ++ tailWord_3985893).sum := by decide
  have hdescent : baseEnd_3985893 < baseStart_3985893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985900 : List Nat := [2, 2, 1, 1, 2, 1, 5, 4, 4]
def baseStart_3985900 : Nat := 118140960795 + 3985900 * 2 ^ 59
def prefixEnd_3985900 : Nat := 4983230072969 + 3 ^ 40 * 3985900 * 2
def baseEnd_3985900 : Nat := 454818342390235640359819

theorem tailTrace_3985900 : CollatzResearch.WordTrace tailWord_3985900 prefixEnd_3985900 454818342390235640359819 := by
  unfold tailWord_3985900
  simp only [CollatzResearch.WordTrace]
  refine ⟨72688858129886256184413577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96918477506515008245884769 72688858129886256184413577)
  ·
    refine ⟨54516643597414692138310183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72688858129886256184413577 54516643597414692138310183)
    ·
      refine ⟨81774965396122038207465275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54516643597414692138310183 81774965396122038207465275)
      ·
        refine ⟨122662448094183057311197913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81774965396122038207465275 122662448094183057311197913)
        ·
          refine ⟨91996836070637292983398435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122662448094183057311197913 91996836070637292983398435)
          ·
            refine ⟨137995254105955939475097653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91996836070637292983398435 137995254105955939475097653)
            ·
              refine ⟨12937055072433369325790405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 137995254105955939475097653 12937055072433369325790405)
              ·
                refine ⟨2425697826081256748585701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12937055072433369325790405 2425697826081256748585701)
                ·
                  refine ⟨454818342390235640359819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2425697826081256748585701 454818342390235640359819)
                  ·
                    rfl

theorem cell22_3985900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 4, 4].length) (baseStart_3985900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3985900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3985900 prefixEnd_3985900 := by exact prefixLift 3985900
  have htrace : WordTrace (prefixWord ++ tailWord_3985900) baseStart_3985900 baseEnd_3985900 := by
    simpa [prefixWord, tailWord_3985900, baseEnd_3985900] using wordTrace_append hprefix tailTrace_3985900
  have hstable : (prefixWord ++ tailWord_3985900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985900).length < 2 ^ (prefixWord ++ tailWord_3985900).sum := by decide
  have hdescent : baseEnd_3985900 < baseStart_3985900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985913 : List Nat := [1, 2, 1, 3, 1, 2, 2, 2, 4, 4]
def baseStart_3985913 : Nat := 118140960795 + 3985913 * 2 ^ 59
def prefixEnd_3985913 : Nat := 4983230072969 + 3 ^ 40 * 3985913 * 2
def baseEnd_3985913 : Nat := 1364459477336379220504417

theorem tailTrace_3985913 : CollatzResearch.WordTrace tailWord_3985913 prefixEnd_3985913 1364459477336379220504417 := by
  unfold tailWord_3985913
  simp only [CollatzResearch.WordTrace]
  refine ⟨145378190408725415589050393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96918793605816943726033595 145378190408725415589050393)
  ·
    refine ⟨109033642806544061691787795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145378190408725415589050393 109033642806544061691787795)
    ·
      refine ⟨163550464209816092537681693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109033642806544061691787795 163550464209816092537681693)
      ·
        refine ⟨61331424078681034701630635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163550464209816092537681693 61331424078681034701630635)
        ·
          refine ⟨91997136118021552052445953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61331424078681034701630635 91997136118021552052445953)
          ·
            refine ⟨68997852088516164039334465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91997136118021552052445953 68997852088516164039334465)
            ·
              refine ⟨51748389066387123029500849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68997852088516164039334465 51748389066387123029500849)
              ·
                refine ⟨38811291799790342272125637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51748389066387123029500849 38811291799790342272125637)
                ·
                  refine ⟨7277117212460689176023557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38811291799790342272125637 7277117212460689176023557)
                  ·
                    refine ⟨1364459477336379220504417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7277117212460689176023557 1364459477336379220504417)
                    ·
                      rfl

theorem cell22_3985913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 4, 4].length) (baseStart_3985913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3985913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3985913 prefixEnd_3985913 := by exact prefixLift 3985913
  have htrace : WordTrace (prefixWord ++ tailWord_3985913) baseStart_3985913 baseEnd_3985913 := by
    simpa [prefixWord, tailWord_3985913, baseEnd_3985913] using wordTrace_append hprefix tailTrace_3985913
  have hstable : (prefixWord ++ tailWord_3985913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985913).length < 2 ^ (prefixWord ++ tailWord_3985913).sum := by decide
  have hdescent : baseEnd_3985913 < baseStart_3985913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985949 : List Nat := [1, 4, 2, 2, 1, 4, 1, 2, 2, 3]
def baseStart_3985949 : Nat := 118140960795 + 3985949 * 2 ^ 59
def prefixEnd_3985949 : Nat := 4983230072969 + 3 ^ 40 * 3985949 * 2
def baseEnd_3985949 : Nat := 1364471800872087126604307

theorem tailTrace_3985949 : CollatzResearch.WordTrace tailWord_3985949 prefixEnd_3985949 1364471800872087126604307 := by
  unfold tailWord_3985949
  simp only [CollatzResearch.WordTrace]
  refine ⟨145379503436594993737360901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96919668957729995824907267 145379503436594993737360901)
  ·
    refine ⟨27258656894361561325755169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145379503436594993737360901 27258656894361561325755169)
    ·
      refine ⟨20443992670771170994316377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27258656894361561325755169 20443992670771170994316377)
      ·
        refine ⟨15332994503078378245737283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20443992670771170994316377 15332994503078378245737283)
        ·
          refine ⟨22999491754617567368605925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15332994503078378245737283 22999491754617567368605925)
          ·
            refine ⟨4312404703990793881613611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22999491754617567368605925 4312404703990793881613611)
            ·
              refine ⟨6468607055986190822420417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4312404703990793881613611 6468607055986190822420417)
              ·
                refine ⟨4851455291989643116815313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6468607055986190822420417 4851455291989643116815313)
                ·
                  refine ⟨3638591468992232337611485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4851455291989643116815313 3638591468992232337611485)
                  ·
                    refine ⟨1364471800872087126604307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3638591468992232337611485 1364471800872087126604307)
                    ·
                      rfl

theorem cell22_3985949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 2, 2, 3].length) (baseStart_3985949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3985949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3985949 prefixEnd_3985949 := by exact prefixLift 3985949
  have htrace : WordTrace (prefixWord ++ tailWord_3985949) baseStart_3985949 baseEnd_3985949 := by
    simpa [prefixWord, tailWord_3985949, baseEnd_3985949] using wordTrace_append hprefix tailTrace_3985949
  have hstable : (prefixWord ++ tailWord_3985949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985949).length < 2 ^ (prefixWord ++ tailWord_3985949).sum := by decide
  have hdescent : baseEnd_3985949 < baseStart_3985949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985966 : List Nat := [4, 1, 3, 1, 3, 1, 3, 1, 2, 3]
def baseStart_3985966 : Nat := 118140960795 + 3985966 * 2 ^ 59
def prefixEnd_3985966 : Nat := 4983230072969 + 3 ^ 40 * 3985966 * 2
def baseEnd_3985966 : Nat := 1364477620319504748929255

theorem tailTrace_3985966 : CollatzResearch.WordTrace tailWord_3985966 prefixEnd_3985966 1364477620319504748929255 := by
  unfold tailWord_3985966
  simp only [CollatzResearch.WordTrace]
  refine ⟨18172515434691675705091219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96920082318355603760486501 18172515434691675705091219)
  ·
    refine ⟨27258773152037513557636829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18172515434691675705091219 27258773152037513557636829)
    ·
      refine ⟨10222039932014067584113811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27258773152037513557636829 10222039932014067584113811)
      ·
        refine ⟨15333059898021101376170717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10222039932014067584113811 15333059898021101376170717)
        ·
          refine ⟨5749897461757913016064019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15333059898021101376170717 5749897461757913016064019)
          ·
            refine ⟨8624846192636869524096029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5749897461757913016064019 8624846192636869524096029)
            ·
              refine ⟨3234317322238826071536011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8624846192636869524096029 3234317322238826071536011)
              ·
                refine ⟨4851475983358239107304017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3234317322238826071536011 4851475983358239107304017)
                ·
                  refine ⟨3638606987518679330478013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4851475983358239107304017 3638606987518679330478013)
                  ·
                    refine ⟨1364477620319504748929255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3638606987518679330478013 1364477620319504748929255)
                    ·
                      rfl

theorem cell22_3985966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_3985966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3985966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3985966 prefixEnd_3985966 := by exact prefixLift 3985966
  have htrace : WordTrace (prefixWord ++ tailWord_3985966) baseStart_3985966 baseEnd_3985966 := by
    simpa [prefixWord, tailWord_3985966, baseEnd_3985966] using wordTrace_append hprefix tailTrace_3985966
  have hstable : (prefixWord ++ tailWord_3985966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985966).length < 2 ^ (prefixWord ++ tailWord_3985966).sum := by decide
  have hdescent : baseEnd_3985966 < baseStart_3985966 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985994 : List Nat := [3, 1, 2, 1, 1, 4, 3, 3, 1, 3]
def baseStart_3985994 : Nat := 118140960795 + 3985994 * 2 ^ 59
def prefixEnd_3985994 : Nat := 4983230072969 + 3 ^ 40 * 3985994 * 2
def baseEnd_3985994 : Nat := 1364487205291722009229169

theorem tailTrace_3985994 : CollatzResearch.WordTrace tailWord_3985994 prefixEnd_3985994 1364487205291722009229169 := by
  unfold tailWord_3985994
  simp only [CollatzResearch.WordTrace]
  refine ⟨36345286180357991605687259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96920763147621310948499357 36345286180357991605687259)
  ·
    refine ⟨54517929270536987408530889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36345286180357991605687259 54517929270536987408530889)
    ·
      refine ⟨40888446952902740556398167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54517929270536987408530889 40888446952902740556398167)
      ·
        refine ⟨61332670429354110834597251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40888446952902740556398167 61332670429354110834597251)
        ·
          refine ⟨91999005644031166251895877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61332670429354110834597251 91999005644031166251895877)
          ·
            refine ⟨17249813558255843672230477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91999005644031166251895877 17249813558255843672230477)
            ·
              refine ⟨6468680084345941377086429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17249813558255843672230477 6468680084345941377086429)
              ·
                refine ⟨2425755031629728016407411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6468680084345941377086429 2425755031629728016407411)
                ·
                  refine ⟨3638632547444592024611117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2425755031629728016407411 3638632547444592024611117)
                  ·
                    refine ⟨1364487205291722009229169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3638632547444592024611117 1364487205291722009229169)
                    ·
                      rfl

theorem cell22_3985994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 3, 1, 3].length) (baseStart_3985994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3985994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3985994 prefixEnd_3985994 := by exact prefixLift 3985994
  have htrace : WordTrace (prefixWord ++ tailWord_3985994) baseStart_3985994 baseEnd_3985994 := by
    simpa [prefixWord, tailWord_3985994, baseEnd_3985994] using wordTrace_append hprefix tailTrace_3985994
  have hstable : (prefixWord ++ tailWord_3985994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985994).length < 2 ^ (prefixWord ++ tailWord_3985994).sum := by decide
  have hdescent : baseEnd_3985994 < baseStart_3985994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986020 : List Nat := [2, 3, 1, 1, 2, 2, 2, 2, 3, 4]
def baseStart_3986020 : Nat := 118140960795 + 3986020 * 2 ^ 59
def prefixEnd_3986020 : Nat := 4983230072969 + 3 ^ 40 * 3986020 * 2
def baseEnd_3986020 : Nat := 1364496105623066608079089

theorem tailTrace_3986020 : CollatzResearch.WordTrace tailWord_3986020 prefixEnd_3986020 1364496105623066608079089 := by
  unfold tailWord_3986020
  simp only [CollatzResearch.WordTrace]
  refine ⟨72691046509668886431597757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96921395346225181908797009 72691046509668886431597757)
  ·
    refine ⟨27259142441125832411849159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72691046509668886431597757 27259142441125832411849159)
    ·
      refine ⟨40888713661688748617773739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27259142441125832411849159 40888713661688748617773739)
      ·
        refine ⟨61333070492533122926660609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40888713661688748617773739 61333070492533122926660609)
        ·
          refine ⟨45999802869399842194995457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61333070492533122926660609 45999802869399842194995457)
          ·
            refine ⟨34499852152049881646246593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45999802869399842194995457 34499852152049881646246593)
            ·
              refine ⟨25874889114037411234684945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34499852152049881646246593 25874889114037411234684945)
              ·
                refine ⟨19406166835528058426013709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25874889114037411234684945 19406166835528058426013709)
                ·
                  refine ⟨7277312563323021909755141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19406166835528058426013709 7277312563323021909755141)
                  ·
                    refine ⟨1364496105623066608079089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7277312563323021909755141 1364496105623066608079089)
                    ·
                      rfl

theorem cell22_3986020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 3, 4].length) (baseStart_3986020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3986020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3986020 prefixEnd_3986020 := by exact prefixLift 3986020
  have htrace : WordTrace (prefixWord ++ tailWord_3986020) baseStart_3986020 baseEnd_3986020 := by
    simpa [prefixWord, tailWord_3986020, baseEnd_3986020] using wordTrace_append hprefix tailTrace_3986020
  have hstable : (prefixWord ++ tailWord_3986020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986020).length < 2 ^ (prefixWord ++ tailWord_3986020).sum := by decide
  have hdescent : baseEnd_3986020 < baseStart_3986020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986118 : List Nat := [6, 1, 2, 1, 2, 1, 1, 1, 4, 3]
def baseStart_3986118 : Nat := 118140960795 + 3986118 * 2 ^ 59
def prefixEnd_3986118 : Nat := 4983230072969 + 3 ^ 40 * 3986118 * 2
def baseEnd_3986118 : Nat := 1364529653025827019128789

theorem tailTrace_3986118 : CollatzResearch.WordTrace tailWord_3986118 prefixEnd_3986118 1364529653025827019128789 := by
  unfold tailWord_3986118
  simp only [CollatzResearch.WordTrace]
  refine ⟨4543302105405710487508219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 96923778248655157066842005 4543302105405710487508219)
  ·
    refine ⟨6814953158108565731262329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4543302105405710487508219 6814953158108565731262329)
    ·
      refine ⟨5111214868581424298446747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6814953158108565731262329 5111214868581424298446747)
      ·
        refine ⟨7666822302872136447670121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5111214868581424298446747 7666822302872136447670121)
        ·
          refine ⟨5750116727154102335752591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7666822302872136447670121 5750116727154102335752591)
          ·
            refine ⟨8625175090731153503628887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5750116727154102335752591 8625175090731153503628887)
            ·
              refine ⟨12937762636096730255443331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8625175090731153503628887 12937762636096730255443331)
              ·
                refine ⟨19406643954145095383164997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12937762636096730255443331 19406643954145095383164997)
                ·
                  refine ⟨3638745741402205384343437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19406643954145095383164997 3638745741402205384343437)
                  ·
                    refine ⟨1364529653025827019128789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3638745741402205384343437 1364529653025827019128789)
                    ·
                      rfl

theorem cell22_3986118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_3986118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3986118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3986118 prefixEnd_3986118 := by exact prefixLift 3986118
  have htrace : WordTrace (prefixWord ++ tailWord_3986118) baseStart_3986118 baseEnd_3986118 := by
    simpa [prefixWord, tailWord_3986118, baseEnd_3986118] using wordTrace_append hprefix tailTrace_3986118
  have hstable : (prefixWord ++ tailWord_3986118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986118).length < 2 ^ (prefixWord ++ tailWord_3986118).sum := by decide
  have hdescent : baseEnd_3986118 < baseStart_3986118 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986129 : List Nat := [1, 2, 2, 1, 2, 3, 1, 6, 1, 3]
def baseStart_3986129 : Nat := 118140960795 + 3986129 * 2 ^ 59
def prefixEnd_3986129 : Nat := 4983230072969 + 3 ^ 40 * 3986129 * 2
def baseEnd_3986129 : Nat := 1364533418550626657103755

theorem tailTrace_3986129 : CollatzResearch.WordTrace tailWord_3986129 prefixEnd_3986129 1364533418550626657103755 := by
  unfold tailWord_3986129
  simp only [CollatzResearch.WordTrace]
  refine ⟨145386068575942884478913441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96924045717295256319275627 145386068575942884478913441)
  ·
    refine ⟨109039551431957163359185081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145386068575942884478913441 109039551431957163359185081)
    ·
      refine ⟨81779663573967872519388811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109039551431957163359185081 81779663573967872519388811)
      ·
        refine ⟨122669495360951808779083217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81779663573967872519388811 122669495360951808779083217)
        ·
          refine ⟨92002121520713856584312413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122669495360951808779083217 92002121520713856584312413)
          ·
            refine ⟨34500795570267696219117155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92002121520713856584312413 34500795570267696219117155)
            ·
              refine ⟨51751193355401544328675733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34500795570267696219117155 51751193355401544328675733)
              ·
                refine ⟨2425837188534447390406675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 51751193355401544328675733 2425837188534447390406675)
                ·
                  refine ⟨3638755782801671085610013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2425837188534447390406675 3638755782801671085610013)
                  ·
                    refine ⟨1364533418550626657103755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3638755782801671085610013 1364533418550626657103755)
                    ·
                      rfl

theorem cell22_3986129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 6, 1, 3].length) (baseStart_3986129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3986129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3986129 prefixEnd_3986129 := by exact prefixLift 3986129
  have htrace : WordTrace (prefixWord ++ tailWord_3986129) baseStart_3986129 baseEnd_3986129 := by
    simpa [prefixWord, tailWord_3986129, baseEnd_3986129] using wordTrace_append hprefix tailTrace_3986129
  have hstable : (prefixWord ++ tailWord_3986129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986129).length < 2 ^ (prefixWord ++ tailWord_3986129).sum := by decide
  have hdescent : baseEnd_3986129 < baseStart_3986129 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986170 : List Nat := [3, 1, 1, 1, 1, 3, 2, 2, 8]
def baseStart_3986170 : Nat := 118140960795 + 3986170 * 2 ^ 59
def prefixEnd_3986170 : Nat := 4983230072969 + 3 ^ 40 * 3986170 * 2
def baseEnd_3986170 : Nat := 454849151229505405609543

theorem tailTrace_3986170 : CollatzResearch.WordTrace tailWord_3986170 prefixEnd_3986170 454849151229505405609543 := by
  unfold tailWord_3986170
  simp only [CollatzResearch.WordTrace]
  refine ⟨36346890992198587120288991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96925042645862898987437309 36346890992198587120288991)
  ·
    refine ⟨54520336488297880680433487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36346890992198587120288991 54520336488297880680433487)
    ·
      refine ⟨81780504732446821020650231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54520336488297880680433487 81780504732446821020650231)
      ·
        refine ⟨122670757098670231530975347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81780504732446821020650231 122670757098670231530975347)
        ·
          refine ⟨184006135648005347296463021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122670757098670231530975347 184006135648005347296463021)
          ·
            refine ⟨69002300868002005236173633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184006135648005347296463021 69002300868002005236173633)
            ·
              refine ⟨51751725651001503927130225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69002300868002005236173633 51751725651001503927130225)
              ·
                refine ⟨38813794238251127945347669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51751725651001503927130225 38813794238251127945347669)
                ·
                  refine ⟨454849151229505405609543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38813794238251127945347669 454849151229505405609543)
                  ·
                    rfl

theorem cell22_3986170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 8].length) (baseStart_3986170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3986170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3986170 prefixEnd_3986170 := by exact prefixLift 3986170
  have htrace : WordTrace (prefixWord ++ tailWord_3986170) baseStart_3986170 baseEnd_3986170 := by
    simpa [prefixWord, tailWord_3986170, baseEnd_3986170] using wordTrace_append hprefix tailTrace_3986170
  have hstable : (prefixWord ++ tailWord_3986170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986170).length < 2 ^ (prefixWord ++ tailWord_3986170).sum := by decide
  have hdescent : baseEnd_3986170 < baseStart_3986170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986202 : List Nat := [3, 1, 1, 3, 2, 1, 2, 3, 1, 5]
def baseStart_3986202 : Nat := 118140960795 + 3986202 * 2 ^ 59
def prefixEnd_3986202 : Nat := 4983230072969 + 3 ^ 40 * 3986202 * 2
def baseEnd_3986202 : Nat := 1364558407942478800028531

theorem tailTrace_3986202 : CollatzResearch.WordTrace tailWord_3986202 prefixEnd_3986202 1364558407942478800028531 := by
  unfold tailWord_3986202
  simp only [CollatzResearch.WordTrace]
  refine ⟨36347182776169604486580215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96925820736452278630880573 36347182776169604486580215)
  ·
    refine ⟨54520774164254406729870323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36347182776169604486580215 54520774164254406729870323)
    ·
      refine ⟨81781161246381610094805485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54520774164254406729870323 81781161246381610094805485)
      ·
        refine ⟨30667935467393103785552057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81781161246381610094805485 30667935467393103785552057)
        ·
          refine ⟨23000951600544827839164043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30667935467393103785552057 23000951600544827839164043)
          ·
            refine ⟨34501427400817241758746065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23000951600544827839164043 34501427400817241758746065)
            ·
              refine ⟨25876070550612931319059549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34501427400817241758746065 25876070550612931319059549)
              ·
                refine ⟨9703526456479849244647331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25876070550612931319059549 9703526456479849244647331)
                ·
                  refine ⟨14555289684719773866970997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9703526456479849244647331 14555289684719773866970997)
                  ·
                    refine ⟨1364558407942478800028531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14555289684719773866970997 1364558407942478800028531)
                    ·
                      rfl

theorem cell22_3986202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 3, 1, 5].length) (baseStart_3986202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3986202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3986202 prefixEnd_3986202 := by exact prefixLift 3986202
  have htrace : WordTrace (prefixWord ++ tailWord_3986202) baseStart_3986202 baseEnd_3986202 := by
    simpa [prefixWord, tailWord_3986202, baseEnd_3986202] using wordTrace_append hprefix tailTrace_3986202
  have hstable : (prefixWord ++ tailWord_3986202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986202).length < 2 ^ (prefixWord ++ tailWord_3986202).sum := by decide
  have hdescent : baseEnd_3986202 < baseStart_3986202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986311 : List Nat := [1, 1, 4, 2, 3, 2, 3, 1, 5]
def baseStart_3986311 : Nat := 118140960795 + 3986311 * 2 ^ 59
def prefixEnd_3986311 : Nat := 4983230072969 + 3 ^ 40 * 3986311 * 2
def baseEnd_3986311 : Nat := 454865240290012949684399

theorem tailTrace_3986311 : CollatzResearch.WordTrace tailWord_3986311 prefixEnd_3986311 454865240290012949684399 := by
  unfold tailWord_3986311
  simp only [CollatzResearch.WordTrace]
  refine ⟨145392706661283529562038787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96928471107522353041359191 145392706661283529562038787)
  ·
    refine ⟨218089059991925294343058181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145392706661283529562038787 218089059991925294343058181)
    ·
      refine ⟨40891698748485992689323409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 218089059991925294343058181 40891698748485992689323409)
      ·
        refine ⟨30668774061364494516992557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40891698748485992689323409 30668774061364494516992557)
        ·
          refine ⟨11500790273011685443872209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30668774061364494516992557 11500790273011685443872209)
          ·
            refine ⟨8625592704758764082904157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11500790273011685443872209 8625592704758764082904157)
            ·
              refine ⟨3234597264284536531089059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8625592704758764082904157 3234597264284536531089059)
              ·
                refine ⟨4851895896426804796633589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3234597264284536531089059 4851895896426804796633589)
                ·
                  refine ⟨454865240290012949684399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4851895896426804796633589 454865240290012949684399)
                  ·
                    rfl

theorem cell22_3986311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 3, 1, 5].length) (baseStart_3986311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3986311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3986311 prefixEnd_3986311 := by exact prefixLift 3986311
  have htrace : WordTrace (prefixWord ++ tailWord_3986311) baseStart_3986311 baseEnd_3986311 := by
    simpa [prefixWord, tailWord_3986311, baseEnd_3986311] using wordTrace_append hprefix tailTrace_3986311
  have hstable : (prefixWord ++ tailWord_3986311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986311).length < 2 ^ (prefixWord ++ tailWord_3986311).sum := by decide
  have hdescent : baseEnd_3986311 < baseStart_3986311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986332 : List Nat := [2, 2, 3, 3, 3, 1, 1, 3, 1, 3]
def baseStart_3986332 : Nat := 118140960795 + 3986332 * 2 ^ 59
def prefixEnd_3986332 : Nat := 4983230072969 + 3 ^ 40 * 3986332 * 2
def baseEnd_3986332 : Nat := 1364602909599201794278133

theorem tailTrace_3986332 : CollatzResearch.WordTrace tailWord_3986332 prefixEnd_3986332 1364602909599201794278133 := by
  unfold tailWord_3986332
  simp only [CollatzResearch.WordTrace]
  refine ⟨72696736297103725074276625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96928981729471633432368833 72696736297103725074276625)
  ·
    refine ⟨54522552222827793805707469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72696736297103725074276625 54522552222827793805707469)
    ·
      refine ⟨20445957083560422677140301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54522552222827793805707469 20445957083560422677140301)
      ·
        refine ⟨7667233906335158503927613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20445957083560422677140301 7667233906335158503927613)
        ·
          refine ⟨2875212714875684438972855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7667233906335158503927613 2875212714875684438972855)
          ·
            refine ⟨4312819072313526658459283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2875212714875684438972855 4312819072313526658459283)
            ·
              refine ⟨6469228608470289987688925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4312819072313526658459283 6469228608470289987688925)
              ·
                refine ⟨2425960728176358745383347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6469228608470289987688925 2425960728176358745383347)
                ·
                  refine ⟨3638941092264538118075021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2425960728176358745383347 3638941092264538118075021)
                  ·
                    refine ⟨1364602909599201794278133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3638941092264538118075021 1364602909599201794278133)
                    ·
                      rfl

theorem cell22_3986332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 3, 1, 3].length) (baseStart_3986332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3986332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3986332 prefixEnd_3986332 := by exact prefixLift 3986332
  have htrace : WordTrace (prefixWord ++ tailWord_3986332) baseStart_3986332 baseEnd_3986332 := by
    simpa [prefixWord, tailWord_3986332, baseEnd_3986332] using wordTrace_append hprefix tailTrace_3986332
  have hstable : (prefixWord ++ tailWord_3986332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986332).length < 2 ^ (prefixWord ++ tailWord_3986332).sum := by decide
  have hdescent : baseEnd_3986332 < baseStart_3986332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986386 : List Nat := [3, 2, 2, 3, 1, 1, 1, 3, 2, 4]
def baseStart_3986386 : Nat := 118140960795 + 3986386 * 2 ^ 59
def prefixEnd_3986386 : Nat := 4983230072969 + 3 ^ 40 * 3986386 * 2
def baseEnd_3986386 : Nat := 1364621394902763653427967

theorem tailTrace_3986386 : CollatzResearch.WordTrace tailWord_3986386 prefixEnd_3986386 1364621394902763653427967 := by
  unfold tailWord_3986386
  simp only [CollatzResearch.WordTrace]
  refine ⟨36348860534002954342754753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96930294757341211580679341 36348860534002954342754753)
  ·
    refine ⟨27261645400502215757066065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36348860534002954342754753 27261645400502215757066065)
    ·
      refine ⟨20446234050376661817799549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27261645400502215757066065 20446234050376661817799549)
      ·
        refine ⟨7667337768891248181674831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20446234050376661817799549 7667337768891248181674831)
        ·
          refine ⟨11501006653336872272512247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7667337768891248181674831 11501006653336872272512247)
          ·
            refine ⟨17251509980005308408768371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11501006653336872272512247 17251509980005308408768371)
            ·
              refine ⟨25877264970007962613152557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17251509980005308408768371 25877264970007962613152557)
              ·
                refine ⟨9703974363752985979932209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25877264970007962613152557 9703974363752985979932209)
                ·
                  refine ⟨7277980772814739484949157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9703974363752985979932209 7277980772814739484949157)
                  ·
                    refine ⟨1364621394902763653427967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7277980772814739484949157 1364621394902763653427967)
                    ·
                      rfl

theorem cell22_3986386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_3986386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3986386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3986386 prefixEnd_3986386 := by exact prefixLift 3986386
  have htrace : WordTrace (prefixWord ++ tailWord_3986386) baseStart_3986386 baseEnd_3986386 := by
    simpa [prefixWord, tailWord_3986386, baseEnd_3986386] using wordTrace_append hprefix tailTrace_3986386
  have hstable : (prefixWord ++ tailWord_3986386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986386).length < 2 ^ (prefixWord ++ tailWord_3986386).sum := by decide
  have hdescent : baseEnd_3986386 < baseStart_3986386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986405 : List Nat := [1, 3, 1, 6, 1, 1, 2, 2, 2, 3]
def baseStart_3986405 : Nat := 118140960795 + 3986405 * 2 ^ 59
def prefixEnd_3986405 : Nat := 4983230072969 + 3 ^ 40 * 3986405 * 2
def baseEnd_3986405 : Nat := 1364627898991053937202909

theorem tailTrace_3986405 : CollatzResearch.WordTrace tailWord_3986405 prefixEnd_3986405 1364627898991053937202909 := by
  unfold tailWord_3986405
  simp only [CollatzResearch.WordTrace]
  refine ⟨145396135122942983615960669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96930756748628655743973779 145396135122942983615960669)
  ·
    refine ⟨54523550671103618855985251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145396135122942983615960669 54523550671103618855985251)
    ·
      refine ⟨81785326006655428283977877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54523550671103618855985251 81785326006655428283977877)
      ·
        refine ⟨3833687156561973200811463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 81785326006655428283977877 3833687156561973200811463)
        ·
          refine ⟨5750530734842959801217195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3833687156561973200811463 5750530734842959801217195)
          ·
            refine ⟨8625796102264439701825793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5750530734842959801217195 8625796102264439701825793)
            ·
              refine ⟨6469347076698329776369345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8625796102264439701825793 6469347076698329776369345)
              ·
                refine ⟨4852010307523747332277009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6469347076698329776369345 4852010307523747332277009)
                ·
                  refine ⟨3639007730642810499207757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4852010307523747332277009 3639007730642810499207757)
                  ·
                    refine ⟨1364627898991053937202909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3639007730642810499207757 1364627898991053937202909)
                    ·
                      rfl

theorem cell22_3986405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 2, 2, 3].length) (baseStart_3986405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3986405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3986405 prefixEnd_3986405 := by exact prefixLift 3986405
  have htrace : WordTrace (prefixWord ++ tailWord_3986405) baseStart_3986405 baseEnd_3986405 := by
    simpa [prefixWord, tailWord_3986405, baseEnd_3986405] using wordTrace_append hprefix tailTrace_3986405
  have hstable : (prefixWord ++ tailWord_3986405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986405).length < 2 ^ (prefixWord ++ tailWord_3986405).sum := by decide
  have hdescent : baseEnd_3986405 < baseStart_3986405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986418 : List Nat := [3, 2, 1, 5, 1, 2, 1, 7]
def baseStart_3986418 : Nat := 118140960795 + 3986418 * 2 ^ 59
def prefixEnd_3986418 : Nat := 4983230072969 + 3 ^ 40 * 3986418 * 2
def baseEnd_3986418 : Nat := 151625816572969581847541

theorem tailTrace_3986418 : CollatzResearch.WordTrace tailWord_3986418 prefixEnd_3986418 151625816572969581847541 := by
  unfold tailWord_3986418
  simp only [CollatzResearch.WordTrace]
  refine ⟨36349152317973971709045977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96931072847930591224122605 36349152317973971709045977)
  ·
    refine ⟨27261864238480478781784483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36349152317973971709045977 27261864238480478781784483)
    ·
      refine ⟨40892796357720718172676725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27261864238480478781784483 40892796357720718172676725)
      ·
        refine ⟨3833699658536317328688443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40892796357720718172676725 3833699658536317328688443)
        ·
          refine ⟨5750549487804475993032665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3833699658536317328688443 5750549487804475993032665)
          ·
            refine ⟨4312912115853356994774499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5750549487804475993032665 4312912115853356994774499)
            ·
              refine ⟨6469368173780035492161749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4312912115853356994774499 6469368173780035492161749)
              ·
                refine ⟨151625816572969581847541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6469368173780035492161749 151625816572969581847541)
                ·
                  rfl

theorem cell22_3986418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 7].length) (baseStart_3986418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3986418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3986418 prefixEnd_3986418 := by exact prefixLift 3986418
  have htrace : WordTrace (prefixWord ++ tailWord_3986418) baseStart_3986418 baseEnd_3986418 := by
    simpa [prefixWord, tailWord_3986418, baseEnd_3986418] using wordTrace_append hprefix tailTrace_3986418
  have hstable : (prefixWord ++ tailWord_3986418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986418).length < 2 ^ (prefixWord ++ tailWord_3986418).sum := by decide
  have hdescent : baseEnd_3986418 < baseStart_3986418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986493 : List Nat := [1, 4, 1, 3, 1, 3, 2, 2, 1, 4]
def baseStart_3986493 : Nat := 118140960795 + 3986493 * 2 ^ 59
def prefixEnd_3986493 : Nat := 4983230072969 + 3 ^ 40 * 3986493 * 2
def baseEnd_3986493 : Nat := 1364658023189451041002639

theorem tailTrace_3986493 : CollatzResearch.WordTrace tailWord_3986493 prefixEnd_3986493 1364658023189451041002639 := by
  unfold tailWord_3986493
  simp only [CollatzResearch.WordTrace]
  refine ⟨145399344746624174645164133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96932896497749449763442755 145399344746624174645164133)
  ·
    refine ⟨27262377139992032745968275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145399344746624174645164133 27262377139992032745968275)
    ·
      refine ⟨40893565709988049118952413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27262377139992032745968275 40893565709988049118952413)
      ·
        refine ⟨15335087141245518419607155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40893565709988049118952413 15335087141245518419607155)
        ·
          refine ⟨23002630711868277629410733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15335087141245518419607155 23002630711868277629410733)
          ·
            refine ⟨8625986516950604111029025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23002630711868277629410733 8625986516950604111029025)
            ·
              refine ⟨6469489887712953083271769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8625986516950604111029025 6469489887712953083271769)
              ·
                refine ⟨4852117415784714812453827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6469489887712953083271769 4852117415784714812453827)
                ·
                  refine ⟨7278176123677072218680741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4852117415784714812453827 7278176123677072218680741)
                  ·
                    refine ⟨1364658023189451041002639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7278176123677072218680741 1364658023189451041002639)
                    ·
                      rfl

theorem cell22_3986493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 2, 1, 4].length) (baseStart_3986493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3986493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3986493 prefixEnd_3986493 := by exact prefixLift 3986493
  have htrace : WordTrace (prefixWord ++ tailWord_3986493) baseStart_3986493 baseEnd_3986493 := by
    simpa [prefixWord, tailWord_3986493, baseEnd_3986493] using wordTrace_append hprefix tailTrace_3986493
  have hstable : (prefixWord ++ tailWord_3986493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986493).length < 2 ^ (prefixWord ++ tailWord_3986493).sum := by decide
  have hdescent : baseEnd_3986493 < baseStart_3986493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986504 : List Nat := [2, 1, 3, 1, 1, 1, 3, 3, 1, 6]
def baseStart_3986504 : Nat := 118140960795 + 3986504 * 2 ^ 59
def prefixEnd_3986504 : Nat := 4983230072969 + 3 ^ 40 * 3986504 * 2
def baseEnd_3986504 : Nat := 1364661788714250678977605

theorem tailTrace_3986504 : CollatzResearch.WordTrace tailWord_3986504 prefixEnd_3986504 1364661788714250678977605 := by
  unfold tailWord_3986504
  simp only [CollatzResearch.WordTrace]
  refine ⟨72699872974792161761907283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96933163966389549015876377 72699872974792161761907283)
  ·
    refine ⟨109049809462188242642860925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72699872974792161761907283 109049809462188242642860925)
    ·
      refine ⟨40893678548320590991072847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109049809462188242642860925 40893678548320590991072847)
      ·
        refine ⟨61340517822480886486609271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40893678548320590991072847 61340517822480886486609271)
        ·
          refine ⟨92010776733721329729913907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61340517822480886486609271 92010776733721329729913907)
          ·
            refine ⟨138016165100581994594870861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92010776733721329729913907 138016165100581994594870861)
            ·
              refine ⟨51756061912718247973076573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138016165100581994594870861 51756061912718247973076573)
              ·
                refine ⟨19408523217269342989903715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51756061912718247973076573 19408523217269342989903715)
                ·
                  refine ⟨29112784825904014484855573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19408523217269342989903715 29112784825904014484855573)
                  ·
                    refine ⟨1364661788714250678977605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29112784825904014484855573 1364661788714250678977605)
                    ·
                      rfl

theorem cell22_3986504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 1, 6].length) (baseStart_3986504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3986504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3986504 prefixEnd_3986504 := by exact prefixLift 3986504
  have htrace : WordTrace (prefixWord ++ tailWord_3986504) baseStart_3986504 baseEnd_3986504 := by
    simpa [prefixWord, tailWord_3986504, baseEnd_3986504] using wordTrace_append hprefix tailTrace_3986504
  have hstable : (prefixWord ++ tailWord_3986504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986504).length < 2 ^ (prefixWord ++ tailWord_3986504).sum := by decide
  have hdescent : baseEnd_3986504 < baseStart_3986504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986506 : List Nat := [3, 1, 2, 1, 1, 2, 3, 2, 4, 3]
def baseStart_3986506 : Nat := 118140960795 + 3986506 * 2 ^ 59
def prefixEnd_3986506 : Nat := 4983230072969 + 3 ^ 40 * 3986506 * 2
def baseEnd_3986506 : Nat := 1364662473355123340427599

theorem tailTrace_3986506 : CollatzResearch.WordTrace tailWord_3986506 prefixEnd_3986506 1364662473355123340427599 := by
  unfold tailWord_3986506
  simp only [CollatzResearch.WordTrace]
  refine ⟨36349954723894269466346843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96933212597051385243591581 36349954723894269466346843)
  ·
    refine ⟨54524932085841404199520265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36349954723894269466346843 54524932085841404199520265)
    ·
      refine ⟨40893699064381053149640199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54524932085841404199520265 40893699064381053149640199)
      ·
        refine ⟨61340548596571579724460299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40893699064381053149640199 61340548596571579724460299)
        ·
          refine ⟨92010822894857369586690449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61340548596571579724460299 92010822894857369586690449)
          ·
            refine ⟨69008117171143027190017837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92010822894857369586690449 69008117171143027190017837)
            ·
              refine ⟨25878043939178635196256689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69008117171143027190017837 25878043939178635196256689)
              ·
                refine ⟨19408532954383976397192517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25878043939178635196256689 19408532954383976397192517)
                ·
                  refine ⟨3639099928946995574473597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19408532954383976397192517 3639099928946995574473597)
                  ·
                    refine ⟨1364662473355123340427599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3639099928946995574473597 1364662473355123340427599)
                    ·
                      rfl

theorem cell22_3986506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 4, 3].length) (baseStart_3986506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3986506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3986506 prefixEnd_3986506 := by exact prefixLift 3986506
  have htrace : WordTrace (prefixWord ++ tailWord_3986506) baseStart_3986506 baseEnd_3986506 := by
    simpa [prefixWord, tailWord_3986506, baseEnd_3986506] using wordTrace_append hprefix tailTrace_3986506
  have hstable : (prefixWord ++ tailWord_3986506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986506).length < 2 ^ (prefixWord ++ tailWord_3986506).sum := by decide
  have hdescent : baseEnd_3986506 < baseStart_3986506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986525 : List Nat := [1, 4, 4, 1, 2, 2, 1, 1, 6]
def baseStart_3986525 : Nat := 118140960795 + 3986525 * 2 ^ 59
def prefixEnd_3986525 : Nat := 4983230072969 + 3 ^ 40 * 3986525 * 2
def baseEnd_3986525 : Nat := 454889659147804541400847

theorem tailTrace_3986525 : CollatzResearch.WordTrace tailWord_3986525 prefixEnd_3986525 454889659147804541400847 := by
  unfold tailWord_3986525
  simp only [CollatzResearch.WordTrace]
  refine ⟨145400511882508244110329029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96933674588338829406886019 145400511882508244110329029)
  ·
    refine ⟨27262595977970295770686693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145400511882508244110329029 27262595977970295770686693)
    ·
      refine ⟨5111736745869430457003755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27262595977970295770686693 5111736745869430457003755)
      ·
        refine ⟨7667605118804145685505633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5111736745869430457003755 7667605118804145685505633)
        ·
          refine ⟨5750703839103109264129225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7667605118804145685505633 5750703839103109264129225)
          ·
            refine ⟨4313027879327331948096919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5750703839103109264129225 4313027879327331948096919)
            ·
              refine ⟨6469541818990997922145379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4313027879327331948096919 6469541818990997922145379)
              ·
                refine ⟨9704312728486496883218069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6469541818990997922145379 9704312728486496883218069)
                ·
                  refine ⟨454889659147804541400847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9704312728486496883218069 454889659147804541400847)
                  ·
                    rfl

theorem cell22_3986525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 1, 6].length) (baseStart_3986525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3986525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3986525 prefixEnd_3986525 := by exact prefixLift 3986525
  have htrace : WordTrace (prefixWord ++ tailWord_3986525) baseStart_3986525 baseEnd_3986525 := by
    simpa [prefixWord, tailWord_3986525, baseEnd_3986525] using wordTrace_append hprefix tailTrace_3986525
  have hstable : (prefixWord ++ tailWord_3986525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986525).length < 2 ^ (prefixWord ++ tailWord_3986525).sum := by decide
  have hdescent : baseEnd_3986525 < baseStart_3986525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986551 : List Nat := [1, 1, 3, 1, 1, 4, 2, 1, 5, 3]
def baseStart_3986551 : Nat := 118140960795 + 3986551 * 2 ^ 59
def prefixEnd_3986551 : Nat := 4983230072969 + 3 ^ 40 * 3986551 * 2
def baseEnd_3986551 : Nat := 1364677877774758223052461

theorem tailTrace_3986551 : CollatzResearch.WordTrace tailWord_3986551 prefixEnd_3986551 1364677877774758223052461 := by
  unfold tailWord_3986551
  simp only [CollatzResearch.WordTrace]
  refine ⟨145401460180414050550775507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96934306786942700367183671 145401460180414050550775507)
  ·
    refine ⟨218102190270621075826163261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145401460180414050550775507 218102190270621075826163261)
    ·
      refine ⟨81788321351482903434811223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218102190270621075826163261 81788321351482903434811223)
      ·
        refine ⟨122682482027224355152216835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81788321351482903434811223 122682482027224355152216835)
        ·
          refine ⟨184023723040836532728325253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122682482027224355152216835 184023723040836532728325253)
          ·
            refine ⟨34504448070156849886560985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 184023723040836532728325253 34504448070156849886560985)
            ·
              refine ⟨25878336052617637414920739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34504448070156849886560985 25878336052617637414920739)
              ·
                refine ⟨38817504078926456122381109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25878336052617637414920739 38817504078926456122381109)
                ·
                  refine ⟨3639141007399355261473229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38817504078926456122381109 3639141007399355261473229)
                  ·
                    refine ⟨1364677877774758223052461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3639141007399355261473229 1364677877774758223052461)
                    ·
                      rfl

theorem cell22_3986551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 5, 3].length) (baseStart_3986551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3986551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3986551 prefixEnd_3986551 := by exact prefixLift 3986551
  have htrace : WordTrace (prefixWord ++ tailWord_3986551) baseStart_3986551 baseEnd_3986551 := by
    simpa [prefixWord, tailWord_3986551, baseEnd_3986551] using wordTrace_append hprefix tailTrace_3986551
  have hstable : (prefixWord ++ tailWord_3986551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986551).length < 2 ^ (prefixWord ++ tailWord_3986551).sum := by decide
  have hdescent : baseEnd_3986551 < baseStart_3986551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986596 : List Nat := [2, 3, 1, 2, 3, 1, 1, 1, 1, 7]
def baseStart_3986596 : Nat := 118140960795 + 3986596 * 2 ^ 59
def prefixEnd_3986596 : Nat := 4983230072969 + 3 ^ 40 * 3986596 * 2
def baseEnd_3986596 : Nat := 1364693282194393105677323

theorem tailTrace_3986596 : CollatzResearch.WordTrace tailWord_3986596 prefixEnd_3986596 1364693282194393105677323 := by
  unfold tailWord_3986596
  simp only [CollatzResearch.WordTrace]
  refine ⟨72701550732625511618081821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96935400976834015490775761 72701550732625511618081821)
  ·
    refine ⟨27263081524734566856780683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72701550732625511618081821 27263081524734566856780683)
    ·
      refine ⟨40894622287101850285171025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27263081524734566856780683 40894622287101850285171025)
      ·
        refine ⟨30670966715326387713878269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40894622287101850285171025 30670966715326387713878269)
        ·
          refine ⟨11501612518247395392704351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30670966715326387713878269 11501612518247395392704351)
          ·
            refine ⟨17252418777371093089056527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11501612518247395392704351 17252418777371093089056527)
            ·
              refine ⟨25878628166056639633584791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17252418777371093089056527 25878628166056639633584791)
              ·
                refine ⟨38817942249084959450377187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25878628166056639633584791 38817942249084959450377187)
                ·
                  refine ⟨58226913373627439175565781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38817942249084959450377187 58226913373627439175565781)
                  ·
                    refine ⟨1364693282194393105677323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58226913373627439175565781 1364693282194393105677323)
                    ·
                      rfl

theorem cell22_3986596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 1, 7].length) (baseStart_3986596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3986596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3986596 prefixEnd_3986596 := by exact prefixLift 3986596
  have htrace : WordTrace (prefixWord ++ tailWord_3986596) baseStart_3986596 baseEnd_3986596 := by
    simpa [prefixWord, tailWord_3986596, baseEnd_3986596] using wordTrace_append hprefix tailTrace_3986596
  have hstable : (prefixWord ++ tailWord_3986596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986596).length < 2 ^ (prefixWord ++ tailWord_3986596).sum := by decide
  have hdescent : baseEnd_3986596 < baseStart_3986596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986611 : List Nat := [1, 1, 1, 2, 3, 2, 4, 1, 3, 4]
def baseStart_3986611 : Nat := 118140960795 + 3986611 * 2 ^ 59
def prefixEnd_3986611 : Nat := 4983230072969 + 3 ^ 40 * 3986611 * 2
def baseEnd_3986611 : Nat := 1364698417000938066552277

theorem tailTrace_3986611 : CollatzResearch.WordTrace tailWord_3986611 prefixEnd_3986611 1364698417000938066552277 := by
  unfold tailWord_3986611
  simp only [CollatzResearch.WordTrace]
  refine ⟨145403648560196680797959687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96935765706797787198639791 145403648560196680797959687)
  ·
    refine ⟨218105472840295021196939531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145403648560196680797959687 218105472840295021196939531)
    ·
      refine ⟨327158209260442531795409297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218105472840295021196939531 327158209260442531795409297)
      ·
        refine ⟨245368656945331898846556973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327158209260442531795409297 245368656945331898846556973)
        ·
          refine ⟨92013246354499462067458865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 245368656945331898846556973 92013246354499462067458865)
          ·
            refine ⟨69009934765874596550594149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92013246354499462067458865 69009934765874596550594149)
            ·
              refine ⟨12939362768601486853236403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69009934765874596550594149 12939362768601486853236403)
              ·
                refine ⟨19409044152902230279854605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12939362768601486853236403 19409044152902230279854605)
                ·
                  refine ⟨7278391557338336354945477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19409044152902230279854605 7278391557338336354945477)
                  ·
                    refine ⟨1364698417000938066552277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7278391557338336354945477 1364698417000938066552277)
                    ·
                      rfl

theorem cell22_3986611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 3, 4].length) (baseStart_3986611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3986611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3986611 prefixEnd_3986611 := by exact prefixLift 3986611
  have htrace : WordTrace (prefixWord ++ tailWord_3986611) baseStart_3986611 baseEnd_3986611 := by
    simpa [prefixWord, tailWord_3986611, baseEnd_3986611] using wordTrace_append hprefix tailTrace_3986611
  have hstable : (prefixWord ++ tailWord_3986611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986611).length < 2 ^ (prefixWord ++ tailWord_3986611).sum := by decide
  have hdescent : baseEnd_3986611 < baseStart_3986611 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986656 : List Nat := [2, 1, 1, 3, 1, 4, 1, 2, 1, 6]
def baseStart_3986656 : Nat := 118140960795 + 3986656 * 2 ^ 59
def prefixEnd_3986656 : Nat := 4983230072969 + 3 ^ 40 * 3986656 * 2
def baseEnd_3986656 : Nat := 1364713821420572949177139

theorem tailTrace_3986656 : CollatzResearch.WordTrace tailWord_3986656 prefixEnd_3986656 1364713821420572949177139 := by
  unfold tailWord_3986656
  simp only [CollatzResearch.WordTrace]
  refine ⟨72702644922516826741673911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96936859896689102322231881 72702644922516826741673911)
  ·
    refine ⟨109053967383775240112510867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72702644922516826741673911 109053967383775240112510867)
    ·
      refine ⟨163580951075662860168766301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109053967383775240112510867 163580951075662860168766301)
      ·
        refine ⟨61342856653373572563287363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163580951075662860168766301 61342856653373572563287363)
        ·
          refine ⟨92014284980060358844931045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61342856653373572563287363 92014284980060358844931045)
          ·
            refine ⟨17252678433761317283424571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92014284980060358844931045 17252678433761317283424571)
            ·
              refine ⟨25879017650641975925136857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17252678433761317283424571 25879017650641975925136857)
              ·
                refine ⟨19409263237981481943852643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25879017650641975925136857 19409263237981481943852643)
                ·
                  refine ⟨29113894856972222915778965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19409263237981481943852643 29113894856972222915778965)
                  ·
                    refine ⟨1364713821420572949177139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29113894856972222915778965 1364713821420572949177139)
                    ·
                      rfl

theorem cell22_3986656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 1, 6].length) (baseStart_3986656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3986656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3986656 prefixEnd_3986656 := by exact prefixLift 3986656
  have htrace : WordTrace (prefixWord ++ tailWord_3986656) baseStart_3986656 baseEnd_3986656 := by
    simpa [prefixWord, tailWord_3986656, baseEnd_3986656] using wordTrace_append hprefix tailTrace_3986656
  have hstable : (prefixWord ++ tailWord_3986656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986656).length < 2 ^ (prefixWord ++ tailWord_3986656).sum := by decide
  have hdescent : baseEnd_3986656 < baseStart_3986656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986750 : List Nat := [4, 2, 1, 2, 1, 1, 4, 2, 5]
def baseStart_3986750 : Nat := 118140960795 + 3986750 * 2 ^ 59
def prefixEnd_3986750 : Nat := 4983230072969 + 3 ^ 40 * 3986750 * 2
def baseEnd_3986750 : Nat := 454915333180529345775617

theorem tailTrace_3986750 : CollatzResearch.WordTrace tailWord_3986750 prefixEnd_3986750 454915333180529345775617 := by
  unfold tailWord_3986750
  simp only [CollatzResearch.WordTrace]
  refine ⟨18176089788336638442158713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96939145537795405024846469 18176089788336638442158713)
  ·
    refine ⟨13632067341252478831619035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18176089788336638442158713 13632067341252478831619035)
    ·
      refine ⟨20448101011878718247428553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13632067341252478831619035 20448101011878718247428553)
      ·
        refine ⟨15336075758909038685571415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20448101011878718247428553 15336075758909038685571415)
        ·
          refine ⟨23004113638363558028357123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15336075758909038685571415 23004113638363558028357123)
          ·
            refine ⟨34506170457545337042535685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23004113638363558028357123 34506170457545337042535685)
            ·
              refine ⟨6469906960789750695475441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34506170457545337042535685 6469906960789750695475441)
              ·
                refine ⟨4852430220592313021606581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6469906960789750695475441 4852430220592313021606581)
                ·
                  refine ⟨454915333180529345775617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4852430220592313021606581 454915333180529345775617)
                  ·
                    rfl

theorem cell22_3986750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 2, 5].length) (baseStart_3986750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3986750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3986750 prefixEnd_3986750 := by exact prefixLift 3986750
  have htrace : WordTrace (prefixWord ++ tailWord_3986750) baseStart_3986750 baseEnd_3986750 := by
    simpa [prefixWord, tailWord_3986750, baseEnd_3986750] using wordTrace_append hprefix tailTrace_3986750
  have hstable : (prefixWord ++ tailWord_3986750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986750).length < 2 ^ (prefixWord ++ tailWord_3986750).sum := by decide
  have hdescent : baseEnd_3986750 < baseStart_3986750 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986797 : List Nat := [1, 5, 1, 1, 1, 3, 4, 1, 1, 4]
def baseStart_3986797 : Nat := 118140960795 + 3986797 * 2 ^ 59
def prefixEnd_3986797 : Nat := 4983230072969 + 3 ^ 40 * 3986797 * 2
def baseEnd_3986797 : Nat := 1364762088602095581401707

theorem tailTrace_3986797 : CollatzResearch.WordTrace tailWord_3986797 prefixEnd_3986797 1364762088602095581401707 := by
  unfold tailWord_3986797
  simp only [CollatzResearch.WordTrace]
  refine ⟨145410432537522834564230645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96940288358348556376153763 145410432537522834564230645)
  ·
    refine ⟨13632228050392765740396623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 145410432537522834564230645 13632228050392765740396623)
    ·
      refine ⟨20448342075589148610594935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13632228050392765740396623 20448342075589148610594935)
      ·
        refine ⟨30672513113383722915892403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20448342075589148610594935 30672513113383722915892403)
        ·
          refine ⟨46008769670075584373838605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30672513113383722915892403 46008769670075584373838605)
          ·
            refine ⟨17253288626278344140189477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46008769670075584373838605 17253288626278344140189477)
            ·
              refine ⟨3234991617427189526285527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17253288626278344140189477 3234991617427189526285527)
              ·
                refine ⟨4852487426140784289428291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3234991617427189526285527 4852487426140784289428291)
                ·
                  refine ⟨7278731139211176434142437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4852487426140784289428291 7278731139211176434142437)
                  ·
                    refine ⟨1364762088602095581401707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7278731139211176434142437 1364762088602095581401707)
                    ·
                      rfl

theorem cell22_3986797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 4, 1, 1, 4].length) (baseStart_3986797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3986797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3986797 prefixEnd_3986797 := by exact prefixLift 3986797
  have htrace : WordTrace (prefixWord ++ tailWord_3986797) baseStart_3986797 baseEnd_3986797 := by
    simpa [prefixWord, tailWord_3986797, baseEnd_3986797] using wordTrace_append hprefix tailTrace_3986797
  have hstable : (prefixWord ++ tailWord_3986797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986797).length < 2 ^ (prefixWord ++ tailWord_3986797).sum := by decide
  have hdescent : baseEnd_3986797 < baseStart_3986797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986827 : List Nat := [1, 1, 1, 1, 4, 3, 5, 1, 2, 3]
def baseStart_3986827 : Nat := 118140960795 + 3986827 * 2 ^ 59
def prefixEnd_3986827 : Nat := 4983230072969 + 3 ^ 40 * 3986827 * 2
def baseEnd_3986827 : Nat := 1364772358215185503151615

theorem tailTrace_3986827 : CollatzResearch.WordTrace tailWord_3986827 prefixEnd_3986827 1364772358215185503151615 := by
  unfold tailWord_3986827
  simp only [CollatzResearch.WordTrace]
  refine ⟨145411526727414149687822735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96941017818276099791881823 145411526727414149687822735)
  ·
    refine ⟨218117290091121224531734103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145411526727414149687822735 218117290091121224531734103)
    ·
      refine ⟨327175935136681836797601155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218117290091121224531734103 327175935136681836797601155)
      ·
        refine ⟨490763902705022755196401733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327175935136681836797601155 490763902705022755196401733)
        ·
          refine ⟨92018231757191766599325325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 490763902705022755196401733 92018231757191766599325325)
          ·
            refine ⟨34506836908946912474746997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92018231757191766599325325 34506836908946912474746997)
            ·
              refine ⟨3235015960213773044507531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34506836908946912474746997 3235015960213773044507531)
              ·
                refine ⟨4852523940320659566761297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3235015960213773044507531 4852523940320659566761297)
                ·
                  refine ⟨3639392955240494675070973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4852523940320659566761297 3639392955240494675070973)
                  ·
                    refine ⟨1364772358215185503151615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3639392955240494675070973 1364772358215185503151615)
                    ·
                      rfl

theorem cell22_3986827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 5, 1, 2, 3].length) (baseStart_3986827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3986827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3986827 prefixEnd_3986827 := by exact prefixLift 3986827
  have htrace : WordTrace (prefixWord ++ tailWord_3986827) baseStart_3986827 baseEnd_3986827 := by
    simpa [prefixWord, tailWord_3986827, baseEnd_3986827] using wordTrace_append hprefix tailTrace_3986827
  have hstable : (prefixWord ++ tailWord_3986827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986827).length < 2 ^ (prefixWord ++ tailWord_3986827).sum := by decide
  have hdescent : baseEnd_3986827 < baseStart_3986827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986840 : List Nat := [2, 1, 2, 5, 2, 1, 1, 8]
def baseStart_3986840 : Nat := 118140960795 + 3986840 * 2 ^ 59
def prefixEnd_3986840 : Nat := 4983230072969 + 3 ^ 40 * 3986840 * 2
def baseEnd_3986840 : Nat := 151641867597873089175175

theorem tailTrace_3986840 : CollatzResearch.WordTrace tailWord_3986840 prefixEnd_3986840 151641867597873089175175 := by
  unfold tailWord_3986840
  simp only [CollatzResearch.WordTrace]
  refine ⟨72706000438183526454022987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96941333917578035272030649 72706000438183526454022987)
  ·
    refine ⟨109059000657275289681034481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72706000438183526454022987 109059000657275289681034481)
    ·
      refine ⟨81794250492956467260775861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109059000657275289681034481 81794250492956467260775861)
      ·
        refine ⟨7668210983714668805697737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81794250492956467260775861 7668210983714668805697737)
        ·
          refine ⟨5751158237786001604273303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7668210983714668805697737 5751158237786001604273303)
          ·
            refine ⟨8626737356679002406409955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5751158237786001604273303 8626737356679002406409955)
            ·
              refine ⟨12940106035018503609614933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8626737356679002406409955 12940106035018503609614933)
              ·
                refine ⟨151641867597873089175175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12940106035018503609614933 151641867597873089175175)
                ·
                  rfl

theorem cell22_3986840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 8].length) (baseStart_3986840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3986840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3986840 prefixEnd_3986840 := by exact prefixLift 3986840
  have htrace : WordTrace (prefixWord ++ tailWord_3986840) baseStart_3986840 baseEnd_3986840 := by
    simpa [prefixWord, tailWord_3986840, baseEnd_3986840] using wordTrace_append hprefix tailTrace_3986840
  have hstable : (prefixWord ++ tailWord_3986840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986840).length < 2 ^ (prefixWord ++ tailWord_3986840).sum := by decide
  have hdescent : baseEnd_3986840 < baseStart_3986840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986846 : List Nat := [4, 3, 1, 2, 2, 2, 1, 3, 4]
def baseStart_3986846 : Nat := 118140960795 + 3986846 * 2 ^ 59
def prefixEnd_3986846 : Nat := 4983230072969 + 3 ^ 40 * 3986846 * 2
def baseEnd_3986846 : Nat := 454926287434491928975519

theorem tailTrace_3986846 : CollatzResearch.WordTrace tailWord_3986846 prefixEnd_3986846 454926287434491928975519 := by
  unfold tailWord_3986846
  simp only [CollatzResearch.WordTrace]
  refine ⟨18176527464293164491595549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96941479809563543955176261 18176527464293164491595549)
  ·
    refine ⟨6816197799109936684348331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18176527464293164491595549 6816197799109936684348331)
    ·
      refine ⟨10224296698664905026522497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6816197799109936684348331 10224296698664905026522497)
      ·
        refine ⟨7668222523998678769891873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10224296698664905026522497 7668222523998678769891873)
        ·
          refine ⟨5751166892999009077418905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7668222523998678769891873 5751166892999009077418905)
          ·
            refine ⟨4313375169749256808064179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5751166892999009077418905 4313375169749256808064179)
            ·
              refine ⟨6470062754623885212096269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4313375169749256808064179 6470062754623885212096269)
              ·
                refine ⟨2426273532983956954536101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6470062754623885212096269 2426273532983956954536101)
                ·
                  refine ⟨454926287434491928975519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2426273532983956954536101 454926287434491928975519)
                  ·
                    rfl

theorem cell22_3986846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_3986846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3986846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3986846 prefixEnd_3986846 := by exact prefixLift 3986846
  have htrace : WordTrace (prefixWord ++ tailWord_3986846) baseStart_3986846 baseEnd_3986846 := by
    simpa [prefixWord, tailWord_3986846, baseEnd_3986846] using wordTrace_append hprefix tailTrace_3986846
  have hstable : (prefixWord ++ tailWord_3986846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986846).length < 2 ^ (prefixWord ++ tailWord_3986846).sum := by decide
  have hdescent : baseEnd_3986846 < baseStart_3986846 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986872 : List Nat := [2, 1, 2, 1, 2, 2, 2, 6, 1, 3]
def baseStart_3986872 : Nat := 118140960795 + 3986872 * 2 ^ 59
def prefixEnd_3986872 : Nat := 4983230072969 + 3 ^ 40 * 3986872 * 2
def baseEnd_3986872 : Nat := 1364787762634820385776477

theorem tailTrace_3986872 : CollatzResearch.WordTrace tailWord_3986872 prefixEnd_3986872 1364787762634820385776477 := by
  unfold tailWord_3986872
  simp only [CollatzResearch.WordTrace]
  refine ⟨72706584006125561186605435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96942112008167414915473913 72706584006125561186605435)
  ·
    refine ⟨109059876009188341779908153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72706584006125561186605435 109059876009188341779908153)
    ·
      refine ⟨81794907006891256334931115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109059876009188341779908153 81794907006891256334931115)
      ·
        refine ⟨122692360510336884502396673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81794907006891256334931115 122692360510336884502396673)
        ·
          refine ⟨92019270382752663376797505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122692360510336884502396673 92019270382752663376797505)
          ·
            refine ⟨69014452787064497532598129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92019270382752663376797505 69014452787064497532598129)
            ·
              refine ⟨51760839590298373149448597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69014452787064497532598129 51760839590298373149448597)
              ·
                refine ⟨2426289355795236241380403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 51760839590298373149448597 2426289355795236241380403)
                ·
                  refine ⟨3639434033692854362070605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2426289355795236241380403 3639434033692854362070605)
                  ·
                    refine ⟨1364787762634820385776477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3639434033692854362070605 1364787762634820385776477)
                    ·
                      rfl

theorem cell22_3986872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 6, 1, 3].length) (baseStart_3986872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3986872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3986872 prefixEnd_3986872 := by exact prefixLift 3986872
  have htrace : WordTrace (prefixWord ++ tailWord_3986872) baseStart_3986872 baseEnd_3986872 := by
    simpa [prefixWord, tailWord_3986872, baseEnd_3986872] using wordTrace_append hprefix tailTrace_3986872
  have hstable : (prefixWord ++ tailWord_3986872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986872).length < 2 ^ (prefixWord ++ tailWord_3986872).sum := by decide
  have hdescent : baseEnd_3986872 < baseStart_3986872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986883 : List Nat := [1, 1, 1, 3, 1, 1, 4, 3, 2, 5]
def baseStart_3986883 : Nat := 118140960795 + 3986883 * 2 ^ 59
def prefixEnd_3986883 : Nat := 4983230072969 + 3 ^ 40 * 3986883 * 2
def baseEnd_3986883 : Nat := 1364791528159620023751443

theorem tailTrace_3986883 : CollatzResearch.WordTrace tailWord_3986883 prefixEnd_3986883 1364791528159620023751443 := by
  unfold tailWord_3986883
  simp only [CollatzResearch.WordTrace]
  refine ⟨145413569215211271251861303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96942379476807514167907535 145413569215211271251861303)
  ·
    refine ⟨218120353822816906877791955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145413569215211271251861303 218120353822816906877791955)
    ·
      refine ⟨327180530734225360316687933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218120353822816906877791955 327180530734225360316687933)
      ·
        refine ⟨122692699025334510118757975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 327180530734225360316687933 122692699025334510118757975)
        ·
          refine ⟨184039048538001765178136963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122692699025334510118757975 184039048538001765178136963)
          ·
            refine ⟨276058572807002647767205445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184039048538001765178136963 276058572807002647767205445)
            ·
              refine ⟨51760982401312996456351021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 276058572807002647767205445 51760982401312996456351021)
              ·
                refine ⟨19410368400492373671131633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51760982401312996456351021 19410368400492373671131633)
                ·
                  refine ⟨14557776300369280253348725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19410368400492373671131633 14557776300369280253348725)
                  ·
                    refine ⟨1364791528159620023751443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14557776300369280253348725 1364791528159620023751443)
                    ·
                      rfl

theorem cell22_3986883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 2, 5].length) (baseStart_3986883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3986883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3986883 prefixEnd_3986883 := by exact prefixLift 3986883
  have htrace : WordTrace (prefixWord ++ tailWord_3986883) baseStart_3986883 baseEnd_3986883 := by
    simpa [prefixWord, tailWord_3986883, baseEnd_3986883] using wordTrace_append hprefix tailTrace_3986883
  have hstable : (prefixWord ++ tailWord_3986883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986883).length < 2 ^ (prefixWord ++ tailWord_3986883).sum := by decide
  have hdescent : baseEnd_3986883 < baseStart_3986883 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987007 : List Nat := [1, 1, 2, 2, 3, 3, 2, 2, 3, 3]
def baseStart_3987007 : Nat := 118140960795 + 3987007 * 2 ^ 59
def prefixEnd_3987007 : Nat := 4983230072969 + 3 ^ 40 * 3987007 * 2
def baseEnd_3987007 : Nat := 1364833975893725033651063

theorem tailTrace_3987007 : CollatzResearch.WordTrace tailWord_3987007 prefixEnd_3987007 1364833975893725033651063 := by
  unfold tailWord_3987007
  simp only [CollatzResearch.WordTrace]
  refine ⟨145418091866762040429375275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96945394577841360286250183 145418091866762040429375275)
  ·
    refine ⟨218127137800143060644062913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145418091866762040429375275 218127137800143060644062913)
    ·
      refine ⟨163595353350107295483047185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218127137800143060644062913 163595353350107295483047185)
      ·
        refine ⟨122696515012580471612285389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163595353350107295483047185 122696515012580471612285389)
        ·
          refine ⟨46011193129717676854607021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122696515012580471612285389 46011193129717676854607021)
          ·
            refine ⟨17254197423644128820477633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46011193129717676854607021 17254197423644128820477633)
            ·
              refine ⟨12940648067733096615358225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17254197423644128820477633 12940648067733096615358225)
              ·
                refine ⟨9705486050799822461518669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12940648067733096615358225 9705486050799822461518669)
                ·
                  refine ⟨3639557269049933423069501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9705486050799822461518669 3639557269049933423069501)
                  ·
                    refine ⟨1364833975893725033651063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3639557269049933423069501 1364833975893725033651063)
                    ·
                      rfl

theorem cell22_3987007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 2, 3, 3].length) (baseStart_3987007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3987007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3987007 prefixEnd_3987007 := by exact prefixLift 3987007
  have htrace : WordTrace (prefixWord ++ tailWord_3987007) baseStart_3987007 baseEnd_3987007 := by
    simpa [prefixWord, tailWord_3987007, baseEnd_3987007] using wordTrace_append hprefix tailTrace_3987007
  have hstable : (prefixWord ++ tailWord_3987007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987007).length < 2 ^ (prefixWord ++ tailWord_3987007).sum := by decide
  have hdescent : baseEnd_3987007 < baseStart_3987007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987020 : List Nat := [2, 2, 1, 3, 1, 3, 1, 2, 7]
def baseStart_3987020 : Nat := 118140960795 + 3987020 * 2 ^ 59
def prefixEnd_3987020 : Nat := 4983230072969 + 3 ^ 40 * 3987020 * 2
def baseEnd_3987020 : Nat := 454946142019799111025341

theorem tailTrace_3987020 : CollatzResearch.WordTrace tailWord_3987020 prefixEnd_3987020 454946142019799111025341 := by
  unfold tailWord_3987020
  simp only [CollatzResearch.WordTrace]
  refine ⟨72709283007857471824799257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96945710677143295766399009 72709283007857471824799257)
  ·
    refine ⟨54531962255893103868599443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72709283007857471824799257 54531962255893103868599443)
    ·
      refine ⟨81797943383839655802899165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54531962255893103868599443 81797943383839655802899165)
      ·
        refine ⟨30674228768939870926087187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81797943383839655802899165 30674228768939870926087187)
        ·
          refine ⟨46011343153409806389130781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30674228768939870926087187 46011343153409806389130781)
          ·
            refine ⟨17254253682528677395924043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46011343153409806389130781 17254253682528677395924043)
            ·
              refine ⟨25881380523793016093886065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17254253682528677395924043 25881380523793016093886065)
              ·
                refine ⟨19411035392844762070414549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25881380523793016093886065 19411035392844762070414549)
                ·
                  refine ⟨454946142019799111025341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19411035392844762070414549 454946142019799111025341)
                  ·
                    rfl

theorem cell22_3987020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 7].length) (baseStart_3987020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3987020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3987020 prefixEnd_3987020 := by exact prefixLift 3987020
  have htrace : WordTrace (prefixWord ++ tailWord_3987020) baseStart_3987020 baseEnd_3987020 := by
    simpa [prefixWord, tailWord_3987020, baseEnd_3987020] using wordTrace_append hprefix tailTrace_3987020
  have hstable : (prefixWord ++ tailWord_3987020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987020).length < 2 ^ (prefixWord ++ tailWord_3987020).sum := by decide
  have hdescent : baseEnd_3987020 < baseStart_3987020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987041 : List Nat := [1, 2, 3, 1, 1, 3, 5, 2, 1, 3]
def baseStart_3987041 : Nat := 118140960795 + 3987041 * 2 ^ 59
def prefixEnd_3987041 : Nat := 4983230072969 + 3 ^ 40 * 3987041 * 2
def baseEnd_3987041 : Nat := 1364845614788560278300959

theorem tailTrace_3987041 : CollatzResearch.WordTrace tailWord_3987041 prefixEnd_3987041 1364845614788560278300959 := by
  unfold tailWord_3987041
  simp only [CollatzResearch.WordTrace]
  refine ⟨145419331948638864236112977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96946221299092576157408651 145419331948638864236112977)
  ·
    refine ⟨109064498961479148177084733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145419331948638864236112977 109064498961479148177084733)
    ·
      refine ⟨40899187110554680566406775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109064498961479148177084733 40899187110554680566406775)
      ·
        refine ⟨61348780665832020849610163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40899187110554680566406775 61348780665832020849610163)
        ·
          refine ⟨92023170998748031274415245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61348780665832020849610163 92023170998748031274415245)
          ·
            refine ⟨34508689124530511727905717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92023170998748031274415245 34508689124530511727905717)
            ·
              refine ⟨3235189605424735474491161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34508689124530511727905717 3235189605424735474491161)
              ·
                refine ⟨2426392204068551605868371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3235189605424735474491161 2426392204068551605868371)
                ·
                  refine ⟨3639588306102827408802557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2426392204068551605868371 3639588306102827408802557)
                  ·
                    refine ⟨1364845614788560278300959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3639588306102827408802557 1364845614788560278300959)
                    ·
                      rfl

theorem cell22_3987041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 5, 2, 1, 3].length) (baseStart_3987041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3987041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3987041 prefixEnd_3987041 := by exact prefixLift 3987041
  have htrace : WordTrace (prefixWord ++ tailWord_3987041) baseStart_3987041 baseEnd_3987041 := by
    simpa [prefixWord, tailWord_3987041, baseEnd_3987041] using wordTrace_append hprefix tailTrace_3987041
  have hstable : (prefixWord ++ tailWord_3987041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987041).length < 2 ^ (prefixWord ++ tailWord_3987041).sum := by decide
  have hdescent : baseEnd_3987041 < baseStart_3987041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987054 : List Nat := [4, 1, 2, 2, 3, 1, 1, 3, 5]
def baseStart_3987054 : Nat := 118140960795 + 3987054 * 2 ^ 59
def prefixEnd_3987054 : Nat := 4983230072969 + 3 ^ 40 * 3987054 * 2
def baseEnd_3987054 : Nat := 454950021651410859241973

theorem tailTrace_3987054 : CollatzResearch.WordTrace tailWord_3987054 prefixEnd_3987054 454950021651410859241973 := by
  unfold tailWord_3987054
  simp only [CollatzResearch.WordTrace]
  refine ⟨18177475762198970932042027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96946537398394511637557477 18177475762198970932042027)
  ·
    refine ⟨27266213643298456398063041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18177475762198970932042027 27266213643298456398063041)
    ·
      refine ⟨20449660232473842298547281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27266213643298456398063041 20449660232473842298547281)
      ·
        refine ⟨15337245174355381723910461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20449660232473842298547281 15337245174355381723910461)
        ·
          refine ⟨5751466940383268146466423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15337245174355381723910461 5751466940383268146466423)
          ·
            refine ⟨8627200410574902219699635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5751466940383268146466423 8627200410574902219699635)
            ·
              refine ⟨12940800615862353329549453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8627200410574902219699635 12940800615862353329549453)
              ·
                refine ⟨4852800230948382498581045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12940800615862353329549453 4852800230948382498581045)
                ·
                  refine ⟨454950021651410859241973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4852800230948382498581045 454950021651410859241973)
                  ·
                    rfl

theorem cell22_3987054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 3, 5].length) (baseStart_3987054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3987054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3987054 prefixEnd_3987054 := by exact prefixLift 3987054
  have htrace : WordTrace (prefixWord ++ tailWord_3987054) baseStart_3987054 baseEnd_3987054 := by
    simpa [prefixWord, tailWord_3987054, baseEnd_3987054] using wordTrace_append hprefix tailTrace_3987054
  have hstable : (prefixWord ++ tailWord_3987054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987054).length < 2 ^ (prefixWord ++ tailWord_3987054).sum := by decide
  have hdescent : baseEnd_3987054 < baseStart_3987054 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987065 : List Nat := [1, 2, 1, 3, 3, 1, 2, 1, 8]
def baseStart_3987065 : Nat := 118140960795 + 3987065 * 2 ^ 59
def prefixEnd_3987065 : Nat := 4983230072969 + 3 ^ 40 * 3987065 * 2
def baseEnd_3987065 : Nat := 454951276826344071900295

theorem tailTrace_3987065 : CollatzResearch.WordTrace tailWord_3987065 prefixEnd_3987065 454951276826344071900295 := by
  unfold tailWord_3987065
  simp only [CollatzResearch.WordTrace]
  refine ⟨145420207300551916334986649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96946804867034610889991099 145420207300551916334986649)
  ·
    refine ⟨109065155475413937251239987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145420207300551916334986649 109065155475413937251239987)
    ·
      refine ⟨163597733213120905876859981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109065155475413937251239987 163597733213120905876859981)
      ·
        refine ⟨61349149954920339703822493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163597733213120905876859981 61349149954920339703822493)
        ·
          refine ⟨23005931233095127388933435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61349149954920339703822493 23005931233095127388933435)
          ·
            refine ⟨34508896849642691083400153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23005931233095127388933435 34508896849642691083400153)
            ·
              refine ⟨25881672637232018312550115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34508896849642691083400153 25881672637232018312550115)
              ·
                refine ⟨38822508955848027468825173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25881672637232018312550115 38822508955848027468825173)
                ·
                  refine ⟨454951276826344071900295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38822508955848027468825173 454951276826344071900295)
                  ·
                    rfl

theorem cell22_3987065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 8].length) (baseStart_3987065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3987065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3987065 prefixEnd_3987065 := by exact prefixLift 3987065
  have htrace : WordTrace (prefixWord ++ tailWord_3987065) baseStart_3987065 baseEnd_3987065 := by
    simpa [prefixWord, tailWord_3987065, baseEnd_3987065] using wordTrace_append hprefix tailTrace_3987065
  have hstable : (prefixWord ++ tailWord_3987065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987065).length < 2 ^ (prefixWord ++ tailWord_3987065).sum := by decide
  have hdescent : baseEnd_3987065 < baseStart_3987065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987084 : List Nat := [2, 2, 1, 2, 1, 1, 7, 1, 1, 4]
def baseStart_3987084 : Nat := 118140960795 + 3987084 * 2 ^ 59
def prefixEnd_3987084 : Nat := 4983230072969 + 3 ^ 40 * 3987084 * 2
def baseEnd_3987084 : Nat := 1364860334567322499475827

theorem tailTrace_3987084 : CollatzResearch.WordTrace tailWord_3987084 prefixEnd_3987084 1364860334567322499475827 := by
  unfold tailWord_3987084
  simp only [CollatzResearch.WordTrace]
  refine ⟨72710450143741541289964153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96947266858322055053285537 72710450143741541289964153)
  ·
    refine ⟨54532837607806155967473115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72710450143741541289964153 54532837607806155967473115)
    ·
      refine ⟨81799256411709233951209673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54532837607806155967473115 81799256411709233951209673)
      ·
        refine ⟨61349442308781925463407255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81799256411709233951209673 61349442308781925463407255)
        ·
          refine ⟨92024163463172888195110883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61349442308781925463407255 92024163463172888195110883)
          ·
            refine ⟨138036245194759332292666325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92024163463172888195110883 138036245194759332292666325)
            ·
              refine ⟨3235224496752171850609367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 138036245194759332292666325 3235224496752171850609367)
              ·
                refine ⟨4852836745128257775914051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3235224496752171850609367 4852836745128257775914051)
                ·
                  refine ⟨7279255117692386663871077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4852836745128257775914051 7279255117692386663871077)
                  ·
                    refine ⟨1364860334567322499475827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7279255117692386663871077 1364860334567322499475827)
                    ·
                      rfl

theorem cell22_3987084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 7, 1, 1, 4].length) (baseStart_3987084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3987084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3987084 prefixEnd_3987084 := by exact prefixLift 3987084
  have htrace : WordTrace (prefixWord ++ tailWord_3987084) baseStart_3987084 baseEnd_3987084 := by
    simpa [prefixWord, tailWord_3987084, baseEnd_3987084] using wordTrace_append hprefix tailTrace_3987084
  have hstable : (prefixWord ++ tailWord_3987084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987084).length < 2 ^ (prefixWord ++ tailWord_3987084).sum := by decide
  have hdescent : baseEnd_3987084 < baseStart_3987084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987092 : List Nat := [2, 4, 2, 2, 3, 1, 2, 2, 1, 3]
def baseStart_3987092 : Nat := 118140960795 + 3987092 * 2 ^ 59
def prefixEnd_3987092 : Nat := 4983230072969 + 3 ^ 40 * 3987092 * 2
def baseEnd_3987092 : Nat := 1364863073130813145275803

theorem tailTrace_3987092 : CollatzResearch.WordTrace tailWord_3987092 prefixEnd_3987092 1364863073130813145275803 := by
  unfold tailWord_3987092
  simp only [CollatzResearch.WordTrace]
  refine ⟨72710596035727049973109765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96947461380969399964146353 72710596035727049973109765)
  ·
    refine ⟨13633236756698821869958081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72710596035727049973109765 13633236756698821869958081)
    ·
      refine ⟨10224927567524116402468561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13633236756698821869958081 10224927567524116402468561)
      ·
        refine ⟨7668695675643087301851421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10224927567524116402468561 7668695675643087301851421)
        ·
          refine ⟨2875760878366157738194283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7668695675643087301851421 2875760878366157738194283)
          ·
            refine ⟨4313641317549236607291425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2875760878366157738194283 4313641317549236607291425)
            ·
              refine ⟨3235230988161927455468569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4313641317549236607291425 3235230988161927455468569)
              ·
                refine ⟨2426423241121445591601427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3235230988161927455468569 2426423241121445591601427)
                ·
                  refine ⟨3639634861682168387402141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2426423241121445591601427 3639634861682168387402141)
                  ·
                    refine ⟨1364863073130813145275803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3639634861682168387402141 1364863073130813145275803)
                    ·
                      rfl

theorem cell22_3987092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_3987092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3987092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3987092 prefixEnd_3987092 := by exact prefixLift 3987092
  have htrace : WordTrace (prefixWord ++ tailWord_3987092) baseStart_3987092 baseEnd_3987092 := by
    simpa [prefixWord, tailWord_3987092, baseEnd_3987092] using wordTrace_append hprefix tailTrace_3987092
  have hstable : (prefixWord ++ tailWord_3987092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987092).length < 2 ^ (prefixWord ++ tailWord_3987092).sum := by decide
  have hdescent : baseEnd_3987092 < baseStart_3987092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987148 : List Nat := [2, 2, 1, 5, 2, 2, 1, 2, 2, 3]
def baseStart_3987148 : Nat := 118140960795 + 3987148 * 2 ^ 59
def prefixEnd_3987148 : Nat := 4983230072969 + 3 ^ 40 * 3987148 * 2
def baseEnd_3987148 : Nat := 1364882243075247665875631

theorem tailTrace_3987148 : CollatzResearch.WordTrace tailWord_3987148 prefixEnd_3987148 1364882243075247665875631 := by
  unfold tailWord_3987148
  simp only [CollatzResearch.WordTrace]
  refine ⟨72711617279625610755129049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96948823039500814340172065 72711617279625610755129049)
  ·
    refine ⟨54533712959719208066346787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72711617279625610755129049 54533712959719208066346787)
    ·
      refine ⟨81800569439578812099520181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54533712959719208066346787 81800569439578812099520181)
      ·
        refine ⟨7668803384960513634330017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81800569439578812099520181 7668803384960513634330017)
        ·
          refine ⟨5751602538720385225747513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7668803384960513634330017 5751602538720385225747513)
          ·
            refine ⟨4313701904040288919310635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5751602538720385225747513 4313701904040288919310635)
            ·
              refine ⟨6470552856060433378965953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4313701904040288919310635 6470552856060433378965953)
              ·
                refine ⟨4852914642045325034224465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6470552856060433378965953 4852914642045325034224465)
                ·
                  refine ⟨3639685981533993775668349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4852914642045325034224465 3639685981533993775668349)
                  ·
                    refine ⟨1364882243075247665875631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3639685981533993775668349 1364882243075247665875631)
                    ·
                      rfl

theorem cell22_3987148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 2, 2, 3].length) (baseStart_3987148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3987148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3987148 prefixEnd_3987148 := by exact prefixLift 3987148
  have htrace : WordTrace (prefixWord ++ tailWord_3987148) baseStart_3987148 baseEnd_3987148 := by
    simpa [prefixWord, tailWord_3987148, baseEnd_3987148] using wordTrace_append hprefix tailTrace_3987148
  have hstable : (prefixWord ++ tailWord_3987148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987148).length < 2 ^ (prefixWord ++ tailWord_3987148).sum := by decide
  have hdescent : baseEnd_3987148 < baseStart_3987148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987159 : List Nat := [1, 1, 3, 2, 1, 3, 4, 1, 3, 3]
def baseStart_3987159 : Nat := 118140960795 + 3987159 * 2 ^ 59
def prefixEnd_3987159 : Nat := 4983230072969 + 3 ^ 40 * 3987159 * 2
def baseEnd_3987159 : Nat := 1364886008600047303850597

theorem tailTrace_3987159 : CollatzResearch.WordTrace tailWord_3987159 prefixEnd_3987159 1364886008600047303850597 := by
  unfold tailWord_3987159
  simp only [CollatzResearch.WordTrace]
  refine ⟨145423635762211370388908531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96949090508140913592605687 145423635762211370388908531)
  ·
    refine ⟨218135453643317055583362797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145423635762211370388908531 218135453643317055583362797)
    ·
      refine ⟨81800795116243895843761049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218135453643317055583362797 81800795116243895843761049)
      ·
        refine ⟨61350596337182921882820787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81800795116243895843761049 61350596337182921882820787)
        ·
          refine ⟨92025894505774382824231181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61350596337182921882820787 92025894505774382824231181)
          ·
            refine ⟨34509710439665393559086693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92025894505774382824231181 34509710439665393559086693)
            ·
              refine ⟨6470570707437261292328755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34509710439665393559086693 6470570707437261292328755)
              ·
                refine ⟨9705856061155891938493133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6470570707437261292328755 9705856061155891938493133)
                ·
                  refine ⟨3639696022933459476934925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9705856061155891938493133 3639696022933459476934925)
                  ·
                    refine ⟨1364886008600047303850597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3639696022933459476934925 1364886008600047303850597)
                    ·
                      rfl

theorem cell22_3987159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 1, 3, 3].length) (baseStart_3987159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3987159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3987159 prefixEnd_3987159 := by exact prefixLift 3987159
  have htrace : WordTrace (prefixWord ++ tailWord_3987159) baseStart_3987159 baseEnd_3987159 := by
    simpa [prefixWord, tailWord_3987159, baseEnd_3987159] using wordTrace_append hprefix tailTrace_3987159
  have hstable : (prefixWord ++ tailWord_3987159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987159).length < 2 ^ (prefixWord ++ tailWord_3987159).sum := by decide
  have hdescent : baseEnd_3987159 < baseStart_3987159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987165 : List Nat := [1, 4, 3, 3, 1, 1, 3, 1, 2, 3]
def baseStart_3987165 : Nat := 118140960795 + 3987165 * 2 ^ 59
def prefixEnd_3987165 : Nat := 4983230072969 + 3 ^ 40 * 3987165 * 2
def baseEnd_3987165 : Nat := 1364888062522665288200579

theorem tailTrace_3987165 : CollatzResearch.WordTrace tailWord_3987165 prefixEnd_3987165 1364888062522665288200579 := by
  unfold tailWord_3987165
  simp only [CollatzResearch.WordTrace]
  refine ⟨145423854600189633413626949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96949236400126422275751299 145423854600189633413626949)
  ·
    refine ⟨27266972737535556265055053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145423854600189633413626949 27266972737535556265055053)
    ·
      refine ⟨10225114776575833599395645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27266972737535556265055053 10225114776575833599395645)
      ·
        refine ⟨3834418041215937599773367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10225114776575833599395645 3834418041215937599773367)
        ·
          refine ⟨5751627061823906399660051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3834418041215937599773367 5751627061823906399660051)
          ·
            refine ⟨8627440592735859599490077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5751627061823906399660051 8627440592735859599490077)
            ·
              refine ⟨3235290222275947349808779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8627440592735859599490077 3235290222275947349808779)
              ·
                refine ⟨4852935333413921024713169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3235290222275947349808779 4852935333413921024713169)
                ·
                  refine ⟨3639701500060440768534877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4852935333413921024713169 3639701500060440768534877)
                  ·
                    refine ⟨1364888062522665288200579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3639701500060440768534877 1364888062522665288200579)
                    ·
                      rfl

theorem cell22_3987165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_3987165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3987165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3987165 prefixEnd_3987165 := by exact prefixLift 3987165
  have htrace : WordTrace (prefixWord ++ tailWord_3987165) baseStart_3987165 baseEnd_3987165 := by
    simpa [prefixWord, tailWord_3987165, baseEnd_3987165] using wordTrace_append hprefix tailTrace_3987165
  have hstable : (prefixWord ++ tailWord_3987165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987165).length < 2 ^ (prefixWord ++ tailWord_3987165).sum := by decide
  have hdescent : baseEnd_3987165 < baseStart_3987165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987236 : List Nat := [2, 3, 1, 3, 2, 1, 3, 2, 1, 4]
def baseStart_3987236 : Nat := 118140960795 + 3987236 * 2 ^ 59
def prefixEnd_3987236 : Nat := 4983230072969 + 3 ^ 40 * 3987236 * 2
def baseEnd_3987236 : Nat := 1364912367273644769675361

theorem tailTrace_3987236 : CollatzResearch.WordTrace tailWord_3987236 prefixEnd_3987236 1364912367273644769675361 := by
  unfold tailWord_3987236
  simp only [CollatzResearch.WordTrace]
  refine ⟨72713222091466206269730781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96950962788621608359641041 72713222091466206269730781)
  ·
    refine ⟨27267458284299827351149043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72713222091466206269730781 27267458284299827351149043)
    ·
      refine ⟨40901187426449741026723565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27267458284299827351149043 40901187426449741026723565)
      ·
        refine ⟨15337945284918652885021337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40901187426449741026723565 15337945284918652885021337)
        ·
          refine ⟨11503458963688989663766003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15337945284918652885021337 11503458963688989663766003)
          ·
            refine ⟨17255188445533484495649005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11503458963688989663766003 17255188445533484495649005)
            ·
              refine ⟨6470695667075056685868377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17255188445533484495649005 6470695667075056685868377)
              ·
                refine ⟨4853021750306292514401283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6470695667075056685868377 4853021750306292514401283)
                ·
                  refine ⟨7279532625459438771601925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4853021750306292514401283 7279532625459438771601925)
                  ·
                    refine ⟨1364912367273644769675361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7279532625459438771601925 1364912367273644769675361)
                    ·
                      rfl

theorem cell22_3987236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 2, 1, 4].length) (baseStart_3987236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3987236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3987236 prefixEnd_3987236 := by exact prefixLift 3987236
  have htrace : WordTrace (prefixWord ++ tailWord_3987236) baseStart_3987236 baseEnd_3987236 := by
    simpa [prefixWord, tailWord_3987236, baseEnd_3987236] using wordTrace_append hprefix tailTrace_3987236
  have hstable : (prefixWord ++ tailWord_3987236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987236).length < 2 ^ (prefixWord ++ tailWord_3987236).sum := by decide
  have hdescent : baseEnd_3987236 < baseStart_3987236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987247 : List Nat := [1, 1, 2, 1, 2, 1, 2, 2, 6, 4]
def baseStart_3987247 : Nat := 118140960795 + 3987247 * 2 ^ 59
def prefixEnd_3987247 : Nat := 4983230072969 + 3 ^ 40 * 3987247 * 2
def baseEnd_3987247 : Nat := 1364916132798444407650327

theorem tailTrace_3987247 : CollatzResearch.WordTrace tailWord_3987247 prefixEnd_3987247 1364916132798444407650327 := by
  unfold tailWord_3987247
  simp only [CollatzResearch.WordTrace]
  refine ⟨145426845385892561418111995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96951230257261707612074663 145426845385892561418111995)
  ·
    refine ⟨218140268078838842127167993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145426845385892561418111995 218140268078838842127167993)
    ·
      refine ⟨163605201059129131595375995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218140268078838842127167993 163605201059129131595375995)
      ·
        refine ⟨245407801588693697393063993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163605201059129131595375995 245407801588693697393063993)
        ·
          refine ⟨184055851191520273044797995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245407801588693697393063993 184055851191520273044797995)
          ·
            refine ⟨276083776787280409567196993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184055851191520273044797995 276083776787280409567196993)
            ·
              refine ⟨207062832590460307175397745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 276083776787280409567196993 207062832590460307175397745)
              ·
                refine ⟨155297124442845230381548309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207062832590460307175397745 155297124442845230381548309)
                ·
                  refine ⟨7279552708258370174135077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 155297124442845230381548309 7279552708258370174135077)
                  ·
                    refine ⟨1364916132798444407650327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7279552708258370174135077 1364916132798444407650327)
                    ·
                      rfl

theorem cell22_3987247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 6, 4].length) (baseStart_3987247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3987247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3987247 prefixEnd_3987247 := by exact prefixLift 3987247
  have htrace : WordTrace (prefixWord ++ tailWord_3987247) baseStart_3987247 baseEnd_3987247 := by
    simpa [prefixWord, tailWord_3987247, baseEnd_3987247] using wordTrace_append hprefix tailTrace_3987247
  have hstable : (prefixWord ++ tailWord_3987247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987247).length < 2 ^ (prefixWord ++ tailWord_3987247).sum := by decide
  have hdescent : baseEnd_3987247 < baseStart_3987247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987249 : List Nat := [1, 2, 2, 3, 2, 3, 1, 2, 1, 5]
def baseStart_3987249 : Nat := 118140960795 + 3987249 * 2 ^ 59
def prefixEnd_3987249 : Nat := 4983230072969 + 3 ^ 40 * 3987249 * 2
def baseEnd_3987249 : Nat := 1364916817439317069100321

theorem tailTrace_3987249 : CollatzResearch.WordTrace tailWord_3987249 prefixEnd_3987249 1364916817439317069100321 := by
  unfold tailWord_3987249
  simp only [CollatzResearch.WordTrace]
  refine ⟨145426918331885315759684801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96951278887923543839789867 145426918331885315759684801)
  ·
    refine ⟨109070188748913986819763601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145426918331885315759684801 109070188748913986819763601)
    ·
      refine ⟨81802641561685490114822701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109070188748913986819763601 81802641561685490114822701)
      ·
        refine ⟨30675990585632058793058513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81802641561685490114822701 30675990585632058793058513)
        ·
          refine ⟨23006992939224044094793885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30675990585632058793058513 23006992939224044094793885)
          ·
            refine ⟨8627622352209016535547707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23006992939224044094793885 8627622352209016535547707)
            ·
              refine ⟨12941433528313524803321561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8627622352209016535547707 12941433528313524803321561)
              ·
                refine ⟨9706075146235143602491171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12941433528313524803321561 9706075146235143602491171)
                ·
                  refine ⟨14559112719352715403736757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9706075146235143602491171 14559112719352715403736757)
                  ·
                    refine ⟨1364916817439317069100321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14559112719352715403736757 1364916817439317069100321)
                    ·
                      rfl

theorem cell22_3987249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 2, 1, 5].length) (baseStart_3987249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3987249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3987249 prefixEnd_3987249 := by exact prefixLift 3987249
  have htrace : WordTrace (prefixWord ++ tailWord_3987249) baseStart_3987249 baseEnd_3987249 := by
    simpa [prefixWord, tailWord_3987249, baseEnd_3987249] using wordTrace_append hprefix tailTrace_3987249
  have hstable : (prefixWord ++ tailWord_3987249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987249).length < 2 ^ (prefixWord ++ tailWord_3987249).sum := by decide
  have hdescent : baseEnd_3987249 < baseStart_3987249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987253 : List Nat := [1, 3, 3, 1, 4, 1, 3, 1, 1, 4]
def baseStart_3987253 : Nat := 118140960795 + 3987253 * 2 ^ 59
def prefixEnd_3987253 : Nat := 4983230072969 + 3 ^ 40 * 3987253 * 2
def baseEnd_3987253 : Nat := 1364918186721062392000309

theorem tailTrace_3987253 : CollatzResearch.WordTrace tailWord_3987253 prefixEnd_3987253 1364918186721062392000309 := by
  unfold tailWord_3987253
  simp only [CollatzResearch.WordTrace]
  refine ⟨145427064223870824442830413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96951376149247216295220275 145427064223870824442830413)
  ·
    refine ⟨54535149083951559166061405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145427064223870824442830413 54535149083951559166061405)
    ·
      refine ⟨20450680906481834687273027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54535149083951559166061405 20450680906481834687273027)
      ·
        refine ⟨30676021359722752030909541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20450680906481834687273027 30676021359722752030909541)
        ·
          refine ⟨5751754004948016005795539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30676021359722752030909541 5751754004948016005795539)
          ·
            refine ⟨8627631007422024008693309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5751754004948016005795539 8627631007422024008693309)
            ·
              refine ⟨3235361627783259003259991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8627631007422024008693309 3235361627783259003259991)
              ·
                refine ⟨4853042441674888504889987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3235361627783259003259991 4853042441674888504889987)
                ·
                  refine ⟨7279563662512332757334981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4853042441674888504889987 7279563662512332757334981)
                  ·
                    refine ⟨1364918186721062392000309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7279563662512332757334981 1364918186721062392000309)
                    ·
                      rfl

theorem cell22_3987253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 3, 1, 1, 4].length) (baseStart_3987253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3987253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3987253 prefixEnd_3987253 := by exact prefixLift 3987253
  have htrace : WordTrace (prefixWord ++ tailWord_3987253) baseStart_3987253 baseEnd_3987253 := by
    simpa [prefixWord, tailWord_3987253, baseEnd_3987253] using wordTrace_append hprefix tailTrace_3987253
  have hstable : (prefixWord ++ tailWord_3987253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987253).length < 2 ^ (prefixWord ++ tailWord_3987253).sum := by decide
  have hdescent : baseEnd_3987253 < baseStart_3987253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987298 : List Nat := [3, 3, 2, 1, 2, 3, 1, 1, 2, 4]
def baseStart_3987298 : Nat := 118140960795 + 3987298 * 2 ^ 59
def prefixEnd_3987298 : Nat := 4983230072969 + 3 ^ 40 * 3987298 * 2
def baseEnd_3987298 : Nat := 1364933591140697274625171

theorem tailTrace_3987298 : CollatzResearch.WordTrace tailWord_3987298 prefixEnd_3987298 1364933591140697274625171 := by
  unfold tailWord_3987298
  simp only [CollatzResearch.WordTrace]
  refine ⟨36357176377176949282054637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96952470339138531418812365 36357176377176949282054637)
  ·
    refine ⟨13633941141441355980770489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36357176377176949282054637 13633941141441355980770489)
    ·
      refine ⟨10225455856081016985577867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13633941141441355980770489 10225455856081016985577867)
      ·
        refine ⟨15338183784121525478366801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10225455856081016985577867 15338183784121525478366801)
        ·
          refine ⟨11503637838091144108775101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15338183784121525478366801 11503637838091144108775101)
          ·
            refine ⟨4313864189284179040790663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11503637838091144108775101 4313864189284179040790663)
            ·
              refine ⟨6470796283926268561185995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4313864189284179040790663 6470796283926268561185995)
              ·
                refine ⟨9706194425889402841778993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6470796283926268561185995 9706194425889402841778993)
                ·
                  refine ⟨7279645819417052131334245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9706194425889402841778993 7279645819417052131334245)
                  ·
                    refine ⟨1364933591140697274625171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7279645819417052131334245 1364933591140697274625171)
                    ·
                      rfl

theorem cell22_3987298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_3987298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3987298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3987298 prefixEnd_3987298 := by exact prefixLift 3987298
  have htrace : WordTrace (prefixWord ++ tailWord_3987298) baseStart_3987298 baseEnd_3987298 := by
    simpa [prefixWord, tailWord_3987298, baseEnd_3987298] using wordTrace_append hprefix tailTrace_3987298
  have hstable : (prefixWord ++ tailWord_3987298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987298).length < 2 ^ (prefixWord ++ tailWord_3987298).sum := by decide
  have hdescent : baseEnd_3987298 < baseStart_3987298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987307 : List Nat := [1, 1, 1, 1, 2, 2, 3, 4, 7]
def baseStart_3987307 : Nat := 118140960795 + 3987307 * 2 ^ 59
def prefixEnd_3987307 : Nat := 4983230072969 + 3 ^ 40 * 3987307 * 2
def baseEnd_3987307 : Nat := 454978890674874750383381

theorem tailTrace_3987307 : CollatzResearch.WordTrace tailWord_3987307 prefixEnd_3987307 454978890674874750383381 := by
  unfold tailWord_3987307
  simp only [CollatzResearch.WordTrace]
  refine ⟨145429033765675191665296175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96952689177116794443530783 145429033765675191665296175)
  ·
    refine ⟨218143550648512787497944263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145429033765675191665296175 218143550648512787497944263)
    ·
      refine ⟨327215325972769181246916395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218143550648512787497944263 327215325972769181246916395)
      ·
        refine ⟨490822988959153771870374593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327215325972769181246916395 490822988959153771870374593)
        ·
          refine ⟨368117241719365328902780945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 490822988959153771870374593 368117241719365328902780945)
          ·
            refine ⟨276087931289523996677085709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 368117241719365328902780945 276087931289523996677085709)
            ·
              refine ⟨103532974233571498753907141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 276087931289523996677085709 103532974233571498753907141)
              ·
                refine ⟨19412432668794656016357589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103532974233571498753907141 19412432668794656016357589)
                ·
                  refine ⟨454978890674874750383381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19412432668794656016357589 454978890674874750383381)
                  ·
                    rfl

theorem cell22_3987307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 7].length) (baseStart_3987307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3987307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3987307 prefixEnd_3987307 := by exact prefixLift 3987307
  have htrace : WordTrace (prefixWord ++ tailWord_3987307) baseStart_3987307 baseEnd_3987307 := by
    simpa [prefixWord, tailWord_3987307, baseEnd_3987307] using wordTrace_append hprefix tailTrace_3987307
  have hstable : (prefixWord ++ tailWord_3987307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987307).length < 2 ^ (prefixWord ++ tailWord_3987307).sum := by decide
  have hdescent : baseEnd_3987307 < baseStart_3987307 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987362 : List Nat := [3, 3, 1, 2, 3, 2, 1, 3, 1, 3]
def baseStart_3987362 : Nat := 118140960795 + 3987362 * 2 ^ 59
def prefixEnd_3987362 : Nat := 4983230072969 + 3 ^ 40 * 3987362 * 2
def baseEnd_3987362 : Nat := 1364955499648622441024975

theorem tailTrace_3987362 : CollatzResearch.WordTrace tailWord_3987362 prefixEnd_3987362 1364955499648622441024975 := by
  unfold tailWord_3987362
  simp only [CollatzResearch.WordTrace]
  refine ⟨36357759945118984014637085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96954026520317290705698893 36357759945118984014637085)
  ·
    refine ⟨13634159979419619005488907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36357759945118984014637085 13634159979419619005488907)
    ·
      refine ⟨20451239969129428508233361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13634159979419619005488907 20451239969129428508233361)
      ·
        refine ⟨15338429976847071381175021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20451239969129428508233361 15338429976847071381175021)
        ·
          refine ⟨5751911241317651767940633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15338429976847071381175021 5751911241317651767940633)
          ·
            refine ⟨4313933430988238825955475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5751911241317651767940633 4313933430988238825955475)
            ·
              refine ⟨6470900146482358238933213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4313933430988238825955475 6470900146482358238933213)
              ·
                refine ⟨2426587554930884339599955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6470900146482358238933213 2426587554930884339599955)
                ·
                  refine ⟨3639881332396326509399933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2426587554930884339599955 3639881332396326509399933)
                  ·
                    refine ⟨1364955499648622441024975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3639881332396326509399933 1364955499648622441024975)
                    ·
                      rfl

theorem cell22_3987362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 3, 1, 3].length) (baseStart_3987362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3987362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3987362 prefixEnd_3987362 := by exact prefixLift 3987362
  have htrace : WordTrace (prefixWord ++ tailWord_3987362) baseStart_3987362 baseEnd_3987362 := by
    simpa [prefixWord, tailWord_3987362, baseEnd_3987362] using wordTrace_append hprefix tailTrace_3987362
  have hstable : (prefixWord ++ tailWord_3987362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987362).length < 2 ^ (prefixWord ++ tailWord_3987362).sum := by decide
  have hdescent : baseEnd_3987362 < baseStart_3987362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987399 : List Nat := [1, 1, 4, 1, 1, 2, 1, 1, 6, 4]
def baseStart_3987399 : Nat := 118140960795 + 3987399 * 2 ^ 59
def prefixEnd_3987399 : Nat := 4983230072969 + 3 ^ 40 * 3987399 * 2
def baseEnd_3987399 : Nat := 1364968165504766677849861

theorem tailTrace_3987399 : CollatzResearch.WordTrace tailWord_3987399 prefixEnd_3987399 1364968165504766677849861 := by
  unfold tailWord_3987399
  simp only [CollatzResearch.WordTrace]
  refine ⟨145432389281341891377645251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96954926187561260918430167 145432389281341891377645251)
  ·
    refine ⟨218148583922012837066467877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145432389281341891377645251 218148583922012837066467877)
    ·
      refine ⟨40902859485377406949962727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 218148583922012837066467877 40902859485377406949962727)
      ·
        refine ⟨61354289228066110424944091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40902859485377406949962727 61354289228066110424944091)
        ·
          refine ⟨92031433842099165637416137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61354289228066110424944091 92031433842099165637416137)
          ·
            refine ⟨69023575381574374228062103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92031433842099165637416137 69023575381574374228062103)
            ·
              refine ⟨103535363072361561342093155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69023575381574374228062103 103535363072361561342093155)
              ·
                refine ⟨155303044608542342013139733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103535363072361561342093155 155303044608542342013139733)
                ·
                  refine ⟨7279830216025422281865925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 155303044608542342013139733 7279830216025422281865925)
                  ·
                    refine ⟨1364968165504766677849861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7279830216025422281865925 1364968165504766677849861)
                    ·
                      rfl

theorem cell22_3987399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 6, 4].length) (baseStart_3987399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3987399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3987399 prefixEnd_3987399 := by exact prefixLift 3987399
  have htrace : WordTrace (prefixWord ++ tailWord_3987399) baseStart_3987399 baseEnd_3987399 := by
    simpa [prefixWord, tailWord_3987399, baseEnd_3987399] using wordTrace_append hprefix tailTrace_3987399
  have hstable : (prefixWord ++ tailWord_3987399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987399).length < 2 ^ (prefixWord ++ tailWord_3987399).sum := by decide
  have hdescent : baseEnd_3987399 < baseStart_3987399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987401 : List Nat := [1, 2, 1, 1, 2, 1, 2, 7, 2, 3]
def baseStart_3987401 : Nat := 118140960795 + 3987401 * 2 ^ 59
def prefixEnd_3987401 : Nat := 4983230072969 + 3 ^ 40 * 3987401 * 2
def baseEnd_3987401 : Nat := 1364968850145639339299855

theorem tailTrace_3987401 : CollatzResearch.WordTrace tailWord_3987401 prefixEnd_3987401 1364968850145639339299855 := by
  unfold tailWord_3987401
  simp only [CollatzResearch.WordTrace]
  refine ⟨145432462227334645719218057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96954974818223097146145371 145432462227334645719218057)
  ·
    refine ⟨109074346670500984289413543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145432462227334645719218057 109074346670500984289413543)
    ·
      refine ⟨163611520005751476434120315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109074346670500984289413543 163611520005751476434120315)
      ·
        refine ⟨245417280008627214651180473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163611520005751476434120315 245417280008627214651180473)
        ·
          refine ⟨184062960006470410988385355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245417280008627214651180473 184062960006470410988385355)
          ·
            refine ⟨276094440009705616482578033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184062960006470410988385355 276094440009705616482578033)
            ·
              refine ⟨207070830007279212361933525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 276094440009705616482578033 207070830007279212361933525)
              ·
                refine ⟨4853222578295606539732817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 207070830007279212361933525 4853222578295606539732817)
                ·
                  refine ⟨3639916933721704904799613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4853222578295606539732817 3639916933721704904799613)
                  ·
                    refine ⟨1364968850145639339299855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3639916933721704904799613 1364968850145639339299855)
                    ·
                      rfl

theorem cell22_3987401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 7, 2, 3].length) (baseStart_3987401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3987401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3987401 prefixEnd_3987401 := by exact prefixLift 3987401
  have htrace : WordTrace (prefixWord ++ tailWord_3987401) baseStart_3987401 baseEnd_3987401 := by
    simpa [prefixWord, tailWord_3987401, baseEnd_3987401] using wordTrace_append hprefix tailTrace_3987401
  have hstable : (prefixWord ++ tailWord_3987401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987401).length < 2 ^ (prefixWord ++ tailWord_3987401).sum := by decide
  have hdescent : baseEnd_3987401 < baseStart_3987401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987416 : List Nat := [2, 1, 2, 2, 2, 2, 4, 1, 2, 4]
def baseStart_3987416 : Nat := 118140960795 + 3987416 * 2 ^ 59
def prefixEnd_3987416 : Nat := 4983230072969 + 3 ^ 40 * 3987416 * 2
def baseEnd_3987416 : Nat := 1364973984952184300174809

theorem tailTrace_3987416 : CollatzResearch.WordTrace tailWord_3987416 prefixEnd_3987416 1364973984952184300174809 := by
  unfold tailWord_3987416
  simp only [CollatzResearch.WordTrace]
  refine ⟨72716504661140151640507051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96955339548186868854009401 72716504661140151640507051)
  ·
    refine ⟨109074756991710227460760577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72716504661140151640507051 109074756991710227460760577)
    ·
      refine ⟨81806067743782670595570433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109074756991710227460760577 81806067743782670595570433)
      ·
        refine ⟨61354550807837002946677825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81806067743782670595570433 61354550807837002946677825)
        ·
          refine ⟨46015913105877752210008369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61354550807837002946677825 46015913105877752210008369)
          ·
            refine ⟨34511934829408314157506277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46015913105877752210008369 34511934829408314157506277)
            ·
              refine ⟨6470987780514058904532427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34511934829408314157506277 6470987780514058904532427)
              ·
                refine ⟨9706481670771088356798641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6470987780514058904532427 9706481670771088356798641)
                ·
                  refine ⟨7279861253078316267598981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9706481670771088356798641 7279861253078316267598981)
                  ·
                    refine ⟨1364973984952184300174809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7279861253078316267598981 1364973984952184300174809)
                    ·
                      rfl

theorem cell22_3987416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 1, 2, 4].length) (baseStart_3987416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3987416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3987416 prefixEnd_3987416 := by exact prefixLift 3987416
  have htrace : WordTrace (prefixWord ++ tailWord_3987416) baseStart_3987416 baseEnd_3987416 := by
    simpa [prefixWord, tailWord_3987416, baseEnd_3987416] using wordTrace_append hprefix tailTrace_3987416
  have hstable : (prefixWord ++ tailWord_3987416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987416).length < 2 ^ (prefixWord ++ tailWord_3987416).sum := by decide
  have hdescent : baseEnd_3987416 < baseStart_3987416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987431 : List Nat := [1, 1, 5, 2, 4, 9]
def baseStart_3987431 : Nat := 118140960795 + 3987431 * 2 ^ 59
def prefixEnd_3987431 : Nat := 4983230072969 + 3 ^ 40 * 3987431 * 2
def baseEnd_3987431 : Nat := 16851594071095422975923

theorem tailTrace_3987431 : CollatzResearch.WordTrace tailWord_3987431 prefixEnd_3987431 16851594071095422975923 := by
  unfold tailWord_3987431
  simp only [CollatzResearch.WordTrace]
  refine ⟨145433556417225960842810147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96955704278150640561873431 145433556417225960842810147)
  ·
    refine ⟨218150334625838941264215221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145433556417225960842810147 218150334625838941264215221)
    ·
      refine ⟨20451593871172400743520177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 218150334625838941264215221 20451593871172400743520177)
      ·
        refine ⟨15338695403379300557640133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20451593871172400743520177 15338695403379300557640133)
        ·
          refine ⟨2876005388133618854557525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15338695403379300557640133 2876005388133618854557525)
          ·
            refine ⟨16851594071095422975923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2876005388133618854557525 16851594071095422975923)
            ·
              rfl

theorem cell22_3987431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 9].length) (baseStart_3987431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3987431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3987431 prefixEnd_3987431 := by exact prefixLift 3987431
  have htrace : WordTrace (prefixWord ++ tailWord_3987431) baseStart_3987431 baseEnd_3987431 := by
    simpa [prefixWord, tailWord_3987431, baseEnd_3987431] using wordTrace_append hprefix tailTrace_3987431
  have hstable : (prefixWord ++ tailWord_3987431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987431).length < 2 ^ (prefixWord ++ tailWord_3987431).sum := by decide
  have hdescent : baseEnd_3987431 < baseStart_3987431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987463 : List Nat := [1, 1, 4, 3, 1, 3, 1, 2, 3, 3]
def baseStart_3987463 : Nat := 118140960795 + 3987463 * 2 ^ 59
def prefixEnd_3987463 : Nat := 4983230072969 + 3 ^ 40 * 3987463 * 2
def baseEnd_3987463 : Nat := 1364990074012691844249665

theorem tailTrace_3987463 : CollatzResearch.WordTrace tailWord_3987463 prefixEnd_3987463 1364990074012691844249665 := by
  unfold tailWord_3987463
  simp only [CollatzResearch.WordTrace]
  refine ⟨145434723553110030307975043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96956482368740020205316695 145434723553110030307975043)
  ·
    refine ⟨218152085329665045461962565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145434723553110030307975043 218152085329665045461962565)
    ·
      refine ⟨40903515999312196024117981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 218152085329665045461962565 40903515999312196024117981)
      ·
        refine ⟨15338818499742073509044243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40903515999312196024117981 15338818499742073509044243)
        ·
          refine ⟨23008227749613110263566365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15338818499742073509044243 23008227749613110263566365)
          ·
            refine ⟨8628085406104916348837387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23008227749613110263566365 8628085406104916348837387)
            ·
              refine ⟨12942128109157374523256081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8628085406104916348837387 12942128109157374523256081)
              ·
                refine ⟨9706596081868030892442061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12942128109157374523256081 9706596081868030892442061)
                ·
                  refine ⟨3639973530700511584665773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9706596081868030892442061 3639973530700511584665773)
                  ·
                    refine ⟨1364990074012691844249665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3639973530700511584665773 1364990074012691844249665)
                    ·
                      rfl

theorem cell22_3987463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 2, 3, 3].length) (baseStart_3987463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3987463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3987463 prefixEnd_3987463 := by exact prefixLift 3987463
  have htrace : WordTrace (prefixWord ++ tailWord_3987463) baseStart_3987463 baseEnd_3987463 := by
    simpa [prefixWord, tailWord_3987463, baseEnd_3987463] using wordTrace_append hprefix tailTrace_3987463
  have hstable : (prefixWord ++ tailWord_3987463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987463).length < 2 ^ (prefixWord ++ tailWord_3987463).sum := by decide
  have hdescent : baseEnd_3987463 < baseStart_3987463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987480 : List Nat := [2, 1, 2, 3, 2, 1, 4, 3, 1, 3]
def baseStart_3987480 : Nat := 118140960795 + 3987480 * 2 ^ 59
def prefixEnd_3987480 : Nat := 4983230072969 + 3 ^ 40 * 3987480 * 2
def baseEnd_3987480 : Nat := 1364995893460109466574613

theorem tailTrace_3987480 : CollatzResearch.WordTrace tailWord_3987480 prefixEnd_3987480 1364995893460109466574613 := by
  unfold tailWord_3987480
  simp only [CollatzResearch.WordTrace]
  refine ⟨72717671797024221105671947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96956895729365628140895929 72717671797024221105671947)
  ·
    refine ⟨109076507695536331658507921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72717671797024221105671947 109076507695536331658507921)
    ·
      refine ⟨81807380771652248743880941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109076507695536331658507921 81807380771652248743880941)
      ·
        refine ⟨30677767789369593278955353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81807380771652248743880941 30677767789369593278955353)
        ·
          refine ⟨23008325842027194959216515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30677767789369593278955353 23008325842027194959216515)
          ·
            refine ⟨34512488763040792438824773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23008325842027194959216515 34512488763040792438824773)
            ·
              refine ⟨6471091643070148582279645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34512488763040792438824773 6471091643070148582279645)
              ·
                refine ⟨2426659366151305718354867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6471091643070148582279645 2426659366151305718354867)
                ·
                  refine ⟨3639989049226958577532301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2426659366151305718354867 3639989049226958577532301)
                  ·
                    refine ⟨1364995893460109466574613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3639989049226958577532301 1364995893460109466574613)
                    ·
                      rfl

theorem cell22_3987480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 3, 1, 3].length) (baseStart_3987480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3987480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3987480 prefixEnd_3987480 := by exact prefixLift 3987480
  have htrace : WordTrace (prefixWord ++ tailWord_3987480) baseStart_3987480 baseEnd_3987480 := by
    simpa [prefixWord, tailWord_3987480, baseEnd_3987480] using wordTrace_append hprefix tailTrace_3987480
  have hstable : (prefixWord ++ tailWord_3987480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987480).length < 2 ^ (prefixWord ++ tailWord_3987480).sum := by decide
  have hdescent : baseEnd_3987480 < baseStart_3987480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987493 : List Nat := [1, 3, 1, 2, 2, 5, 1, 2, 5]
def baseStart_3987493 : Nat := 118140960795 + 3987493 * 2 ^ 59
def prefixEnd_3987493 : Nat := 4983230072969 + 3 ^ 40 * 3987493 * 2
def baseEnd_3987493 : Nat := 455000114541927255333191

theorem tailTrace_3987493 : CollatzResearch.WordTrace tailWord_3987493 prefixEnd_3987493 455000114541927255333191 := by
  unfold tailWord_3987493
  simp only [CollatzResearch.WordTrace]
  refine ⟨145435817743001345431567133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96957211828667563621044755 145435817743001345431567133)
  ·
    refine ⟨54538431653625504536837675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145435817743001345431567133 54538431653625504536837675)
    ·
      refine ⟨81807647480438256805256513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54538431653625504536837675 81807647480438256805256513)
      ·
        refine ⟨61355735610328692603942385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81807647480438256805256513 61355735610328692603942385)
        ·
          refine ⟨46016801707746519452956789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61355735610328692603942385 46016801707746519452956789)
          ·
            refine ⟨4314075160101236198714699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46016801707746519452956789 4314075160101236198714699)
            ·
              refine ⟨6471112740151854298072049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4314075160101236198714699 6471112740151854298072049)
              ·
                refine ⟨4853334555113890723554037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6471112740151854298072049 4853334555113890723554037)
                ·
                  refine ⟨455000114541927255333191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4853334555113890723554037 455000114541927255333191)
                  ·
                    rfl

theorem cell22_3987493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 2, 5].length) (baseStart_3987493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3987493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3987493 prefixEnd_3987493 := by exact prefixLift 3987493
  have htrace : WordTrace (prefixWord ++ tailWord_3987493) baseStart_3987493 baseEnd_3987493 := by
    simpa [prefixWord, tailWord_3987493, baseEnd_3987493] using wordTrace_append hprefix tailTrace_3987493
  have hstable : (prefixWord ++ tailWord_3987493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987493).length < 2 ^ (prefixWord ++ tailWord_3987493).sum := by decide
  have hdescent : baseEnd_3987493 < baseStart_3987493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987510 : List Nat := [5, 1, 2, 1, 1, 1, 5, 1, 5]
def baseStart_3987510 : Nat := 118140960795 + 3987510 * 2 ^ 59
def prefixEnd_3987510 : Nat := 4983230072969 + 3 ^ 40 * 3987510 * 2
def baseEnd_3987510 : Nat := 455002054357733129441507

theorem tailTrace_3987510 : CollatzResearch.WordTrace tailWord_3987510 prefixEnd_3987510 455002054357733129441507 := by
  unfold tailWord_3987510
  simp only [CollatzResearch.WordTrace]
  refine ⟨9089777361496234833433499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96957625189293171556623989 9089777361496234833433499)
  ·
    refine ⟨13634666042244352250150249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9089777361496234833433499 13634666042244352250150249)
    ·
      refine ⟨10225999531683264187612687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13634666042244352250150249 10225999531683264187612687)
      ·
        refine ⟨15338999297524896281419031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10225999531683264187612687 15338999297524896281419031)
        ·
          refine ⟨23008498946287344422128547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15338999297524896281419031 23008498946287344422128547)
          ·
            refine ⟨34512748419431016633192821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23008498946287344422128547 34512748419431016633192821)
            ·
              refine ⟨3235570164321657809361827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34512748419431016633192821 3235570164321657809361827)
              ·
                refine ⟨4853355246482486714042741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3235570164321657809361827 4853355246482486714042741)
                ·
                  refine ⟨455002054357733129441507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4853355246482486714042741 455002054357733129441507)
                  ·
                    rfl

theorem cell22_3987510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 5, 1, 5].length) (baseStart_3987510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3987510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3987510 prefixEnd_3987510 := by exact prefixLift 3987510
  have htrace : WordTrace (prefixWord ++ tailWord_3987510) baseStart_3987510 baseEnd_3987510 := by
    simpa [prefixWord, tailWord_3987510, baseEnd_3987510] using wordTrace_append hprefix tailTrace_3987510
  have hstable : (prefixWord ++ tailWord_3987510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987510).length < 2 ^ (prefixWord ++ tailWord_3987510).sum := by decide
  have hdescent : baseEnd_3987510 < baseStart_3987510 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987553 : List Nat := [1, 2, 3, 1, 1, 2, 1, 6, 2, 3]
def baseStart_3987553 : Nat := 118140960795 + 3987553 * 2 ^ 59
def prefixEnd_3987553 : Nat := 4983230072969 + 3 ^ 40 * 3987553 * 2
def baseEnd_3987553 : Nat := 1365020882851961609499389

theorem tailTrace_3987553 : CollatzResearch.WordTrace tailWord_3987553 prefixEnd_3987553 1365020882851961609499389 := by
  unfold tailWord_3987553
  simp only [CollatzResearch.WordTrace]
  refine ⟨145438006122783975678751313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96958670748522650452500875 145438006122783975678751313)
  ·
    refine ⟨109078504592087981759063485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145438006122783975678751313 109078504592087981759063485)
    ·
      refine ⟨40904439222032993159648807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109078504592087981759063485 40904439222032993159648807)
      ·
        refine ⟨61356658833049489739473211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40904439222032993159648807 61356658833049489739473211)
        ·
          refine ⟨92034988249574234609209817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61356658833049489739473211 92034988249574234609209817)
          ·
            refine ⟨69026241187180675956907363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92034988249574234609209817 69026241187180675956907363)
            ·
              refine ⟨103539361780771013935361045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69026241187180675956907363 103539361780771013935361045)
              ·
                refine ⟨4853407583473641278220049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 103539361780771013935361045 4853407583473641278220049)
                ·
                  refine ⟨3640055687605230958665037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4853407583473641278220049 3640055687605230958665037)
                  ·
                    refine ⟨1365020882851961609499389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3640055687605230958665037 1365020882851961609499389)
                    ·
                      rfl

theorem cell22_3987553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 6, 2, 3].length) (baseStart_3987553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3987553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3987553 prefixEnd_3987553 := by exact prefixLift 3987553
  have htrace : WordTrace (prefixWord ++ tailWord_3987553) baseStart_3987553 baseEnd_3987553 := by
    simpa [prefixWord, tailWord_3987553, baseEnd_3987553] using wordTrace_append hprefix tailTrace_3987553
  have hstable : (prefixWord ++ tailWord_3987553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987553).length < 2 ^ (prefixWord ++ tailWord_3987553).sum := by decide
  have hdescent : baseEnd_3987553 < baseStart_3987553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987570 : List Nat := [3, 2, 1, 2, 2, 3, 1, 3, 2, 3]
def baseStart_3987570 : Nat := 118140960795 + 3987570 * 2 ^ 59
def prefixEnd_3987570 : Nat := 4983230072969 + 3 ^ 40 * 3987570 * 2
def baseEnd_3987570 : Nat := 1365026702299379231824337

theorem tailTrace_3987570 : CollatzResearch.WordTrace tailWord_3987570 prefixEnd_3987570 1365026702299379231824337 := by
  unfold tailWord_3987570
  simp only [CollatzResearch.WordTrace]
  refine ⟨36359656540930596895530041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96959084109148258388080109 36359656540930596895530041)
  ·
    refine ⟨27269742405697947671647531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36359656540930596895530041 27269742405697947671647531)
    ·
      refine ⟨40904613608546921507471297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27269742405697947671647531 40904613608546921507471297)
      ·
        refine ⟨30678460206410191130603473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40904613608546921507471297 30678460206410191130603473)
        ·
          refine ⟨23008845154807643347952605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30678460206410191130603473 23008845154807643347952605)
          ·
            refine ⟨8628316933052866255482227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23008845154807643347952605 8628316933052866255482227)
            ·
              refine ⟨12942475399579299383223341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8628316933052866255482227 12942475399579299383223341)
              ·
                refine ⟨4853428274842237268708753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12942475399579299383223341 4853428274842237268708753)
                ·
                  refine ⟨3640071206131677951531565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4853428274842237268708753 3640071206131677951531565)
                  ·
                    refine ⟨1365026702299379231824337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3640071206131677951531565 1365026702299379231824337)
                    ·
                      rfl

theorem cell22_3987570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 3, 2, 3].length) (baseStart_3987570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3987570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3987570 prefixEnd_3987570 := by exact prefixLift 3987570
  have htrace : WordTrace (prefixWord ++ tailWord_3987570) baseStart_3987570 baseEnd_3987570 := by
    simpa [prefixWord, tailWord_3987570, baseEnd_3987570] using wordTrace_append hprefix tailTrace_3987570
  have hstable : (prefixWord ++ tailWord_3987570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987570).length < 2 ^ (prefixWord ++ tailWord_3987570).sum := by decide
  have hdescent : baseEnd_3987570 < baseStart_3987570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987585 : List Nat := [1, 2, 4, 2, 3, 1, 2, 1, 2, 4]
def baseStart_3987585 : Nat := 118140960795 + 3987585 * 2 ^ 59
def prefixEnd_3987585 : Nat := 4983230072969 + 3 ^ 40 * 3987585 * 2
def baseEnd_3987585 : Nat := 1365031837105924192699291

theorem tailTrace_3987585 : CollatzResearch.WordTrace tailWord_3987585 prefixEnd_3987585 1365031837105924192699291 := by
  unfold tailWord_3987585
  simp only [CollatzResearch.WordTrace]
  refine ⟨145439173258668045143916209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96959448839112030095944139 145439173258668045143916209)
  ·
    refine ⟨109079379944001033857937157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145439173258668045143916209 109079379944001033857937157)
    ·
      refine ⟨20452383739500193848363217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109079379944001033857937157 20452383739500193848363217)
      ·
        refine ⟨15339287804625145386272413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20452383739500193848363217 15339287804625145386272413)
        ·
          refine ⟨5752232926734429519852155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15339287804625145386272413 5752232926734429519852155)
          ·
            refine ⟨8628349390101644279778233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5752232926734429519852155 8628349390101644279778233)
            ·
              refine ⟨6471262042576233209833675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8628349390101644279778233 6471262042576233209833675)
              ·
                refine ⟨9706893063864349814750513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6471262042576233209833675 9706893063864349814750513)
                ·
                  refine ⟨7280169797898262361062885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9706893063864349814750513 7280169797898262361062885)
                  ·
                    refine ⟨1365031837105924192699291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7280169797898262361062885 1365031837105924192699291)
                    ·
                      rfl

theorem cell22_3987585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_3987585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3987585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3987585 prefixEnd_3987585 := by exact prefixLift 3987585
  have htrace : WordTrace (prefixWord ++ tailWord_3987585) baseStart_3987585 baseEnd_3987585 := by
    simpa [prefixWord, tailWord_3987585, baseEnd_3987585] using wordTrace_append hprefix tailTrace_3987585
  have hstable : (prefixWord ++ tailWord_3987585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987585).length < 2 ^ (prefixWord ++ tailWord_3987585).sum := by decide
  have hdescent : baseEnd_3987585 < baseStart_3987585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987604 : List Nat := [2, 4, 2, 3, 1, 1, 2, 2, 2, 3]
def baseStart_3987604 : Nat := 118140960795 + 3987604 * 2 ^ 59
def prefixEnd_3987604 : Nat := 4983230072969 + 3 ^ 40 * 3987604 * 2
def baseEnd_3987604 : Nat := 1365038341194214476474233

theorem tailTrace_3987604 : CollatzResearch.WordTrace tailWord_3987604 prefixEnd_3987604 1365038341194214476474233 := by
  unfold tailWord_3987604
  simp only [CollatzResearch.WordTrace]
  refine ⟨72719933122799605694428933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96959910830399474259238577 72719933122799605694428933)
  ·
    refine ⟨13634987460524926067705425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72719933122799605694428933 13634987460524926067705425)
    ·
      refine ⟨10226240595393694550779069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13634987460524926067705425 10226240595393694550779069)
      ·
        refine ⟨3834840223272635456542151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10226240595393694550779069 3834840223272635456542151)
        ·
          refine ⟨5752260334908953184813227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3834840223272635456542151 5752260334908953184813227)
          ·
            refine ⟨8628390502363429777219841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5752260334908953184813227 8628390502363429777219841)
            ·
              refine ⟨6471292876772572332914881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8628390502363429777219841 6471292876772572332914881)
              ·
                refine ⟨4853469657579429249686161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6471292876772572332914881 4853469657579429249686161)
                ·
                  refine ⟨3640102243184571937264621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4853469657579429249686161 3640102243184571937264621)
                  ·
                    refine ⟨1365038341194214476474233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3640102243184571937264621 1365038341194214476474233)
                    ·
                      rfl

theorem cell22_3987604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_3987604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3987604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3987604 prefixEnd_3987604 := by exact prefixLift 3987604
  have htrace : WordTrace (prefixWord ++ tailWord_3987604) baseStart_3987604 baseEnd_3987604 := by
    simpa [prefixWord, tailWord_3987604, baseEnd_3987604] using wordTrace_append hprefix tailTrace_3987604
  have hstable : (prefixWord ++ tailWord_3987604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987604).length < 2 ^ (prefixWord ++ tailWord_3987604).sum := by decide
  have hdescent : baseEnd_3987604 < baseStart_3987604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987636 : List Nat := [2, 5, 3, 1, 1, 2, 1, 1, 2, 4]
def baseStart_3987636 : Nat := 118140960795 + 3987636 * 2 ^ 59
def prefixEnd_3987636 : Nat := 4983230072969 + 3 ^ 40 * 3987636 * 2
def baseEnd_3987636 : Nat := 1365049295448177059674135

theorem tailTrace_3987636 : CollatzResearch.WordTrace tailWord_3987636 prefixEnd_3987636 1365049295448177059674135 := by
  unfold tailWord_3987636
  simp only [CollatzResearch.WordTrace]
  refine ⟨72720516690741640427011381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96960688920988853902681841 72720516690741640427011381)
  ·
    refine ⟨6817548439757028790032317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72720516690741640427011381 6817548439757028790032317)
    ·
      refine ⟨2556580664908885796262119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6817548439757028790032317 2556580664908885796262119)
      ·
        refine ⟨3834870997363328694393179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2556580664908885796262119 3834870997363328694393179)
        ·
          refine ⟨5752306496044993041589769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3834870997363328694393179 5752306496044993041589769)
          ·
            refine ⟨4314229872033744781192327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5752306496044993041589769 4314229872033744781192327)
            ·
              refine ⟨6471344808050617171788491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4314229872033744781192327 6471344808050617171788491)
              ·
                refine ⟨9707017212075925757682737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6471344808050617171788491 9707017212075925757682737)
                ·
                  refine ⟨7280262909056944318262053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9707017212075925757682737 7280262909056944318262053)
                  ·
                    refine ⟨1365049295448177059674135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7280262909056944318262053 1365049295448177059674135)
                    ·
                      rfl

theorem cell22_3987636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_3987636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3987636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3987636 prefixEnd_3987636 := by exact prefixLift 3987636
  have htrace : WordTrace (prefixWord ++ tailWord_3987636) baseStart_3987636 baseEnd_3987636 := by
    simpa [prefixWord, tailWord_3987636, baseEnd_3987636] using wordTrace_append hprefix tailTrace_3987636
  have hstable : (prefixWord ++ tailWord_3987636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987636).length < 2 ^ (prefixWord ++ tailWord_3987636).sum := by decide
  have hdescent : baseEnd_3987636 < baseStart_3987636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987656 : List Nat := [2, 1, 3, 1, 2, 1, 1, 1, 10]
def baseStart_3987656 : Nat := 118140960795 + 3987656 * 2 ^ 59
def prefixEnd_3987656 : Nat := 4983230072969 + 3 ^ 40 * 3987656 * 2
def baseEnd_3987656 : Nat := 455018713952301224724691

theorem tailTrace_3987656 : CollatzResearch.WordTrace tailWord_3987656 prefixEnd_3987656 455018713952301224724691 := by
  unfold tailWord_3987656
  simp only [CollatzResearch.WordTrace]
  refine ⟨72720881420705412134875411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96961175227607216179833881 72720881420705412134875411)
  ·
    refine ⟨109081322131058118202313117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72720881420705412134875411 109081322131058118202313117)
    ·
      refine ⟨40905495799146794325867419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109081322131058118202313117 40905495799146794325867419)
      ·
        refine ⟨61358243698720191488801129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40905495799146794325867419 61358243698720191488801129)
        ·
          refine ⟨46018682774040143616600847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61358243698720191488801129 46018682774040143616600847)
          ·
            refine ⟨69028024161060215424901271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46018682774040143616600847 69028024161060215424901271)
            ·
              refine ⟨103542036241590323137351907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69028024161060215424901271 103542036241590323137351907)
              ·
                refine ⟨155313054362385484706027861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103542036241590323137351907 155313054362385484706027861)
                ·
                  refine ⟨455018713952301224724691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 155313054362385484706027861 455018713952301224724691)
                  ·
                    rfl

theorem cell22_3987656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 10].length) (baseStart_3987656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3987656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3987656 prefixEnd_3987656 := by exact prefixLift 3987656
  have htrace : WordTrace (prefixWord ++ tailWord_3987656) baseStart_3987656 baseEnd_3987656 := by
    simpa [prefixWord, tailWord_3987656, baseEnd_3987656] using wordTrace_append hprefix tailTrace_3987656
  have hstable : (prefixWord ++ tailWord_3987656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987656).length < 2 ^ (prefixWord ++ tailWord_3987656).sum := by decide
  have hdescent : baseEnd_3987656 < baseStart_3987656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987720 : List Nat := [2, 1, 3, 2, 3, 2, 1, 2, 2, 4]
def baseStart_3987720 : Nat := 118140960795 + 3987720 * 2 ^ 59
def prefixEnd_3987720 : Nat := 4983230072969 + 3 ^ 40 * 3987720 * 2
def baseEnd_3987720 : Nat := 1365078050364828840573877

theorem tailTrace_3987720 : CollatzResearch.WordTrace tailWord_3987720 prefixEnd_3987720 1365078050364828840573877 := by
  unfold tailWord_3987720
  simp only [CollatzResearch.WordTrace]
  refine ⟨72722048556589481600040307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96962731408785975466720409 72722048556589481600040307)
  ·
    refine ⟨109083072834884222400060461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72722048556589481600040307 109083072834884222400060461)
    ·
      refine ⟨40906152313081583400022673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109083072834884222400060461 40906152313081583400022673)
      ·
        refine ⟨30679614234811187550017005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40906152313081583400022673 30679614234811187550017005)
        ·
          refine ⟨11504855338054195331256377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30679614234811187550017005 11504855338054195331256377)
          ·
            refine ⟨8628641503540646498442283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11504855338054195331256377 8628641503540646498442283)
            ·
              refine ⟨12942962255310969747663425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8628641503540646498442283 12942962255310969747663425)
              ·
                refine ⟨9707221691483227310747569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12942962255310969747663425 9707221691483227310747569)
                ·
                  refine ⟨7280416268612420483060677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9707221691483227310747569 7280416268612420483060677)
                  ·
                    refine ⟨1365078050364828840573877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7280416268612420483060677 1365078050364828840573877)
                    ·
                      rfl

theorem cell22_3987720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 2, 2, 4].length) (baseStart_3987720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3987720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3987720 prefixEnd_3987720 := by exact prefixLift 3987720
  have htrace : WordTrace (prefixWord ++ tailWord_3987720) baseStart_3987720 baseEnd_3987720 := by
    simpa [prefixWord, tailWord_3987720, baseEnd_3987720] using wordTrace_append hprefix tailTrace_3987720
  have hstable : (prefixWord ++ tailWord_3987720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987720).length < 2 ^ (prefixWord ++ tailWord_3987720).sum := by decide
  have hdescent : baseEnd_3987720 < baseStart_3987720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987784 : List Nat := [2, 1, 3, 1, 1, 2, 6, 2, 1, 3]
def baseStart_3987784 : Nat := 118140960795 + 3987784 * 2 ^ 59
def prefixEnd_3987784 : Nat := 4983230072969 + 3 ^ 40 * 3987784 * 2
def baseEnd_3987784 : Nat := 1365099958872754006973681

theorem tailTrace_3987784 : CollatzResearch.WordTrace tailWord_3987784 prefixEnd_3987784 1365099958872754006973681 := by
  unfold tailWord_3987784
  simp only [CollatzResearch.WordTrace]
  refine ⟨72723215692473551065205203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96964287589964734753606937 72723215692473551065205203)
  ·
    refine ⟨109084823538710326597807805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72723215692473551065205203 109084823538710326597807805)
    ·
      refine ⟨40906808827016372474177927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109084823538710326597807805 40906808827016372474177927)
      ·
        refine ⟨61360213240524558711266891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40906808827016372474177927 61360213240524558711266891)
        ·
          refine ⟨92040319860786838066900337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61360213240524558711266891 92040319860786838066900337)
          ·
            refine ⟨69030239895590128550175253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92040319860786838066900337 69030239895590128550175253)
            ·
              refine ⟨3235792495105787275789465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 69030239895590128550175253 3235792495105787275789465)
              ·
                refine ⟨2426844371329340456842099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3235792495105787275789465 2426844371329340456842099)
                ·
                  refine ⟨3640266556994010685263149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2426844371329340456842099 3640266556994010685263149)
                  ·
                    refine ⟨1365099958872754006973681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3640266556994010685263149 1365099958872754006973681)
                    ·
                      rfl

theorem cell22_3987784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 6, 2, 1, 3].length) (baseStart_3987784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3987784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3987784 prefixEnd_3987784 := by exact prefixLift 3987784
  have htrace : WordTrace (prefixWord ++ tailWord_3987784) baseStart_3987784 baseEnd_3987784 := by
    simpa [prefixWord, tailWord_3987784, baseEnd_3987784] using wordTrace_append hprefix tailTrace_3987784
  have hstable : (prefixWord ++ tailWord_3987784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987784).length < 2 ^ (prefixWord ++ tailWord_3987784).sum := by decide
  have hdescent : baseEnd_3987784 < baseStart_3987784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987823 : List Nat := [1, 1, 2, 1, 3, 1, 2, 3, 3, 5]
def baseStart_3987823 : Nat := 118140960795 + 3987823 * 2 ^ 59
def prefixEnd_3987823 : Nat := 4983230072969 + 3 ^ 40 * 3987823 * 2
def baseEnd_3987823 : Nat := 1365113309369770905248561

theorem tailTrace_3987823 : CollatzResearch.WordTrace tailWord_3987823 prefixEnd_3987823 1365113309369770905248561 := by
  unfold tailWord_3987823
  simp only [CollatzResearch.WordTrace]
  refine ⟨145447853831805811791080123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96965235887870541194053415 145447853831805811791080123)
  ·
    refine ⟨218171780747708717686620185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145447853831805811791080123 218171780747708717686620185)
    ·
      refine ⟨163628835560781538264965139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218171780747708717686620185 163628835560781538264965139)
      ·
        refine ⟨245443253341172307397447709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163628835560781538264965139 245443253341172307397447709)
        ·
          refine ⟨92041220002939615274042891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 245443253341172307397447709 92041220002939615274042891)
          ·
            refine ⟨138061830004409422911064337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92041220002939615274042891 138061830004409422911064337)
            ·
              refine ⟨103546372503307067183298253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138061830004409422911064337 103546372503307067183298253)
              ·
                refine ⟨38829889688740150193736845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103546372503307067183298253 38829889688740150193736845)
                ·
                  refine ⟨14561208633277556322651317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38829889688740150193736845 14561208633277556322651317)
                  ·
                    refine ⟨1365113309369770905248561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14561208633277556322651317 1365113309369770905248561)
                    ·
                      rfl

theorem cell22_3987823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 3, 5].length) (baseStart_3987823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3987823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3987823 prefixEnd_3987823 := by exact prefixLift 3987823
  have htrace : WordTrace (prefixWord ++ tailWord_3987823) baseStart_3987823 baseEnd_3987823 := by
    simpa [prefixWord, tailWord_3987823, baseEnd_3987823] using wordTrace_append hprefix tailTrace_3987823
  have hstable : (prefixWord ++ tailWord_3987823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987823).length < 2 ^ (prefixWord ++ tailWord_3987823).sum := by decide
  have hdescent : baseEnd_3987823 < baseStart_3987823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987908 : List Nat := [2, 3, 3, 2, 2, 2, 2, 1, 2, 3]
def baseStart_3987908 : Nat := 118140960795 + 3987908 * 2 ^ 59
def prefixEnd_3987908 : Nat := 4983230072969 + 3 ^ 40 * 3987908 * 2
def baseEnd_3987908 : Nat := 1365142406606859016873301

theorem tailTrace_3987908 : CollatzResearch.WordTrace tailWord_3987908 prefixEnd_3987908 1365142406606859016873301 := by
  unfold tailWord_3987908
  simp only [CollatzResearch.WordTrace]
  refine ⟨72725477018248935653962189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96967302690998580871949585 72725477018248935653962189)
  ·
    refine ⟨27272053881843350870235821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72725477018248935653962189 27272053881843350870235821)
    ·
      refine ⟨10227020205691256576338433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27272053881843350870235821 10227020205691256576338433)
      ·
        refine ⟨7670265154268442432253825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10227020205691256576338433 7670265154268442432253825)
        ·
          refine ⟨5752698865701331824190369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7670265154268442432253825 5752698865701331824190369)
          ·
            refine ⟨4314524149275998868142777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5752698865701331824190369 4314524149275998868142777)
            ·
              refine ⟨3235893111956999151107083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4314524149275998868142777 3235893111956999151107083)
              ·
                refine ⟨4853839667935498726660625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3235893111956999151107083 4853839667935498726660625)
                ·
                  refine ⟨3640379750951624044995469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4853839667935498726660625 3640379750951624044995469)
                  ·
                    refine ⟨1365142406606859016873301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3640379750951624044995469 1365142406606859016873301)
                    ·
                      rfl

theorem cell22_3987908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_3987908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3987908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3987908 prefixEnd_3987908 := by exact prefixLift 3987908
  have htrace : WordTrace (prefixWord ++ tailWord_3987908) baseStart_3987908 baseEnd_3987908 := by
    simpa [prefixWord, tailWord_3987908, baseEnd_3987908] using wordTrace_append hprefix tailTrace_3987908
  have hstable : (prefixWord ++ tailWord_3987908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987908).length < 2 ^ (prefixWord ++ tailWord_3987908).sum := by decide
  have hdescent : baseEnd_3987908 < baseStart_3987908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987949 : List Nat := [1, 5, 1, 3, 1, 2, 2, 2, 5]
def baseStart_3987949 : Nat := 118140960795 + 3987949 * 2 ^ 59
def prefixEnd_3987949 : Nat := 4983230072969 + 3 ^ 40 * 3987949 * 2
def baseEnd_3987949 : Nat := 455052147248249525532725

theorem tailTrace_3987949 : CollatzResearch.WordTrace tailWord_3987949 prefixEnd_3987949 455052147248249525532725 := by
  unfold tailWord_3987949
  simp only [CollatzResearch.WordTrace]
  refine ⟨145452449429349335310166901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96968299619566223540111267 145452449429349335310166901)
  ·
    refine ⟨13636167134001500185328147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 145452449429349335310166901 13636167134001500185328147)
    ·
      refine ⟨20454250701002250277992221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13636167134001500185328147 20454250701002250277992221)
      ·
        refine ⟨7670344012875843854247083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20454250701002250277992221 7670344012875843854247083)
        ·
          refine ⟨11505516019313765781370625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7670344012875843854247083 11505516019313765781370625)
          ·
            refine ⟨8629137014485324336027969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11505516019313765781370625 8629137014485324336027969)
            ·
              refine ⟨6471852760863993252020977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8629137014485324336027969 6471852760863993252020977)
              ·
                refine ⟨4853889570647994939015733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6471852760863993252020977 4853889570647994939015733)
                ·
                  refine ⟨455052147248249525532725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4853889570647994939015733 455052147248249525532725)
                  ·
                    rfl

theorem cell22_3987949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 2, 5].length) (baseStart_3987949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3987949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3987949 prefixEnd_3987949 := by exact prefixLift 3987949
  have htrace : WordTrace (prefixWord ++ tailWord_3987949) baseStart_3987949 baseEnd_3987949 := by
    simpa [prefixWord, tailWord_3987949, baseEnd_3987949] using wordTrace_append hprefix tailTrace_3987949
  have hstable : (prefixWord ++ tailWord_3987949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987949).length < 2 ^ (prefixWord ++ tailWord_3987949).sum := by decide
  have hdescent : baseEnd_3987949 < baseStart_3987949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987960 : List Nat := [2, 1, 2, 1, 1, 4, 2, 3, 6]
def baseStart_3987960 : Nat := 118140960795 + 3987960 * 2 ^ 59
def prefixEnd_3987960 : Nat := 4983230072969 + 3 ^ 40 * 3987960 * 2
def baseEnd_3987960 : Nat := 455053402423182738191047

theorem tailTrace_3987960 : CollatzResearch.WordTrace tailWord_3987960 prefixEnd_3987960 455053402423182738191047 := by
  unfold tailWord_3987960
  simp only [CollatzResearch.WordTrace]
  refine ⟨72726425316154742094408667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96968567088206322792544889 72726425316154742094408667)
  ·
    refine ⟨109089637974232113141613001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72726425316154742094408667 109089637974232113141613001)
    ·
      refine ⟨81817228480674084856209751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109089637974232113141613001 81817228480674084856209751)
      ·
        refine ⟨122725842721011127284314627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81817228480674084856209751 122725842721011127284314627)
        ·
          refine ⟨184088764081516690926471941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122725842721011127284314627 184088764081516690926471941)
          ·
            refine ⟨34516643265284379548713489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 184088764081516690926471941 34516643265284379548713489)
            ·
              refine ⟨25887482448963284661535117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34516643265284379548713489 25887482448963284661535117)
              ·
                refine ⟨9707805918361231748075669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25887482448963284661535117 9707805918361231748075669)
                ·
                  refine ⟨455053402423182738191047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9707805918361231748075669 455053402423182738191047)
                  ·
                    rfl

theorem cell22_3987960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 3, 6].length) (baseStart_3987960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3987960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3987960 prefixEnd_3987960 := by exact prefixLift 3987960
  have htrace : WordTrace (prefixWord ++ tailWord_3987960) baseStart_3987960 baseEnd_3987960 := by
    simpa [prefixWord, tailWord_3987960, baseEnd_3987960] using wordTrace_append hprefix tailTrace_3987960
  have hstable : (prefixWord ++ tailWord_3987960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987960).length < 2 ^ (prefixWord ++ tailWord_3987960).sum := by decide
  have hdescent : baseEnd_3987960 < baseStart_3987960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987992 : List Nat := [2, 1, 2, 3, 3, 1, 2, 2, 1, 5]
def baseStart_3987992 : Nat := 118140960795 + 3987992 * 2 ^ 59
def prefixEnd_3987992 : Nat := 4983230072969 + 3 ^ 40 * 3987992 * 2
def baseEnd_3987992 : Nat := 1365171161523510797773043

theorem tailTrace_3987992 : CollatzResearch.WordTrace tailWord_3987992 prefixEnd_3987992 1365171161523510797773043 := by
  unfold tailWord_3987992
  simp only [CollatzResearch.WordTrace]
  refine ⟨72727008884096776826991115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96969345178795702435988153 72727008884096776826991115)
  ·
    refine ⟨109090513326145165240486673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72727008884096776826991115 109090513326145165240486673)
    ·
      refine ⟨81817884994608873930365005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109090513326145165240486673 81817884994608873930365005)
      ·
        refine ⟨30681706872978327723886877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81817884994608873930365005 30681706872978327723886877)
        ·
          refine ⟨11505640077366872896457579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30681706872978327723886877 11505640077366872896457579)
          ·
            refine ⟨17258460116050309344686369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11505640077366872896457579 17258460116050309344686369)
            ·
              refine ⟨12943845087037732008514777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17258460116050309344686369 12943845087037732008514777)
              ·
                refine ⟨9707883815278299006386083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12943845087037732008514777 9707883815278299006386083)
                ·
                  refine ⟨14561825722917448509579125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9707883815278299006386083 14561825722917448509579125)
                  ·
                    refine ⟨1365171161523510797773043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14561825722917448509579125 1365171161523510797773043)
                    ·
                      rfl

theorem cell22_3987992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 2, 1, 5].length) (baseStart_3987992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3987992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3987992 prefixEnd_3987992 := by exact prefixLift 3987992
  have htrace : WordTrace (prefixWord ++ tailWord_3987992) baseStart_3987992 baseEnd_3987992 := by
    simpa [prefixWord, tailWord_3987992, baseEnd_3987992] using wordTrace_append hprefix tailTrace_3987992
  have hstable : (prefixWord ++ tailWord_3987992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987992).length < 2 ^ (prefixWord ++ tailWord_3987992).sum := by decide
  have hdescent : baseEnd_3987992 < baseStart_3987992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987996 : List Nat := [2, 2, 3, 1, 2, 4, 2, 1, 1, 4]
def baseStart_3987996 : Nat := 118140960795 + 3987996 * 2 ^ 59
def prefixEnd_3987996 : Nat := 4983230072969 + 3 ^ 40 * 3987996 * 2
def baseEnd_3987996 : Nat := 1365172530805256120673031

theorem tailTrace_3987996 : CollatzResearch.WordTrace tailWord_3987996 prefixEnd_3987996 1365172530805256120673031 := by
  unfold tailWord_3987996
  simp only [CollatzResearch.WordTrace]
  refine ⟨72727081830089531168563921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96969442440119374891418561 72727081830089531168563921)
  ·
    refine ⟨54545311372567148376422941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72727081830089531168563921 54545311372567148376422941)
    ·
      refine ⟨20454491764712680641158603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54545311372567148376422941 20454491764712680641158603)
      ·
        refine ⟨30681737647069020961737905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20454491764712680641158603 30681737647069020961737905)
        ·
          refine ⟨23011303235301765721303429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30681737647069020961737905 23011303235301765721303429)
          ·
            refine ⟨4314619356619081072744393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23011303235301765721303429 4314619356619081072744393)
            ·
              refine ⟨3235964517464310804558295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4314619356619081072744393 3235964517464310804558295)
              ·
                refine ⟨4853946776196466206837443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3235964517464310804558295 4853946776196466206837443)
                ·
                  refine ⟨7280920164294699310256165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4853946776196466206837443 7280920164294699310256165)
                  ·
                    refine ⟨1365172530805256120673031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7280920164294699310256165 1365172530805256120673031)
                    ·
                      rfl

theorem cell22_3987996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 2, 1, 1, 4].length) (baseStart_3987996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3987996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3987996 prefixEnd_3987996 := by exact prefixLift 3987996
  have htrace : WordTrace (prefixWord ++ tailWord_3987996) baseStart_3987996 baseEnd_3987996 := by
    simpa [prefixWord, tailWord_3987996, baseEnd_3987996] using wordTrace_append hprefix tailTrace_3987996
  have hstable : (prefixWord ++ tailWord_3987996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987996).length < 2 ^ (prefixWord ++ tailWord_3987996).sum := by decide
  have hdescent : baseEnd_3987996 < baseStart_3987996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988026 : List Nat := [3, 1, 1, 1, 3, 4, 3, 1, 2, 3]
def baseStart_3988026 : Nat := 118140960795 + 3988026 * 2 ^ 59
def prefixEnd_3988026 : Nat := 4983230072969 + 3 ^ 40 * 3988026 * 2
def baseEnd_3988026 : Nat := 1365182800418346042422939

theorem tailTrace_3988026 : CollatzResearch.WordTrace tailWord_3988026 prefixEnd_3988026 1365182800418346042422939 := by
  unfold tailWord_3988026
  simp only [CollatzResearch.WordTrace]
  refine ⟨36363814462517594365179983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96970171900046918307146621 36363814462517594365179983)
  ·
    refine ⟨54545721693776391547769975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36363814462517594365179983 54545721693776391547769975)
    ·
      refine ⟨81818582540664587321654963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54545721693776391547769975 81818582540664587321654963)
      ·
        refine ⟨122727873810996880982482445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81818582540664587321654963 122727873810996880982482445)
        ·
          refine ⟨46022952679123830368430917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122727873810996880982482445 46022952679123830368430917)
          ·
            refine ⟨8629303627335718194080797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46022952679123830368430917 8629303627335718194080797)
            ·
              refine ⟨3235988860250894322780299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8629303627335718194080797 3235988860250894322780299)
              ·
                refine ⟨4853983290376341484170449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3235988860250894322780299 4853983290376341484170449)
                ·
                  refine ⟨3640487467782256113127837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4853983290376341484170449 3640487467782256113127837)
                  ·
                    refine ⟨1365182800418346042422939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3640487467782256113127837 1365182800418346042422939)
                    ·
                      rfl

theorem cell22_3988026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 3, 1, 2, 3].length) (baseStart_3988026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3988026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3988026 prefixEnd_3988026 := by exact prefixLift 3988026
  have htrace : WordTrace (prefixWord ++ tailWord_3988026) baseStart_3988026 baseEnd_3988026 := by
    simpa [prefixWord, tailWord_3988026, baseEnd_3988026] using wordTrace_append hprefix tailTrace_3988026
  have hstable : (prefixWord ++ tailWord_3988026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988026).length < 2 ^ (prefixWord ++ tailWord_3988026).sum := by decide
  have hdescent : baseEnd_3988026 < baseStart_3988026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988035 : List Nat := [1, 1, 1, 3, 1, 2, 1, 4, 2, 6]
def baseStart_3988035 : Nat := 118140960795 + 3988035 * 2 ^ 59
def prefixEnd_3988035 : Nat := 4983230072969 + 3 ^ 40 * 3988035 * 2
def baseEnd_3988035 : Nat := 1365185881302273018947911

theorem tailTrace_3988035 : CollatzResearch.WordTrace tailWord_3988035 prefixEnd_3988035 1365185881302273018947911 := by
  unfold tailWord_3988035
  simp only [CollatzResearch.WordTrace]
  refine ⟨145455586107037771997797559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96970390738025181331865039 145455586107037771997797559)
  ·
    refine ⟨218183379160556657996696339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145455586107037771997797559 218183379160556657996696339)
    ·
      refine ⟨327275068740834986995044509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218183379160556657996696339 327275068740834986995044509)
      ·
        refine ⟨122728150777813120123141691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 327275068740834986995044509 122728150777813120123141691)
        ·
          refine ⟨184092226166719680184712537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122728150777813120123141691 184092226166719680184712537)
          ·
            refine ⟨138069169625039760138534403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184092226166719680184712537 138069169625039760138534403)
            ·
              refine ⟨207103754437559640207801605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138069169625039760138534403 207103754437559640207801605)
              ·
                refine ⟨38831953957042432538962801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 207103754437559640207801605 38831953957042432538962801)
                ·
                  refine ⟨29123965467781824404222101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38831953957042432538962801 29123965467781824404222101)
                  ·
                    refine ⟨1365185881302273018947911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29123965467781824404222101 1365185881302273018947911)
                    ·
                      rfl

theorem cell22_3988035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 6].length) (baseStart_3988035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3988035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3988035 prefixEnd_3988035 := by exact prefixLift 3988035
  have htrace : WordTrace (prefixWord ++ tailWord_3988035) baseStart_3988035 baseEnd_3988035 := by
    simpa [prefixWord, tailWord_3988035, baseEnd_3988035] using wordTrace_append hprefix tailTrace_3988035
  have hstable : (prefixWord ++ tailWord_3988035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988035).length < 2 ^ (prefixWord ++ tailWord_3988035).sum := by decide
  have hdescent : baseEnd_3988035 < baseStart_3988035 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988039 : List Nat := [1, 1, 4, 1, 4, 3, 2, 6]
def baseStart_3988039 : Nat := 118140960795 + 3988039 * 2 ^ 59
def prefixEnd_3988039 : Nat := 4983230072969 + 3 ^ 40 * 3988039 * 2
def baseEnd_3988039 : Nat := 151687472287113149094211

theorem tailTrace_3988039 : CollatzResearch.WordTrace tailWord_3988039 prefixEnd_3988039 151687472287113149094211 := by
  unfold tailWord_3988039
  simp only [CollatzResearch.WordTrace]
  refine ⟨145455731999023280680943171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96970487999348853787295447 145455731999023280680943171)
  ·
    refine ⟨218183597998534921021414757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145455731999023280680943171 218183597998534921021414757)
    ·
      refine ⟨40909424624725297691515267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 218183597998534921021414757 40909424624725297691515267)
      ·
        refine ⟨61364136937087946537272901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40909424624725297691515267 61364136937087946537272901)
        ·
          refine ⟨11505775675703989975738669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61364136937087946537272901 11505775675703989975738669)
          ·
            refine ⟨4314665878388996240902001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11505775675703989975738669 4314665878388996240902001)
            ·
              refine ⟨3235999408791747180676501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4314665878388996240902001 3235999408791747180676501)
              ·
                refine ⟨151687472287113149094211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3235999408791747180676501 151687472287113149094211)
                ·
                  rfl

theorem cell22_3988039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 2, 6].length) (baseStart_3988039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3988039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3988039 prefixEnd_3988039 := by exact prefixLift 3988039
  have htrace : WordTrace (prefixWord ++ tailWord_3988039) baseStart_3988039 baseEnd_3988039 := by
    simpa [prefixWord, tailWord_3988039, baseEnd_3988039] using wordTrace_append hprefix tailTrace_3988039
  have hstable : (prefixWord ++ tailWord_3988039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988039).length < 2 ^ (prefixWord ++ tailWord_3988039).sum := by decide
  have hdescent : baseEnd_3988039 < baseStart_3988039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988062 : List Nat := [4, 4, 1, 2, 1, 1, 3, 2, 4]
def baseStart_3988062 : Nat := 118140960795 + 3988062 * 2 ^ 59
def prefixEnd_3988062 : Nat := 4983230072969 + 3 ^ 40 * 3988062 * 2
def baseEnd_3988062 : Nat := 455065041318017982840943

theorem tailTrace_3988062 : CollatzResearch.WordTrace tailWord_3988062 prefixEnd_3988062 455065041318017982840943 := by
  unfold tailWord_3988062
  simp only [CollatzResearch.WordTrace]
  refine ⟨18182071359742494451128805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96971047251959970406020293 18182071359742494451128805)
  ·
    refine ⟨3409138379951717709586651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18182071359742494451128805 3409138379951717709586651)
    ·
      refine ⟨5113707569927576564379977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3409138379951717709586651 5113707569927576564379977)
      ·
        refine ⟨3835280677445682423284983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5113707569927576564379977 3835280677445682423284983)
        ·
          refine ⟨5752921016168523634927475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3835280677445682423284983 5752921016168523634927475)
          ·
            refine ⟨8629381524252785452391213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5752921016168523634927475 8629381524252785452391213)
            ·
              refine ⟨3236018071594794544646705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8629381524252785452391213 3236018071594794544646705)
              ·
                refine ⟨2427013553696095908485029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3236018071594794544646705 2427013553696095908485029)
                ·
                  refine ⟨455065041318017982840943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2427013553696095908485029 455065041318017982840943)
                  ·
                    rfl

theorem cell22_3988062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_3988062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3988062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3988062 prefixEnd_3988062 := by exact prefixLift 3988062
  have htrace : WordTrace (prefixWord ++ tailWord_3988062) baseStart_3988062 baseEnd_3988062 := by
    simpa [prefixWord, tailWord_3988062, baseEnd_3988062] using wordTrace_append hprefix tailTrace_3988062
  have hstable : (prefixWord ++ tailWord_3988062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988062).length < 2 ^ (prefixWord ++ tailWord_3988062).sum := by decide
  have hdescent : baseEnd_3988062 < baseStart_3988062 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988067 : List Nat := [1, 1, 1, 5, 1, 2, 2, 4, 5]
def baseStart_3988067 : Nat := 118140960795 + 3988067 * 2 ^ 59
def prefixEnd_3988067 : Nat := 4983230072969 + 3 ^ 40 * 3988067 * 2
def baseEnd_3988067 : Nat := 455065611852078534049271

theorem tailTrace_3988067 : CollatzResearch.WordTrace tailWord_3988067 prefixEnd_3988067 455065611852078534049271 := by
  unfold tailWord_3988067
  simp only [CollatzResearch.WordTrace]
  refine ⟨145456753242921841462962455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96971168828614560975308303 145456753242921841462962455)
  ·
    refine ⟨218185129864382762194443683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145456753242921841462962455 218185129864382762194443683)
    ·
      refine ⟨327277694796574143291665525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218185129864382762194443683 327277694796574143291665525)
      ·
        refine ⟨30682283887178825933593643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 327277694796574143291665525 30682283887178825933593643)
        ·
          refine ⟨46023425830768238900390465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30682283887178825933593643 46023425830768238900390465)
          ·
            refine ⟨34517569373076179175292849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46023425830768238900390465 34517569373076179175292849)
            ·
              refine ⟨25888177029807134381469637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34517569373076179175292849 25888177029807134381469637)
              ·
                refine ⟨4854033193088837696525557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25888177029807134381469637 4854033193088837696525557)
                ·
                  refine ⟨455065611852078534049271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4854033193088837696525557 455065611852078534049271)
                  ·
                    rfl

theorem cell22_3988067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 4, 5].length) (baseStart_3988067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3988067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3988067 prefixEnd_3988067 := by exact prefixLift 3988067
  have htrace : WordTrace (prefixWord ++ tailWord_3988067) baseStart_3988067 baseEnd_3988067 := by
    simpa [prefixWord, tailWord_3988067, baseEnd_3988067] using wordTrace_append hprefix tailTrace_3988067
  have hstable : (prefixWord ++ tailWord_3988067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988067).length < 2 ^ (prefixWord ++ tailWord_3988067).sum := by decide
  have hdescent : baseEnd_3988067 < baseStart_3988067 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988122 : List Nat := [3, 1, 1, 6, 1, 2, 2, 2, 1, 3]
def baseStart_3988122 : Nat := 118140960795 + 3988122 * 2 ^ 59
def prefixEnd_3988122 : Nat := 4983230072969 + 3 ^ 40 * 3988122 * 2
def baseEnd_3988122 : Nat := 1365215663180233792022645

theorem tailTrace_3988122 : CollatzResearch.WordTrace tailWord_3988122 prefixEnd_3988122 1365215663180233792022645 := by
  unfold tailWord_3988122
  simp only [CollatzResearch.WordTrace]
  refine ⟨36364689814430646464053655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96972506171815057237476413 36364689814430646464053655)
  ·
    refine ⟨54547034721645969696080483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36364689814430646464053655 54547034721645969696080483)
    ·
      refine ⟨81820552082468954544120725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54547034721645969696080483 81820552082468954544120725)
      ·
        refine ⟨3835338378865732244255659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 81820552082468954544120725 3835338378865732244255659)
        ·
          refine ⟨5753007568298598366383489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3835338378865732244255659 5753007568298598366383489)
          ·
            refine ⟨4314755676223948774787617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5753007568298598366383489 4314755676223948774787617)
            ·
              refine ⟨3236066757167961581090713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4314755676223948774787617 3236066757167961581090713)
              ·
                refine ⟨2427050067875971185818035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3236066757167961581090713 2427050067875971185818035)
                ·
                  refine ⟨3640575101813956778727053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2427050067875971185818035 3640575101813956778727053)
                  ·
                    refine ⟨1365215663180233792022645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3640575101813956778727053 1365215663180233792022645)
                    ·
                      rfl

theorem cell22_3988122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 2, 2, 1, 3].length) (baseStart_3988122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3988122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3988122 prefixEnd_3988122 := by exact prefixLift 3988122
  have htrace : WordTrace (prefixWord ++ tailWord_3988122) baseStart_3988122 baseEnd_3988122 := by
    simpa [prefixWord, tailWord_3988122, baseEnd_3988122] using wordTrace_append hprefix tailTrace_3988122
  have hstable : (prefixWord ++ tailWord_3988122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988122).length < 2 ^ (prefixWord ++ tailWord_3988122).sum := by decide
  have hdescent : baseEnd_3988122 < baseStart_3988122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988159 : List Nat := [1, 1, 2, 2, 2, 4, 3, 1, 2, 4]
def baseStart_3988159 : Nat := 118140960795 + 3988159 * 2 ^ 59
def prefixEnd_3988159 : Nat := 4983230072969 + 3 ^ 40 * 3988159 * 2
def baseEnd_3988159 : Nat := 1365228329036378028847531

theorem tailTrace_3988159 : CollatzResearch.WordTrace tailWord_3988159 prefixEnd_3988159 1365228329036378028847531 := by
  unfold tailWord_3988159
  simp only [CollatzResearch.WordTrace]
  refine ⟨145460108758588541175311531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96973405839059027450207687 145460108758588541175311531)
  ·
    refine ⟨218190163137882811762967297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145460108758588541175311531 218190163137882811762967297)
    ·
      refine ⟨163642622353412108822225473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218190163137882811762967297 163642622353412108822225473)
      ·
        refine ⟨122731966765059081616669105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163642622353412108822225473 122731966765059081616669105)
        ·
          refine ⟨92048975073794311212501829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122731966765059081616669105 92048975073794311212501829)
          ·
            refine ⟨17259182826336433352344093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92048975073794311212501829 17259182826336433352344093)
            ·
              refine ⟨6472193559876162507129035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17259182826336433352344093 6472193559876162507129035)
              ·
                refine ⟨9708290339814243760693553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6472193559876162507129035 9708290339814243760693553)
                ·
                  refine ⟨7281217754860682820520165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9708290339814243760693553 7281217754860682820520165)
                  ·
                    refine ⟨1365228329036378028847531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7281217754860682820520165 1365228329036378028847531)
                    ·
                      rfl

theorem cell22_3988159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 1, 2, 4].length) (baseStart_3988159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3988159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3988159 prefixEnd_3988159 := by exact prefixLift 3988159
  have htrace : WordTrace (prefixWord ++ tailWord_3988159) baseStart_3988159 baseEnd_3988159 := by
    simpa [prefixWord, tailWord_3988159, baseEnd_3988159] using wordTrace_append hprefix tailTrace_3988159
  have hstable : (prefixWord ++ tailWord_3988159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988159).length < 2 ^ (prefixWord ++ tailWord_3988159).sum := by decide
  have hdescent : baseEnd_3988159 < baseStart_3988159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988206 : List Nat := [4, 1, 2, 1, 1, 3, 2, 2, 3, 3]
def baseStart_3988206 : Nat := 118140960795 + 3988206 * 2 ^ 59
def prefixEnd_3988206 : Nat := 4983230072969 + 3 ^ 40 * 3988206 * 2
def baseEnd_3988206 : Nat := 1365244418096885572922387

theorem tailTrace_3988206 : CollatzResearch.WordTrace tailWord_3988206 prefixEnd_3988206 1365244418096885572922387 := by
  unfold tailWord_3988206
  simp only [CollatzResearch.WordTrace]
  refine ⟨18182727873677283525284059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96974548659612178801514981 18182727873677283525284059)
  ·
    refine ⟨27274091810515925287926089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18182727873677283525284059 27274091810515925287926089)
    ·
      refine ⟨20455568857886943965944567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27274091810515925287926089 20455568857886943965944567)
      ·
        refine ⟨30683353286830415948916851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20455568857886943965944567 30683353286830415948916851)
        ·
          refine ⟨46025029930245623923375277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30683353286830415948916851 46025029930245623923375277)
          ·
            refine ⟨17259386223842108971265729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46025029930245623923375277 17259386223842108971265729)
            ·
              refine ⟨12944539667881581728449297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17259386223842108971265729 12944539667881581728449297)
              ·
                refine ⟨9708404750911186296336973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12944539667881581728449297 9708404750911186296336973)
                ·
                  refine ⟨3640651781591694861126365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9708404750911186296336973 3640651781591694861126365)
                  ·
                    refine ⟨1365244418096885572922387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3640651781591694861126365 1365244418096885572922387)
                    ·
                      rfl

theorem cell22_3988206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 2, 3, 3].length) (baseStart_3988206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3988206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3988206 prefixEnd_3988206 := by exact prefixLift 3988206
  have htrace : WordTrace (prefixWord ++ tailWord_3988206) baseStart_3988206 baseEnd_3988206 := by
    simpa [prefixWord, tailWord_3988206, baseEnd_3988206] using wordTrace_append hprefix tailTrace_3988206
  have hstable : (prefixWord ++ tailWord_3988206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988206).length < 2 ^ (prefixWord ++ tailWord_3988206).sum := by decide
  have hdescent : baseEnd_3988206 < baseStart_3988206 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988217 : List Nat := [1, 2, 1, 3, 1, 1, 1, 4, 1, 7]
def baseStart_3988217 : Nat := 118140960795 + 3988217 * 2 ^ 59
def prefixEnd_3988217 : Nat := 4983230072969 + 3 ^ 40 * 3988217 * 2
def baseEnd_3988217 : Nat := 1365248183621685210897353

theorem tailTrace_3988217 : CollatzResearch.WordTrace tailWord_3988217 prefixEnd_3988217 1365248183621685210897353 := by
  unfold tailWord_3988217
  simp only [CollatzResearch.WordTrace]
  refine ⟨145462224192378417080922905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96974816128252278053948603 145462224192378417080922905)
  ·
    refine ⟨109096668144283812810692179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145462224192378417080922905 109096668144283812810692179)
    ·
      refine ⟨163645002216425719216038269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109096668144283812810692179 163645002216425719216038269)
      ·
        refine ⟨61366875831159644706014351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163645002216425719216038269 61366875831159644706014351)
        ·
          refine ⟨92050313746739467059021527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61366875831159644706014351 92050313746739467059021527)
          ·
            refine ⟨138075470620109200588532291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92050313746739467059021527 138075470620109200588532291)
            ·
              refine ⟨207113205930163800882798437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138075470620109200588532291 207113205930163800882798437)
              ·
                refine ⟨38833726111905712665524707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 207113205930163800882798437 38833726111905712665524707)
                ·
                  refine ⟨58250589167858568998287061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38833726111905712665524707 58250589167858568998287061)
                  ·
                    refine ⟨1365248183621685210897353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58250589167858568998287061 1365248183621685210897353)
                    ·
                      rfl

theorem cell22_3988217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 7].length) (baseStart_3988217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3988217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3988217 prefixEnd_3988217 := by exact prefixLift 3988217
  have htrace : WordTrace (prefixWord ++ tailWord_3988217) baseStart_3988217 baseEnd_3988217 := by
    simpa [prefixWord, tailWord_3988217, baseEnd_3988217] using wordTrace_append hprefix tailTrace_3988217
  have hstable : (prefixWord ++ tailWord_3988217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988217).length < 2 ^ (prefixWord ++ tailWord_3988217).sum := by decide
  have hdescent : baseEnd_3988217 < baseStart_3988217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988253 : List Nat := [1, 4, 2, 4, 1, 1, 1, 3, 5]
def baseStart_3988253 : Nat := 118140960795 + 3988253 * 2 ^ 59
def prefixEnd_3988253 : Nat := 4983230072969 + 3 ^ 40 * 3988253 * 2
def baseEnd_3988253 : Nat := 455086835719131038999081

theorem tailTrace_3988253 : CollatzResearch.WordTrace tailWord_3988253 prefixEnd_3988253 455086835719131038999081 := by
  unfold tailWord_3988253
  simp only [CollatzResearch.WordTrace]
  refine ⟨145463537220247995229233413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96975691480165330152822275 145463537220247995229233413)
  ·
    refine ⟨27274413228796499105481265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145463537220247995229233413 27274413228796499105481265)
    ·
      refine ⟨20455809921597374329110949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27274413228796499105481265 20455809921597374329110949)
      ·
        refine ⟨3835464360299507686708303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20455809921597374329110949 3835464360299507686708303)
        ·
          refine ⟨5753196540449261530062455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3835464360299507686708303 5753196540449261530062455)
          ·
            refine ⟨8629794810673892295093683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5753196540449261530062455 8629794810673892295093683)
            ·
              refine ⟨12944692216010838442640525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8629794810673892295093683 12944692216010838442640525)
              ·
                refine ⟨4854259581004064415990197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12944692216010838442640525 4854259581004064415990197)
                ·
                  refine ⟨455086835719131038999081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4854259581004064415990197 455086835719131038999081)
                  ·
                    rfl

theorem cell22_3988253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 3, 5].length) (baseStart_3988253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3988253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3988253 prefixEnd_3988253 := by exact prefixLift 3988253
  have htrace : WordTrace (prefixWord ++ tailWord_3988253) baseStart_3988253 baseEnd_3988253 := by
    simpa [prefixWord, tailWord_3988253, baseEnd_3988253] using wordTrace_append hprefix tailTrace_3988253
  have hstable : (prefixWord ++ tailWord_3988253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988253).length < 2 ^ (prefixWord ++ tailWord_3988253).sum := by decide
  have hdescent : baseEnd_3988253 < baseStart_3988253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988264 : List Nat := [2, 1, 5, 1, 1, 1, 2, 1, 8]
def baseStart_3988264 : Nat := 118140960795 + 3988264 * 2 ^ 59
def prefixEnd_3988264 : Nat := 4983230072969 + 3 ^ 40 * 3988264 * 2
def baseEnd_3988264 : Nat := 455088090894064251657403

theorem tailTrace_3988264 : CollatzResearch.WordTrace tailWord_3988264 prefixEnd_3988264 455088090894064251657403 := by
  unfold tailWord_3988264
  simp only [CollatzResearch.WordTrace]
  refine ⟨72731969211604072053941923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96975958948805429405255897 72731969211604072053941923)
  ·
    refine ⟨109097953817406108080912885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72731969211604072053941923 109097953817406108080912885)
    ·
      refine ⟨10227933170381822632585583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 109097953817406108080912885 10227933170381822632585583)
      ·
        refine ⟨15341899755572733948878375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10227933170381822632585583 15341899755572733948878375)
        ·
          refine ⟨23012849633359100923317563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15341899755572733948878375 23012849633359100923317563)
          ·
            refine ⟨34519274450038651384976345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23012849633359100923317563 34519274450038651384976345)
            ·
              refine ⟨25889455837528988538732259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34519274450038651384976345 25889455837528988538732259)
              ·
                refine ⟨38834183756293482808098389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25889455837528988538732259 38834183756293482808098389)
                ·
                  refine ⟨455088090894064251657403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38834183756293482808098389 455088090894064251657403)
                  ·
                    rfl

theorem cell22_3988264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 8].length) (baseStart_3988264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3988264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3988264 prefixEnd_3988264 := by exact prefixLift 3988264
  have htrace : WordTrace (prefixWord ++ tailWord_3988264) baseStart_3988264 baseEnd_3988264 := by
    simpa [prefixWord, tailWord_3988264, baseEnd_3988264] using wordTrace_append hprefix tailTrace_3988264
  have hstable : (prefixWord ++ tailWord_3988264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988264).length < 2 ^ (prefixWord ++ tailWord_3988264).sum := by decide
  have hdescent : baseEnd_3988264 < baseStart_3988264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988279 : List Nat := [1, 1, 3, 1, 2, 1, 5, 2, 1, 5]
def baseStart_3988279 : Nat := 118140960795 + 3988279 * 2 ^ 59
def prefixEnd_3988279 : Nat := 4983230072969 + 3 ^ 40 * 3988279 * 2
def baseEnd_3988279 : Nat := 1365269407488737715847163

theorem tailTrace_3988279 : CollatzResearch.WordTrace tailWord_3988279 prefixEnd_3988279 1365269407488737715847163 := by
  unfold tailWord_3988279
  simp only [CollatzResearch.WordTrace]
  refine ⟨145464485518153801669679891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96976323678769201113119927 145464485518153801669679891)
  ·
    refine ⟨218196728277230702504519837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145464485518153801669679891 218196728277230702504519837)
    ·
      refine ⟨81823773103961513439194939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218196728277230702504519837 81823773103961513439194939)
      ·
        refine ⟨122735659655942270158792409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81823773103961513439194939 122735659655942270158792409)
        ·
          refine ⟨92051744741956702619094307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122735659655942270158792409 92051744741956702619094307)
          ·
            refine ⟨138077617112935053928641461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92051744741956702619094307 138077617112935053928641461)
            ·
              refine ⟨12944776604337661305810137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 138077617112935053928641461 12944776604337661305810137)
              ·
                refine ⟨9708582453253245979357603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12944776604337661305810137 9708582453253245979357603)
                ·
                  refine ⟨14562873679879868969036405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9708582453253245979357603 14562873679879868969036405)
                  ·
                    refine ⟨1365269407488737715847163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14562873679879868969036405 1365269407488737715847163)
                    ·
                      rfl

theorem cell22_3988279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 2, 1, 5].length) (baseStart_3988279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3988279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3988279 prefixEnd_3988279 := by exact prefixLift 3988279
  have htrace : WordTrace (prefixWord ++ tailWord_3988279) baseStart_3988279 baseEnd_3988279 := by
    simpa [prefixWord, tailWord_3988279, baseEnd_3988279] using wordTrace_append hprefix tailTrace_3988279
  have hstable : (prefixWord ++ tailWord_3988279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988279).length < 2 ^ (prefixWord ++ tailWord_3988279).sum := by decide
  have hdescent : baseEnd_3988279 < baseStart_3988279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988328 : List Nat := [2, 1, 4, 2, 1, 4, 1, 1, 2, 4]
def baseStart_3988328 : Nat := 118140960795 + 3988328 * 2 ^ 59
def prefixEnd_3988328 : Nat := 4983230072969 + 3 ^ 40 * 3988328 * 2
def baseEnd_3988328 : Nat := 1365286181190117921372013

theorem tailTrace_3988328 : CollatzResearch.WordTrace tailWord_3988328 prefixEnd_3988328 1365286181190117921372013 := by
  unfold tailWord_3988328
  simp only [CollatzResearch.WordTrace]
  refine ⟨72733136347488141519106819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96977515129984188692142425 72733136347488141519106819)
  ·
    refine ⟨109099704521232212278660229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72733136347488141519106819 109099704521232212278660229)
    ·
      refine ⟨20456194597731039802248793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109099704521232212278660229 20456194597731039802248793)
      ·
        refine ⟨15342145948298279851686595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20456194597731039802248793 15342145948298279851686595)
        ·
          refine ⟨23013218922447419777529893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15342145948298279851686595 23013218922447419777529893)
          ·
            refine ⟨4314978547958891208286855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23013218922447419777529893 4314978547958891208286855)
            ·
              refine ⟨6472467821938336812430283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4314978547958891208286855 6472467821938336812430283)
              ·
                refine ⟨9708701732907505218645425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6472467821938336812430283 9708701732907505218645425)
                ·
                  refine ⟨7281526299680628913984069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9708701732907505218645425 7281526299680628913984069)
                  ·
                    refine ⟨1365286181190117921372013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7281526299680628913984069 1365286181190117921372013)
                    ·
                      rfl

theorem cell22_3988328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 1, 2, 4].length) (baseStart_3988328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3988328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3988328 prefixEnd_3988328 := by exact prefixLift 3988328
  have htrace : WordTrace (prefixWord ++ tailWord_3988328) baseStart_3988328 baseEnd_3988328 := by
    simpa [prefixWord, tailWord_3988328, baseEnd_3988328] using wordTrace_append hprefix tailTrace_3988328
  have hstable : (prefixWord ++ tailWord_3988328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988328).length < 2 ^ (prefixWord ++ tailWord_3988328).sum := by decide
  have hdescent : baseEnd_3988328 < baseStart_3988328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988416 : List Nat := [2, 1, 1, 2, 3, 3, 3, 1, 6]
def baseStart_3988416 : Nat := 118140960795 + 3988416 * 2 ^ 59
def prefixEnd_3988416 : Nat := 4983230072969 + 3 ^ 40 * 3988416 * 2
def baseEnd_3988416 : Nat := 455105435129505008390581

theorem tailTrace_3988416 : CollatzResearch.WordTrace tailWord_3988416 prefixEnd_3988416 455105435129505008390581 := by
  unfold tailWord_3988416
  simp only [CollatzResearch.WordTrace]
  refine ⟨72734741159328737033708551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96979654879104982711611401 72734741159328737033708551)
  ·
    refine ⟨109102111738993105550562827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72734741159328737033708551 109102111738993105550562827)
    ·
      refine ⟨163653167608489658325844241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109102111738993105550562827 163653167608489658325844241)
      ·
        refine ⟨122739875706367243744383181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163653167608489658325844241 122739875706367243744383181)
        ·
          refine ⟨46027453389887716404143693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122739875706367243744383181 46027453389887716404143693)
          ·
            refine ⟨17260295021207893651553885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46027453389887716404143693 17260295021207893651553885)
            ·
              refine ⟨6472610632952960119332707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17260295021207893651553885 6472610632952960119332707)
              ·
                refine ⟨9708915949429440178999061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6472610632952960119332707 9708915949429440178999061)
                ·
                  refine ⟨455105435129505008390581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9708915949429440178999061 455105435129505008390581)
                  ·
                    rfl

theorem cell22_3988416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 1, 6].length) (baseStart_3988416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3988416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3988416 prefixEnd_3988416 := by exact prefixLift 3988416
  have htrace : WordTrace (prefixWord ++ tailWord_3988416) baseStart_3988416 baseEnd_3988416 := by
    simpa [prefixWord, tailWord_3988416, baseEnd_3988416] using wordTrace_append hprefix tailTrace_3988416
  have hstable : (prefixWord ++ tailWord_3988416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988416).length < 2 ^ (prefixWord ++ tailWord_3988416).sum := by decide
  have hdescent : baseEnd_3988416 < baseStart_3988416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988465 : List Nat := [1, 2, 2, 2, 4, 2, 2, 2, 2, 3]
def baseStart_3988465 : Nat := 118140960795 + 3988465 * 2 ^ 59
def prefixEnd_3988465 : Nat := 4983230072969 + 3 ^ 40 * 3988465 * 2
def baseEnd_3988465 : Nat := 1365333079089895230696593

theorem tailTrace_3988465 : CollatzResearch.WordTrace tailWord_3988465 prefixEnd_3988465 1365333079089895230696593 := by
  unfold tailWord_3988465
  simp only [CollatzResearch.WordTrace]
  refine ⟨145471269495479955435950849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96980846330319970290633899 145471269495479955435950849)
  ·
    refine ⟨109103452121609966576963137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145471269495479955435950849 109103452121609966576963137)
    ·
      refine ⟨81827589091207474932722353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109103452121609966576963137 81827589091207474932722353)
      ·
        refine ⟨61370691818405606199541765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81827589091207474932722353 61370691818405606199541765)
        ·
          refine ⟨11507004715951051162414081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61370691818405606199541765 11507004715951051162414081)
          ·
            refine ⟨8630253536963288371810561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11507004715951051162414081 8630253536963288371810561)
            ·
              refine ⟨6472690152722466278857921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8630253536963288371810561 6472690152722466278857921)
              ·
                refine ⟨4854517614541849709143441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6472690152722466278857921 4854517614541849709143441)
                ·
                  refine ⟨3640888210906387281857581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4854517614541849709143441 3640888210906387281857581)
                  ·
                    refine ⟨1365333079089895230696593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3640888210906387281857581 1365333079089895230696593)
                    ·
                      rfl

theorem cell22_3988465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 2, 2, 3].length) (baseStart_3988465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3988465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3988465 prefixEnd_3988465 := by exact prefixLift 3988465
  have htrace : WordTrace (prefixWord ++ tailWord_3988465) baseStart_3988465 baseEnd_3988465 := by
    simpa [prefixWord, tailWord_3988465, baseEnd_3988465] using wordTrace_append hprefix tailTrace_3988465
  have hstable : (prefixWord ++ tailWord_3988465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988465).length < 2 ^ (prefixWord ++ tailWord_3988465).sum := by decide
  have hdescent : baseEnd_3988465 < baseStart_3988465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988482 : List Nat := [3, 4, 1, 3, 1, 1, 2, 1, 1, 5]
def baseStart_3988482 : Nat := 118140960795 + 3988482 * 2 ^ 59
def prefixEnd_3988482 : Nat := 4983230072969 + 3 ^ 40 * 3988482 * 2
def baseEnd_3988482 : Nat := 1365338898537312853021541

theorem tailTrace_3988482 : CollatzResearch.WordTrace tailWord_3988482 prefixEnd_3988482 1365338898537312853021541 := by
  unfold tailWord_3988482
  simp only [CollatzResearch.WordTrace]
  refine ⟨36367972384104591834829925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96981259690945578226213133 36367972384104591834829925)
  ·
    refine ⟨6818994822019610969030611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36367972384104591834829925 6818994822019610969030611)
    ·
      refine ⟨10228492233029416453545917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6818994822019610969030611 10228492233029416453545917)
      ·
        refine ⟨3835684587386031170079719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10228492233029416453545917 3835684587386031170079719)
        ·
          refine ⟨5753526881079046755119579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3835684587386031170079719 5753526881079046755119579)
          ·
            refine ⟨8630290321618570132679369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5753526881079046755119579 8630290321618570132679369)
            ·
              refine ⟨6472717741213927599509527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8630290321618570132679369 6472717741213927599509527)
              ·
                refine ⟨9709076611820891399264291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6472717741213927599509527 9709076611820891399264291)
                ·
                  refine ⟨14563614917731337098896437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9709076611820891399264291 14563614917731337098896437)
                  ·
                    refine ⟨1365338898537312853021541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14563614917731337098896437 1365338898537312853021541)
                    ·
                      rfl

theorem cell22_3988482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_3988482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3988482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3988482 prefixEnd_3988482 := by exact prefixLift 3988482
  have htrace : WordTrace (prefixWord ++ tailWord_3988482) baseStart_3988482 baseEnd_3988482 := by
    simpa [prefixWord, tailWord_3988482, baseEnd_3988482] using wordTrace_append hprefix tailTrace_3988482
  have hstable : (prefixWord ++ tailWord_3988482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988482).length < 2 ^ (prefixWord ++ tailWord_3988482).sum := by decide
  have hdescent : baseEnd_3988482 < baseStart_3988482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988506 : List Nat := [3, 1, 1, 3, 1, 2, 2, 2, 7]
def baseStart_3988506 : Nat := 118140960795 + 3988506 * 2 ^ 59
def prefixEnd_3988506 : Nat := 4983230072969 + 3 ^ 40 * 3988506 * 2
def baseEnd_3988506 : Nat := 455115704742594930140489

theorem tailTrace_3988506 : CollatzResearch.WordTrace tailWord_3988506 prefixEnd_3988506 455115704742594930140489 := by
  unfold tailWord_3988506
  simp only [CollatzResearch.WordTrace]
  refine ⟨36368191222082854859548343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96981843258887612958795581 36368191222082854859548343)
  ·
    refine ⟨54552286833124282289322515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36368191222082854859548343 54552286833124282289322515)
    ·
      refine ⟨81828430249686423433983773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54552286833124282289322515 81828430249686423433983773)
      ·
        refine ⟨30685661343632408787743915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81828430249686423433983773 30685661343632408787743915)
        ·
          refine ⟨46028492015448613181615873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30685661343632408787743915 46028492015448613181615873)
          ·
            refine ⟨34521369011586459886211905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46028492015448613181615873 34521369011586459886211905)
            ·
              refine ⟨25891026758689844914658929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34521369011586459886211905 25891026758689844914658929)
              ·
                refine ⟨19418270069017383685994197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25891026758689844914658929 19418270069017383685994197)
                ·
                  refine ⟨455115704742594930140489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19418270069017383685994197 455115704742594930140489)
                  ·
                    rfl

theorem cell22_3988506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 7].length) (baseStart_3988506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3988506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3988506 prefixEnd_3988506 := by exact prefixLift 3988506
  have htrace : WordTrace (prefixWord ++ tailWord_3988506) baseStart_3988506 baseEnd_3988506 := by
    simpa [prefixWord, tailWord_3988506, baseEnd_3988506] using wordTrace_append hprefix tailTrace_3988506
  have hstable : (prefixWord ++ tailWord_3988506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988506).length < 2 ^ (prefixWord ++ tailWord_3988506).sum := by decide
  have hdescent : baseEnd_3988506 < baseStart_3988506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988540 : List Nat := [2, 2, 2, 2, 2, 3, 3, 1, 5]
def baseStart_3988540 : Nat := 118140960795 + 3988540 * 2 ^ 59
def prefixEnd_3988540 : Nat := 4983230072969 + 3 ^ 40 * 3988540 * 2
def baseEnd_3988540 : Nat := 455119584374206678357121

theorem tailTrace_3988540 : CollatzResearch.WordTrace tailWord_3988540 prefixEnd_3988540 455119584374206678357121 := by
  unfold tailWord_3988540
  simp only [CollatzResearch.WordTrace]
  refine ⟨72737002485104121622465537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96982669980138828829954049 72737002485104121622465537)
  ·
    refine ⟨54552751863828091216849153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72737002485104121622465537 54552751863828091216849153)
    ·
      refine ⟨40914563897871068412636865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54552751863828091216849153 40914563897871068412636865)
      ·
        refine ⟨30685922923403301309477649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40914563897871068412636865 30685922923403301309477649)
        ·
          refine ⟨23014442192552475982108237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30685922923403301309477649 23014442192552475982108237)
          ·
            refine ⟨8630415822207178493290589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23014442192552475982108237 8630415822207178493290589)
            ·
              refine ⟨3236405933327691934983971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8630415822207178493290589 3236405933327691934983971)
              ·
                refine ⟨4854608899991537902475957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3236405933327691934983971 4854608899991537902475957)
                ·
                  refine ⟨455119584374206678357121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4854608899991537902475957 455119584374206678357121)
                  ·
                    rfl

theorem cell22_3988540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 3, 1, 5].length) (baseStart_3988540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3988540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3988540 prefixEnd_3988540 := by exact prefixLift 3988540
  have htrace : WordTrace (prefixWord ++ tailWord_3988540) baseStart_3988540 baseEnd_3988540 := by
    simpa [prefixWord, tailWord_3988540, baseEnd_3988540] using wordTrace_append hprefix tailTrace_3988540
  have hstable : (prefixWord ++ tailWord_3988540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988540).length < 2 ^ (prefixWord ++ tailWord_3988540).sum := by decide
  have hdescent : baseEnd_3988540 < baseStart_3988540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988692 : List Nat := [2, 4, 1, 4, 1, 1, 1, 1, 7]
def baseStart_3988692 : Nat := 118140960795 + 3988692 * 2 ^ 59
def prefixEnd_3988692 : Nat := 4983230072969 + 3 ^ 40 * 3988692 * 2
def baseEnd_3988692 : Nat := 455136928609647435090299

theorem tailTrace_3988692 : CollatzResearch.WordTrace tailWord_3988692 prefixEnd_3988692 455136928609647435090299 := by
  unfold tailWord_3988692
  simp only [CollatzResearch.WordTrace]
  refine ⟨72739774432828786602232165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96986365910438382136309553 72739774432828786602232165)
  ·
    refine ⟨13638707706155397487918531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72739774432828786602232165 13638707706155397487918531)
    ·
      refine ⟨20458061559233096231877797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13638707706155397487918531 20458061559233096231877797)
      ·
        refine ⟨3835886542356205543477087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20458061559233096231877797 3835886542356205543477087)
        ·
          refine ⟨5753829813534308315215631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3835886542356205543477087 5753829813534308315215631)
          ·
            refine ⟨8630744720301462472823447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5753829813534308315215631 8630744720301462472823447)
            ·
              refine ⟨12946117080452193709235171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8630744720301462472823447 12946117080452193709235171)
              ·
                refine ⟨19419175620678290563852757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12946117080452193709235171 19419175620678290563852757)
                ·
                  refine ⟨455136928609647435090299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19419175620678290563852757 455136928609647435090299)
                  ·
                    rfl

theorem cell22_3988692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 7].length) (baseStart_3988692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3988692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3988692 prefixEnd_3988692 := by exact prefixLift 3988692
  have htrace : WordTrace (prefixWord ++ tailWord_3988692) baseStart_3988692 baseEnd_3988692 := by
    simpa [prefixWord, tailWord_3988692, baseEnd_3988692] using wordTrace_append hprefix tailTrace_3988692
  have hstable : (prefixWord ++ tailWord_3988692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988692).length < 2 ^ (prefixWord ++ tailWord_3988692).sum := by decide
  have hdescent : baseEnd_3988692 < baseStart_3988692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988703 : List Nat := [1, 1, 2, 3, 2, 1, 3, 3, 6]
def baseStart_3988703 : Nat := 118140960795 + 3988703 * 2 ^ 59
def prefixEnd_3988703 : Nat := 4983230072969 + 3 ^ 40 * 3988703 * 2
def baseEnd_3988703 : Nat := 455138183784580647748621

theorem tailTrace_3988703 : CollatzResearch.WordTrace tailWord_3988703 prefixEnd_3988703 455138183784580647748621 := by
  unfold tailWord_3988703
  simp only [CollatzResearch.WordTrace]
  refine ⟨145479950068617722083114763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96986633379078481388743175 145479950068617722083114763)
  ·
    refine ⟨218219925102926583124672145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145479950068617722083114763 218219925102926583124672145)
    ·
      refine ⟨163664943827194937343504109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218219925102926583124672145 163664943827194937343504109)
      ·
        refine ⟨61374353935198101503814041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163664943827194937343504109 61374353935198101503814041)
        ·
          refine ⟨46030765451398576127860531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61374353935198101503814041 46030765451398576127860531)
          ·
            refine ⟨69046148177097864191790797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46030765451398576127860531 69046148177097864191790797)
            ·
              refine ⟨25892305566411699071921549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69046148177097864191790797 25892305566411699071921549)
              ·
                refine ⟨9709614587404387151970581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25892305566411699071921549 9709614587404387151970581)
                ·
                  refine ⟨455138183784580647748621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9709614587404387151970581 455138183784580647748621)
                  ·
                    rfl

theorem cell22_3988703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 3, 6].length) (baseStart_3988703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3988703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3988703 prefixEnd_3988703 := by exact prefixLift 3988703
  have htrace : WordTrace (prefixWord ++ tailWord_3988703) baseStart_3988703 baseEnd_3988703 := by
    simpa [prefixWord, tailWord_3988703, baseEnd_3988703] using wordTrace_append hprefix tailTrace_3988703
  have hstable : (prefixWord ++ tailWord_3988703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988703).length < 2 ^ (prefixWord ++ tailWord_3988703).sum := by decide
  have hdescent : baseEnd_3988703 < baseStart_3988703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988735 : List Nat := [1, 1, 2, 2, 1, 5, 1, 2, 4, 3]
def baseStart_3988735 : Nat := 118140960795 + 3988735 * 2 ^ 59
def prefixEnd_3988735 : Nat := 4983230072969 + 3 ^ 40 * 3988735 * 2
def baseEnd_3988735 : Nat := 1365425505607704526445765

theorem tailTrace_3988735 : CollatzResearch.WordTrace tailWord_3988735 prefixEnd_3988735 1365425505607704526445765 := by
  unfold tailWord_3988735
  simp only [CollatzResearch.WordTrace]
  refine ⟨145481117204501791548279659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96987411469667861032186439 145481117204501791548279659)
  ·
    refine ⟨218221675806752687322419489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145481117204501791548279659 218221675806752687322419489)
    ·
      refine ⟨163666256855064515491814617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218221675806752687322419489 163666256855064515491814617)
      ·
        refine ⟨122749692641298386618860963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163666256855064515491814617 122749692641298386618860963)
        ·
          refine ⟨184124538961947579928291445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122749692641298386618860963 184124538961947579928291445)
          ·
            refine ⟨17261675527682585618277323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 184124538961947579928291445 17261675527682585618277323)
            ·
              refine ⟨25892513291523878427415985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17261675527682585618277323 25892513291523878427415985)
              ·
                refine ⟨19419384968642908820561989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25892513291523878427415985 19419384968642908820561989)
                ·
                  refine ⟨3641134681620545403855373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19419384968642908820561989 3641134681620545403855373)
                  ·
                    refine ⟨1365425505607704526445765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3641134681620545403855373 1365425505607704526445765)
                    ·
                      rfl

theorem cell22_3988735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 4, 3].length) (baseStart_3988735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3988735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3988735 prefixEnd_3988735 := by exact prefixLift 3988735
  have htrace : WordTrace (prefixWord ++ tailWord_3988735) baseStart_3988735 baseEnd_3988735 := by
    simpa [prefixWord, tailWord_3988735, baseEnd_3988735] using wordTrace_append hprefix tailTrace_3988735
  have hstable : (prefixWord ++ tailWord_3988735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988735).length < 2 ^ (prefixWord ++ tailWord_3988735).sum := by decide
  have hdescent : baseEnd_3988735 < baseStart_3988735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988737 : List Nat := [1, 2, 4, 1, 1, 3, 3, 3, 4]
def baseStart_3988737 : Nat := 118140960795 + 3988737 * 2 ^ 59
def prefixEnd_3988737 : Nat := 4983230072969 + 3 ^ 40 * 3988737 * 2
def baseEnd_3988737 : Nat := 455142063416192395965253

theorem tailTrace_3988737 : CollatzResearch.WordTrace tailWord_3988737 prefixEnd_3988737 455142063416192395965253 := by
  unfold tailWord_3988737
  simp only [CollatzResearch.WordTrace]
  refine ⟨145481190150494545889852465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96987460100329697259901643 145481190150494545889852465)
  ·
    refine ⟨109110892612870909417389349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145481190150494545889852465 109110892612870909417389349)
    ·
      refine ⟨20458292364913295515760503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109110892612870909417389349 20458292364913295515760503)
      ·
        refine ⟨30687438547369943273640755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20458292364913295515760503 30687438547369943273640755)
        ·
          refine ⟨46031157821054914910461133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30687438547369943273640755 46031157821054914910461133)
          ·
            refine ⟨17261684182895593091422925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46031157821054914910461133 17261684182895593091422925)
            ·
              refine ⟨6473131568585847409283597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17261684182895593091422925 6473131568585847409283597)
              ·
                refine ⟨2427424338219692778481349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6473131568585847409283597 2427424338219692778481349)
                ·
                  refine ⟨455142063416192395965253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2427424338219692778481349 455142063416192395965253)
                  ·
                    rfl

theorem cell22_3988737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 3, 4].length) (baseStart_3988737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3988737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3988737 prefixEnd_3988737 := by exact prefixLift 3988737
  have htrace : WordTrace (prefixWord ++ tailWord_3988737) baseStart_3988737 baseEnd_3988737 := by
    simpa [prefixWord, tailWord_3988737, baseEnd_3988737] using wordTrace_append hprefix tailTrace_3988737
  have hstable : (prefixWord ++ tailWord_3988737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988737).length < 2 ^ (prefixWord ++ tailWord_3988737).sum := by decide
  have hdescent : baseEnd_3988737 < baseStart_3988737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988748 : List Nat := [2, 2, 1, 2, 2, 3, 10]
def baseStart_3988748 : Nat := 118140960795 + 3988748 * 2 ^ 59
def prefixEnd_3988748 : Nat := 4983230072969 + 3 ^ 40 * 3988748 * 2
def baseEnd_3988748 : Nat := 50571479843458400958175

theorem tailTrace_3988748 : CollatzResearch.WordTrace tailWord_3988748 prefixEnd_3988748 50571479843458400958175 := by
  unfold tailWord_3988748
  simp only [CollatzResearch.WordTrace]
  refine ⟨72740795676727347384251449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96987727568969796512335265 72740795676727347384251449)
  ·
    refine ⟨54555596757545510538188587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72740795676727347384251449 54555596757545510538188587)
    ·
      refine ⟨81833395136318265807282881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54555596757545510538188587 81833395136318265807282881)
      ·
        refine ⟨61375046352238699355462161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81833395136318265807282881 61375046352238699355462161)
        ·
          refine ⟨46031284764179024516596621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61375046352238699355462161 46031284764179024516596621)
          ·
            refine ⟨17261731786567134193723733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46031284764179024516596621 17261731786567134193723733)
            ·
              refine ⟨50571479843458400958175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17261731786567134193723733 50571479843458400958175)
              ·
                rfl

theorem cell22_3988748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 10].length) (baseStart_3988748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3988748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3988748 prefixEnd_3988748 := by exact prefixLift 3988748
  have htrace : WordTrace (prefixWord ++ tailWord_3988748) baseStart_3988748 baseEnd_3988748 := by
    simpa [prefixWord, tailWord_3988748, baseEnd_3988748] using wordTrace_append hprefix tailTrace_3988748
  have hstable : (prefixWord ++ tailWord_3988748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988748).length < 2 ^ (prefixWord ++ tailWord_3988748).sum := by decide
  have hdescent : baseEnd_3988748 < baseStart_3988748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988750 : List Nat := [4, 1, 1, 2, 1, 3, 1, 1, 4, 4]
def baseStart_3988750 : Nat := 118140960795 + 3988750 * 2 ^ 59
def prefixEnd_3988750 : Nat := 4983230072969 + 3 ^ 40 * 3988750 * 2
def baseEnd_3988750 : Nat := 1365430640414249487320719

theorem tailTrace_3988750 : CollatzResearch.WordTrace tailWord_3988750 prefixEnd_3988750 1365430640414249487320719 := by
  unfold tailWord_3988750
  simp only [CollatzResearch.WordTrace]
  refine ⟨18185208037430931138759463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96987776199631632740050469 18185208037430931138759463)
  ·
    refine ⟨27277812056146396708139195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18185208037430931138759463 27277812056146396708139195)
    ·
      refine ⟨40916718084219595062208793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27277812056146396708139195 40916718084219595062208793)
      ·
        refine ⟨30687538563164696296656595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40916718084219595062208793 30687538563164696296656595)
        ·
          refine ⟨46031307844747044444984893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30687538563164696296656595 46031307844747044444984893)
          ·
            refine ⟨17261740441780141666869335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46031307844747044444984893 17261740441780141666869335)
            ·
              refine ⟨25892610662670212500304003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17261740441780141666869335 25892610662670212500304003)
              ·
                refine ⟨38838915994005318750456005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25892610662670212500304003 38838915994005318750456005)
                ·
                  refine ⟨7282296748875997265710501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38838915994005318750456005 7282296748875997265710501)
                  ·
                    refine ⟨1365430640414249487320719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7282296748875997265710501 1365430640414249487320719)
                    ·
                      rfl

theorem cell22_3988750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 4, 4].length) (baseStart_3988750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3988750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3988750 prefixEnd_3988750 := by exact prefixLift 3988750
  have htrace : WordTrace (prefixWord ++ tailWord_3988750) baseStart_3988750 baseEnd_3988750 := by
    simpa [prefixWord, tailWord_3988750, baseEnd_3988750] using wordTrace_append hprefix tailTrace_3988750
  have hstable : (prefixWord ++ tailWord_3988750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988750).length < 2 ^ (prefixWord ++ tailWord_3988750).sum := by decide
  have hdescent : baseEnd_3988750 < baseStart_3988750 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988765 : List Nat := [1, 4, 2, 3, 1, 1, 1, 9]
def baseStart_3988765 : Nat := 118140960795 + 3988765 * 2 ^ 59
def prefixEnd_3988765 : Nat := 4983230072969 + 3 ^ 40 * 3988765 * 2
def baseEnd_3988765 : Nat := 151715086135643827577297

theorem tailTrace_3988765 : CollatzResearch.WordTrace tailWord_3988765 prefixEnd_3988765 151715086135643827577297 := by
  unfold tailWord_3988765
  simp only [CollatzResearch.WordTrace]
  refine ⟨145482211394393106671871749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96988140929595404447914499 145482211394393106671871749)
  ·
    refine ⟨27277914636448707500975953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145482211394393106671871749 27277914636448707500975953)
    ·
      refine ⟨20458435977336530625731965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27277914636448707500975953 20458435977336530625731965)
      ·
        refine ⟨7671913491501198984649487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20458435977336530625731965 7671913491501198984649487)
        ·
          refine ⟨11507870237251798476974231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7671913491501198984649487 11507870237251798476974231)
          ·
            refine ⟨17261805355877697715461347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11507870237251798476974231 17261805355877697715461347)
            ·
              refine ⟨25892708033816546573192021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17261805355877697715461347 25892708033816546573192021)
              ·
                refine ⟨151715086135643827577297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25892708033816546573192021 151715086135643827577297)
                ·
                  rfl

theorem cell22_3988765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 9].length) (baseStart_3988765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3988765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3988765 prefixEnd_3988765 := by exact prefixLift 3988765
  have htrace : WordTrace (prefixWord ++ tailWord_3988765) baseStart_3988765 baseEnd_3988765 := by
    simpa [prefixWord, tailWord_3988765, baseEnd_3988765] using wordTrace_append hprefix tailTrace_3988765
  have hstable : (prefixWord ++ tailWord_3988765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988765).length < 2 ^ (prefixWord ++ tailWord_3988765).sum := by decide
  have hdescent : baseEnd_3988765 < baseStart_3988765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988780 : List Nat := [2, 2, 1, 1, 1, 3, 1, 3, 5, 3]
def baseStart_3988780 : Nat := 118140960795 + 3988780 * 2 ^ 59
def prefixEnd_3988780 : Nat := 4983230072969 + 3 ^ 40 * 3988780 * 2
def baseEnd_3988780 : Nat := 1365440910027339409070627

theorem tailTrace_3988780 : CollatzResearch.WordTrace tailWord_3988780 prefixEnd_3988780 1365440910027339409070627 := by
  unfold tailWord_3988780
  simp only [CollatzResearch.WordTrace]
  refine ⟨72741379244669382116833897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96988505659559176155778529 72741379244669382116833897)
  ·
    refine ⟨54556034433502036587625423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72741379244669382116833897 54556034433502036587625423)
    ·
      refine ⟨81834051650253054881438135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54556034433502036587625423 81834051650253054881438135)
      ·
        refine ⟨122751077475379582322157203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81834051650253054881438135 122751077475379582322157203)
        ·
          refine ⟨184126616213069373483235805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122751077475379582322157203 184126616213069373483235805)
          ·
            refine ⟨69047481079901015056213427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184126616213069373483235805 69047481079901015056213427)
            ·
              refine ⟨103571221619851522584320141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69047481079901015056213427 103571221619851522584320141)
              ·
                refine ⟨38839208107444320969120053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103571221619851522584320141 38839208107444320969120053)
                ·
                  refine ⟨3641175760072905090855005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38839208107444320969120053 3641175760072905090855005)
                  ·
                    refine ⟨1365440910027339409070627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3641175760072905090855005 1365440910027339409070627)
                    ·
                      rfl

theorem cell22_3988780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 3].length) (baseStart_3988780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3988780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3988780 prefixEnd_3988780 := by exact prefixLift 3988780
  have htrace : WordTrace (prefixWord ++ tailWord_3988780) baseStart_3988780 baseEnd_3988780 := by
    simpa [prefixWord, tailWord_3988780, baseEnd_3988780] using wordTrace_append hprefix tailTrace_3988780
  have hstable : (prefixWord ++ tailWord_3988780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988780).length < 2 ^ (prefixWord ++ tailWord_3988780).sum := by decide
  have hdescent : baseEnd_3988780 < baseStart_3988780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988814 : List Nat := [4, 1, 1, 1, 1, 1, 5, 4, 1, 3]
def baseStart_3988814 : Nat := 118140960795 + 3988814 * 2 ^ 59
def prefixEnd_3988814 : Nat := 4983230072969 + 3 ^ 40 * 3988814 * 2
def baseEnd_3988814 : Nat := 1365452548922174653720523

theorem tailTrace_3988814 : CollatzResearch.WordTrace tailWord_3988814 prefixEnd_3988814 1365452548922174653720523 := by
  unfold tailWord_3988814
  simp only [CollatzResearch.WordTrace]
  refine ⟨18185499821401948505050687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96989332380810392026936997 18185499821401948505050687)
  ·
    refine ⟨27278249732102922757576031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18185499821401948505050687 27278249732102922757576031)
    ·
      refine ⟨40917374598154384136364047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27278249732102922757576031 40917374598154384136364047)
      ·
        refine ⟨61376061897231576204546071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40917374598154384136364047 61376061897231576204546071)
        ·
          refine ⟨92064092845847364306819107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61376061897231576204546071 92064092845847364306819107)
          ·
            refine ⟨138096139268771046460228661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92064092845847364306819107 138096139268771046460228661)
            ·
              refine ⟨12946513056447285605646437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 138096139268771046460228661 12946513056447285605646437)
              ·
                refine ⟨2427471198083866051058707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12946513056447285605646437 2427471198083866051058707)
                ·
                  refine ⟨3641206797125799076588061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2427471198083866051058707 3641206797125799076588061)
                  ·
                    refine ⟨1365452548922174653720523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3641206797125799076588061 1365452548922174653720523)
                    ·
                      rfl

theorem cell22_3988814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 4, 1, 3].length) (baseStart_3988814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3988814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3988814 prefixEnd_3988814 := by exact prefixLift 3988814
  have htrace : WordTrace (prefixWord ++ tailWord_3988814) baseStart_3988814 baseEnd_3988814 := by
    simpa [prefixWord, tailWord_3988814, baseEnd_3988814] using wordTrace_append hprefix tailTrace_3988814
  have hstable : (prefixWord ++ tailWord_3988814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988814).length < 2 ^ (prefixWord ++ tailWord_3988814).sum := by decide
  have hdescent : baseEnd_3988814 < baseStart_3988814 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988872 : List Nat := [2, 1, 3, 3, 1, 3, 2, 1, 6]
def baseStart_3988872 : Nat := 118140960795 + 3988872 * 2 ^ 59
def prefixEnd_3988872 : Nat := 4983230072969 + 3 ^ 40 * 3988872 * 2
def baseEnd_3988872 : Nat := 455157467835827278590115

theorem tailTrace_3988872 : CollatzResearch.WordTrace tailWord_3988872 prefixEnd_3988872 455157467835827278590115 := by
  unfold tailWord_3988872
  simp only [CollatzResearch.WordTrace]
  refine ⟨72743057002502731973008435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96990742670003642630677913 72743057002502731973008435)
  ·
    refine ⟨109114585503754097959512653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72743057002502731973008435 109114585503754097959512653)
    ·
      refine ⟨40917969563907786734817245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109114585503754097959512653 40917969563907786734817245)
      ·
        refine ⟨15344238586465420025556467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40917969563907786734817245 15344238586465420025556467)
        ·
          refine ⟨23016357879698130038334701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15344238586465420025556467 23016357879698130038334701)
          ·
            refine ⟨8631134204886798764375513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23016357879698130038334701 8631134204886798764375513)
            ·
              refine ⟨6473350653665099073281635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8631134204886798764375513 6473350653665099073281635)
              ·
                refine ⟨9710025980497648609922453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6473350653665099073281635 9710025980497648609922453)
                ·
                  refine ⟨455157467835827278590115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9710025980497648609922453 455157467835827278590115)
                  ·
                    rfl

theorem cell22_3988872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 1, 6].length) (baseStart_3988872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3988872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3988872 prefixEnd_3988872 := by exact prefixLift 3988872
  have htrace : WordTrace (prefixWord ++ tailWord_3988872) baseStart_3988872 baseEnd_3988872 := by
    simpa [prefixWord, tailWord_3988872, baseEnd_3988872] using wordTrace_append hprefix tailTrace_3988872
  have hstable : (prefixWord ++ tailWord_3988872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988872).length < 2 ^ (prefixWord ++ tailWord_3988872).sum := by decide
  have hdescent : baseEnd_3988872 < baseStart_3988872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988885 : List Nat := [1, 3, 2, 1, 1, 2, 3, 2, 1, 6]
def baseStart_3988885 : Nat := 118140960795 + 3988885 * 2 ^ 59
def prefixEnd_3988885 : Nat := 4983230072969 + 3 ^ 40 * 3988885 * 2
def baseEnd_3988885 : Nat := 1365476853673154135195305

theorem tailTrace_3988885 : CollatzResearch.WordTrace tailWord_3988885 prefixEnd_3988885 1365476853673154135195305 := by
  unfold tailWord_3988885
  simp only [CollatzResearch.WordTrace]
  refine ⟨145486588153958367166240109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96991058769305578110826739 145486588153958367166240109)
  ·
    refine ⟨54557470557734387687340041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145486588153958367166240109 54557470557734387687340041)
    ·
      refine ⟨40918102918300790765505031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54557470557734387687340041 40918102918300790765505031)
      ·
        refine ⟨61377154377451186148257547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40918102918300790765505031 61377154377451186148257547)
        ·
          refine ⟨92065731566176779222386321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61377154377451186148257547 92065731566176779222386321)
          ·
            refine ⟨69049298674632584416789741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92065731566176779222386321 69049298674632584416789741)
            ·
              refine ⟨25893487002987219156296153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69049298674632584416789741 25893487002987219156296153)
              ·
                refine ⟨19420115252240414367222115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25893487002987219156296153 19420115252240414367222115)
                ·
                  refine ⟨29130172878360621550833173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19420115252240414367222115 29130172878360621550833173)
                  ·
                    refine ⟨1365476853673154135195305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29130172878360621550833173 1365476853673154135195305)
                    ·
                      rfl

theorem cell22_3988885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 6].length) (baseStart_3988885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3988885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3988885 prefixEnd_3988885 := by exact prefixLift 3988885
  have htrace : WordTrace (prefixWord ++ tailWord_3988885) baseStart_3988885 baseEnd_3988885 := by
    simpa [prefixWord, tailWord_3988885, baseEnd_3988885] using wordTrace_append hprefix tailTrace_3988885
  have hstable : (prefixWord ++ tailWord_3988885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988885).length < 2 ^ (prefixWord ++ tailWord_3988885).sum := by decide
  have hdescent : baseEnd_3988885 < baseStart_3988885 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988917 : List Nat := [1, 3, 3, 2, 2, 3, 8]
def baseStart_3988917 : Nat := 118140960795 + 3988917 * 2 ^ 59
def prefixEnd_3988917 : Nat := 4983230072969 + 3 ^ 40 * 3988917 * 2
def baseEnd_3988917 : Nat := 50573622515819137718341

theorem tailTrace_3988917 : CollatzResearch.WordTrace tailWord_3988917 prefixEnd_3988917 50573622515819137718341 := by
  unfold tailWord_3988917
  simp only [CollatzResearch.WordTrace]
  refine ⟨145487755289842436631405005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96991836859894957754270003 145487755289842436631405005)
  ·
    refine ⟨54557908233690913736776877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145487755289842436631405005 54557908233690913736776877)
    ·
      refine ⟨20459215587634092651291329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54557908233690913736776877 20459215587634092651291329)
      ·
        refine ⟨15344411690725569488468497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20459215587634092651291329 15344411690725569488468497)
        ·
          refine ⟨11508308768044177116351373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15344411690725569488468497 11508308768044177116351373)
          ·
            refine ⟨4315615788016566418631765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11508308768044177116351373 4315615788016566418631765)
            ·
              refine ⟨50573622515819137718341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4315615788016566418631765 50573622515819137718341)
              ·
                rfl

theorem cell22_3988917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 8].length) (baseStart_3988917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3988917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3988917 prefixEnd_3988917 := by exact prefixLift 3988917
  have htrace : WordTrace (prefixWord ++ tailWord_3988917) baseStart_3988917 baseEnd_3988917 := by
    simpa [prefixWord, tailWord_3988917, baseEnd_3988917] using wordTrace_append hprefix tailTrace_3988917
  have hstable : (prefixWord ++ tailWord_3988917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988917).length < 2 ^ (prefixWord ++ tailWord_3988917).sum := by decide
  have hdescent : baseEnd_3988917 < baseStart_3988917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988960 : List Nat := [2, 1, 1, 3, 1, 1, 2, 1, 3, 7]
def baseStart_3988960 : Nat := 118140960795 + 3988960 * 2 ^ 59
def prefixEnd_3988960 : Nat := 4983230072969 + 3 ^ 40 * 3988960 * 2
def baseEnd_3988960 : Nat := 1365502527705878939570075

theorem tailTrace_3988960 : CollatzResearch.WordTrace tailWord_3988960 prefixEnd_3988960 1365502527705878939570075 := by
  unfold tailWord_3988960
  simp only [CollatzResearch.WordTrace]
  refine ⟨72744661814343327487610167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96992882419124436650146889 72744661814343327487610167)
  ·
    refine ⟨109116992721514991231415251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72744661814343327487610167 109116992721514991231415251)
    ·
      refine ⟨163675489082272486847122877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109116992721514991231415251 163675489082272486847122877)
      ·
        refine ⟨61378308405852182567671079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163675489082272486847122877 61378308405852182567671079)
        ·
          refine ⟨92067462608778273851506619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61378308405852182567671079 92067462608778273851506619)
          ·
            refine ⟨138101193913167410777259929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92067462608778273851506619 138101193913167410777259929)
            ·
              refine ⟨103575895434875558082944947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138101193913167410777259929 103575895434875558082944947)
              ·
                refine ⟨155363843152313337124417421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103575895434875558082944947 155363843152313337124417421)
                ·
                  refine ⟨58261441182117501421656533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 155363843152313337124417421 58261441182117501421656533)
                  ·
                    refine ⟨1365502527705878939570075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58261441182117501421656533 1365502527705878939570075)
                    ·
                      rfl

theorem cell22_3988960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 3, 7].length) (baseStart_3988960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3988960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3988960 prefixEnd_3988960 := by exact prefixLift 3988960
  have htrace : WordTrace (prefixWord ++ tailWord_3988960) baseStart_3988960 baseEnd_3988960 := by
    simpa [prefixWord, tailWord_3988960, baseEnd_3988960] using wordTrace_append hprefix tailTrace_3988960
  have hstable : (prefixWord ++ tailWord_3988960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988960).length < 2 ^ (prefixWord ++ tailWord_3988960).sum := by decide
  have hdescent : baseEnd_3988960 < baseStart_3988960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988994 : List Nat := [3, 4, 1, 2, 1, 1, 1, 1, 1, 7]
def baseStart_3988994 : Nat := 118140960795 + 3988994 * 2 ^ 59
def prefixEnd_3988994 : Nat := 4983230072969 + 3 ^ 40 * 3988994 * 2
def baseEnd_3988994 : Nat := 1365514166600714184219971

theorem tailTrace_3988994 : CollatzResearch.WordTrace tailWord_3988994 prefixEnd_3988994 1365514166600714184219971 := by
  unfold tailWord_3988994
  simp only [CollatzResearch.WordTrace]
  refine ⟨36372640927640869695489509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96993709140375652521305357 36372640927640869695489509)
  ·
    refine ⟨6819870173932663067904283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36372640927640869695489509 6819870173932663067904283)
    ·
      refine ⟨10229805260898994601856425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6819870173932663067904283 10229805260898994601856425)
      ·
        refine ⟨7672353945674245951392319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10229805260898994601856425 7672353945674245951392319)
        ·
          refine ⟨11508530918511368927088479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7672353945674245951392319 11508530918511368927088479)
          ·
            refine ⟨17262796377767053390632719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11508530918511368927088479 17262796377767053390632719)
            ·
              refine ⟨25894194566650580085949079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17262796377767053390632719 25894194566650580085949079)
              ·
                refine ⟨38841291849975870128923619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25894194566650580085949079 38841291849975870128923619)
                ·
                  refine ⟨58261937774963805193385429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38841291849975870128923619 58261937774963805193385429)
                  ·
                    refine ⟨1365514166600714184219971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58261937774963805193385429 1365514166600714184219971)
                    ·
                      rfl

theorem cell22_3988994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_3988994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3988994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3988994 prefixEnd_3988994 := by exact prefixLift 3988994
  have htrace : WordTrace (prefixWord ++ tailWord_3988994) baseStart_3988994 baseEnd_3988994 := by
    simpa [prefixWord, tailWord_3988994, baseEnd_3988994] using wordTrace_append hprefix tailTrace_3988994
  have hstable : (prefixWord ++ tailWord_3988994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988994).length < 2 ^ (prefixWord ++ tailWord_3988994).sum := by decide
  have hdescent : baseEnd_3988994 < baseStart_3988994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989026 : List Nat := [3, 3, 1, 1, 1, 1, 6, 1, 1, 4]
def baseStart_3989026 : Nat := 118140960795 + 3989026 * 2 ^ 59
def prefixEnd_3989026 : Nat := 4983230072969 + 3 ^ 40 * 3989026 * 2
def baseEnd_3989026 : Nat := 1365525120854676767419873

theorem tailTrace_3989026 : CollatzResearch.WordTrace tailWord_3989026 prefixEnd_3989026 1365525120854676767419873 := by
  unfold tailWord_3989026
  simp only [CollatzResearch.WordTrace]
  refine ⟨36372932711611887061780733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96994487230965032164748621 36372932711611887061780733)
  ·
    refine ⟨13639849766854457648167775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36372932711611887061780733 13639849766854457648167775)
    ·
      refine ⟨20459774650281686472251663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13639849766854457648167775 20459774650281686472251663)
      ·
        refine ⟨30689661975422529708377495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20459774650281686472251663 30689661975422529708377495)
        ·
          refine ⟨46034492963133794562566243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30689661975422529708377495 46034492963133794562566243)
          ·
            refine ⟨69051739444700691843849365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46034492963133794562566243 69051739444700691843849365)
            ·
              refine ⟨3236800286470344930180439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 69051739444700691843849365 3236800286470344930180439)
              ·
                refine ⟨4855200429705517395270659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3236800286470344930180439 4855200429705517395270659)
                ·
                  refine ⟨7282800644558276092905989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4855200429705517395270659 7282800644558276092905989)
                  ·
                    refine ⟨1365525120854676767419873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7282800644558276092905989 1365525120854676767419873)
                    ·
                      rfl

theorem cell22_3989026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 6, 1, 1, 4].length) (baseStart_3989026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3989026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3989026 prefixEnd_3989026 := by exact prefixLift 3989026
  have htrace : WordTrace (prefixWord ++ tailWord_3989026) baseStart_3989026 baseEnd_3989026 := by
    simpa [prefixWord, tailWord_3989026, baseEnd_3989026] using wordTrace_append hprefix tailTrace_3989026
  have hstable : (prefixWord ++ tailWord_3989026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989026).length < 2 ^ (prefixWord ++ tailWord_3989026).sum := by decide
  have hdescent : baseEnd_3989026 < baseStart_3989026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989097 : List Nat := [1, 2, 1, 1, 1, 4, 4, 1, 7]
def baseStart_3989097 : Nat := 118140960795 + 3989097 * 2 ^ 59
def prefixEnd_3989097 : Nat := 4983230072969 + 3 ^ 40 * 3989097 * 2
def baseEnd_3989097 : Nat := 455183141868552082964885

theorem tailTrace_3989097 : CollatzResearch.WordTrace tailWord_3989097 prefixEnd_3989097 455183141868552082964885 := by
  unfold tailWord_3989097
  simp only [CollatzResearch.WordTrace]
  refine ⟨145494320429190327372957545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96996213619460218248638363 145494320429190327372957545)
  ·
    refine ⟨109120740321892745529718159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145494320429190327372957545 109120740321892745529718159)
    ·
      refine ⟨163681110482839118294577239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109120740321892745529718159 163681110482839118294577239)
      ·
        refine ⟨245521665724258677441865859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163681110482839118294577239 245521665724258677441865859)
        ·
          refine ⟨368282498586388016162798789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245521665724258677441865859 368282498586388016162798789)
          ·
            refine ⟨69052968484947753030524773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 368282498586388016162798789 69052968484947753030524773)
            ·
              refine ⟨12947431590927703693223395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69052968484947753030524773 12947431590927703693223395)
              ·
                refine ⟨19421147386391555539835093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12947431590927703693223395 19421147386391555539835093)
                ·
                  refine ⟨455183141868552082964885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19421147386391555539835093 455183141868552082964885)
                  ·
                    rfl

theorem cell22_3989097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 7].length) (baseStart_3989097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3989097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3989097 prefixEnd_3989097 := by exact prefixLift 3989097
  have htrace : WordTrace (prefixWord ++ tailWord_3989097) baseStart_3989097 baseEnd_3989097 := by
    simpa [prefixWord, tailWord_3989097, baseEnd_3989097] using wordTrace_append hprefix tailTrace_3989097
  have hstable : (prefixWord ++ tailWord_3989097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989097).length < 2 ^ (prefixWord ++ tailWord_3989097).sum := by decide
  have hdescent : baseEnd_3989097 < baseStart_3989097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989238 : List Nat := [5, 1, 1, 1, 1, 5, 2, 6]
def baseStart_3989238 : Nat := 118140960795 + 3989238 * 2 ^ 59
def prefixEnd_3989238 : Nat := 4983230072969 + 3 ^ 40 * 3989238 * 2
def baseEnd_3989238 : Nat := 151733076976353209013247

theorem tailTrace_3989238 : CollatzResearch.WordTrace tailWord_3989238 prefixEnd_3989238 151733076976353209013247 := by
  unfold tailWord_3989238
  simp only [CollatzResearch.WordTrace]
  refine ⟨9093716445104969278365023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96999642081119672302560245 9093716445104969278365023)
  ·
    refine ⟨13640574667657453917547535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9093716445104969278365023 13640574667657453917547535)
    ·
      refine ⟨20460862001486180876321303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13640574667657453917547535 20460862001486180876321303)
      ·
        refine ⟨30691293002229271314481955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20460862001486180876321303 30691293002229271314481955)
        ·
          refine ⟨46036939503343906971722933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30691293002229271314481955 46036939503343906971722933)
          ·
            refine ⟨4315963078438491278599025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46036939503343906971722933 4315963078438491278599025)
            ·
              refine ⟨3236972308828868458949269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4315963078438491278599025 3236972308828868458949269)
              ·
                refine ⟨151733076976353209013247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3236972308828868458949269 151733076976353209013247)
                ·
                  rfl

theorem cell22_3989238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 2, 6].length) (baseStart_3989238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3989238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3989238 prefixEnd_3989238 := by exact prefixLift 3989238
  have htrace : WordTrace (prefixWord ++ tailWord_3989238) baseStart_3989238 baseEnd_3989238 := by
    simpa [prefixWord, tailWord_3989238, baseEnd_3989238] using wordTrace_append hprefix tailTrace_3989238
  have hstable : (prefixWord ++ tailWord_3989238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989238).length < 2 ^ (prefixWord ++ tailWord_3989238).sum := by decide
  have hdescent : baseEnd_3989238 < baseStart_3989238 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989249 : List Nat := [1, 2, 4, 1, 1, 1, 3, 2, 7]
def baseStart_3989249 : Nat := 118140960795 + 3989249 * 2 ^ 59
def prefixEnd_3989249 : Nat := 4983230072969 + 3 ^ 40 * 3989249 * 2
def baseEnd_3989249 : Nat := 455200486103992839698063

theorem tailTrace_3989249 : CollatzResearch.WordTrace tailWord_3989249 prefixEnd_3989249 455200486103992839698063 := by
  unfold tailWord_3989249
  simp only [CollatzResearch.WordTrace]
  refine ⟨145499864324639657332490801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96999909549759771554993867 145499864324639657332490801)
  ·
    refine ⟨109124898243479742999368101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145499864324639657332490801 109124898243479742999368101)
    ·
      refine ⟨20460918420652451812381519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109124898243479742999368101 20460918420652451812381519)
      ·
        refine ⟨30691377630978677718572279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20460918420652451812381519 30691377630978677718572279)
        ·
          refine ⟨46037066446468016577858419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30691377630978677718572279 46037066446468016577858419)
          ·
            refine ⟨69055599669702024866787629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46037066446468016577858419 69055599669702024866787629)
            ·
              refine ⟨25895849876138259325045361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69055599669702024866787629 25895849876138259325045361)
              ·
                refine ⟨19421887407103694493784021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25895849876138259325045361 19421887407103694493784021)
                ·
                  refine ⟨455200486103992839698063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19421887407103694493784021 455200486103992839698063)
                  ·
                    rfl

theorem cell22_3989249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 7].length) (baseStart_3989249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3989249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3989249 prefixEnd_3989249 := by exact prefixLift 3989249
  have htrace : WordTrace (prefixWord ++ tailWord_3989249) baseStart_3989249 baseEnd_3989249 := by
    simpa [prefixWord, tailWord_3989249, baseEnd_3989249] using wordTrace_append hprefix tailTrace_3989249
  have hstable : (prefixWord ++ tailWord_3989249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989249).length < 2 ^ (prefixWord ++ tailWord_3989249).sum := by decide
  have hdescent : baseEnd_3989249 < baseStart_3989249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989261 : List Nat := [1, 7, 2, 1, 1, 1, 3, 2, 4]
def baseStart_3989261 : Nat := 118140960795 + 3989261 * 2 ^ 59
def prefixEnd_3989261 : Nat := 4983230072969 + 3 ^ 40 * 3989261 * 2
def baseEnd_3989261 : Nat := 455201855385738162598051

theorem tailTrace_3989261 : CollatzResearch.WordTrace tailWord_3989261 prefixEnd_3989261 455201855385738162598051 := by
  unfold tailWord_3989261
  simp only [CollatzResearch.WordTrace]
  refine ⟨145500302000596183381927637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97000201333730788921285091 145500302000596183381927637)
  ·
    refine ⟨3410163328138973048013929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 145500302000596183381927637 3410163328138973048013929)
    ·
      refine ⟨2557622496104229786010447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3410163328138973048013929 2557622496104229786010447)
      ·
        refine ⟨3836433744156344679015671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2557622496104229786010447 3836433744156344679015671)
        ·
          refine ⟨5754650616234517018523507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3836433744156344679015671 5754650616234517018523507)
          ·
            refine ⟨8631975924351775527785261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5754650616234517018523507 8631975924351775527785261)
            ·
              refine ⟨3236990971631915822919473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8631975924351775527785261 3236990971631915822919473)
              ·
                refine ⟨2427743228723936867189605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3236990971631915822919473 2427743228723936867189605)
                ·
                  refine ⟨455201855385738162598051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2427743228723936867189605 455201855385738162598051)
                  ·
                    rfl

theorem cell22_3989261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_3989261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3989261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3989261 prefixEnd_3989261 := by exact prefixLift 3989261
  have htrace : WordTrace (prefixWord ++ tailWord_3989261) baseStart_3989261 baseEnd_3989261 := by
    simpa [prefixWord, tailWord_3989261, baseEnd_3989261] using wordTrace_append hprefix tailTrace_3989261
  have hstable : (prefixWord ++ tailWord_3989261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989261).length < 2 ^ (prefixWord ++ tailWord_3989261).sum := by decide
  have hdescent : baseEnd_3989261 < baseStart_3989261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989343 : List Nat := [1, 1, 2, 3, 1, 4, 2, 3, 2, 3]
def baseStart_3989343 : Nat := 118140960795 + 3989343 * 2 ^ 59
def prefixEnd_3989343 : Nat := 4983230072969 + 3 ^ 40 * 3989343 * 2
def baseEnd_3989343 : Nat := 1365633636432993607243901

theorem tailTrace_3989343 : CollatzResearch.WordTrace tailWord_3989343 prefixEnd_3989343 1365633636432993607243901 := by
  unfold tailWord_3989343
  simp only [CollatzResearch.WordTrace]
  refine ⟨145503292786299111386412683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97002195190866074257608455 145503292786299111386412683)
  ·
    refine ⟨218254939179448667079619025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145503292786299111386412683 218254939179448667079619025)
    ·
      refine ⟨163691204384586500309714269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218254939179448667079619025 163691204384586500309714269)
      ·
        refine ⟨61384201644219937616142851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163691204384586500309714269 61384201644219937616142851)
        ·
          refine ⟨92076302466329906424214277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61384201644219937616142851 92076302466329906424214277)
          ·
            refine ⟨17264306712436857454540177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92076302466329906424214277 17264306712436857454540177)
            ·
              refine ⟨12948230034327643090905133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17264306712436857454540177 12948230034327643090905133)
              ·
                refine ⟨4855586262872866159089425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12948230034327643090905133 4855586262872866159089425)
                ·
                  refine ⟨3641689697154649619317069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4855586262872866159089425 3641689697154649619317069)
                  ·
                    refine ⟨1365633636432993607243901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3641689697154649619317069 1365633636432993607243901)
                    ·
                      rfl

theorem cell22_3989343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 3, 2, 3].length) (baseStart_3989343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3989343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3989343 prefixEnd_3989343 := by exact prefixLift 3989343
  have htrace : WordTrace (prefixWord ++ tailWord_3989343) baseStart_3989343 baseEnd_3989343 := by
    simpa [prefixWord, tailWord_3989343, baseEnd_3989343] using wordTrace_append hprefix tailTrace_3989343
  have hstable : (prefixWord ++ tailWord_3989343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989343).length < 2 ^ (prefixWord ++ tailWord_3989343).sum := by decide
  have hdescent : baseEnd_3989343 < baseStart_3989343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989358 : List Nat := [4, 1, 2, 3, 1, 2, 1, 1, 1, 6]
def baseStart_3989358 : Nat := 118140960795 + 3989358 * 2 ^ 59
def prefixEnd_3989358 : Nat := 4983230072969 + 3 ^ 40 * 3989358 * 2
def baseEnd_3989358 : Nat := 1365638771239538568118855

theorem tailTrace_3989358 : CollatzResearch.WordTrace tailWord_3989358 prefixEnd_3989358 1365638771239538568118855 := by
  unfold tailWord_3989358
  simp only [CollatzResearch.WordTrace]
  refine ⟨18187979985155596118526091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97002559920829845965472485 18187979985155596118526091)
  ·
    refine ⟨27281969977733394177789137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18187979985155596118526091 27281969977733394177789137)
    ·
      refine ⟨20461477483300045633341853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27281969977733394177789137 20461477483300045633341853)
      ·
        refine ⟨7673054056237517112503195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20461477483300045633341853 7673054056237517112503195)
        ·
          refine ⟨11509581084356275668754793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7673054056237517112503195 11509581084356275668754793)
          ·
            refine ⟨8632185813267206751566095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11509581084356275668754793 8632185813267206751566095)
            ·
              refine ⟨12948278719900810127349143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8632185813267206751566095 12948278719900810127349143)
              ·
                refine ⟨19422418079851215191023715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12948278719900810127349143 19422418079851215191023715)
                ·
                  refine ⟨29133627119776822786535573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19422418079851215191023715 29133627119776822786535573)
                  ·
                    refine ⟨1365638771239538568118855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29133627119776822786535573 1365638771239538568118855)
                    ·
                      rfl

theorem cell22_3989358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_3989358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3989358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3989358 prefixEnd_3989358 := by exact prefixLift 3989358
  have htrace : WordTrace (prefixWord ++ tailWord_3989358) baseStart_3989358 baseEnd_3989358 := by
    simpa [prefixWord, tailWord_3989358, baseEnd_3989358] using wordTrace_append hprefix tailTrace_3989358
  have hstable : (prefixWord ++ tailWord_3989358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989358).length < 2 ^ (prefixWord ++ tailWord_3989358).sum := by decide
  have hdescent : baseEnd_3989358 < baseStart_3989358 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989371 : List Nat := [1, 1, 1, 1, 1, 5, 1, 1, 7, 3]
def baseStart_3989371 : Nat := 118140960795 + 3989371 * 2 ^ 59
def prefixEnd_3989371 : Nat := 4983230072969 + 3 ^ 40 * 3989371 * 2
def baseEnd_3989371 : Nat := 1365643221405210867543815

theorem tailTrace_3989371 : CollatzResearch.WordTrace tailWord_3989371 prefixEnd_3989371 1365643221405210867543815 := by
  unfold tailWord_3989371
  simp only [CollatzResearch.WordTrace]
  refine ⟨145504314030197672168431967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97002876020131781445621311 145504314030197672168431967)
  ·
    refine ⟨218256471045296508252647951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145504314030197672168431967 218256471045296508252647951)
    ·
      refine ⟨327384706567944762378971927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218256471045296508252647951 327384706567944762378971927)
      ·
        refine ⟨491077059851917143568457891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327384706567944762378971927 491077059851917143568457891)
        ·
          refine ⟨736615589777875715352686837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 491077059851917143568457891 736615589777875715352686837)
          ·
            refine ⟨69057711541675848314314391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 736615589777875715352686837 69057711541675848314314391)
            ·
              refine ⟨103586567312513772471471587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69057711541675848314314391 103586567312513772471471587)
              ·
                refine ⟨155379850968770658707207381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103586567312513772471471587 155379850968770658707207381)
                ·
                  refine ⟨3641715257080562313450173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 155379850968770658707207381 3641715257080562313450173)
                  ·
                    refine ⟨1365643221405210867543815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3641715257080562313450173 1365643221405210867543815)
                    ·
                      rfl

theorem cell22_3989371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 7, 3].length) (baseStart_3989371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3989371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3989371 prefixEnd_3989371 := by exact prefixLift 3989371
  have htrace : WordTrace (prefixWord ++ tailWord_3989371) baseStart_3989371 baseEnd_3989371 := by
    simpa [prefixWord, tailWord_3989371, baseEnd_3989371] using wordTrace_append hprefix tailTrace_3989371
  have hstable : (prefixWord ++ tailWord_3989371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989371).length < 2 ^ (prefixWord ++ tailWord_3989371).sum := by decide
  have hdescent : baseEnd_3989371 < baseStart_3989371 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989401 : List Nat := [1, 2, 1, 2, 1, 3, 2, 5, 5]
def baseStart_3989401 : Nat := 118140960795 + 3989401 * 2 ^ 59
def prefixEnd_3989401 : Nat := 4983230072969 + 3 ^ 40 * 3989401 * 2
def baseEnd_3989401 : Nat := 455217830339433596431241

theorem tailTrace_3989401 : CollatzResearch.WordTrace tailWord_3989401 prefixEnd_3989401 455217830339433596431241 := by
  unfold tailWord_3989401
  simp only [CollatzResearch.WordTrace]
  refine ⟨145505408220088987292024057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97003605480059324861349371 145505408220088987292024057)
  ·
    refine ⟨109129056165066740469018043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145505408220088987292024057 109129056165066740469018043)
    ·
      refine ⟨163693584247600110703527065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109129056165066740469018043 163693584247600110703527065)
      ·
        refine ⟨122770188185700083027645299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163693584247600110703527065 122770188185700083027645299)
        ·
          refine ⟨184155282278550124541467949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122770188185700083027645299 184155282278550124541467949)
          ·
            refine ⟨69058230854456296703050481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184155282278550124541467949 69058230854456296703050481)
            ·
              refine ⟨51793673140842222527287861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69058230854456296703050481 51793673140842222527287861)
              ·
                refine ⟨4855656856953958361933237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51793673140842222527287861 4855656856953958361933237)
                ·
                  refine ⟨455217830339433596431241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4855656856953958361933237 455217830339433596431241)
                  ·
                    rfl

theorem cell22_3989401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 5, 5].length) (baseStart_3989401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3989401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3989401 prefixEnd_3989401 := by exact prefixLift 3989401
  have htrace : WordTrace (prefixWord ++ tailWord_3989401) baseStart_3989401 baseEnd_3989401 := by
    simpa [prefixWord, tailWord_3989401, baseEnd_3989401] using wordTrace_append hprefix tailTrace_3989401
  have hstable : (prefixWord ++ tailWord_3989401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989401).length < 2 ^ (prefixWord ++ tailWord_3989401).sum := by decide
  have hdescent : baseEnd_3989401 < baseStart_3989401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989431 : List Nat := [1, 1, 3, 1, 3, 1, 1, 2, 5, 4]
def baseStart_3989431 : Nat := 118140960795 + 3989431 * 2 ^ 59
def prefixEnd_3989431 : Nat := 4983230072969 + 3 ^ 40 * 3989431 * 2
def baseEnd_3989431 : Nat := 1365663760631390711043631

theorem tailTrace_3989431 : CollatzResearch.WordTrace tailWord_3989431 prefixEnd_3989431 1365663760631390711043631 := by
  unfold tailWord_3989431
  simp only [CollatzResearch.WordTrace]
  refine ⟨145506502409980302415616147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97004334939986868277077431 145506502409980302415616147)
  ·
    refine ⟨218259753614970453623424221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145506502409980302415616147 218259753614970453623424221)
    ·
      refine ⟨81847407605613920108784083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218259753614970453623424221 81847407605613920108784083)
      ·
        refine ⟨122771111408420880163176125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81847407605613920108784083 122771111408420880163176125)
        ·
          refine ⟨46039166778157830061191047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122771111408420880163176125 46039166778157830061191047)
          ·
            refine ⟨69058750167236745091786571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46039166778157830061191047 69058750167236745091786571)
            ·
              refine ⟨103588125250855117637679857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69058750167236745091786571 103588125250855117637679857)
              ·
                refine ⟨77691093938141338228259893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103588125250855117637679857 77691093938141338228259893)
                ·
                  refine ⟨7283540056700750458899365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77691093938141338228259893 7283540056700750458899365)
                  ·
                    refine ⟨1365663760631390711043631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7283540056700750458899365 1365663760631390711043631)
                    ·
                      rfl

theorem cell22_3989431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 5, 4].length) (baseStart_3989431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3989431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3989431 prefixEnd_3989431 := by exact prefixLift 3989431
  have htrace : WordTrace (prefixWord ++ tailWord_3989431) baseStart_3989431 baseEnd_3989431 := by
    simpa [prefixWord, tailWord_3989431, baseEnd_3989431] using wordTrace_append hprefix tailTrace_3989431
  have hstable : (prefixWord ++ tailWord_3989431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989431).length < 2 ^ (prefixWord ++ tailWord_3989431).sum := by decide
  have hdescent : baseEnd_3989431 < baseStart_3989431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989497 : List Nat := [1, 2, 1, 3, 1, 6, 2, 2, 4]
def baseStart_3989497 : Nat := 118140960795 + 3989497 * 2 ^ 59
def prefixEnd_3989497 : Nat := 4983230072969 + 3 ^ 40 * 3989497 * 2
def baseEnd_3989497 : Nat := 455228784593396179631143

theorem tailTrace_3989497 : CollatzResearch.WordTrace tailWord_3989497 prefixEnd_3989497 455228784593396179631143 := by
  unfold tailWord_3989497
  simp only [CollatzResearch.WordTrace]
  refine ⟨145508909627741195687518745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97005939751827463791679163 145508909627741195687518745)
  ·
    refine ⟨109131682220805896765639059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145508909627741195687518745 109131682220805896765639059)
    ·
      refine ⟨163697523331208845148458589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109131682220805896765639059 163697523331208845148458589)
      ·
        refine ⟨61386571249203316930671971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163697523331208845148458589 61386571249203316930671971)
        ·
          refine ⟨92079856873804975396007957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61386571249203316930671971 92079856873804975396007957)
          ·
            refine ⟨4316243290959608221687873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 92079856873804975396007957 4316243290959608221687873)
            ·
              refine ⟨3237182468219706166265905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4316243290959608221687873 3237182468219706166265905)
              ·
                refine ⟨2427886851164779624699429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3237182468219706166265905 2427886851164779624699429)
                ·
                  refine ⟨455228784593396179631143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2427886851164779624699429 455228784593396179631143)
                  ·
                    rfl

theorem cell22_3989497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 2, 2, 4].length) (baseStart_3989497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3989497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3989497 prefixEnd_3989497 := by exact prefixLift 3989497
  have htrace : WordTrace (prefixWord ++ tailWord_3989497) baseStart_3989497 baseEnd_3989497 := by
    simpa [prefixWord, tailWord_3989497, baseEnd_3989497] using wordTrace_append hprefix tailTrace_3989497
  have hstable : (prefixWord ++ tailWord_3989497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989497).length < 2 ^ (prefixWord ++ tailWord_3989497).sum := by decide
  have hdescent : baseEnd_3989497 < baseStart_3989497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989523 : List Nat := [1, 1, 1, 2, 1, 4, 3, 1, 5, 3]
def baseStart_3989523 : Nat := 118140960795 + 3989523 * 2 ^ 59
def prefixEnd_3989523 : Nat := 4983230072969 + 3 ^ 40 * 3989523 * 2
def baseEnd_3989523 : Nat := 1365695254111533137743349

theorem tailTrace_3989523 : CollatzResearch.WordTrace tailWord_3989523 prefixEnd_3989523 1365695254111533137743349 := by
  unfold tailWord_3989523
  simp only [CollatzResearch.WordTrace]
  refine ⟨145509857925647002127965223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97006571950431334751976815 145509857925647002127965223)
  ·
    refine ⟨218264786888470503191947835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145509857925647002127965223 218264786888470503191947835)
    ·
      refine ⟨327397180332705754787921753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218264786888470503191947835 327397180332705754787921753)
      ·
        refine ⟨245547885249529316090941315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327397180332705754787921753 245547885249529316090941315)
        ·
          refine ⟨368321827874293974136411973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245547885249529316090941315 368321827874293974136411973)
          ·
            refine ⟨69060342726430120150577245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 368321827874293974136411973 69060342726430120150577245)
            ·
              refine ⟨25897628522411295056466467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69060342726430120150577245 25897628522411295056466467)
              ·
                refine ⟨38846442783616942584699701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25897628522411295056466467 38846442783616942584699701)
                ·
                  refine ⟨3641854010964088367315597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38846442783616942584699701 3641854010964088367315597)
                  ·
                    refine ⟨1365695254111533137743349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3641854010964088367315597 1365695254111533137743349)
                    ·
                      rfl

theorem cell22_3989523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 5, 3].length) (baseStart_3989523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3989523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3989523 prefixEnd_3989523 := by exact prefixLift 3989523
  have htrace : WordTrace (prefixWord ++ tailWord_3989523) baseStart_3989523 baseEnd_3989523 := by
    simpa [prefixWord, tailWord_3989523, baseEnd_3989523] using wordTrace_append hprefix tailTrace_3989523
  have hstable : (prefixWord ++ tailWord_3989523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989523).length < 2 ^ (prefixWord ++ tailWord_3989523).sum := by decide
  have hdescent : baseEnd_3989523 < baseStart_3989523 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989525 : List Nat := [1, 3, 2, 1, 5, 1, 3, 6]
def baseStart_3989525 : Nat := 118140960795 + 3989525 * 2 ^ 59
def prefixEnd_3989525 : Nat := 4983230072969 + 3 ^ 40 * 3989525 * 2
def baseEnd_3989525 : Nat := 151743993194711755465927

theorem tailTrace_3989525 : CollatzResearch.WordTrace tailWord_3989525 prefixEnd_3989525 151743993194711755465927 := by
  unfold tailWord_3989525
  simp only [CollatzResearch.WordTrace]
  refine ⟨145509930871639756469538029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97006620581093170979692019 145509930871639756469538029)
  ·
    refine ⟨54566224076864908676076761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145509930871639756469538029 54566224076864908676076761)
    ·
      refine ⟨40924668057648681507057571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54566224076864908676076761 40924668057648681507057571)
      ·
        refine ⟨61387002086473022260586357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40924668057648681507057571 61387002086473022260586357)
        ·
          refine ⟨5755031445606845836929971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61387002086473022260586357 5755031445606845836929971)
          ·
            refine ⟨8632547168410268755394957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5755031445606845836929971 8632547168410268755394957)
            ·
              refine ⟨3237205188153850783273109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8632547168410268755394957 3237205188153850783273109)
              ·
                refine ⟨151743993194711755465927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3237205188153850783273109 151743993194711755465927)
                ·
                  rfl

theorem cell22_3989525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 3, 6].length) (baseStart_3989525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3989525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3989525 prefixEnd_3989525 := by exact prefixLift 3989525
  have htrace : WordTrace (prefixWord ++ tailWord_3989525) baseStart_3989525 baseEnd_3989525 := by
    simpa [prefixWord, tailWord_3989525, baseEnd_3989525] using wordTrace_append hprefix tailTrace_3989525
  have hstable : (prefixWord ++ tailWord_3989525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989525).length < 2 ^ (prefixWord ++ tailWord_3989525).sum := by decide
  have hdescent : baseEnd_3989525 < baseStart_3989525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989527 : List Nat := [1, 1, 3, 5, 2, 2, 1, 1, 2, 4]
def baseStart_3989527 : Nat := 118140960795 + 3989527 * 2 ^ 59
def prefixEnd_3989527 : Nat := 4983230072969 + 3 ^ 40 * 3989527 * 2
def baseEnd_3989527 : Nat := 1365696623393278460643337

theorem tailTrace_3989527 : CollatzResearch.WordTrace tailWord_3989527 prefixEnd_3989527 1365696623393278460643337 := by
  unfold tailWord_3989527
  simp only [CollatzResearch.WordTrace]
  refine ⟨145510003817632510811110835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97006669211755007207407223 145510003817632510811110835)
  ·
    refine ⟨218265005726448766216666253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145510003817632510811110835 218265005726448766216666253)
    ·
      refine ⟨81849377147418287331249845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218265005726448766216666253 81849377147418287331249845)
      ·
        refine ⟨7673379107570464437304673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81849377147418287331249845 7673379107570464437304673)
        ·
          refine ⟨5755034330677848327978505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7673379107570464437304673 5755034330677848327978505)
          ·
            refine ⟨4316275748008386245983879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5755034330677848327978505 4316275748008386245983879)
            ·
              refine ⟨6474413622012579368975819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4316275748008386245983879 6474413622012579368975819)
              ·
                refine ⟨9711620433018869053463729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6474413622012579368975819 9711620433018869053463729)
                ·
                  refine ⟨7283715324764151790097797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9711620433018869053463729 7283715324764151790097797)
                  ·
                    refine ⟨1365696623393278460643337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7283715324764151790097797 1365696623393278460643337)
                    ·
                      rfl

theorem cell22_3989527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 1, 2, 4].length) (baseStart_3989527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3989527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3989527 prefixEnd_3989527 := by exact prefixLift 3989527
  have htrace : WordTrace (prefixWord ++ tailWord_3989527) baseStart_3989527 baseEnd_3989527 := by
    simpa [prefixWord, tailWord_3989527, baseEnd_3989527] using wordTrace_append hprefix tailTrace_3989527
  have hstable : (prefixWord ++ tailWord_3989527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989527).length < 2 ^ (prefixWord ++ tailWord_3989527).sum := by decide
  have hdescent : baseEnd_3989527 < baseStart_3989527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989553 : List Nat := [1, 2, 2, 3, 1, 4, 1, 1, 7]
def baseStart_3989553 : Nat := 118140960795 + 3989553 * 2 ^ 59
def prefixEnd_3989553 : Nat := 4983230072969 + 3 ^ 40 * 3989553 * 2
def baseEnd_3989553 : Nat := 455235174574874353164419

theorem tailTrace_3989553 : CollatzResearch.WordTrace tailWord_3989553 prefixEnd_3989553 455235174574874353164419 := by
  unfold tailWord_3989553
  simp only [CollatzResearch.WordTrace]
  refine ⟨145510952115538317251557313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97007301410358878167704875 145510952115538317251557313)
  ·
    refine ⟨109133214086653737938667985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145510952115538317251557313 109133214086653737938667985)
    ·
      refine ⟨81849910564990303454000989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109133214086653737938667985 81849910564990303454000989)
      ·
        refine ⟨30693716461871363795250371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81849910564990303454000989 30693716461871363795250371)
        ·
          refine ⟨46040574692807045692875557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30693716461871363795250371 46040574692807045692875557)
          ·
            refine ⟨8632607754901321067414167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46040574692807045692875557 8632607754901321067414167)
            ·
              refine ⟨12948911632351981601121251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8632607754901321067414167 12948911632351981601121251)
              ·
                refine ⟨19423367448527972401681877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12948911632351981601121251 19423367448527972401681877)
                ·
                  refine ⟨455235174574874353164419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19423367448527972401681877 455235174574874353164419)
                  ·
                    rfl

theorem cell22_3989553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 7].length) (baseStart_3989553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3989553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3989553 prefixEnd_3989553 := by exact prefixLift 3989553
  have htrace : WordTrace (prefixWord ++ tailWord_3989553) baseStart_3989553 baseEnd_3989553 := by
    simpa [prefixWord, tailWord_3989553, baseEnd_3989553] using wordTrace_append hprefix tailTrace_3989553
  have hstable : (prefixWord ++ tailWord_3989553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989553).length < 2 ^ (prefixWord ++ tailWord_3989553).sum := by decide
  have hdescent : baseEnd_3989553 < baseStart_3989553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989557 : List Nat := [1, 3, 3, 1, 1, 1, 4, 4, 1, 3]
def baseStart_3989557 : Nat := 118140960795 + 3989557 * 2 ^ 59
def prefixEnd_3989557 : Nat := 4983230072969 + 3 ^ 40 * 3989557 * 2
def baseEnd_3989557 : Nat := 1365706893006368382393245

theorem tailTrace_3989557 : CollatzResearch.WordTrace tailWord_3989557 prefixEnd_3989557 1365706893006368382393245 := by
  unfold tailWord_3989557
  simp only [CollatzResearch.WordTrace]
  refine ⟨145511098007523825934702925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97007398671682550623135283 145511098007523825934702925)
  ·
    refine ⟨54566661752821434725513597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145511098007523825934702925 54566661752821434725513597)
    ·
      refine ⟨20462498157308038022067599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54566661752821434725513597 20462498157308038022067599)
      ·
        refine ⟨30693747235962057033101399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20462498157308038022067599 30693747235962057033101399)
        ·
          refine ⟨46040620853943085549652099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30693747235962057033101399 46040620853943085549652099)
          ·
            refine ⟨69060931280914628324478149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46040620853943085549652099 69060931280914628324478149)
            ·
              refine ⟨12948924615171492810839653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69060931280914628324478149 12948924615171492810839653)
              ·
                refine ⟨2427923365344654902032435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12948924615171492810839653 2427923365344654902032435)
                ·
                  refine ⟨3641885048016982353048653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2427923365344654902032435 3641885048016982353048653)
                  ·
                    refine ⟨1365706893006368382393245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3641885048016982353048653 1365706893006368382393245)
                    ·
                      rfl

theorem cell22_3989557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 4, 1, 3].length) (baseStart_3989557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3989557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3989557 prefixEnd_3989557 := by exact prefixLift 3989557
  have htrace : WordTrace (prefixWord ++ tailWord_3989557) baseStart_3989557 baseEnd_3989557 := by
    simpa [prefixWord, tailWord_3989557, baseEnd_3989557] using wordTrace_append hprefix tailTrace_3989557
  have hstable : (prefixWord ++ tailWord_3989557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989557).length < 2 ^ (prefixWord ++ tailWord_3989557).sum := by decide
  have hdescent : baseEnd_3989557 < baseStart_3989557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989568 : List Nat := [2, 1, 1, 2, 2, 4, 2, 1, 2, 5]
def baseStart_3989568 : Nat := 118140960795 + 3989568 * 2 ^ 59
def prefixEnd_3989568 : Nat := 4983230072969 + 3 ^ 40 * 3989568 * 2
def baseEnd_3989568 : Nat := 1365710658531168020368211

theorem tailTrace_3989568 : CollatzResearch.WordTrace tailWord_3989568 prefixEnd_3989568 1365710658531168020368211 := by
  unfold tailWord_3989568
  simp only [CollatzResearch.WordTrace]
  refine ⟨72755749605241987406676679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97007666140322649875568905 72755749605241987406676679)
  ·
    refine ⟨109133624407862981110015019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72755749605241987406676679 109133624407862981110015019)
    ·
      refine ⟨163700436611794471665022529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109133624407862981110015019 163700436611794471665022529)
      ·
        refine ⟨122775327458845853748766897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163700436611794471665022529 122775327458845853748766897)
        ·
          refine ⟨92081495594134390311575173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122775327458845853748766897 92081495594134390311575173)
          ·
            refine ⟨17265280423900198183420345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92081495594134390311575173 17265280423900198183420345)
            ·
              refine ⟨12948960317925148637565259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17265280423900198183420345 12948960317925148637565259)
              ·
                refine ⟨19423440476887722956347889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12948960317925148637565259 19423440476887722956347889)
                ·
                  refine ⟨14567580357665792217260917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19423440476887722956347889 14567580357665792217260917)
                  ·
                    refine ⟨1365710658531168020368211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14567580357665792217260917 1365710658531168020368211)
                    ·
                      rfl

theorem cell22_3989568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 2, 5].length) (baseStart_3989568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3989568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3989568 prefixEnd_3989568 := by exact prefixLift 3989568
  have htrace : WordTrace (prefixWord ++ tailWord_3989568) baseStart_3989568 baseEnd_3989568 := by
    simpa [prefixWord, tailWord_3989568, baseEnd_3989568] using wordTrace_append hprefix tailTrace_3989568
  have hstable : (prefixWord ++ tailWord_3989568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989568).length < 2 ^ (prefixWord ++ tailWord_3989568).sum := by decide
  have hdescent : baseEnd_3989568 < baseStart_3989568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989600 : List Nat := [2, 1, 1, 3, 2, 3, 2, 3, 1, 4]
def baseStart_3989600 : Nat := 118140960795 + 3989600 * 2 ^ 59
def prefixEnd_3989600 : Nat := 4983230072969 + 3 ^ 40 * 3989600 * 2
def baseEnd_3989600 : Nat := 1365721612785130603568113

theorem tailTrace_3989600 : CollatzResearch.WordTrace tailWord_3989600 prefixEnd_3989600 1365721612785130603568113 := by
  unfold tailWord_3989600
  simp only [CollatzResearch.WordTrace]
  refine ⟨72756333173184022139259127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97008444230912029519012169 72756333173184022139259127)
  ·
    refine ⟨109134499759776033208888691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72756333173184022139259127 109134499759776033208888691)
    ·
      refine ⟨163701749639664049813333037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109134499759776033208888691 163701749639664049813333037)
      ·
        refine ⟨61388156114874018679999889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163701749639664049813333037 61388156114874018679999889)
        ·
          refine ⟨46041117086155514009999917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61388156114874018679999889 46041117086155514009999917)
          ·
            refine ⟨17265418907308317753749969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46041117086155514009999917 17265418907308317753749969)
            ·
              refine ⟨12949064180481238315312477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17265418907308317753749969 12949064180481238315312477)
              ·
                refine ⟨4855899067680464368242179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12949064180481238315312477 4855899067680464368242179)
                ·
                  refine ⟨7283848601520696552363269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4855899067680464368242179 7283848601520696552363269)
                  ·
                    refine ⟨1365721612785130603568113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7283848601520696552363269 1365721612785130603568113)
                    ·
                      rfl

theorem cell22_3989600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 3, 1, 4].length) (baseStart_3989600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3989600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3989600 prefixEnd_3989600 := by exact prefixLift 3989600
  have htrace : WordTrace (prefixWord ++ tailWord_3989600) baseStart_3989600 baseEnd_3989600 := by
    simpa [prefixWord, tailWord_3989600, baseEnd_3989600] using wordTrace_append hprefix tailTrace_3989600
  have hstable : (prefixWord ++ tailWord_3989600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989600).length < 2 ^ (prefixWord ++ tailWord_3989600).sum := by decide
  have hdescent : baseEnd_3989600 < baseStart_3989600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989615 : List Nat := [1, 1, 2, 1, 3, 6, 1, 1, 6]
def baseStart_3989615 : Nat := 118140960795 + 3989615 * 2 ^ 59
def prefixEnd_3989615 : Nat := 4983230072969 + 3 ^ 40 * 3989615 * 2
def baseEnd_3989615 : Nat := 455242249197225188147689

theorem tailTrace_3989615 : CollatzResearch.WordTrace tailWord_3989615 prefixEnd_3989615 455242249197225188147689 := by
  unfold tailWord_3989615
  simp only [CollatzResearch.WordTrace]
  refine ⟨145513213441313701840314299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97008808960875801226876199 145513213441313701840314299)
  ·
    refine ⟨218269820161970552760471449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145513213441313701840314299 218269820161970552760471449)
    ·
      refine ⟨163702365121477914570353587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218269820161970552760471449 163702365121477914570353587)
      ·
        refine ⟨245553547682216871855530381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163702365121477914570353587 245553547682216871855530381)
        ·
          refine ⟨92082580380831326945823893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 245553547682216871855530381 92082580380831326945823893)
          ·
            refine ⟨4316370955351468450585495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 92082580380831326945823893 4316370955351468450585495)
            ·
              refine ⟨6474556433027202675878243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4316370955351468450585495 6474556433027202675878243)
              ·
                refine ⟨9711834649540804013817365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6474556433027202675878243 9711834649540804013817365)
                ·
                  refine ⟨455242249197225188147689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9711834649540804013817365 455242249197225188147689)
                  ·
                    rfl

theorem cell22_3989615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 1, 6].length) (baseStart_3989615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3989615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3989615 prefixEnd_3989615 := by exact prefixLift 3989615
  have htrace : WordTrace (prefixWord ++ tailWord_3989615) baseStart_3989615 baseEnd_3989615 := by
    simpa [prefixWord, tailWord_3989615, baseEnd_3989615] using wordTrace_append hprefix tailTrace_3989615
  have hstable : (prefixWord ++ tailWord_3989615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989615).length < 2 ^ (prefixWord ++ tailWord_3989615).sum := by decide
  have hdescent : baseEnd_3989615 < baseStart_3989615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989666 : List Nat := [3, 3, 1, 3, 1, 3, 2, 2, 4]
def baseStart_3989666 : Nat := 118140960795 + 3989666 * 2 ^ 59
def prefixEnd_3989666 : Nat := 4983230072969 + 3 ^ 40 * 3989666 * 2
def baseEnd_3989666 : Nat := 455248068644642810472637

theorem tailTrace_3989666 : CollatzResearch.WordTrace tailWord_3989666 prefixEnd_3989666 455248068644642810472637 := by
  unfold tailWord_3989666
  simp only [CollatzResearch.WordTrace]
  refine ⟨36378768391032234387605213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97010049042752625033613901 36378768391032234387605213)
  ·
    refine ⟨13642038146637087895351955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36378768391032234387605213 13642038146637087895351955)
    ·
      refine ⟨20463057219955631843027933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13642038146637087895351955 20463057219955631843027933)
      ·
        refine ⟨7673646457483361941135475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20463057219955631843027933 7673646457483361941135475)
        ·
          refine ⟨11510469686225042911703213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7673646457483361941135475 11510469686225042911703213)
          ·
            refine ⟨4316426132334391091888705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11510469686225042911703213 4316426132334391091888705)
            ·
              refine ⟨3237319599250793318916529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4316426132334391091888705 3237319599250793318916529)
              ·
                refine ⟨2427989699438094989187397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3237319599250793318916529 2427989699438094989187397)
                ·
                  refine ⟨455248068644642810472637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2427989699438094989187397 455248068644642810472637)
                  ·
                    rfl

theorem cell22_3989666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 2, 2, 4].length) (baseStart_3989666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3989666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3989666 prefixEnd_3989666 := by exact prefixLift 3989666
  have htrace : WordTrace (prefixWord ++ tailWord_3989666) baseStart_3989666 baseEnd_3989666 := by
    simpa [prefixWord, tailWord_3989666, baseEnd_3989666] using wordTrace_append hprefix tailTrace_3989666
  have hstable : (prefixWord ++ tailWord_3989666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989666).length < 2 ^ (prefixWord ++ tailWord_3989666).sum := by decide
  have hdescent : baseEnd_3989666 < baseStart_3989666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989677 : List Nat := [1, 5, 2, 1, 2, 3, 1, 7]
def baseStart_3989677 : Nat := 118140960795 + 3989677 * 2 ^ 59
def prefixEnd_3989677 : Nat := 4983230072969 + 3 ^ 40 * 3989677 * 2
def baseEnd_3989677 : Nat := 151749774606525341043653

theorem tailTrace_3989677 : CollatzResearch.WordTrace tailWord_3989677 prefixEnd_3989677 151749774606525341043653 := by
  unfold tailWord_3989677
  simp only [CollatzResearch.WordTrace]
  refine ⟨145515474767089086429071285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97010316511392724286047523 145515474767089086429071285)
  ·
    refine ⟨13642075759414601852725433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 145515474767089086429071285 13642075759414601852725433)
    ·
      refine ⟨10231556819560951389544075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13642075759414601852725433 10231556819560951389544075)
      ·
        refine ⟨15347335229341427084316113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10231556819560951389544075 15347335229341427084316113)
        ·
          refine ⟨11510501422006070313237085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15347335229341427084316113 11510501422006070313237085)
          ·
            refine ⟨4316438033252276367463907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11510501422006070313237085 4316438033252276367463907)
            ·
              refine ⟨6474657049878414551195861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4316438033252276367463907 6474657049878414551195861)
              ·
                refine ⟨151749774606525341043653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6474657049878414551195861 151749774606525341043653)
                ·
                  rfl

theorem cell22_3989677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 7].length) (baseStart_3989677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3989677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3989677 prefixEnd_3989677 := by exact prefixLift 3989677
  have htrace : WordTrace (prefixWord ++ tailWord_3989677) baseStart_3989677 baseEnd_3989677 := by
    simpa [prefixWord, tailWord_3989677, baseEnd_3989677] using wordTrace_append hprefix tailTrace_3989677
  have hstable : (prefixWord ++ tailWord_3989677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989677).length < 2 ^ (prefixWord ++ tailWord_3989677).sum := by decide
  have hdescent : baseEnd_3989677 < baseStart_3989677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989720 : List Nat := [2, 1, 2, 2, 4, 1, 1, 2, 2, 5]
def baseStart_3989720 : Nat := 118140960795 + 3989720 * 2 ^ 59
def prefixEnd_3989720 : Nat := 4983230072969 + 3 ^ 40 * 3989720 * 2
def baseEnd_3989720 : Nat := 1365762691237490290567745

theorem tailTrace_3989720 : CollatzResearch.WordTrace tailWord_3989720 prefixEnd_3989720 1365762691237490290567745 := by
  unfold tailWord_3989720
  simp only [CollatzResearch.WordTrace]
  refine ⟨72758521552966652386443307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97011362070622203181924409 72758521552966652386443307)
  ·
    refine ⟨109137782329449978579664961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72758521552966652386443307 109137782329449978579664961)
    ·
      refine ⟨81853336747087483934748721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109137782329449978579664961 81853336747087483934748721)
      ·
        refine ⟨61390002560315612951061541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81853336747087483934748721 61390002560315612951061541)
        ·
          refine ⟨11510625480059177428324039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61390002560315612951061541 11510625480059177428324039)
          ·
            refine ⟨17265938220088766142486059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11510625480059177428324039 17265938220088766142486059)
            ·
              refine ⟨25898907330133149213729089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17265938220088766142486059 25898907330133149213729089)
              ·
                refine ⟨19424180497599861910296817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25898907330133149213729089 19424180497599861910296817)
                ·
                  refine ⟨14568135373199896432722613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19424180497599861910296817 14568135373199896432722613)
                  ·
                    refine ⟨1365762691237490290567745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14568135373199896432722613 1365762691237490290567745)
                    ·
                      rfl

theorem cell22_3989720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 2, 5].length) (baseStart_3989720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3989720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3989720 prefixEnd_3989720 := by exact prefixLift 3989720
  have htrace : WordTrace (prefixWord ++ tailWord_3989720) baseStart_3989720 baseEnd_3989720 := by
    simpa [prefixWord, tailWord_3989720, baseEnd_3989720] using wordTrace_append hprefix tailTrace_3989720
  have hstable : (prefixWord ++ tailWord_3989720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989720).length < 2 ^ (prefixWord ++ tailWord_3989720).sum := by decide
  have hdescent : baseEnd_3989720 < baseStart_3989720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989784 : List Nat := [2, 1, 2, 3, 1, 2, 5, 2, 4]
def baseStart_3989784 : Nat := 118140960795 + 3989784 * 2 ^ 59
def prefixEnd_3989784 : Nat := 4983230072969 + 3 ^ 40 * 3989784 * 2
def baseEnd_3989784 : Nat := 455261533248471818989183

theorem tailTrace_3989784 : CollatzResearch.WordTrace tailWord_3989784 prefixEnd_3989784 455261533248471818989183 := by
  unfold tailWord_3989784
  simp only [CollatzResearch.WordTrace]
  refine ⟨72759688688850721851608203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97012918251800962468810937 72759688688850721851608203)
  ·
    refine ⟨109139533033276082777412305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72759688688850721851608203 109139533033276082777412305)
    ·
      refine ⟨81854649774957062083059229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109139533033276082777412305 81854649774957062083059229)
      ·
        refine ⟨30695493665608898281147211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81854649774957062083059229 30695493665608898281147211)
        ·
          refine ⟨46043240498413347421720817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30695493665608898281147211 46043240498413347421720817)
          ·
            refine ⟨34532430373810010566290613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46043240498413347421720817 34532430373810010566290613)
            ·
              refine ⟨3237415347544688490589745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34532430373810010566290613 3237415347544688490589745)
              ·
                refine ⟨2428061510658516367942309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3237415347544688490589745 2428061510658516367942309)
                ·
                  refine ⟨455261533248471818989183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2428061510658516367942309 455261533248471818989183)
                  ·
                    rfl

theorem cell22_3989784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 5, 2, 4].length) (baseStart_3989784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3989784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3989784 prefixEnd_3989784 := by exact prefixLift 3989784
  have htrace : WordTrace (prefixWord ++ tailWord_3989784) baseStart_3989784 baseEnd_3989784 := by
    simpa [prefixWord, tailWord_3989784, baseEnd_3989784] using wordTrace_append hprefix tailTrace_3989784
  have hstable : (prefixWord ++ tailWord_3989784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989784).length < 2 ^ (prefixWord ++ tailWord_3989784).sum := by decide
  have hdescent : baseEnd_3989784 < baseStart_3989784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989795 : List Nat := [1, 1, 1, 4, 2, 2, 4, 7]
def baseStart_3989795 : Nat := 118140960795 + 3989795 * 2 ^ 59
def prefixEnd_3989795 : Nat := 4983230072969 + 3 ^ 40 * 3989795 * 2
def baseEnd_3989795 : Nat := 151754262807801677215835

theorem tailTrace_3989795 : CollatzResearch.WordTrace tailWord_3989795 prefixEnd_3989795 151754262807801677215835 := by
  unfold tailWord_3989795
  simp only [CollatzResearch.WordTrace]
  refine ⟨145519778580661592581866839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97013185720441061721244559 145519778580661592581866839)
  ·
    refine ⟨218279667870992388872800259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145519778580661592581866839 218279667870992388872800259)
    ·
      refine ⟨327419501806488583309200389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218279667870992388872800259 327419501806488583309200389)
      ·
        refine ⟨61391156588716609370475073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 327419501806488583309200389 61391156588716609370475073)
        ·
          refine ⟨46043367441537457027856305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61391156588716609370475073 46043367441537457027856305)
          ·
            refine ⟨34532525581153092770892229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46043367441537457027856305 34532525581153092770892229)
            ·
              refine ⟨6474848546466204894542293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34532525581153092770892229 6474848546466204894542293)
              ·
                refine ⟨151754262807801677215835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6474848546466204894542293 151754262807801677215835)
                ·
                  rfl

theorem cell22_3989795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 7].length) (baseStart_3989795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3989795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3989795 prefixEnd_3989795 := by exact prefixLift 3989795
  have htrace : WordTrace (prefixWord ++ tailWord_3989795) baseStart_3989795 baseEnd_3989795 := by
    simpa [prefixWord, tailWord_3989795, baseEnd_3989795] using wordTrace_append hprefix tailTrace_3989795
  have hstable : (prefixWord ++ tailWord_3989795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989795).length < 2 ^ (prefixWord ++ tailWord_3989795).sum := by decide
  have hdescent : baseEnd_3989795 < baseStart_3989795 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989812 : List Nat := [2, 5, 1, 1, 1, 2, 2, 8]
def baseStart_3989812 : Nat := 118140960795 + 3989812 * 2 ^ 59
def prefixEnd_3989812 : Nat := 4983230072969 + 3 ^ 40 * 3989812 * 2
def baseEnd_3989812 : Nat := 151754909413070301918607

theorem tailTrace_3989812 : CollatzResearch.WordTrace tailWord_3989812 prefixEnd_3989812 151754909413070301918607 := by
  unfold tailWord_3989812
  simp only [CollatzResearch.WordTrace]
  refine ⟨72760199310800002242617845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97013599081066669656823793 72760199310800002242617845)
  ·
    refine ⟨6821268685387500210245423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72760199310800002242617845 6821268685387500210245423)
    ·
      refine ⟨10231903028081250315368135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6821268685387500210245423 10231903028081250315368135)
      ·
        refine ⟨15347854542121875473052203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10231903028081250315368135 15347854542121875473052203)
        ·
          refine ⟨23021781813182813209578305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15347854542121875473052203 23021781813182813209578305)
          ·
            refine ⟨17266336359887109907183729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23021781813182813209578305 17266336359887109907183729)
            ·
              refine ⟨12949752269915332430387797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17266336359887109907183729 12949752269915332430387797)
              ·
                refine ⟨151754909413070301918607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12949752269915332430387797 151754909413070301918607)
                ·
                  rfl

theorem cell22_3989812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 8].length) (baseStart_3989812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3989812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3989812 prefixEnd_3989812 := by exact prefixLift 3989812
  have htrace : WordTrace (prefixWord ++ tailWord_3989812) baseStart_3989812 baseEnd_3989812 := by
    simpa [prefixWord, tailWord_3989812, baseEnd_3989812] using wordTrace_append hprefix tailTrace_3989812
  have hstable : (prefixWord ++ tailWord_3989812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989812).length < 2 ^ (prefixWord ++ tailWord_3989812).sum := by decide
  have hdescent : baseEnd_3989812 < baseStart_3989812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989855 : List Nat := [1, 1, 2, 3, 1, 2, 3, 1, 1, 7]
def baseStart_3989855 : Nat := 118140960795 + 3989855 * 2 ^ 59
def prefixEnd_3989855 : Nat := 4983230072969 + 3 ^ 40 * 3989855 * 2
def baseEnd_3989855 : Nat := 1365808904496394938442331

theorem tailTrace_3989855 : CollatzResearch.WordTrace tailWord_3989855 prefixEnd_3989855 1365808904496394938442331 := by
  unfold tailWord_3989855
  simp only [CollatzResearch.WordTrace]
  refine ⟨145521966960444222829051019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97014644640296148552700679 145521966960444222829051019)
  ·
    refine ⟨218282950440666334243576529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145521966960444222829051019 218282950440666334243576529)
    ·
      refine ⟨163712212830499750682682397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218282950440666334243576529 163712212830499750682682397)
      ·
        refine ⟨61392079811437406506005899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163712212830499750682682397 61392079811437406506005899)
        ·
          refine ⟨92088119717156109759008849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61392079811437406506005899 92088119717156109759008849)
          ·
            refine ⟨69066089787867082319256637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92088119717156109759008849 69066089787867082319256637)
            ·
              refine ⟨25899783670450155869721239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69066089787867082319256637 25899783670450155869721239)
              ·
                refine ⟨38849675505675233804581859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25899783670450155869721239 38849675505675233804581859)
                ·
                  refine ⟨58274513258512850706872789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38849675505675233804581859 58274513258512850706872789)
                  ·
                    refine ⟨1365808904496394938442331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58274513258512850706872789 1365808904496394938442331)
                    ·
                      rfl

theorem cell22_3989855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 7].length) (baseStart_3989855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3989855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3989855 prefixEnd_3989855 := by exact prefixLift 3989855
  have htrace : WordTrace (prefixWord ++ tailWord_3989855) baseStart_3989855 baseEnd_3989855 := by
    simpa [prefixWord, tailWord_3989855, baseEnd_3989855] using wordTrace_append hprefix tailTrace_3989855
  have hstable : (prefixWord ++ tailWord_3989855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989855).length < 2 ^ (prefixWord ++ tailWord_3989855).sum := by decide
  have hdescent : baseEnd_3989855 < baseStart_3989855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989887 : List Nat := [1, 1, 2, 2, 1, 1, 2, 7, 1, 4]
def baseStart_3989887 : Nat := 118140960795 + 3989887 * 2 ^ 59
def prefixEnd_3989887 : Nat := 4983230072969 + 3 ^ 40 * 3989887 * 2
def baseEnd_3989887 : Nat := 1365819858750357521642233

theorem tailTrace_3989887 : CollatzResearch.WordTrace tailWord_3989887 prefixEnd_3989887 1365819858750357521642233 := by
  unfold tailWord_3989887
  simp only [CollatzResearch.WordTrace]
  refine ⟨145523134096328292294215915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97015422730885528196143943 145523134096328292294215915)
  ·
    refine ⟨218284701144492438441323873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145523134096328292294215915 218284701144492438441323873)
    ·
      refine ⟨163713525858369328830992905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218284701144492438441323873 163713525858369328830992905)
      ·
        refine ⟨122785144393776996623244679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163713525858369328830992905 122785144393776996623244679)
        ·
          refine ⟨184177716590665494934867019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122785144393776996623244679 184177716590665494934867019)
          ·
            refine ⟨276266574885998242402300529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184177716590665494934867019 276266574885998242402300529)
            ·
              refine ⟨207199931164498681801725397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 276266574885998242402300529 207199931164498681801725397)
              ·
                refine ⟨4856248386667937854727939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 207199931164498681801725397 4856248386667937854727939)
                ·
                  refine ⟨7284372580001906782091909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4856248386667937854727939 7284372580001906782091909)
                  ·
                    refine ⟨1365819858750357521642233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7284372580001906782091909 1365819858750357521642233)
                    ·
                      rfl

theorem cell22_3989887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 7, 1, 4].length) (baseStart_3989887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3989887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3989887 prefixEnd_3989887 := by exact prefixLift 3989887
  have htrace : WordTrace (prefixWord ++ tailWord_3989887) baseStart_3989887 baseEnd_3989887 := by
    simpa [prefixWord, tailWord_3989887, baseEnd_3989887] using wordTrace_append hprefix tailTrace_3989887
  have hstable : (prefixWord ++ tailWord_3989887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989887).length < 2 ^ (prefixWord ++ tailWord_3989887).sum := by decide
  have hdescent : baseEnd_3989887 < baseStart_3989887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989891 : List Nat := [1, 1, 1, 3, 7, 1, 1, 2, 5]
def baseStart_3989891 : Nat := 118140960795 + 3989891 * 2 ^ 59
def prefixEnd_3989891 : Nat := 4983230072969 + 3 ^ 40 * 3989891 * 2
def baseEnd_3989891 : Nat := 455273742677367614847407

theorem tailTrace_3989891 : CollatzResearch.WordTrace tailWord_3989891 prefixEnd_3989891 455273742677367614847407 := by
  unfold tailWord_3989891
  simp only [CollatzResearch.WordTrace]
  refine ⟨145523279988313800977361527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97015519992209200651574351 145523279988313800977361527)
  ·
    refine ⟨218284919982470701466042291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145523279988313800977361527 218284919982470701466042291)
    ·
      refine ⟨327427379973706052199063437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218284919982470701466042291 327427379973706052199063437)
      ·
        refine ⟨122785267490139769574648789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 327427379973706052199063437 122785267490139769574648789)
        ·
          refine ⟨2877779706800150849405831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 122785267490139769574648789 2877779706800150849405831)
          ·
            refine ⟨4316669560200226274108747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2877779706800150849405831 4316669560200226274108747)
            ·
              refine ⟨6475004340300339411163121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4316669560200226274108747 6475004340300339411163121)
              ·
                refine ⟨4856253255225254558372341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6475004340300339411163121 4856253255225254558372341)
                ·
                  refine ⟨455273742677367614847407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4856253255225254558372341 455273742677367614847407)
                  ·
                    rfl

theorem cell22_3989891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 2, 5].length) (baseStart_3989891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3989891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3989891 prefixEnd_3989891 := by exact prefixLift 3989891
  have htrace : WordTrace (prefixWord ++ tailWord_3989891) baseStart_3989891 baseEnd_3989891 := by
    simpa [prefixWord, tailWord_3989891, baseEnd_3989891] using wordTrace_append hprefix tailTrace_3989891
  have hstable : (prefixWord ++ tailWord_3989891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989891).length < 2 ^ (prefixWord ++ tailWord_3989891).sum := by decide
  have hdescent : baseEnd_3989891 < baseStart_3989891 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989932 : List Nat := [2, 2, 1, 1, 1, 1, 3, 5, 2, 4]
def baseStart_3989932 : Nat := 118140960795 + 3989932 * 2 ^ 59
def prefixEnd_3989932 : Nat := 4983230072969 + 3 ^ 40 * 3989932 * 2
def baseEnd_3989932 : Nat := 1365835263169992404267095

theorem tailTrace_3989932 : CollatzResearch.WordTrace tailWord_3989932 prefixEnd_3989932 1365835263169992404267095 := by
  unfold tailWord_3989932
  simp only [CollatzResearch.WordTrace]
  refine ⟨72762387690582632489802025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97016516920776843319736033 72762387690582632489802025)
  ·
    refine ⟨54571790767936974367351519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72762387690582632489802025 54571790767936974367351519)
    ·
      refine ⟨81857686151905461551027279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54571790767936974367351519 81857686151905461551027279)
      ·
        refine ⟨122786529227858192326540919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81857686151905461551027279 122786529227858192326540919)
        ·
          refine ⟨184179793841787288489811379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122786529227858192326540919 184179793841787288489811379)
          ·
            refine ⟨276269690762680932734717069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184179793841787288489811379 276269690762680932734717069)
            ·
              refine ⟨103601134036005349775518901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 276269690762680932734717069 103601134036005349775518901)
              ·
                refine ⟨9712606315875501541454897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103601134036005349775518901 9712606315875501541454897)
                ·
                  refine ⟨7284454736906626156091173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9712606315875501541454897 7284454736906626156091173)
                  ·
                    refine ⟨1365835263169992404267095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7284454736906626156091173 1365835263169992404267095)
                    ·
                      rfl

theorem cell22_3989932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 4].length) (baseStart_3989932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3989932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3989932 prefixEnd_3989932 := by exact prefixLift 3989932
  have htrace : WordTrace (prefixWord ++ tailWord_3989932) baseStart_3989932 baseEnd_3989932 := by
    simpa [prefixWord, tailWord_3989932, baseEnd_3989932] using wordTrace_append hprefix tailTrace_3989932
  have hstable : (prefixWord ++ tailWord_3989932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989932).length < 2 ^ (prefixWord ++ tailWord_3989932).sum := by decide
  have hdescent : baseEnd_3989932 < baseStart_3989932 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989949 : List Nat := [1, 4, 1, 2, 2, 3, 1, 2, 2, 4]
def baseStart_3989949 : Nat := 118140960795 + 3989949 * 2 ^ 59
def prefixEnd_3989949 : Nat := 4983230072969 + 3 ^ 40 * 3989949 * 2
def baseEnd_3989949 : Nat := 1365841082617410026592043

theorem tailTrace_3989949 : CollatzResearch.WordTrace tailWord_3989949 prefixEnd_3989949 1365841082617410026592043 := by
  unfold tailWord_3989949
  simp only [CollatzResearch.WordTrace]
  refine ⟨145525395422103676882972901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97016930281402451255315267 145525395422103676882972901)
  ·
    refine ⟨27286011641644439415557419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145525395422103676882972901 27286011641644439415557419)
    ·
      refine ⟨40929017462466659123336129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27286011641644439415557419 40929017462466659123336129)
      ·
        refine ⟨30696763096849994342502097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40929017462466659123336129 30696763096849994342502097)
        ·
          refine ⟨23022572322637495756876573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30696763096849994342502097 23022572322637495756876573)
          ·
            refine ⟨8633464620989060908828715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23022572322637495756876573 8633464620989060908828715)
            ·
              refine ⟨12950196931483591363243073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8633464620989060908828715 12950196931483591363243073)
              ·
                refine ⟨9712647698612693522432305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12950196931483591363243073 9712647698612693522432305)
                ·
                  refine ⟨7284485773959520141824229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9712647698612693522432305 7284485773959520141824229)
                  ·
                    refine ⟨1365841082617410026592043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7284485773959520141824229 1365841082617410026592043)
                    ·
                      rfl

theorem cell22_3989949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 2, 2, 4].length) (baseStart_3989949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3989949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3989949 prefixEnd_3989949 := by exact prefixLift 3989949
  have htrace : WordTrace (prefixWord ++ tailWord_3989949) baseStart_3989949 baseEnd_3989949 := by
    simpa [prefixWord, tailWord_3989949, baseEnd_3989949] using wordTrace_append hprefix tailTrace_3989949
  have hstable : (prefixWord ++ tailWord_3989949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989949).length < 2 ^ (prefixWord ++ tailWord_3989949).sum := by decide
  have hdescent : baseEnd_3989949 < baseStart_3989949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989964 : List Nat := [2, 2, 1, 4, 3, 1, 2, 7]
def baseStart_3989964 : Nat := 118140960795 + 3989964 * 2 ^ 59
def prefixEnd_3989964 : Nat := 4983230072969 + 3 ^ 40 * 3989964 * 2
def baseEnd_3989964 : Nat := 151760690824883887496333

theorem tailTrace_3989964 : CollatzResearch.WordTrace tailWord_3989964 prefixEnd_3989964 151760690824883887496333 := by
  unfold tailWord_3989964
  simp only [CollatzResearch.WordTrace]
  refine ⟨72762971258524667222384473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97017295011366222963179297 72762971258524667222384473)
  ·
    refine ⟨54572228443893500416788355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72762971258524667222384473 54572228443893500416788355)
    ·
      refine ⟨81858342665840250625182533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54572228443893500416788355 81858342665840250625182533)
      ·
        refine ⟨15348439249845046992221725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81858342665840250625182533 15348439249845046992221725)
        ·
          refine ⟨5755664718691892622083147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15348439249845046992221725 5755664718691892622083147)
          ·
            refine ⟨8633497078037838933124721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5755664718691892622083147 8633497078037838933124721)
            ·
              refine ⟨6475122808528379199843541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8633497078037838933124721 6475122808528379199843541)
              ·
                refine ⟨151760690824883887496333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6475122808528379199843541 151760690824883887496333)
                ·
                  rfl

theorem cell22_3989964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 7].length) (baseStart_3989964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3989964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3989964 prefixEnd_3989964 := by exact prefixLift 3989964
  have htrace : WordTrace (prefixWord ++ tailWord_3989964) baseStart_3989964 baseEnd_3989964 := by
    simpa [prefixWord, tailWord_3989964, baseEnd_3989964] using wordTrace_append hprefix tailTrace_3989964
  have hstable : (prefixWord ++ tailWord_3989964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989964).length < 2 ^ (prefixWord ++ tailWord_3989964).sum := by decide
  have hdescent : baseEnd_3989964 < baseStart_3989964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989996 : List Nat := [2, 2, 1, 1, 2, 1, 4, 5, 1, 3]
def baseStart_3989996 : Nat := 118140960795 + 3989996 * 2 ^ 59
def prefixEnd_3989996 : Nat := 4983230072969 + 3 ^ 40 * 3989996 * 2
def baseEnd_3989996 : Nat := 1365857171677917570666899

theorem tailTrace_3989996 : CollatzResearch.WordTrace tailWord_3989996 prefixEnd_3989996 1365857171677917570666899 := by
  unfold tailWord_3989996
  simp only [CollatzResearch.WordTrace]
  refine ⟨72763554826466701954966921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97018073101955602606622561 72763554826466701954966921)
  ·
    refine ⟨54572666119850026466225191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72763554826466701954966921 54572666119850026466225191)
    ·
      refine ⟨81858999179775039699337787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54572666119850026466225191 81858999179775039699337787)
      ·
        refine ⟨122788498769662559549006681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81858999179775039699337787 122788498769662559549006681)
        ·
          refine ⟨92091374077246919661755011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122788498769662559549006681 92091374077246919661755011)
          ·
            refine ⟨138137061115870379492632517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92091374077246919661755011 138137061115870379492632517)
            ·
              refine ⟨25900698959225696154868597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138137061115870379492632517 25900698959225696154868597)
              ·
                refine ⟨2428190527427409014518931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25900698959225696154868597 2428190527427409014518931)
                ·
                  refine ⟨3642285791141113521778397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2428190527427409014518931 3642285791141113521778397)
                  ·
                    refine ⟨1365857171677917570666899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3642285791141113521778397 1365857171677917570666899)
                    ·
                      rfl

theorem cell22_3989996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 5, 1, 3].length) (baseStart_3989996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3989996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3989996 prefixEnd_3989996 := by exact prefixLift 3989996
  have htrace : WordTrace (prefixWord ++ tailWord_3989996) baseStart_3989996 baseEnd_3989996 := by
    simpa [prefixWord, tailWord_3989996, baseEnd_3989996] using wordTrace_append hprefix tailTrace_3989996
  have hstable : (prefixWord ++ tailWord_3989996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989996).length < 2 ^ (prefixWord ++ tailWord_3989996).sum := by decide
  have hdescent : baseEnd_3989996 < baseStart_3989996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990193 : List Nat := [1, 2, 2, 6, 1, 1, 1, 1, 2, 5]
def baseStart_3990193 : Nat := 118140960795 + 3990193 * 2 ^ 59
def prefixEnd_3990193 : Nat := 4983230072969 + 3 ^ 40 * 3990193 * 2
def baseEnd_3990193 : Nat := 1365924608803874723491295

theorem tailTrace_3990193 : CollatzResearch.WordTrace tailWord_3990193 prefixEnd_3990193 1365924608803874723491295 := by
  unfold tailWord_3990193
  simp only [CollatzResearch.WordTrace]
  refine ⟨145534294833219706554855233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97022863222146471036570155 145534294833219706554855233)
  ·
    refine ⟨109150721124914779916141425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145534294833219706554855233 109150721124914779916141425)
    ·
      refine ⟨81863040843686084937106069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109150721124914779916141425 81863040843686084937106069)
      ·
        refine ⟨3837330039547785231426847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 81863040843686084937106069 3837330039547785231426847)
        ·
          refine ⟨5755995059321677847140271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3837330039547785231426847 5755995059321677847140271)
          ·
            refine ⟨8633992588982516770710407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5755995059321677847140271 8633992588982516770710407)
            ·
              refine ⟨12950988883473775156065611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8633992588982516770710407 12950988883473775156065611)
              ·
                refine ⟨19426483325210662734098417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12950988883473775156065611 19426483325210662734098417)
                ·
                  refine ⟨14569862493907997050573813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19426483325210662734098417 14569862493907997050573813)
                  ·
                    refine ⟨1365924608803874723491295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14569862493907997050573813 1365924608803874723491295)
                    ·
                      rfl

theorem cell22_3990193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 2, 5].length) (baseStart_3990193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3990193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3990193 prefixEnd_3990193 := by exact prefixLift 3990193
  have htrace : WordTrace (prefixWord ++ tailWord_3990193) baseStart_3990193 baseEnd_3990193 := by
    simpa [prefixWord, tailWord_3990193, baseEnd_3990193] using wordTrace_append hprefix tailTrace_3990193
  have hstable : (prefixWord ++ tailWord_3990193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990193).length < 2 ^ (prefixWord ++ tailWord_3990193).sum := by decide
  have hdescent : baseEnd_3990193 < baseStart_3990193 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990206 : List Nat := [4, 2, 1, 1, 2, 1, 3, 2, 6]
def baseStart_3990206 : Nat := 118140960795 + 3990206 * 2 ^ 59
def prefixEnd_3990206 : Nat := 4983230072969 + 3 ^ 40 * 3990206 * 2
def baseEnd_3990206 : Nat := 455309686323182340972085

theorem tailTrace_3990206 : CollatzResearch.WordTrace tailWord_3990206 prefixEnd_3990206 455309686323182340972085 := by
  unfold tailWord_3990206
  simp only [CollatzResearch.WordTrace]
  refine ⟨18191846122771576221884809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97023179321448406516718981 18191846122771576221884809)
  ·
    refine ⟨13643884592078682166413607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18191846122771576221884809 13643884592078682166413607)
    ·
      refine ⟨20465826888118023249620411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13643884592078682166413607 20465826888118023249620411)
      ·
        refine ⟨30698740332177034874430617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20465826888118023249620411 30698740332177034874430617)
        ·
          refine ⟨23024055249132776155822963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30698740332177034874430617 23024055249132776155822963)
          ·
            refine ⟨34536082873699164233734445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23024055249132776155822963 34536082873699164233734445)
            ·
              refine ⟨12951031077637186587650417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34536082873699164233734445 12951031077637186587650417)
              ·
                refine ⟨9713273308227889940737813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12951031077637186587650417 9713273308227889940737813)
                ·
                  refine ⟨455309686323182340972085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9713273308227889940737813 455309686323182340972085)
                  ·
                    rfl

theorem cell22_3990206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_3990206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3990206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3990206 prefixEnd_3990206 := by exact prefixLift 3990206
  have htrace : WordTrace (prefixWord ++ tailWord_3990206) baseStart_3990206 baseEnd_3990206 := by
    simpa [prefixWord, tailWord_3990206, baseEnd_3990206] using wordTrace_append hprefix tailTrace_3990206
  have hstable : (prefixWord ++ tailWord_3990206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990206).length < 2 ^ (prefixWord ++ tailWord_3990206).sum := by decide
  have hdescent : baseEnd_3990206 < baseStart_3990206 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990234 : List Nat := [3, 1, 1, 2, 2, 2, 11]
def baseStart_3990234 : Nat := 118140960795 + 3990234 * 2 ^ 59
def prefixEnd_3990234 : Nat := 4983230072969 + 3 ^ 40 * 3990234 * 2
def baseEnd_3990234 : Nat := 50590320145991269748747

theorem tailTrace_3990234 : CollatzResearch.WordTrace tailWord_3990234 prefixEnd_3990234 50590320145991269748747 := by
  unfold tailWord_3990234
  simp only [CollatzResearch.WordTrace]
  refine ⟨36383947556517792639274439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97023860150714113704731837 36383947556517792639274439)
  ·
    refine ⟨54575921334776688958911659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36383947556517792639274439 54575921334776688958911659)
    ·
      refine ⟨81863882002165033438367489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54575921334776688958911659 81863882002165033438367489)
      ·
        refine ⟨61397911501623775078775617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81863882002165033438367489 61397911501623775078775617)
        ·
          refine ⟨46048433626217831309081713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61397911501623775078775617 46048433626217831309081713)
          ·
            refine ⟨34536325219663373481811285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46048433626217831309081713 34536325219663373481811285)
            ·
              refine ⟨50590320145991269748747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 34536325219663373481811285 50590320145991269748747)
              ·
                rfl

theorem cell22_3990234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 11].length) (baseStart_3990234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3990234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3990234 prefixEnd_3990234 := by exact prefixLift 3990234
  have htrace : WordTrace (prefixWord ++ tailWord_3990234) baseStart_3990234 baseEnd_3990234 := by
    simpa [prefixWord, tailWord_3990234, baseEnd_3990234] using wordTrace_append hprefix tailTrace_3990234
  have hstable : (prefixWord ++ tailWord_3990234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990234).length < 2 ^ (prefixWord ++ tailWord_3990234).sum := by decide
  have hdescent : baseEnd_3990234 < baseStart_3990234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990255 : List Nat := [1, 1, 2, 1, 5, 3, 3, 1, 2, 3]
def baseStart_3990255 : Nat := 118140960795 + 3990255 * 2 ^ 59
def prefixEnd_3990255 : Nat := 4983230072969 + 3 ^ 40 * 3990255 * 2
def baseEnd_3990255 : Nat := 1365945832670927228441105

theorem tailTrace_3990255 : CollatzResearch.WordTrace tailWord_3990255 prefixEnd_3990255 1365945832670927228441105 := by
  unfold tailWord_3990255
  simp only [CollatzResearch.WordTrace]
  refine ⟨145536556158995091143612219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97024370772663394095741479 145536556158995091143612219)
  ·
    refine ⟨218304834238492636715418329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145536556158995091143612219 218304834238492636715418329)
    ·
      refine ⟨163728625678869477536563747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218304834238492636715418329 163728625678869477536563747)
      ·
        refine ⟨245592938518304216304845621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163728625678869477536563747 245592938518304216304845621)
        ·
          refine ⟨23024337986091020278579277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 245592938518304216304845621 23024337986091020278579277)
          ·
            refine ⟨8634126744784132604467229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23024337986091020278579277 8634126744784132604467229)
            ·
              refine ⟨3237797529294049726675211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8634126744784132604467229 3237797529294049726675211)
              ·
                refine ⟨4856696293941074590012817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3237797529294049726675211 4856696293941074590012817)
                ·
                  refine ⟨3642522220455805942509613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4856696293941074590012817 3642522220455805942509613)
                  ·
                    refine ⟨1365945832670927228441105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3642522220455805942509613 1365945832670927228441105)
                    ·
                      rfl

theorem cell22_3990255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 3, 1, 2, 3].length) (baseStart_3990255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3990255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3990255 prefixEnd_3990255 := by exact prefixLift 3990255
  have htrace : WordTrace (prefixWord ++ tailWord_3990255) baseStart_3990255 baseEnd_3990255 := by
    simpa [prefixWord, tailWord_3990255, baseEnd_3990255] using wordTrace_append hprefix tailTrace_3990255
  have hstable : (prefixWord ++ tailWord_3990255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990255).length < 2 ^ (prefixWord ++ tailWord_3990255).sum := by decide
  have hdescent : baseEnd_3990255 < baseStart_3990255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990268 : List Nat := [2, 2, 2, 1, 3, 4, 2, 6]
def baseStart_3990268 : Nat := 118140960795 + 3990268 * 2 ^ 59
def prefixEnd_3990268 : Nat := 4983230072969 + 3 ^ 40 * 3990268 * 2
def baseEnd_3990268 : Nat := 151772253648511058651785

theorem tailTrace_3990268 : CollatzResearch.WordTrace tailWord_3990268 prefixEnd_3990268 151772253648511058651785 := by
  unfold tailWord_3990268
  simp only [CollatzResearch.WordTrace]
  refine ⟨72768515153973997181917729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97024686871965329575890305 72768515153973997181917729)
  ·
    refine ⟨54576386365480497886438297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72768515153973997181917729 54576386365480497886438297)
    ·
      refine ⟨40932289774110373414828723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54576386365480497886438297 40932289774110373414828723)
      ·
        refine ⟨61398434661165560122243085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40932289774110373414828723 61398434661165560122243085)
        ·
          refine ⟨23024412997937085045841157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61398434661165560122243085 23024412997937085045841157)
          ·
            refine ⟨4317077437113203446095217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23024412997937085045841157 4317077437113203446095217)
            ·
              refine ⟨3237808077834902584571413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4317077437113203446095217 3237808077834902584571413)
              ·
                refine ⟨151772253648511058651785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3237808077834902584571413 151772253648511058651785)
                ·
                  rfl

theorem cell22_3990268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 2, 6].length) (baseStart_3990268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3990268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3990268 prefixEnd_3990268 := by exact prefixLift 3990268
  have htrace : WordTrace (prefixWord ++ tailWord_3990268) baseStart_3990268 baseEnd_3990268 := by
    simpa [prefixWord, tailWord_3990268, baseEnd_3990268] using wordTrace_append hprefix tailTrace_3990268
  have hstable : (prefixWord ++ tailWord_3990268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990268).length < 2 ^ (prefixWord ++ tailWord_3990268).sum := by decide
  have hdescent : baseEnd_3990268 < baseStart_3990268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990296 : List Nat := [2, 1, 2, 3, 1, 1, 1, 6, 5]
def baseStart_3990296 : Nat := 118140960795 + 3990296 * 2 ^ 59
def prefixEnd_3990296 : Nat := 4983230072969 + 3 ^ 40 * 3990296 * 2
def baseEnd_3990296 : Nat := 455319955936272262721993

theorem tailTrace_3990296 : CollatzResearch.WordTrace tailWord_3990296 prefixEnd_3990296 455319955936272262721993 := by
  unfold tailWord_3990296
  simp only [CollatzResearch.WordTrace]
  refine ⟨72769025775923277572927371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97025367701231036763903161 72769025775923277572927371)
  ·
    refine ⟨109153538663884916359391057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72769025775923277572927371 109153538663884916359391057)
    ·
      refine ⟨81865153997913687269543293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109153538663884916359391057 81865153997913687269543293)
      ·
        refine ⟨30699432749217632726078735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81865153997913687269543293 30699432749217632726078735)
        ·
          refine ⟨46049149123826449089118103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30699432749217632726078735 46049149123826449089118103)
          ·
            refine ⟨69073723685739673633677155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46049149123826449089118103 69073723685739673633677155)
            ·
              refine ⟨103610585528609510450515733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69073723685739673633677155 103610585528609510450515733)
              ·
                refine ⟨4856746196653570802367925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 103610585528609510450515733 4856746196653570802367925)
                ·
                  refine ⟨455319955936272262721993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4856746196653570802367925 455319955936272262721993)
                  ·
                    rfl

theorem cell22_3990296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 6, 5].length) (baseStart_3990296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3990296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3990296 prefixEnd_3990296 := by exact prefixLift 3990296
  have htrace : WordTrace (prefixWord ++ tailWord_3990296) baseStart_3990296 baseEnd_3990296 := by
    simpa [prefixWord, tailWord_3990296, baseEnd_3990296] using wordTrace_append hprefix tailTrace_3990296
  have hstable : (prefixWord ++ tailWord_3990296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990296).length < 2 ^ (prefixWord ++ tailWord_3990296).sum := by decide
  have hdescent : baseEnd_3990296 < baseStart_3990296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990300 : List Nat := [2, 2, 3, 1, 1, 5, 1, 1, 3, 3]
def baseStart_3990300 : Nat := 118140960795 + 3990300 * 2 ^ 59
def prefixEnd_3990300 : Nat := 4983230072969 + 3 ^ 40 * 3990300 * 2
def baseEnd_3990300 : Nat := 1365961237090562111065967

theorem tailTrace_3990300 : CollatzResearch.WordTrace tailWord_3990300 prefixEnd_3990300 1365961237090562111065967 := by
  unfold tailWord_3990300
  simp only [CollatzResearch.WordTrace]
  refine ⟨72769098721916031914500177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97025464962554709219333569 72769098721916031914500177)
  ·
    refine ⟨54576824041437023935875133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72769098721916031914500177 54576824041437023935875133)
    ·
      refine ⟨20466309015538883975953175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54576824041437023935875133 20466309015538883975953175)
      ·
        refine ⟨30699463523308325963929763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20466309015538883975953175 30699463523308325963929763)
        ·
          refine ⟨46049195284962488945894645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30699463523308325963929763 46049195284962488945894645)
          ·
            refine ⟨4317112057965233338677623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46049195284962488945894645 4317112057965233338677623)
            ·
              refine ⟨6475668086947850008016435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4317112057965233338677623 6475668086947850008016435)
              ·
                refine ⟨9713502130421775012024653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6475668086947850008016435 9713502130421775012024653)
                ·
                  refine ⟨3642563298908165629509245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9713502130421775012024653 3642563298908165629509245)
                  ·
                    refine ⟨1365961237090562111065967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3642563298908165629509245 1365961237090562111065967)
                    ·
                      rfl

theorem cell22_3990300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 1, 3, 3].length) (baseStart_3990300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3990300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3990300 prefixEnd_3990300 := by exact prefixLift 3990300
  have htrace : WordTrace (prefixWord ++ tailWord_3990300) baseStart_3990300 baseEnd_3990300 := by
    simpa [prefixWord, tailWord_3990300, baseEnd_3990300] using wordTrace_append hprefix tailTrace_3990300
  have hstable : (prefixWord ++ tailWord_3990300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990300).length < 2 ^ (prefixWord ++ tailWord_3990300).sum := by decide
  have hdescent : baseEnd_3990300 < baseStart_3990300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990386 : List Nat := [3, 2, 1, 2, 1, 1, 2, 10]
def baseStart_3990386 : Nat := 118140960795 + 3990386 * 2 ^ 59
def prefixEnd_3990386 : Nat := 4983230072969 + 3 ^ 40 * 3990386 * 2
def baseEnd_3990386 : Nat := 151776741849787394823967

theorem tailTrace_3990386 : CollatzResearch.WordTrace tailWord_3990386 prefixEnd_3990386 151776741849787394823967 := by
  unfold tailWord_3990386
  simp only [CollatzResearch.WordTrace]
  refine ⟨36385333530380125129157753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97027556081013667011087341 36385333530380125129157753)
  ·
    refine ⟨27289000147785093846868315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36385333530380125129157753 27289000147785093846868315)
    ·
      refine ⟨40933500221677640770302473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27289000147785093846868315 40933500221677640770302473)
      ·
        refine ⟨30700125166258230577726855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40933500221677640770302473 30700125166258230577726855)
        ·
          refine ⟨46050187749387345866590283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30700125166258230577726855 46050187749387345866590283)
          ·
            refine ⟨69075281624081018799885425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46050187749387345866590283 69075281624081018799885425)
            ·
              refine ⟨51806461218060764099914069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69075281624081018799885425 51806461218060764099914069)
              ·
                refine ⟨151776741849787394823967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 51806461218060764099914069 151776741849787394823967)
                ·
                  rfl

theorem cell22_3990386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 10].length) (baseStart_3990386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3990386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3990386 prefixEnd_3990386 := by exact prefixLift 3990386
  have htrace : WordTrace (prefixWord ++ tailWord_3990386) baseStart_3990386 baseEnd_3990386 := by
    simpa [prefixWord, tailWord_3990386, baseEnd_3990386] using wordTrace_append hprefix tailTrace_3990386
  have hstable : (prefixWord ++ tailWord_3990386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990386).length < 2 ^ (prefixWord ++ tailWord_3990386).sum := by decide
  have hdescent : baseEnd_3990386 < baseStart_3990386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990390 : List Nat := [5, 1, 1, 3, 1, 1, 2, 2, 1, 5]
def baseStart_3990390 : Nat := 118140960795 + 3990390 * 2 ^ 59
def prefixEnd_3990390 : Nat := 4983230072969 + 3 ^ 40 * 3990390 * 2
def baseEnd_3990390 : Nat := 1365992045929831876315691

theorem tailTrace_3990390 : CollatzResearch.WordTrace tailWord_3990390 prefixEnd_3990390 1365992045929831876315691 := by
  unfold tailWord_3990390
  simp only [CollatzResearch.WordTrace]
  refine ⟨9096342500844125574986039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97027653342337339466517749 9096342500844125574986039)
  ·
    refine ⟨13644513751266188362479059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9096342500844125574986039 13644513751266188362479059)
    ·
      refine ⟨20466770626899282543718589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13644513751266188362479059 20466770626899282543718589)
      ·
        refine ⟨7675038985087230953894471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20466770626899282543718589 7675038985087230953894471)
        ·
          refine ⟨11512558477630846430841707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7675038985087230953894471 11512558477630846430841707)
          ·
            refine ⟨17268837716446269646262561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11512558477630846430841707 17268837716446269646262561)
            ·
              refine ⟨12951628287334702234696921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17268837716446269646262561 12951628287334702234696921)
              ·
                refine ⟨9713721215501026676022691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12951628287334702234696921 9713721215501026676022691)
                ·
                  refine ⟨14570581823251540014034037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9713721215501026676022691 14570581823251540014034037)
                  ·
                    refine ⟨1365992045929831876315691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14570581823251540014034037 1365992045929831876315691)
                    ·
                      rfl

theorem cell22_3990390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_3990390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3990390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3990390 prefixEnd_3990390 := by exact prefixLift 3990390
  have htrace : WordTrace (prefixWord ++ tailWord_3990390) baseStart_3990390 baseEnd_3990390 := by
    simpa [prefixWord, tailWord_3990390, baseEnd_3990390] using wordTrace_append hprefix tailTrace_3990390
  have hstable : (prefixWord ++ tailWord_3990390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990390).length < 2 ^ (prefixWord ++ tailWord_3990390).sum := by decide
  have hdescent : baseEnd_3990390 < baseStart_3990390 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990407 : List Nat := [1, 1, 4, 2, 3, 3, 1, 2, 2, 3]
def baseStart_3990407 : Nat := 118140960795 + 3990407 * 2 ^ 59
def prefixEnd_3990407 : Nat := 4983230072969 + 3 ^ 40 * 3990407 * 2
def baseEnd_3990407 : Nat := 1365997865377249498640639

theorem tailTrace_3990407 : CollatzResearch.WordTrace tailWord_3990407 prefixEnd_3990407 1365997865377249498640639 := by
  unfold tailWord_3990407
  simp only [CollatzResearch.WordTrace]
  refine ⟨145542100054444421103145475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97028066702962947402096983 145542100054444421103145475)
  ·
    refine ⟨218313150081666631654718213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145542100054444421103145475 218313150081666631654718213)
    ·
      refine ⟨40933715640312493435259665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 218313150081666631654718213 40933715640312493435259665)
      ·
        refine ⟨30700286730234370076444749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40933715640312493435259665 30700286730234370076444749)
        ·
          refine ⟨11512607523837888778666781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30700286730234370076444749 11512607523837888778666781)
          ·
            refine ⟨4317227821439208292000043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11512607523837888778666781 4317227821439208292000043)
            ·
              refine ⟨6475841732158812438000065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4317227821439208292000043 6475841732158812438000065)
              ·
                refine ⟨4856881299119109328500049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6475841732158812438000065 4856881299119109328500049)
                ·
                  refine ⟨3642660974339331996375037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4856881299119109328500049 3642660974339331996375037)
                  ·
                    refine ⟨1365997865377249498640639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3642660974339331996375037 1365997865377249498640639)
                    ·
                      rfl

theorem cell22_3990407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 2, 2, 3].length) (baseStart_3990407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3990407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3990407 prefixEnd_3990407 := by exact prefixLift 3990407
  have htrace : WordTrace (prefixWord ++ tailWord_3990407) baseStart_3990407 baseEnd_3990407 := by
    simpa [prefixWord, tailWord_3990407, baseEnd_3990407] using wordTrace_append hprefix tailTrace_3990407
  have hstable : (prefixWord ++ tailWord_3990407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990407).length < 2 ^ (prefixWord ++ tailWord_3990407).sum := by decide
  have hdescent : baseEnd_3990407 < baseStart_3990407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990422 : List Nat := [5, 3, 1, 1, 1, 1, 1, 2, 1, 6]
def baseStart_3990422 : Nat := 118140960795 + 3990422 * 2 ^ 59
def prefixEnd_3990422 : Nat := 4983230072969 + 3 ^ 40 * 3990422 * 2
def baseEnd_3990422 : Nat := 1366003000183794459515593

theorem tailTrace_3990422 : CollatzResearch.WordTrace tailWord_3990422 prefixEnd_3990422 1366003000183794459515593 := by
  unfold tailWord_3990422
  simp only [CollatzResearch.WordTrace]
  refine ⟨9096415446836879916558845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97028431432926719109961013 9096415446836879916558845)
  ·
    refine ⟨3411155792563829968709567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9096415446836879916558845 3411155792563829968709567)
    ·
      refine ⟨5116733688845744953064351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3411155792563829968709567 5116733688845744953064351)
      ·
        refine ⟨7675100533268617429596527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5116733688845744953064351 7675100533268617429596527)
        ·
          refine ⟨11512650799902926144394791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7675100533268617429596527 11512650799902926144394791)
          ·
            refine ⟨17268976199854389216592187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11512650799902926144394791 17268976199854389216592187)
            ·
              refine ⟨25903464299781583824888281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17268976199854389216592187 25903464299781583824888281)
              ·
                refine ⟨19427598224836187868666211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25903464299781583824888281 19427598224836187868666211)
                ·
                  refine ⟨29141397337254281802999317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19427598224836187868666211 29141397337254281802999317)
                  ·
                    refine ⟨1366003000183794459515593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29141397337254281802999317 1366003000183794459515593)
                    ·
                      rfl

theorem cell22_3990422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_3990422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3990422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3990422 prefixEnd_3990422 := by exact prefixLift 3990422
  have htrace : WordTrace (prefixWord ++ tailWord_3990422) baseStart_3990422 baseEnd_3990422 := by
    simpa [prefixWord, tailWord_3990422, baseEnd_3990422] using wordTrace_append hprefix tailTrace_3990422
  have hstable : (prefixWord ++ tailWord_3990422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990422).length < 2 ^ (prefixWord ++ tailWord_3990422).sum := by decide
  have hdescent : baseEnd_3990422 < baseStart_3990422 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990454 : List Nat := [5, 1, 4, 1, 1, 2, 8]
def baseStart_3990454 : Nat := 118140960795 + 3990454 * 2 ^ 59
def prefixEnd_3990454 : Nat := 4983230072969 + 3 ^ 40 * 3990454 * 2
def baseEnd_3990454 : Nat := 50593109423620631211685

theorem tailTrace_3990454 : CollatzResearch.WordTrace tailWord_3990454 prefixEnd_3990454 50593109423620631211685 := by
  unfold tailWord_3990454
  simp only [CollatzResearch.WordTrace]
  refine ⟨9096488392829634258131651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97029209523516098753404277 9096488392829634258131651)
  ·
    refine ⟨13644732589244451387197477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9096488392829634258131651 13644732589244451387197477)
    ·
      refine ⟨2558387360483334635099527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13644732589244451387197477 2558387360483334635099527)
      ·
        refine ⟨3837581040725001952649291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2558387360483334635099527 3837581040725001952649291)
        ·
          refine ⟨5756371561087502928973937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3837581040725001952649291 5756371561087502928973937)
          ·
            refine ⟨4317278670815627196730453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5756371561087502928973937 4317278670815627196730453)
            ·
              refine ⟨50593109423620631211685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4317278670815627196730453 50593109423620631211685)
              ·
                rfl

theorem cell22_3990454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 8].length) (baseStart_3990454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3990454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3990454 prefixEnd_3990454 := by exact prefixLift 3990454
  have htrace : WordTrace (prefixWord ++ tailWord_3990454) baseStart_3990454 baseEnd_3990454 := by
    simpa [prefixWord, tailWord_3990454, baseEnd_3990454] using wordTrace_append hprefix tailTrace_3990454
  have hstable : (prefixWord ++ tailWord_3990454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990454).length < 2 ^ (prefixWord ++ tailWord_3990454).sum := by decide
  have hdescent : baseEnd_3990454 < baseStart_3990454 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990482 : List Nat := [3, 2, 2, 3, 1, 1, 4, 1, 5]
def baseStart_3990482 : Nat := 118140960795 + 3990482 * 2 ^ 59
def prefixEnd_3990482 : Nat := 4983230072969 + 3 ^ 40 * 3990482 * 2
def baseEnd_3990482 : Nat := 455341179803324767671803

theorem tailTrace_3990482 : CollatzResearch.WordTrace tailWord_3990482 prefixEnd_3990482 455341179803324767671803 := by
  unfold tailWord_3990482
  simp only [CollatzResearch.WordTrace]
  refine ⟨36386208882293177228031425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97029890352781805941417133 36386208882293177228031425)
  ·
    refine ⟨27289656661719882921023569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36386208882293177228031425 27289656661719882921023569)
    ·
      refine ⟨20467242496289912190767677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27289656661719882921023569 20467242496289912190767677)
      ·
        refine ⟨7675215936108717071537879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20467242496289912190767677 7675215936108717071537879)
        ·
          refine ⟨11512823904163075607306819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7675215936108717071537879 11512823904163075607306819)
          ·
            refine ⟨17269235856244613410960229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11512823904163075607306819 17269235856244613410960229)
            ·
              refine ⟨3237981723045865014555043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17269235856244613410960229 3237981723045865014555043)
              ·
                refine ⟨4856972584568797521832565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3237981723045865014555043 4856972584568797521832565)
                ·
                  refine ⟨455341179803324767671803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4856972584568797521832565 455341179803324767671803)
                  ·
                    rfl

theorem cell22_3990482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 4, 1, 5].length) (baseStart_3990482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3990482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3990482 prefixEnd_3990482 := by exact prefixLift 3990482
  have htrace : WordTrace (prefixWord ++ tailWord_3990482) baseStart_3990482 baseEnd_3990482 := by
    simpa [prefixWord, tailWord_3990482, baseEnd_3990482] using wordTrace_append hprefix tailTrace_3990482
  have hstable : (prefixWord ++ tailWord_3990482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990482).length < 2 ^ (prefixWord ++ tailWord_3990482).sum := by decide
  have hdescent : baseEnd_3990482 < baseStart_3990482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990495 : List Nat := [1, 1, 2, 3, 5, 1, 1, 1, 3, 4]
def baseStart_3990495 : Nat := 118140960795 + 3990495 * 2 ^ 59
def prefixEnd_3990495 : Nat := 4983230072969 + 3 ^ 40 * 3990495 * 2
def baseEnd_3990495 : Nat := 1366027989575646602440369

theorem tailTrace_3990495 : CollatzResearch.WordTrace tailWord_3990495 prefixEnd_3990495 1366027989575646602440369 := by
  unfold tailWord_3990495
  simp only [CollatzResearch.WordTrace]
  refine ⟨145545309678125612132348939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97030206452083741421565959 145545309678125612132348939)
  ·
    refine ⟨218317964517188418198523409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145545309678125612132348939 218317964517188418198523409)
    ·
      refine ⟨163738473387891313648892557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218317964517188418198523409 163738473387891313648892557)
      ·
        refine ⟨61401927520459242618334709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163738473387891313648892557 61401927520459242618334709)
        ·
          refine ⟨5756430705043053995468879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61401927520459242618334709 5756430705043053995468879)
          ·
            refine ⟨8634646057564580993203319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5756430705043053995468879 8634646057564580993203319)
            ·
              refine ⟨12951969086346871489804979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8634646057564580993203319 12951969086346871489804979)
              ·
                refine ⟨19427953629520307234707469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12951969086346871489804979 19427953629520307234707469)
                ·
                  refine ⟨7285482611070115213015301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19427953629520307234707469 7285482611070115213015301)
                  ·
                    refine ⟨1366027989575646602440369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7285482611070115213015301 1366027989575646602440369)
                    ·
                      rfl

theorem cell22_3990495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 3, 4].length) (baseStart_3990495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3990495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3990495 prefixEnd_3990495 := by exact prefixLift 3990495
  have htrace : WordTrace (prefixWord ++ tailWord_3990495) baseStart_3990495 baseEnd_3990495 := by
    simpa [prefixWord, tailWord_3990495, baseEnd_3990495] using wordTrace_append hprefix tailTrace_3990495
  have hstable : (prefixWord ++ tailWord_3990495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990495).length < 2 ^ (prefixWord ++ tailWord_3990495).sum := by decide
  have hdescent : baseEnd_3990495 < baseStart_3990495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990542 : List Nat := [4, 1, 1, 2, 2, 2, 2, 3, 2, 3]
def baseStart_3990542 : Nat := 118140960795 + 3990542 * 2 ^ 59
def prefixEnd_3990542 : Nat := 4983230072969 + 3 ^ 40 * 3990542 * 2
def baseEnd_3990542 : Nat := 1366044078636154146515225

theorem tailTrace_3990542 : CollatzResearch.WordTrace tailWord_3990542 prefixEnd_3990542 1366044078636154146515225 := by
  unfold tailWord_3990542
  simp only [CollatzResearch.WordTrace]
  refine ⟨18193377988619417394913735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97031349272636892772873253 18193377988619417394913735)
  ·
    refine ⟨27290066982929126092370603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18193377988619417394913735 27290066982929126092370603)
    ·
      refine ⟨40935100474393689138555905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27290066982929126092370603 40935100474393689138555905)
      ·
        refine ⟨30701325355795266853916929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40935100474393689138555905 30701325355795266853916929)
        ·
          refine ⟨23025994016846450140437697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30701325355795266853916929 23025994016846450140437697)
          ·
            refine ⟨17269495512634837605328273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23025994016846450140437697 17269495512634837605328273)
            ·
              refine ⟨12952121634476128203996205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17269495512634837605328273 12952121634476128203996205)
              ·
                refine ⟨4857045612928548076498577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12952121634476128203996205 4857045612928548076498577)
                ·
                  refine ⟨3642784209696411057373933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4857045612928548076498577 3642784209696411057373933)
                  ·
                    refine ⟨1366044078636154146515225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3642784209696411057373933 1366044078636154146515225)
                    ·
                      rfl

theorem cell22_3990542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 3, 2, 3].length) (baseStart_3990542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3990542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3990542 prefixEnd_3990542 := by exact prefixLift 3990542
  have htrace : WordTrace (prefixWord ++ tailWord_3990542) baseStart_3990542 baseEnd_3990542 := by
    simpa [prefixWord, tailWord_3990542, baseEnd_3990542] using wordTrace_append hprefix tailTrace_3990542
  have hstable : (prefixWord ++ tailWord_3990542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990542).length < 2 ^ (prefixWord ++ tailWord_3990542).sum := by decide
  have hdescent : baseEnd_3990542 < baseStart_3990542 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990675 : List Nat := [1, 1, 1, 2, 1, 2, 5, 3, 2, 4]
def baseStart_3990675 : Nat := 118140960795 + 3990675 * 2 ^ 59
def prefixEnd_3990675 : Nat := 4983230072969 + 3 ^ 40 * 3990675 * 2
def baseEnd_3990675 : Nat := 1366089607254186132939817

theorem tailTrace_3990675 : CollatzResearch.WordTrace tailWord_3990675 prefixEnd_3990675 1366089607254186132939817 := by
  unfold tailWord_3990675
  simp only [CollatzResearch.WordTrace]
  refine ⟨145551874817473502873901479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97034583211649001915934319 145551874817473502873901479)
  ·
    refine ⟨218327812226210254310852219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145551874817473502873901479 218327812226210254310852219)
    ·
      refine ⟨327491718339315381466278329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218327812226210254310852219 327491718339315381466278329)
      ·
        refine ⟨245618788754486536099708747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327491718339315381466278329 245618788754486536099708747)
        ·
          refine ⟨368428183131729804149563121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245618788754486536099708747 368428183131729804149563121)
          ·
            refine ⟨276321137348797353112172341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 368428183131729804149563121 276321137348797353112172341)
            ·
              refine ⟨25905106626449751854266157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 276321137348797353112172341 25905106626449751854266157)
              ·
                refine ⟨9714414984918656945349809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25905106626449751854266157 9714414984918656945349809)
                ·
                  refine ⟨7285811238688992709012357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9714414984918656945349809 7285811238688992709012357)
                  ·
                    refine ⟨1366089607254186132939817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7285811238688992709012357 1366089607254186132939817)
                    ·
                      rfl

theorem cell22_3990675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 3, 2, 4].length) (baseStart_3990675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3990675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3990675 prefixEnd_3990675 := by exact prefixLift 3990675
  have htrace : WordTrace (prefixWord ++ tailWord_3990675) baseStart_3990675 baseEnd_3990675 := by
    simpa [prefixWord, tailWord_3990675, baseEnd_3990675] using wordTrace_append hprefix tailTrace_3990675
  have hstable : (prefixWord ++ tailWord_3990675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990675).length < 2 ^ (prefixWord ++ tailWord_3990675).sum := by decide
  have hdescent : baseEnd_3990675 < baseStart_3990675 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990690 : List Nat := [3, 3, 1, 3, 12]
def baseStart_3990690 : Nat := 118140960795 + 3990690 * 2 ^ 59
def prefixEnd_3990690 : Nat := 4983230072969 + 3 ^ 40 * 3990690 * 2
def baseEnd_3990690 : Nat := 5621789061978317258497

theorem tailTrace_3990690 : CollatzResearch.WordTrace tailWord_3990690 prefixEnd_3990690 5621789061978317258497 := by
  unfold tailWord_3990690
  simp only [CollatzResearch.WordTrace]
  refine ⟨36388105478104790108924381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97034947941612773623798349 36388105478104790108924381)
  ·
    refine ⟨13645539554289296290846643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36388105478104790108924381 13645539554289296290846643)
    ·
      refine ⟨20468309331433944436269965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13645539554289296290846643 20468309331433944436269965)
      ·
        refine ⟨7675615999287729163601237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20468309331433944436269965 7675615999287729163601237)
        ·
          refine ⟨5621789061978317258497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 7675615999287729163601237 5621789061978317258497)
          ·
            rfl

theorem cell22_3990690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 12].length) (baseStart_3990690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3990690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3990690 prefixEnd_3990690 := by exact prefixLift 3990690
  have htrace : WordTrace (prefixWord ++ tailWord_3990690) baseStart_3990690 baseEnd_3990690 := by
    simpa [prefixWord, tailWord_3990690, baseEnd_3990690] using wordTrace_append hprefix tailTrace_3990690
  have hstable : (prefixWord ++ tailWord_3990690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990690).length < 2 ^ (prefixWord ++ tailWord_3990690).sum := by decide
  have hdescent : baseEnd_3990690 < baseStart_3990690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990692 : List Nat := [2, 3, 1, 2, 3, 1, 2, 2, 2, 4]
def baseStart_3990692 : Nat := 118140960795 + 3990692 * 2 ^ 59
def prefixEnd_3990692 : Nat := 4983230072969 + 3 ^ 40 * 3990692 * 2
def baseEnd_3990692 : Nat := 1366095426701603755264765

theorem tailTrace_3990692 : CollatzResearch.WordTrace tailWord_3990692 prefixEnd_3990692 1366095426701603755264765 := by
  unfold tailWord_3990692
  simp only [CollatzResearch.WordTrace]
  refine ⟨72776247429205957388635165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97034996572274609851513553 72776247429205957388635165)
  ·
    refine ⟨27291092785952234020738187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72776247429205957388635165 27291092785952234020738187)
    ·
      refine ⟨40936639178928351031107281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27291092785952234020738187 40936639178928351031107281)
      ·
        refine ⟨30702479384196263273330461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40936639178928351031107281 30702479384196263273330461)
        ·
          refine ⟨11513429769073598727498923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30702479384196263273330461 11513429769073598727498923)
          ·
            refine ⟨17270144653610398091248385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11513429769073598727498923 17270144653610398091248385)
            ·
              refine ⟨12952608490207798568436289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17270144653610398091248385 12952608490207798568436289)
              ·
                refine ⟨9714456367655848926327217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12952608490207798568436289 9714456367655848926327217)
                ·
                  refine ⟨7285842275741886694745413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9714456367655848926327217 7285842275741886694745413)
                  ·
                    refine ⟨1366095426701603755264765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7285842275741886694745413 1366095426701603755264765)
                    ·
                      rfl

theorem cell22_3990692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 2, 2, 4].length) (baseStart_3990692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3990692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3990692 prefixEnd_3990692 := by exact prefixLift 3990692
  have htrace : WordTrace (prefixWord ++ tailWord_3990692) baseStart_3990692 baseEnd_3990692 := by
    simpa [prefixWord, tailWord_3990692, baseEnd_3990692] using wordTrace_append hprefix tailTrace_3990692
  have hstable : (prefixWord ++ tailWord_3990692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990692).length < 2 ^ (prefixWord ++ tailWord_3990692).sum := by decide
  have hdescent : baseEnd_3990692 < baseStart_3990692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990724 : List Nat := [2, 3, 3, 1, 3, 1, 3, 6]
def baseStart_3990724 : Nat := 118140960795 + 3990724 * 2 ^ 59
def prefixEnd_3990724 : Nat := 4983230072969 + 3 ^ 40 * 3990724 * 2
def baseEnd_3990724 : Nat := 151789597883951815384963

theorem tailTrace_3990724 : CollatzResearch.WordTrace tailWord_3990724 prefixEnd_3990724 151789597883951815384963 := by
  unfold tailWord_3990724
  simp only [CollatzResearch.WordTrace]
  refine ⟨72776830997147992121217613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97035774662863989494956817 72776830997147992121217613)
  ·
    refine ⟨27291311623930497045456605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72776830997147992121217613 27291311623930497045456605)
    ·
      refine ⟨10234241858973936392046227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27291311623930497045456605 10234241858973936392046227)
      ·
        refine ⟨15351362788460904588069341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10234241858973936392046227 15351362788460904588069341)
        ·
          refine ⟨5756761045672839220526003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15351362788460904588069341 5756761045672839220526003)
          ·
            refine ⟨8635141568509258830789005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5756761045672839220526003 8635141568509258830789005)
            ·
              refine ⟨3238178088190972061545877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8635141568509258830789005 3238178088190972061545877)
              ·
                refine ⟨151789597883951815384963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3238178088190972061545877 151789597883951815384963)
                ·
                  rfl

theorem cell22_3990724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 3, 6].length) (baseStart_3990724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3990724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3990724 prefixEnd_3990724 := by exact prefixLift 3990724
  have htrace : WordTrace (prefixWord ++ tailWord_3990724) baseStart_3990724 baseEnd_3990724 := by
    simpa [prefixWord, tailWord_3990724, baseEnd_3990724] using wordTrace_append hprefix tailTrace_3990724
  have hstable : (prefixWord ++ tailWord_3990724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990724).length < 2 ^ (prefixWord ++ tailWord_3990724).sum := by decide
  have hdescent : baseEnd_3990724 < baseStart_3990724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990752 : List Nat := [2, 1, 1, 3, 1, 4, 3, 2, 5]
def baseStart_3990752 : Nat := 118140960795 + 3990752 * 2 ^ 59
def prefixEnd_3990752 : Nat := 4983230072969 + 3 ^ 40 * 3990752 * 2
def baseEnd_3990752 : Nat := 455371988642594532921527

theorem tailTrace_3990752 : CollatzResearch.WordTrace tailWord_3990752 prefixEnd_3990752 455371988642594532921527 := by
  unfold tailWord_3990752
  simp only [CollatzResearch.WordTrace]
  refine ⟨72777341619097272512227255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97036455492129696682969673 72777341619097272512227255)
  ·
    refine ⟨109166012428645908768340883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72777341619097272512227255 109166012428645908768340883)
    ·
      refine ⟨163749018642968863152511325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109166012428645908768340883 163749018642968863152511325)
      ·
        refine ⟨61405881991113323682191747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163749018642968863152511325 61405881991113323682191747)
        ·
          refine ⟨92108822986669985523287621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61405881991113323682191747 92108822986669985523287621)
          ·
            refine ⟨17270404310000622285616429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92108822986669985523287621 17270404310000622285616429)
            ·
              refine ⟨6476401616250233357106161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17270404310000622285616429 6476401616250233357106161)
              ·
                refine ⟨4857301212187675017829621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6476401616250233357106161 4857301212187675017829621)
                ·
                  refine ⟨455371988642594532921527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4857301212187675017829621 455371988642594532921527)
                  ·
                    rfl

theorem cell22_3990752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 2, 5].length) (baseStart_3990752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3990752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3990752 prefixEnd_3990752 := by exact prefixLift 3990752
  have htrace : WordTrace (prefixWord ++ tailWord_3990752) baseStart_3990752 baseEnd_3990752 := by
    simpa [prefixWord, tailWord_3990752, baseEnd_3990752] using wordTrace_append hprefix tailTrace_3990752
  have hstable : (prefixWord ++ tailWord_3990752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990752).length < 2 ^ (prefixWord ++ tailWord_3990752).sum := by decide
  have hdescent : baseEnd_3990752 < baseStart_3990752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990844 : List Nat := [2, 2, 2, 2, 1, 4, 2, 1, 2, 4]
def baseStart_3990844 : Nat := 118140960795 + 3990844 * 2 ^ 59
def prefixEnd_3990844 : Nat := 4983230072969 + 3 ^ 40 * 3990844 * 2
def baseEnd_3990844 : Nat := 1366147459407926025464299

theorem tailTrace_3990844 : CollatzResearch.WordTrace tailWord_3990844 prefixEnd_3990844 1366147459407926025464299 := by
  unfold tailWord_3990844
  simp only [CollatzResearch.WordTrace]
  refine ⟨72779019376930622368401793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97038692502574163157869057 72779019376930622368401793)
  ·
    refine ⟨54584264532697966776301345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72779019376930622368401793 54584264532697966776301345)
    ·
      refine ⟨40938198399523475082226009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54584264532697966776301345 40938198399523475082226009)
      ·
        refine ⟨30703648799642606311669507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40938198399523475082226009 30703648799642606311669507)
        ·
          refine ⟨46055473199463909467504261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30703648799642606311669507 46055473199463909467504261)
          ·
            refine ⟨8635401224899483025157049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46055473199463909467504261 8635401224899483025157049)
            ·
              refine ⟨6476550918674612268867787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8635401224899483025157049 6476550918674612268867787)
              ·
                refine ⟨9714826378011918403301681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6476550918674612268867787 9714826378011918403301681)
                ·
                  refine ⟨7286119783508938802476261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9714826378011918403301681 7286119783508938802476261)
                  ·
                    refine ⟨1366147459407926025464299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7286119783508938802476261 1366147459407926025464299)
                    ·
                      rfl

theorem cell22_3990844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 1, 2, 4].length) (baseStart_3990844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3990844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3990844 prefixEnd_3990844 := by exact prefixLift 3990844
  have htrace : WordTrace (prefixWord ++ tailWord_3990844) baseStart_3990844 baseEnd_3990844 := by
    simpa [prefixWord, tailWord_3990844, baseEnd_3990844] using wordTrace_append hprefix tailTrace_3990844
  have hstable : (prefixWord ++ tailWord_3990844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990844).length < 2 ^ (prefixWord ++ tailWord_3990844).sum := by decide
  have hdescent : baseEnd_3990844 < baseStart_3990844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990921 : List Nat := [1, 2, 1, 1, 7, 2, 1, 2, 5]
def baseStart_3990921 : Nat := 118140960795 + 3990921 * 2 ^ 59
def prefixEnd_3990921 : Nat := 4983230072969 + 3 ^ 40 * 3990921 * 2
def baseEnd_3990921 : Nat := 455391272693841163763021

theorem tailTrace_3990921 : CollatzResearch.WordTrace tailWord_3990921 prefixEnd_3990921 455391272693841163763021 := by
  unfold tailWord_3990921
  simp only [CollatzResearch.WordTrace]
  refine ⟨145560847174582286887356617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97040564783054857924904411 145560847174582286887356617)
  ·
    refine ⟨109170635380936715165517463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145560847174582286887356617 109170635380936715165517463)
    ·
      refine ⟨163755953071405072748276195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109170635380936715165517463 163755953071405072748276195)
      ·
        refine ⟨245633929607107609122414293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163755953071405072748276195 245633929607107609122414293)
        ·
          refine ⟨5757045225166584588806585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 245633929607107609122414293 5757045225166584588806585)
          ·
            refine ⟨4317783918874938441604939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5757045225166584588806585 4317783918874938441604939)
            ·
              refine ⟨6476675878312407662407409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4317783918874938441604939 6476675878312407662407409)
              ·
                refine ⟨4857506908734305746805557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6476675878312407662407409 4857506908734305746805557)
                ·
                  refine ⟨455391272693841163763021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4857506908734305746805557 455391272693841163763021)
                  ·
                    rfl

theorem cell22_3990921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 2, 5].length) (baseStart_3990921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3990921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3990921 prefixEnd_3990921 := by exact prefixLift 3990921
  have htrace : WordTrace (prefixWord ++ tailWord_3990921) baseStart_3990921 baseEnd_3990921 := by
    simpa [prefixWord, tailWord_3990921, baseEnd_3990921] using wordTrace_append hprefix tailTrace_3990921
  have hstable : (prefixWord ++ tailWord_3990921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990921).length < 2 ^ (prefixWord ++ tailWord_3990921).sum := by decide
  have hdescent : baseEnd_3990921 < baseStart_3990921 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990951 : List Nat := [1, 1, 6, 1, 1, 1, 4, 2, 1, 4]
def baseStart_3990951 : Nat := 118140960795 + 3990951 * 2 ^ 59
def prefixEnd_3990951 : Nat := 4983230072969 + 3 ^ 40 * 3990951 * 2
def baseEnd_3990951 : Nat := 1366184087694613413038971

theorem tailTrace_3990951 : CollatzResearch.WordTrace tailWord_3990951 prefixEnd_3990951 1366184087694613413038971 := by
  unfold tailWord_3990951
  simp only [CollatzResearch.WordTrace]
  refine ⟨145561941364473602010948707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97041294242982401340632471 145561941364473602010948707)
  ·
    refine ⟨218342912046710403016423061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145561941364473602010948707 218342912046710403016423061)
    ·
      refine ⟨10234824002189550141394831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 218342912046710403016423061 10234824002189550141394831)
      ·
        refine ⟨15352236003284325212092247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10234824002189550141394831 15352236003284325212092247)
        ·
          refine ⟨23028354004926487818138371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15352236003284325212092247 23028354004926487818138371)
          ·
            refine ⟨34542531007389731727207557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23028354004926487818138371 34542531007389731727207557)
            ·
              refine ⟨6476724563885574698851417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34542531007389731727207557 6476724563885574698851417)
              ·
                refine ⟨4857543422914181024138563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6476724563885574698851417 4857543422914181024138563)
                ·
                  refine ⟨7286315134371271536207845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4857543422914181024138563 7286315134371271536207845)
                  ·
                    refine ⟨1366184087694613413038971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7286315134371271536207845 1366184087694613413038971)
                    ·
                      rfl

theorem cell22_3990951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_3990951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3990951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3990951 prefixEnd_3990951 := by exact prefixLift 3990951
  have htrace : WordTrace (prefixWord ++ tailWord_3990951) baseStart_3990951 baseEnd_3990951 := by
    simpa [prefixWord, tailWord_3990951, baseEnd_3990951] using wordTrace_append hprefix tailTrace_3990951
  have hstable : (prefixWord ++ tailWord_3990951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990951).length < 2 ^ (prefixWord ++ tailWord_3990951).sum := by decide
  have hdescent : baseEnd_3990951 < baseStart_3990951 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3991060 : List Nat := [2, 4, 3, 1, 2, 1, 1, 2, 3, 3]
def baseStart_3991060 : Nat := 118140960795 + 3991060 * 2 ^ 59
def prefixEnd_3991060 : Nat := 4983230072969 + 3 ^ 40 * 3991060 * 2
def baseEnd_3991060 : Nat := 1366221400622173462063637

theorem tailTrace_3991060 : CollatzResearch.WordTrace tailWord_3991060 prefixEnd_3991060 1366221400622173462063637 := by
  unfold tailWord_3991060
  simp only [CollatzResearch.WordTrace]
  refine ⟨72782958460539356813333317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97043944614052475751111089 72782958460539356813333317)
  ·
    refine ⟨13646804711351129402499997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72782958460539356813333317 13646804711351129402499997)
    ·
      refine ⟨5117551766756673525937499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13646804711351129402499997 5117551766756673525937499)
      ·
        refine ⟨7676327650135010288906249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5117551766756673525937499 7676327650135010288906249)
        ·
          refine ⟨5757245737601257716679687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7676327650135010288906249 5757245737601257716679687)
          ·
            refine ⟨8635868606401886575019531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5757245737601257716679687 8635868606401886575019531)
            ·
              refine ⟨12953802909602829862529297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8635868606401886575019531 12953802909602829862529297)
              ·
                refine ⟨9715352182202122396896973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12953802909602829862529297 9715352182202122396896973)
                ·
                  refine ⟨3643257068325795898836365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9715352182202122396896973 3643257068325795898836365)
                  ·
                    refine ⟨1366221400622173462063637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3643257068325795898836365 1366221400622173462063637)
                    ·
                      rfl

theorem cell22_3991060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_3991060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3991060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3991060 prefixEnd_3991060 := by exact prefixLift 3991060
  have htrace : WordTrace (prefixWord ++ tailWord_3991060) baseStart_3991060 baseEnd_3991060 := by
    simpa [prefixWord, tailWord_3991060, baseEnd_3991060] using wordTrace_append hprefix tailTrace_3991060
  have hstable : (prefixWord ++ tailWord_3991060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3991060).length < 2 ^ (prefixWord ++ tailWord_3991060).sum := by decide
  have hdescent : baseEnd_3991060 < baseStart_3991060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3991060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3991114 : List Nat := [3, 1, 2, 1, 1, 3, 1, 1, 3, 6]
def baseStart_3991114 : Nat := 118140960795 + 3991114 * 2 ^ 59
def prefixEnd_3991114 : Nat := 4983230072969 + 3 ^ 40 * 3991114 * 2
def baseEnd_3991114 : Nat := 1366239885925735321213471

theorem tailTrace_3991114 : CollatzResearch.WordTrace tailWord_3991114 prefixEnd_3991114 1366239885925735321213471 := by
  unfold tailWord_3991114
  simp only [CollatzResearch.WordTrace]
  refine ⟨36391971615720770212283099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97045257641922053899421597 36391971615720770212283099)
  ·
    refine ⟨54587957423581155318424649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36391971615720770212283099 54587957423581155318424649)
    ·
      refine ⟨40940968067685866488818487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54587957423581155318424649 40940968067685866488818487)
      ·
        refine ⟨61411452101528799733227731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40940968067685866488818487 61411452101528799733227731)
        ·
          refine ⟨92117178152293199599841597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61411452101528799733227731 92117178152293199599841597)
          ·
            refine ⟨34543941807109949849940599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92117178152293199599841597 34543941807109949849940599)
            ·
              refine ⟨51815912710664924774910899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34543941807109949849940599 51815912710664924774910899)
              ·
                refine ⟨77723869065997387162366349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51815912710664924774910899 77723869065997387162366349)
                ·
                  refine ⟨29146450899749020185887381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77723869065997387162366349 29146450899749020185887381)
                  ·
                    refine ⟨1366239885925735321213471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29146450899749020185887381 1366239885925735321213471)
                    ·
                      rfl

theorem cell22_3991114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_3991114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3991114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3991114 prefixEnd_3991114 := by exact prefixLift 3991114
  have htrace : WordTrace (prefixWord ++ tailWord_3991114) baseStart_3991114 baseEnd_3991114 := by
    simpa [prefixWord, tailWord_3991114, baseEnd_3991114] using wordTrace_append hprefix tailTrace_3991114
  have hstable : (prefixWord ++ tailWord_3991114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3991114).length < 2 ^ (prefixWord ++ tailWord_3991114).sum := by decide
  have hdescent : baseEnd_3991114 < baseStart_3991114 := by decide
  rcases family_descends (prefixWord ++ tailWord_3991114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3991116 : List Nat := [2, 2, 1, 3, 1, 3, 3, 1, 1, 5]
def baseStart_3991116 : Nat := 118140960795 + 3991116 * 2 ^ 59
def prefixEnd_3991116 : Nat := 4983230072969 + 3 ^ 40 * 3991116 * 2
def baseEnd_3991116 : Nat := 1366240570566607982663465

theorem tailTrace_3991116 : CollatzResearch.WordTrace tailWord_3991116 prefixEnd_3991116 1366240570566607982663465 := by
  unfold tailWord_3991116
  simp only [CollatzResearch.WordTrace]
  refine ⟨72783979704437917595352601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97045306272583890127136801 72783979704437917595352601)
  ·
    refine ⟨54587984778328438196514451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72783979704437917595352601 54587984778328438196514451)
    ·
      refine ⟨81881977167492657294771677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54587984778328438196514451 81881977167492657294771677)
      ·
        refine ⟨30705741437809746485539379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81881977167492657294771677 30705741437809746485539379)
        ·
          refine ⟨46058612156714619728309069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30705741437809746485539379 46058612156714619728309069)
          ·
            refine ⟨17271979558767982398115901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46058612156714619728309069 17271979558767982398115901)
            ·
              refine ⟨6476992334537993399293463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17271979558767982398115901 6476992334537993399293463)
              ·
                refine ⟨9715488501806990098940195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6476992334537993399293463 9715488501806990098940195)
                ·
                  refine ⟨14573232752710485148410293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9715488501806990098940195 14573232752710485148410293)
                  ·
                    refine ⟨1366240570566607982663465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14573232752710485148410293 1366240570566607982663465)
                    ·
                      rfl

theorem cell22_3991116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 1, 1, 5].length) (baseStart_3991116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3991116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3991116 prefixEnd_3991116 := by exact prefixLift 3991116
  have htrace : WordTrace (prefixWord ++ tailWord_3991116) baseStart_3991116 baseEnd_3991116 := by
    simpa [prefixWord, tailWord_3991116, baseEnd_3991116] using wordTrace_append hprefix tailTrace_3991116
  have hstable : (prefixWord ++ tailWord_3991116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3991116).length < 2 ^ (prefixWord ++ tailWord_3991116).sum := by decide
  have hdescent : baseEnd_3991116 < baseStart_3991116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3991116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3991146 : List Nat := [3, 1, 3, 2, 1, 4, 8]
def baseStart_3991146 : Nat := 118140960795 + 3991146 * 2 ^ 59
def prefixEnd_3991146 : Nat := 4983230072969 + 3 ^ 40 * 3991146 * 2
def baseEnd_3991146 : Nat := 50601882969618440904199

theorem tailTrace_3991146 : CollatzResearch.WordTrace tailWord_3991146 prefixEnd_3991146 50601882969618440904199 := by
  unfold tailWord_3991146
  simp only [CollatzResearch.WordTrace]
  refine ⟨36392263399691787578574323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97046035732511433542864861 36392263399691787578574323)
  ·
    refine ⟨54588395099537681367861485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36392263399691787578574323 54588395099537681367861485)
    ·
      refine ⟨20470648162326630512948057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54588395099537681367861485 20470648162326630512948057)
      ·
        refine ⟨15352986121744972884711043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20470648162326630512948057 15352986121744972884711043)
        ·
          refine ⟨23029479182617459327066565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15352986121744972884711043 23029479182617459327066565)
          ·
            refine ⟨4318027346740773623824981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23029479182617459327066565 4318027346740773623824981)
            ·
              refine ⟨50601882969618440904199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4318027346740773623824981 50601882969618440904199)
              ·
                rfl

theorem cell22_3991146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 8].length) (baseStart_3991146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3991146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3991146 prefixEnd_3991146 := by exact prefixLift 3991146
  have htrace : WordTrace (prefixWord ++ tailWord_3991146) baseStart_3991146 baseEnd_3991146 := by
    simpa [prefixWord, tailWord_3991146, baseEnd_3991146] using wordTrace_append hprefix tailTrace_3991146
  have hstable : (prefixWord ++ tailWord_3991146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3991146).length < 2 ^ (prefixWord ++ tailWord_3991146).sum := by decide
  have hdescent : baseEnd_3991146 < baseStart_3991146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3991146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3991159 : List Nat := [1, 1, 3, 1, 1, 3, 1, 3, 2, 6]
def baseStart_3991159 : Nat := 118140960795 + 3991159 * 2 ^ 59
def prefixEnd_3991159 : Nat := 4983230072969 + 3 ^ 40 * 3991159 * 2
def baseEnd_3991159 : Nat := 1366255290345370203838333

theorem tailTrace_3991159 : CollatzResearch.WordTrace tailWord_3991159 prefixEnd_3991159 1366255290345370203838333 := by
  unfold tailWord_3991159
  simp only [CollatzResearch.WordTrace]
  refine ⟨145569527747720053534520531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97046351831813369023013687 145569527747720053534520531)
  ·
    refine ⟨218354291621580080301780797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145569527747720053534520531 218354291621580080301780797)
    ·
      refine ⟨81882859358092530113167799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218354291621580080301780797 81882859358092530113167799)
      ·
        refine ⟨122824289037138795169751699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81882859358092530113167799 122824289037138795169751699)
        ·
          refine ⟨184236433555708192754627549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122824289037138795169751699 184236433555708192754627549)
          ·
            refine ⟨69088662583390572282985331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184236433555708192754627549 69088662583390572282985331)
            ·
              refine ⟨103632993875085858424477997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69088662583390572282985331 103632993875085858424477997)
              ·
                refine ⟨38862372703157196909179249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103632993875085858424477997 38862372703157196909179249)
                ·
                  refine ⟨29146779527367897681884437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38862372703157196909179249 29146779527367897681884437)
                  ·
                    refine ⟨1366255290345370203838333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29146779527367897681884437 1366255290345370203838333)
                    ·
                      rfl

theorem cell22_3991159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 6].length) (baseStart_3991159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3991159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3991159 prefixEnd_3991159 := by exact prefixLift 3991159
  have htrace : WordTrace (prefixWord ++ tailWord_3991159) baseStart_3991159 baseEnd_3991159 := by
    simpa [prefixWord, tailWord_3991159, baseEnd_3991159] using wordTrace_append hprefix tailTrace_3991159
  have hstable : (prefixWord ++ tailWord_3991159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3991159).length < 2 ^ (prefixWord ++ tailWord_3991159).sum := by decide
  have hdescent : baseEnd_3991159 < baseStart_3991159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3991159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3991268 : List Nat := [2, 3, 1, 1, 1, 3, 3, 1, 4, 3]
def baseStart_3991268 : Nat := 118140960795 + 3991268 * 2 ^ 59
def prefixEnd_3991268 : Nat := 4983230072969 + 3 ^ 40 * 3991268 * 2
def baseEnd_3991268 : Nat := 1366292603272930252862999

theorem tailTrace_3991268 : CollatzResearch.WordTrace tailWord_3991268 prefixEnd_3991268 1366292603272930252862999 := by
  unfold tailWord_3991268
  simp only [CollatzResearch.WordTrace]
  refine ⟨72786751652162582575119229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97049002202883443433492305 72786751652162582575119229)
  ·
    refine ⟨27295031869560968465669711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72786751652162582575119229 27295031869560968465669711)
    ·
      refine ⟨40942547804341452698504567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27295031869560968465669711 40942547804341452698504567)
      ·
        refine ⟨61413821706512179047756851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40942547804341452698504567 61413821706512179047756851)
        ·
          refine ⟨92120732559768268571635277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61413821706512179047756851 92120732559768268571635277)
          ·
            refine ⟨34545274709913100714363229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92120732559768268571635277 34545274709913100714363229)
            ·
              refine ⟨12954478016217412767886211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34545274709913100714363229 12954478016217412767886211)
              ·
                refine ⟨19431717024326119151829317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12954478016217412767886211 19431717024326119151829317)
                ·
                  refine ⟨3643446942061147340967997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19431717024326119151829317 3643446942061147340967997)
                  ·
                    refine ⟨1366292603272930252862999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3643446942061147340967997 1366292603272930252862999)
                    ·
                      rfl

theorem cell22_3991268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 4, 3].length) (baseStart_3991268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3991268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3991268 prefixEnd_3991268 := by exact prefixLift 3991268
  have htrace : WordTrace (prefixWord ++ tailWord_3991268) baseStart_3991268 baseEnd_3991268 := by
    simpa [prefixWord, tailWord_3991268, baseEnd_3991268] using wordTrace_append hprefix tailTrace_3991268
  have hstable : (prefixWord ++ tailWord_3991268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3991268).length < 2 ^ (prefixWord ++ tailWord_3991268).sum := by decide
  have hdescent : baseEnd_3991268 < baseStart_3991268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3991268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3991298 : List Nat := [3, 4, 1, 1, 1, 1, 3, 8]
def baseStart_3991298 : Nat := 118140960795 + 3991298 * 2 ^ 59
def prefixEnd_3991298 : Nat := 4983230072969 + 3 ^ 40 * 3991298 * 2
def baseEnd_3991298 : Nat := 151811430320668908290323

theorem tailTrace_3991298 : CollatzResearch.WordTrace tailWord_3991298 prefixEnd_3991298 151811430320668908290323 := by
  unfold tailWord_3991298
  simp only [CollatzResearch.WordTrace]
  refine ⟨36393649373554120068457637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97049731662810986849220365 36393649373554120068457637)
  ·
    refine ⟨6823809257541397512835807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36393649373554120068457637 6823809257541397512835807)
    ·
      refine ⟨10235713886312096269253711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6823809257541397512835807 10235713886312096269253711)
      ·
        refine ⟨15353570829468144403880567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10235713886312096269253711 15353570829468144403880567)
        ·
          refine ⟨23030356244202216605820851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15353570829468144403880567 23030356244202216605820851)
          ·
            refine ⟨34545534366303324908731277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23030356244202216605820851 34545534366303324908731277)
            ·
              refine ⟨12954575387363746840774229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34545534366303324908731277 12954575387363746840774229)
              ·
                refine ⟨151811430320668908290323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12954575387363746840774229 151811430320668908290323)
                ·
                  rfl

theorem cell22_3991298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 8].length) (baseStart_3991298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3991298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3991298 prefixEnd_3991298 := by exact prefixLift 3991298
  have htrace : WordTrace (prefixWord ++ tailWord_3991298) baseStart_3991298 baseEnd_3991298 := by
    simpa [prefixWord, tailWord_3991298, baseEnd_3991298] using wordTrace_append hprefix tailTrace_3991298
  have hstable : (prefixWord ++ tailWord_3991298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3991298).length < 2 ^ (prefixWord ++ tailWord_3991298).sum := by decide
  have hdescent : baseEnd_3991298 < baseStart_3991298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3991298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3991403 : List Nat := [1, 1, 1, 1, 2, 2, 3, 2, 6, 3]
def baseStart_3991403 : Nat := 118140960795 + 3991403 * 2 ^ 59
def prefixEnd_3991403 : Nat := 4983230072969 + 3 ^ 40 * 3991403 * 2
def baseEnd_3991403 : Nat := 1366338816531834900737585

theorem tailTrace_3991403 : CollatzResearch.WordTrace tailWord_3991403 prefixEnd_3991403 1366338816531834900737585 := by
  unfold tailWord_3991403
  simp only [CollatzResearch.WordTrace]
  refine ⟨145578427158836083206402863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97052284772557388804268575 145578427158836083206402863)
  ·
    refine ⟨218367640738254124809604295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145578427158836083206402863 218367640738254124809604295)
    ·
      refine ⟨327551461107381187214406443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218367640738254124809604295 327551461107381187214406443)
      ·
        refine ⟨491327191661071780821609665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327551461107381187214406443 491327191661071780821609665)
        ·
          refine ⟨368495393745803835616207249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 491327191661071780821609665 368495393745803835616207249)
          ·
            refine ⟨276371545309352876712155437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 368495393745803835616207249 276371545309352876712155437)
            ·
              refine ⟨103639329491007328767058289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 276371545309352876712155437 103639329491007328767058289)
              ·
                refine ⟨77729497118255496575293717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103639329491007328767058289 77729497118255496575293717)
                ·
                  refine ⟨3643570177418226401966893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 77729497118255496575293717 3643570177418226401966893)
                  ·
                    refine ⟨1366338816531834900737585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3643570177418226401966893 1366338816531834900737585)
                    ·
                      rfl

theorem cell22_3991403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 6, 3].length) (baseStart_3991403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3991403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3991403 prefixEnd_3991403 := by exact prefixLift 3991403
  have htrace : WordTrace (prefixWord ++ tailWord_3991403) baseStart_3991403 baseEnd_3991403 := by
    simpa [prefixWord, tailWord_3991403, baseEnd_3991403] using wordTrace_append hprefix tailTrace_3991403
  have hstable : (prefixWord ++ tailWord_3991403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3991403).length < 2 ^ (prefixWord ++ tailWord_3991403).sum := by decide
  have hdescent : baseEnd_3991403 < baseStart_3991403 := by decide
  rcases family_descends (prefixWord ++ tailWord_3991403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3991482 : List Nat := [3, 1, 1, 1, 2, 1, 2, 7, 1, 3]
def baseStart_3991482 : Nat := 118140960795 + 3991482 * 2 ^ 59
def prefixEnd_3991482 : Nat := 4983230072969 + 3 ^ 40 * 3991482 * 2
def baseEnd_3991482 : Nat := 1366365859846305028012343

theorem tailTrace_3991482 : CollatzResearch.WordTrace tailWord_3991482 prefixEnd_3991482 1366365859846305028012343 := by
  unfold tailWord_3991482
  simp only [CollatzResearch.WordTrace]
  refine ⟨36395327131387469924632175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97054205683699919799019133 36395327131387469924632175)
  ·
    refine ⟨54592990697081204886948263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36395327131387469924632175 54592990697081204886948263)
    ·
      refine ⟨81889486045621807330422395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54592990697081204886948263 81889486045621807330422395)
      ·
        refine ⟨122834229068432710995633593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81889486045621807330422395 122834229068432710995633593)
        ·
          refine ⟨92125671801324533246725195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122834229068432710995633593 92125671801324533246725195)
          ·
            refine ⟨138188507701986799870087793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92125671801324533246725195 138188507701986799870087793)
            ·
              refine ⟨103641380776490099902565845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138188507701986799870087793 103641380776490099902565845)
              ·
                refine ⟨2429094861948986716466387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 103641380776490099902565845 2429094861948986716466387)
                ·
                  refine ⟨3643642292923480074699581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2429094861948986716466387 3643642292923480074699581)
                  ·
                    refine ⟨1366365859846305028012343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3643642292923480074699581 1366365859846305028012343)
                    ·
                      rfl

theorem cell22_3991482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 7, 1, 3].length) (baseStart_3991482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3991482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3991482 prefixEnd_3991482 := by exact prefixLift 3991482
  have htrace : WordTrace (prefixWord ++ tailWord_3991482) baseStart_3991482 baseEnd_3991482 := by
    simpa [prefixWord, tailWord_3991482, baseEnd_3991482] using wordTrace_append hprefix tailTrace_3991482
  have hstable : (prefixWord ++ tailWord_3991482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3991482).length < 2 ^ (prefixWord ++ tailWord_3991482).sum := by decide
  have hdescent : baseEnd_3991482 < baseStart_3991482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3991482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3991493 : List Nat := [1, 3, 1, 1, 1, 1, 1, 6, 2, 5]
def baseStart_3991493 : Nat := 118140960795 + 3991493 * 2 ^ 59
def prefixEnd_3991493 : Nat := 4983230072969 + 3 ^ 40 * 3991493 * 2
def baseEnd_3991493 : Nat := 1366369625371104665987309

theorem tailTrace_3991493 : CollatzResearch.WordTrace tailWord_3991493 prefixEnd_3991493 1366369625371104665987309 := by
  unfold tailWord_3991493
  simp only [CollatzResearch.WordTrace]
  refine ⟨145581709728510028577179133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97054473152340019051452755 145581709728510028577179133)
  ·
    refine ⟨54593141148191260716442175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145581709728510028577179133 54593141148191260716442175)
    ·
      refine ⟨81889711722286891074663263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54593141148191260716442175 81889711722286891074663263)
      ·
        refine ⟨122834567583430336611994895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81889711722286891074663263 122834567583430336611994895)
        ·
          refine ⟨184251851375145504917992343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122834567583430336611994895 184251851375145504917992343)
          ·
            refine ⟨276377777062718257376988515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184251851375145504917992343 276377777062718257376988515)
            ·
              refine ⟨414566665594077386065482773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276377777062718257376988515 414566665594077386065482773)
              ·
                refine ⟨19432812449722377471819505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 414566665594077386065482773 19432812449722377471819505)
                ·
                  refine ⟨14574609337291783103864629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19432812449722377471819505 14574609337291783103864629)
                  ·
                    refine ⟨1366369625371104665987309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14574609337291783103864629 1366369625371104665987309)
                    ·
                      rfl

theorem cell22_3991493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 2, 5].length) (baseStart_3991493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3991493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3991493 prefixEnd_3991493 := by exact prefixLift 3991493
  have htrace : WordTrace (prefixWord ++ tailWord_3991493) baseStart_3991493 baseEnd_3991493 := by
    simpa [prefixWord, tailWord_3991493, baseEnd_3991493] using wordTrace_append hprefix tailTrace_3991493
  have hstable : (prefixWord ++ tailWord_3991493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3991493).length < 2 ^ (prefixWord ++ tailWord_3991493).sum := by decide
  have hdescent : baseEnd_3991493 < baseStart_3991493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3991493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3991499 : List Nat := [1, 1, 1, 1, 3, 4, 5, 2, 1, 3]
def baseStart_3991499 : Nat := 118140960795 + 3991499 * 2 ^ 59
def prefixEnd_3991499 : Nat := 4983230072969 + 3 ^ 40 * 3991499 * 2
def baseEnd_3991499 : Nat := 1366371679293722650337291

theorem tailTrace_3991499 : CollatzResearch.WordTrace tailWord_3991499 prefixEnd_3991499 1366371679293722650337291 := by
  unfold tailWord_3991499
  simp only [CollatzResearch.WordTrace]
  refine ⟨145581928566488291601897551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97054619044325527734598367 145581928566488291601897551)
  ·
    refine ⟨218372892849732437402846327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145581928566488291601897551 218372892849732437402846327)
    ·
      refine ⟨327559339274598656104269491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218372892849732437402846327 327559339274598656104269491)
      ·
        refine ⟨491339008911897984156404237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327559339274598656104269491 491339008911897984156404237)
        ·
          refine ⟨184252128341961744058651589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 491339008911897984156404237 184252128341961744058651589)
          ·
            refine ⟨34547274064117827010997173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 184252128341961744058651589 34547274064117827010997173)
            ·
              refine ⟨3238806943511046282280985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34547274064117827010997173 3238806943511046282280985)
              ·
                refine ⟨2429105207633284711710739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3238806943511046282280985 2429105207633284711710739)
                ·
                  refine ⟨3643657811449927067566109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2429105207633284711710739 3643657811449927067566109)
                  ·
                    refine ⟨1366371679293722650337291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3643657811449927067566109 1366371679293722650337291)
                    ·
                      rfl

theorem cell22_3991499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 5, 2, 1, 3].length) (baseStart_3991499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3991499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3991499 prefixEnd_3991499 := by exact prefixLift 3991499
  have htrace : WordTrace (prefixWord ++ tailWord_3991499) baseStart_3991499 baseEnd_3991499 := by
    simpa [prefixWord, tailWord_3991499, baseEnd_3991499] using wordTrace_append hprefix tailTrace_3991499
  have hstable : (prefixWord ++ tailWord_3991499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3991499).length < 2 ^ (prefixWord ++ tailWord_3991499).sum := by decide
  have hdescent : baseEnd_3991499 < baseStart_3991499 := by decide
  rcases family_descends (prefixWord ++ tailWord_3991499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3991555 : List Nat := [1, 1, 1, 3, 2, 1, 1, 5, 4, 3]
def baseStart_3991555 : Nat := 118140960795 + 3991555 * 2 ^ 59
def prefixEnd_3991555 : Nat := 4983230072969 + 3 ^ 40 * 3991555 * 2
def baseEnd_3991555 : Nat := 1366390849238157170937119

theorem tailTrace_3991555 : CollatzResearch.WordTrace tailWord_3991555 prefixEnd_3991555 1366390849238157170937119 := by
  unfold tailWord_3991555
  simp only [CollatzResearch.WordTrace]
  refine ⟨145583971054285413165936119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97055980702856942110624079 145583971054285413165936119)
  ·
    refine ⟨218375956581428119748904179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145583971054285413165936119 218375956581428119748904179)
    ·
      refine ⟨327563934872142179623356269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218375956581428119748904179 327563934872142179623356269)
      ·
        refine ⟨122836475577053317358758601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 327563934872142179623356269 122836475577053317358758601)
        ·
          refine ⟨92127356682789988019068951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122836475577053317358758601 92127356682789988019068951)
          ·
            refine ⟨138191035024184982028603427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92127356682789988019068951 138191035024184982028603427)
            ·
              refine ⟨207286552536277473042905141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138191035024184982028603427 207286552536277473042905141)
              ·
                refine ⟨19433114300276013097772357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 207286552536277473042905141 19433114300276013097772357)
                ·
                  refine ⟨3643708931301752455832317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19433114300276013097772357 3643708931301752455832317)
                  ·
                    refine ⟨1366390849238157170937119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3643708931301752455832317 1366390849238157170937119)
                    ·
                      rfl

theorem cell22_3991555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 4, 3].length) (baseStart_3991555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3991555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3991555 prefixEnd_3991555 := by exact prefixLift 3991555
  have htrace : WordTrace (prefixWord ++ tailWord_3991555) baseStart_3991555 baseEnd_3991555 := by
    simpa [prefixWord, tailWord_3991555, baseEnd_3991555] using wordTrace_append hprefix tailTrace_3991555
  have hstable : (prefixWord ++ tailWord_3991555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3991555).length < 2 ^ (prefixWord ++ tailWord_3991555).sum := by decide
  have hdescent : baseEnd_3991555 < baseStart_3991555 := by decide
  rcases family_descends (prefixWord ++ tailWord_3991555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3991557 : List Nat := [1, 3, 1, 1, 2, 5, 1, 4, 4]
def baseStart_3991557 : Nat := 118140960795 + 3991557 * 2 ^ 59
def prefixEnd_3991557 : Nat := 4983230072969 + 3 ^ 40 * 3991557 * 2
def baseEnd_3991557 : Nat := 455463844626343277462371

theorem tailTrace_3991557 : CollatzResearch.WordTrace tailWord_3991557 prefixEnd_3991557 455463844626343277462371 := by
  unfold tailWord_3991557
  simp only [CollatzResearch.WordTrace]
  refine ⟨145584044000278167507508925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97056029333518778338339283 145584044000278167507508925)
  ·
    refine ⟨54594016500104312815315847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145584044000278167507508925 54594016500104312815315847)
    ·
      refine ⟨81891024750156469222973771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54594016500104312815315847 81891024750156469222973771)
      ·
        refine ⟨122836537125234703834460657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81891024750156469222973771 122836537125234703834460657)
        ·
          refine ⟨92127402843926027875845493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122836537125234703834460657 92127402843926027875845493)
          ·
            refine ⟨8636944016618065113360515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92127402843926027875845493 8636944016618065113360515)
            ·
              refine ⟨12955416024927097670040773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8636944016618065113360515 12955416024927097670040773)
              ·
                refine ⟨2429140504673830813132645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12955416024927097670040773 2429140504673830813132645)
                ·
                  refine ⟨455463844626343277462371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2429140504673830813132645 455463844626343277462371)
                  ·
                    rfl

theorem cell22_3991557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 4, 4].length) (baseStart_3991557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3991557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3991557 prefixEnd_3991557 := by exact prefixLift 3991557
  have htrace : WordTrace (prefixWord ++ tailWord_3991557) baseStart_3991557 baseEnd_3991557 := by
    simpa [prefixWord, tailWord_3991557, baseEnd_3991557] using wordTrace_append hprefix tailTrace_3991557
  have hstable : (prefixWord ++ tailWord_3991557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3991557).length < 2 ^ (prefixWord ++ tailWord_3991557).sum := by decide
  have hdescent : baseEnd_3991557 < baseStart_3991557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3991557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3991591 : List Nat := [1, 1, 7, 1, 2, 1, 2, 3, 4]
def baseStart_3991591 : Nat := 118140960795 + 3991591 * 2 ^ 59
def prefixEnd_3991591 : Nat := 4983230072969 + 3 ^ 40 * 3991591 * 2
def baseEnd_3991591 : Nat := 455467724257955025679003

theorem tailTrace_3991591 : CollatzResearch.WordTrace tailWord_3991591 prefixEnd_3991591 455467724257955025679003 := by
  unfold tailWord_3991591
  simp only [CollatzResearch.WordTrace]
  refine ⟨145585284082154991314246627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97056856054769994209497751 145585284082154991314246627)
  ·
    refine ⟨218377926123232486971369941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145585284082154991314246627 218377926123232486971369941)
    ·
      refine ⟨5118232643513261413391483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 218377926123232486971369941 5118232643513261413391483)
      ·
        refine ⟨7677348965269892120087225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5118232643513261413391483 7677348965269892120087225)
        ·
          refine ⟨5758011723952419090065419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7677348965269892120087225 5758011723952419090065419)
          ·
            refine ⟨8637017585928628635098129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5758011723952419090065419 8637017585928628635098129)
            ·
              refine ⟨6477763189446471476323597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8637017585928628635098129 6477763189446471476323597)
              ·
                refine ⟨2429161196042426803621349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6477763189446471476323597 2429161196042426803621349)
                ·
                  refine ⟨455467724257955025679003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2429161196042426803621349 455467724257955025679003)
                  ·
                    rfl

theorem cell22_3991591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 3, 4].length) (baseStart_3991591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3991591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3991591 prefixEnd_3991591 := by exact prefixLift 3991591
  have htrace : WordTrace (prefixWord ++ tailWord_3991591) baseStart_3991591 baseEnd_3991591 := by
    simpa [prefixWord, tailWord_3991591, baseEnd_3991591] using wordTrace_append hprefix tailTrace_3991591
  have hstable : (prefixWord ++ tailWord_3991591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3991591).length < 2 ^ (prefixWord ++ tailWord_3991591).sum := by decide
  have hdescent : baseEnd_3991591 < baseStart_3991591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3991591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3991681 : List Nat := [1, 2, 4, 2, 3, 2, 2, 1, 5]
def baseStart_3991681 : Nat := 118140960795 + 3991681 * 2 ^ 59
def prefixEnd_3991681 : Nat := 4983230072969 + 3 ^ 40 * 3991681 * 2
def baseEnd_3991681 : Nat := 455477993871044947428911

theorem tailTrace_3991681 : CollatzResearch.WordTrace tailWord_3991681 prefixEnd_3991681 455477993871044947428911 := by
  unfold tailWord_3991681
  simp only [CollatzResearch.WordTrace]
  refine ⟨145588566651828936685022897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97059044434552624456681931 145588566651828936685022897)
  ·
    refine ⟨109191424988871702513767173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145588566651828936685022897 109191424988871702513767173)
    ·
      refine ⟨20473392185413444221331345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109191424988871702513767173 20473392185413444221331345)
      ·
        refine ⟨15355044139060083165998509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20473392185413444221331345 15355044139060083165998509)
        ·
          refine ⟨5758141552147531187249441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15355044139060083165998509 5758141552147531187249441)
          ·
            refine ⟨4318606164110648390437081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5758141552147531187249441 4318606164110648390437081)
            ·
              refine ⟨3238954623082986292827811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4318606164110648390437081 3238954623082986292827811)
              ·
                refine ⟨4858431934624479439241717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3238954623082986292827811 4858431934624479439241717)
                ·
                  refine ⟨455477993871044947428911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4858431934624479439241717 455477993871044947428911)
                  ·
                    rfl

theorem cell22_3991681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 2, 1, 5].length) (baseStart_3991681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3991681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3991681 prefixEnd_3991681 := by exact prefixLift 3991681
  have htrace : WordTrace (prefixWord ++ tailWord_3991681) baseStart_3991681 baseEnd_3991681 := by
    simpa [prefixWord, tailWord_3991681, baseEnd_3991681] using wordTrace_append hprefix tailTrace_3991681
  have hstable : (prefixWord ++ tailWord_3991681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3991681).length < 2 ^ (prefixWord ++ tailWord_3991681).sum := by decide
  have hdescent : baseEnd_3991681 < baseStart_3991681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3991681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3991694 : List Nat := [4, 1, 1, 3, 3, 1, 1, 1, 3, 4]
def baseStart_3991694 : Nat := 118140960795 + 3991694 * 2 ^ 59
def prefixEnd_3991694 : Nat := 4983230072969 + 3 ^ 40 * 3991694 * 2
def baseEnd_3991694 : Nat := 1366438431778807141711693

theorem tailTrace_3991694 : CollatzResearch.WordTrace tailWord_3991694 prefixEnd_3991694 1366438431778807141711693 := by
  unfold tailWord_3991694
  simp only [CollatzResearch.WordTrace]
  refine ⟨18198630100097729988155767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97059360533854559936830757 18198630100097729988155767)
  ·
    refine ⟨27297945150146594982233651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18198630100097729988155767 27297945150146594982233651)
    ·
      refine ⟨40946917725219892473350477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27297945150146594982233651 40946917725219892473350477)
      ·
        refine ⟨15355094146957459677506429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40946917725219892473350477 15355094146957459677506429)
        ·
          refine ⟨5758160305109047379064911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15355094146957459677506429 5758160305109047379064911)
          ·
            refine ⟨8637240457663571068597367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5758160305109047379064911 8637240457663571068597367)
            ·
              refine ⟨12955860686495356602896051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8637240457663571068597367 12955860686495356602896051)
              ·
                refine ⟨19433791029743034904344077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12955860686495356602896051 19433791029743034904344077)
                ·
                  refine ⟨7287671636153638089129029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19433791029743034904344077 7287671636153638089129029)
                  ·
                    refine ⟨1366438431778807141711693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7287671636153638089129029 1366438431778807141711693)
                    ·
                      rfl

theorem cell22_3991694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 3, 4].length) (baseStart_3991694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3991694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3991694 prefixEnd_3991694 := by exact prefixLift 3991694
  have htrace : WordTrace (prefixWord ++ tailWord_3991694) baseStart_3991694 baseEnd_3991694 := by
    simpa [prefixWord, tailWord_3991694, baseEnd_3991694] using wordTrace_append hprefix tailTrace_3991694
  have hstable : (prefixWord ++ tailWord_3991694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3991694).length < 2 ^ (prefixWord ++ tailWord_3991694).sum := by decide
  have hdescent : baseEnd_3991694 < baseStart_3991694 := by decide
  rcases family_descends (prefixWord ++ tailWord_3991694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3991705 : List Nat := [1, 2, 1, 2, 1, 2, 1, 5, 1, 6]
def baseStart_3991705 : Nat := 118140960795 + 3991705 * 2 ^ 59
def prefixEnd_3991705 : Nat := 4983230072969 + 3 ^ 40 * 3991705 * 2
def baseEnd_3991705 : Nat := 1366442197303606779686659

theorem tailTrace_3991705 : CollatzResearch.WordTrace tailWord_3991705 prefixEnd_3991705 1366442197303606779686659 := by
  unfold tailWord_3991705
  simp only [CollatzResearch.WordTrace]
  refine ⟨145589442003741988783896569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97059628002494659189264379 145589442003741988783896569)
  ·
    refine ⟨109192081502806491587922427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145589442003741988783896569 109192081502806491587922427)
    ·
      refine ⟨163788122254209737381883641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109192081502806491587922427 163788122254209737381883641)
      ·
        refine ⟨122841091690657303036412731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163788122254209737381883641 122841091690657303036412731)
        ·
          refine ⟨184261637535985954554619097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122841091690657303036412731 184261637535985954554619097)
          ·
            refine ⟨138196228151989465915964323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184261637535985954554619097 138196228151989465915964323)
            ·
              refine ⟨207294342227984198873946485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138196228151989465915964323 207294342227984198873946485)
              ·
                refine ⟨19433844583873518644432483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 207294342227984198873946485 19433844583873518644432483)
                ·
                  refine ⟨29150766875810277966648725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19433844583873518644432483 29150766875810277966648725)
                  ·
                    refine ⟨1366442197303606779686659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29150766875810277966648725 1366442197303606779686659)
                    ·
                      rfl

theorem cell22_3991705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 6].length) (baseStart_3991705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3991705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3991705 prefixEnd_3991705 := by exact prefixLift 3991705
  have htrace : WordTrace (prefixWord ++ tailWord_3991705) baseStart_3991705 baseEnd_3991705 := by
    simpa [prefixWord, tailWord_3991705, baseEnd_3991705] using wordTrace_append hprefix tailTrace_3991705
  have hstable : (prefixWord ++ tailWord_3991705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3991705).length < 2 ^ (prefixWord ++ tailWord_3991705).sum := by decide
  have hdescent : baseEnd_3991705 < baseStart_3991705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3991705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3991711 : List Nat := [1, 1, 2, 6, 1, 2, 3, 1, 1, 4]
def baseStart_3991711 : Nat := 118140960795 + 3991711 * 2 ^ 59
def prefixEnd_3991711 : Nat := 4983230072969 + 3 ^ 40 * 3991711 * 2
def baseEnd_3991711 : Nat := 1366444251226224764036641

theorem tailTrace_3991711 : CollatzResearch.WordTrace tailWord_3991711 prefixEnd_3991711 1366444251226224764036641 := by
  unfold tailWord_3991711
  simp only [CollatzResearch.WordTrace]
  refine ⟨145589660841720251808614987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97059773894480167872409991 145589660841720251808614987)
  ·
    refine ⟨218384491262580377712922481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145589660841720251808614987 218384491262580377712922481)
    ·
      refine ⟨163788368446935283284691861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218384491262580377712922481 163788368446935283284691861)
      ·
        refine ⟨7677579770950091403969931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 163788368446935283284691861 7677579770950091403969931)
        ·
          refine ⟨11516369656425137105954897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7677579770950091403969931 11516369656425137105954897)
          ·
            refine ⟨8637277242318852829466173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11516369656425137105954897 8637277242318852829466173)
            ·
              refine ⟨3238978965869569811049815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8637277242318852829466173 3238978965869569811049815)
              ·
                refine ⟨4858468448804354716574723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3238978965869569811049815 4858468448804354716574723)
                ·
                  refine ⟨7287702673206532074862085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4858468448804354716574723 7287702673206532074862085)
                  ·
                    refine ⟨1366444251226224764036641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7287702673206532074862085 1366444251226224764036641)
                    ·
                      rfl

theorem cell22_3991711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 3, 1, 1, 4].length) (baseStart_3991711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3991711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3991711 prefixEnd_3991711 := by exact prefixLift 3991711
  have htrace : WordTrace (prefixWord ++ tailWord_3991711) baseStart_3991711 baseEnd_3991711 := by
    simpa [prefixWord, tailWord_3991711, baseEnd_3991711] using wordTrace_append hprefix tailTrace_3991711
  have hstable : (prefixWord ++ tailWord_3991711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3991711).length < 2 ^ (prefixWord ++ tailWord_3991711).sum := by decide
  have hdescent : baseEnd_3991711 < baseStart_3991711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3991711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3991786 : List Nat := [3, 1, 3, 1, 1, 2, 1, 6, 1, 3]
def baseStart_3991786 : Nat := 118140960795 + 3991786 * 2 ^ 59
def prefixEnd_3991786 : Nat := 4983230072969 + 3 ^ 40 * 3991786 * 2
def baseEnd_3991786 : Nat := 1366469925258949568411411

theorem tailTrace_3991786 : CollatzResearch.WordTrace tailWord_3991786 prefixEnd_3991786 1366469925258949568411411 := by
  unfold tailWord_3991786
  simp only [CollatzResearch.WordTrace]
  refine ⟨36398099079112134904398803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97061597544299026411730141 36398099079112134904398803)
  ·
    refine ⟨54597148618668202356598205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36398099079112134904398803 54597148618668202356598205)
    ·
      refine ⟨20473930732000575883724327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54597148618668202356598205 20473930732000575883724327)
      ·
        refine ⟨30710896098000863825586491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20473930732000575883724327 30710896098000863825586491)
        ·
          refine ⟨46066344147001295738379737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30710896098000863825586491 46066344147001295738379737)
          ·
            refine ⟨34549758110250971803784803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46066344147001295738379737 34549758110250971803784803)
            ·
              refine ⟨51824637165376457705677205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34549758110250971803784803 51824637165376457705677205)
              ·
                refine ⟨2429279867127021454953619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 51824637165376457705677205 2429279867127021454953619)
                ·
                  refine ⟨3643919800690532182430429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2429279867127021454953619 3643919800690532182430429)
                  ·
                    refine ⟨1366469925258949568411411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3643919800690532182430429 1366469925258949568411411)
                    ·
                      rfl

theorem cell22_3991786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 6, 1, 3].length) (baseStart_3991786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3991786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3991786 prefixEnd_3991786 := by exact prefixLift 3991786
  have htrace : WordTrace (prefixWord ++ tailWord_3991786) baseStart_3991786 baseEnd_3991786 := by
    simpa [prefixWord, tailWord_3991786, baseEnd_3991786] using wordTrace_append hprefix tailTrace_3991786
  have hstable : (prefixWord ++ tailWord_3991786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3991786).length < 2 ^ (prefixWord ++ tailWord_3991786).sum := by decide
  have hdescent : baseEnd_3991786 < baseStart_3991786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3991786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3991829 : List Nat := [1, 3, 2, 1, 2, 1, 4, 3, 1, 4]
def baseStart_3991829 : Nat := 118140960795 + 3991829 * 2 ^ 59
def prefixEnd_3991829 : Nat := 4983230072969 + 3 ^ 40 * 3991829 * 2
def baseEnd_3991829 : Nat := 1366484645037711789586279

theorem tailTrace_3991829 : CollatzResearch.WordTrace tailWord_3991829 prefixEnd_3991829 1366484645037711789586279 := by
  unfold tailWord_3991829
  simp only [CollatzResearch.WordTrace]
  refine ⟨145593964655292757961410541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97062643103528505307607027 145593964655292757961410541)
  ·
    refine ⟨54597736745734784235528953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145593964655292757961410541 54597736745734784235528953)
    ·
      refine ⟨40948302559301088176646715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54597736745734784235528953 40948302559301088176646715)
      ·
        refine ⟨61422453838951632264970073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40948302559301088176646715 61422453838951632264970073)
        ·
          refine ⟨46066840379213724198727555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61422453838951632264970073 46066840379213724198727555)
          ·
            refine ⟨69100260568820586298091333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46066840379213724198727555 69100260568820586298091333)
            ·
              refine ⟨12956298856653859930892125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69100260568820586298091333 12956298856653859930892125)
              ·
                refine ⟨4858612071245197474084547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12956298856653859930892125 4858612071245197474084547)
                ·
                  refine ⟨7287918106867796211126821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4858612071245197474084547 7287918106867796211126821)
                  ·
                    refine ⟨1366484645037711789586279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7287918106867796211126821 1366484645037711789586279)
                    ·
                      rfl

theorem cell22_3991829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 3, 1, 4].length) (baseStart_3991829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3991829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3991829 prefixEnd_3991829 := by exact prefixLift 3991829
  have htrace : WordTrace (prefixWord ++ tailWord_3991829) baseStart_3991829 baseEnd_3991829 := by
    simpa [prefixWord, tailWord_3991829, baseEnd_3991829] using wordTrace_append hprefix tailTrace_3991829
  have hstable : (prefixWord ++ tailWord_3991829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3991829).length < 2 ^ (prefixWord ++ tailWord_3991829).sum := by decide
  have hdescent : baseEnd_3991829 < baseStart_3991829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3991829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3991844 : List Nat := [2, 3, 1, 3, 1, 2, 3, 1, 6]
def baseStart_3991844 : Nat := 118140960795 + 3991844 * 2 ^ 59
def prefixEnd_3991844 : Nat := 4983230072969 + 3 ^ 40 * 3991844 * 2
def baseEnd_3991844 : Nat := 455496593281418916820411

theorem tailTrace_3991844 : CollatzResearch.WordTrace tailWord_3991844 prefixEnd_3991844 455496593281418916820411 := by
  unfold tailWord_3991844
  simp only [CollatzResearch.WordTrace]
  refine ⟨72797255875119207761603293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97063007833492277015471057 72797255875119207761603293)
  ·
    refine ⟨27298970953169702910601235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72797255875119207761603293 27298970953169702910601235)
    ·
      refine ⟨40948456429754554365901853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27298970953169702910601235 40948456429754554365901853)
      ·
        refine ⟨15355671161157957887213195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40948456429754554365901853 15355671161157957887213195)
        ·
          refine ⟨23033506741736936830819793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15355671161157957887213195 23033506741736936830819793)
          ·
            refine ⟨17275130056302702623114845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23033506741736936830819793 17275130056302702623114845)
            ·
              refine ⟨6478173771113513483668067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17275130056302702623114845 6478173771113513483668067)
              ·
                refine ⟨9717260656670270225502101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6478173771113513483668067 9717260656670270225502101)
                ·
                  refine ⟨455496593281418916820411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9717260656670270225502101 455496593281418916820411)
                  ·
                    rfl

theorem cell22_3991844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 1, 6].length) (baseStart_3991844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3991844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3991844 prefixEnd_3991844 := by exact prefixLift 3991844
  have htrace : WordTrace (prefixWord ++ tailWord_3991844) baseStart_3991844 baseEnd_3991844 := by
    simpa [prefixWord, tailWord_3991844, baseEnd_3991844] using wordTrace_append hprefix tailTrace_3991844
  have hstable : (prefixWord ++ tailWord_3991844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3991844).length < 2 ^ (prefixWord ++ tailWord_3991844).sum := by decide
  have hdescent : baseEnd_3991844 < baseStart_3991844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3991844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3991850 : List Nat := [3, 1, 4, 2, 3, 1, 2, 1, 5]
def baseStart_3991850 : Nat := 118140960795 + 3991850 * 2 ^ 59
def prefixEnd_3991850 : Nat := 4983230072969 + 3 ^ 40 * 3991850 * 2
def baseEnd_3991850 : Nat := 455497277922291578270405

theorem tailTrace_3991850 : CollatzResearch.WordTrace tailWord_3991850 prefixEnd_3991850 455497277922291578270405 := by
  unfold tailWord_3991850
  simp only [CollatzResearch.WordTrace]
  refine ⟨36398682647054169636981251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97063153725477785698616669 36398682647054169636981251)
  ·
    refine ⟨54598023970581254455471877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36398682647054169636981251 54598023970581254455471877)
    ·
      refine ⟨10237129494483985210400977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54598023970581254455471877 10237129494483985210400977)
      ·
        refine ⟨7677847120862988907800733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10237129494483985210400977 7677847120862988907800733)
        ·
          refine ⟨2879192670323620840425275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7677847120862988907800733 2879192670323620840425275)
          ·
            refine ⟨4318789005485431260637913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2879192670323620840425275 4318789005485431260637913)
            ·
              refine ⟨3239091754114073445478435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4318789005485431260637913 3239091754114073445478435)
              ·
                refine ⟨4858637631171110168217653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3239091754114073445478435 4858637631171110168217653)
                ·
                  refine ⟨455497277922291578270405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4858637631171110168217653 455497277922291578270405)
                  ·
                    rfl

theorem cell22_3991850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 2, 1, 5].length) (baseStart_3991850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3991850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3991850 prefixEnd_3991850 := by exact prefixLift 3991850
  have htrace : WordTrace (prefixWord ++ tailWord_3991850) baseStart_3991850 baseEnd_3991850 := by
    simpa [prefixWord, tailWord_3991850, baseEnd_3991850] using wordTrace_append hprefix tailTrace_3991850
  have hstable : (prefixWord ++ tailWord_3991850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3991850).length < 2 ^ (prefixWord ++ tailWord_3991850).sum := by decide
  have hdescent : baseEnd_3991850 < baseStart_3991850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3991850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3991893 : List Nat := [1, 3, 2, 2, 4, 1, 2, 2, 2, 3]
def baseStart_3991893 : Nat := 118140960795 + 3991893 * 2 ^ 59
def prefixEnd_3991893 : Nat := 4983230072969 + 3 ^ 40 * 3991893 * 2
def baseEnd_3991893 : Nat := 1366506553545636955986083

theorem tailTrace_3991893 : CollatzResearch.WordTrace tailWord_3991893 prefixEnd_3991893 1366506553545636955986083 := by
  unfold tailWord_3991893
  simp only [CollatzResearch.WordTrace]
  refine ⟨145596298927060896891740333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97064199284707264594493555 145596298927060896891740333)
  ·
    refine ⟨54598612097647836334402625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145596298927060896891740333 54598612097647836334402625)
    ·
      refine ⟨40948959073235877250801969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54598612097647836334402625 40948959073235877250801969)
      ·
        refine ⟨30711719304926907938101477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40948959073235877250801969 30711719304926907938101477)
        ·
          refine ⟨5758447369673795238394027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30711719304926907938101477 5758447369673795238394027)
          ·
            refine ⟨8637671054510692857591041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5758447369673795238394027 8637671054510692857591041)
            ·
              refine ⟨6478253290883019643193281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8637671054510692857591041 6478253290883019643193281)
              ·
                refine ⟨4858689968162264732394961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6478253290883019643193281 4858689968162264732394961)
                ·
                  refine ⟨3644017476121698549296221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4858689968162264732394961 3644017476121698549296221)
                  ·
                    refine ⟨1366506553545636955986083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3644017476121698549296221 1366506553545636955986083)
                    ·
                      rfl

theorem cell22_3991893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 2, 2, 3].length) (baseStart_3991893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3991893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3991893 prefixEnd_3991893 := by exact prefixLift 3991893
  have htrace : WordTrace (prefixWord ++ tailWord_3991893) baseStart_3991893 baseEnd_3991893 := by
    simpa [prefixWord, tailWord_3991893, baseEnd_3991893] using wordTrace_append hprefix tailTrace_3991893
  have hstable : (prefixWord ++ tailWord_3991893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3991893).length < 2 ^ (prefixWord ++ tailWord_3991893).sum := by decide
  have hdescent : baseEnd_3991893 < baseStart_3991893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3991893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3991906 : List Nat := [3, 3, 2, 1, 1, 4, 1, 7]
def baseStart_3991906 : Nat := 118140960795 + 3991906 * 2 ^ 59
def prefixEnd_3991906 : Nat := 4983230072969 + 3 ^ 40 * 3991906 * 2
def baseEnd_3991906 : Nat := 151834555967923250601227

theorem tailTrace_3991906 : CollatzResearch.WordTrace tailWord_3991906 prefixEnd_3991906 151834555967923250601227 := by
  unfold tailWord_3991906
  simp only [CollatzResearch.WordTrace]
  refine ⟨36399193269003450027990893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97064515384009200074642381 36399193269003450027990893)
  ·
    refine ⟨13649697475876293760496585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36399193269003450027990893 13649697475876293760496585)
    ·
      refine ⟨10237273106907220320372439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13649697475876293760496585 10237273106907220320372439)
      ·
        refine ⟨15355909660360830480558659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10237273106907220320372439 15355909660360830480558659)
        ·
          refine ⟨23033864490541245720837989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15355909660360830480558659 23033864490541245720837989)
          ·
            refine ⟨4318849591976483572657123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23033864490541245720837989 4318849591976483572657123)
            ·
              refine ⟨6478274387964725358985685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4318849591976483572657123 6478274387964725358985685)
              ·
                refine ⟨151834555967923250601227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6478274387964725358985685 151834555967923250601227)
                ·
                  rfl

theorem cell22_3991906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 7].length) (baseStart_3991906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3991906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3991906 prefixEnd_3991906 := by exact prefixLift 3991906
  have htrace : WordTrace (prefixWord ++ tailWord_3991906) baseStart_3991906 baseEnd_3991906 := by
    simpa [prefixWord, tailWord_3991906, baseEnd_3991906] using wordTrace_append hprefix tailTrace_3991906
  have hstable : (prefixWord ++ tailWord_3991906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3991906).length < 2 ^ (prefixWord ++ tailWord_3991906).sum := by decide
  have hdescent : baseEnd_3991906 < baseStart_3991906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3991906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3991994 : List Nat := [3, 1, 1, 1, 2, 1, 1, 6, 1, 5]
def baseStart_3991994 : Nat := 118140960795 + 3991994 * 2 ^ 59
def prefixEnd_3991994 : Nat := 4983230072969 + 3 ^ 40 * 3991994 * 2
def baseEnd_3991994 : Nat := 1366541127909706359210773

theorem tailTrace_3991994 : CollatzResearch.WordTrace tailWord_3991994 prefixEnd_3991994 1366541127909706359210773 := by
  unfold tailWord_3991994
  simp only [CollatzResearch.WordTrace]
  refine ⟨36399995674923747785291759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97066655133129994094111357 36399995674923747785291759)
  ·
    refine ⟨54599993512385621677937639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36399995674923747785291759 54599993512385621677937639)
    ·
      refine ⟨81899990268578432516906459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54599993512385621677937639 81899990268578432516906459)
      ·
        refine ⟨122849985402867648775359689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81899990268578432516906459 122849985402867648775359689)
        ·
          refine ⟨92137489052150736581519767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122849985402867648775359689 92137489052150736581519767)
          ·
            refine ⟨138206233578226104872279651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92137489052150736581519767 138206233578226104872279651)
            ·
              refine ⟨207309350367339157308419477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138206233578226104872279651 207309350367339157308419477)
              ·
                refine ⟨9717625798469022998832163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 207309350367339157308419477 9717625798469022998832163)
                ·
                  refine ⟨14576438697703534498248245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9717625798469022998832163 14576438697703534498248245)
                  ·
                    refine ⟨1366541127909706359210773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14576438697703534498248245 1366541127909706359210773)
                    ·
                      rfl

theorem cell22_3991994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 6, 1, 5].length) (baseStart_3991994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3991994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3991994 prefixEnd_3991994 := by exact prefixLift 3991994
  have htrace : WordTrace (prefixWord ++ tailWord_3991994) baseStart_3991994 baseEnd_3991994 := by
    simpa [prefixWord, tailWord_3991994, baseEnd_3991994] using wordTrace_append hprefix tailTrace_3991994
  have hstable : (prefixWord ++ tailWord_3991994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3991994).length < 2 ^ (prefixWord ++ tailWord_3991994).sum := by decide
  have hdescent : baseEnd_3991994 < baseStart_3991994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3991994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992009 : List Nat := [1, 2, 1, 1, 2, 1, 5, 1, 4, 4]
def baseStart_3992009 : Nat := 118140960795 + 3992009 * 2 ^ 59
def prefixEnd_3992009 : Nat := 4983230072969 + 3 ^ 40 * 3992009 * 2
def baseEnd_3992009 : Nat := 1366546262716251320085727

theorem tailTrace_3992009 : CollatzResearch.WordTrace tailWord_3992009 prefixEnd_3992009 1366546262716251320085727 := by
  unfold tailWord_3992009
  simp only [CollatzResearch.WordTrace]
  refine ⟨145600529794640648702963081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97067019863093765801975387 145600529794640648702963081)
  ·
    refine ⟨109200397345980486527222311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145600529794640648702963081 109200397345980486527222311)
    ·
      refine ⟨163800596018970729790833467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109200397345980486527222311 163800596018970729790833467)
      ·
        refine ⟨245700894028456094686250201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163800596018970729790833467 245700894028456094686250201)
        ·
          refine ⟨184275670521342071014687651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245700894028456094686250201 184275670521342071014687651)
          ·
            refine ⟨276413505782013106522031477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184275670521342071014687651 276413505782013106522031477)
            ·
              refine ⟨25913766167063728736440451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 276413505782013106522031477 25913766167063728736440451)
              ·
                refine ⟨38870649250595593104660677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25913766167063728736440451 38870649250595593104660677)
                ·
                  refine ⟨7288246734486673707123877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38870649250595593104660677 7288246734486673707123877)
                  ·
                    refine ⟨1366546262716251320085727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7288246734486673707123877 1366546262716251320085727)
                    ·
                      rfl

theorem cell22_3992009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 4, 4].length) (baseStart_3992009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3992009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3992009 prefixEnd_3992009 := by exact prefixLift 3992009
  have htrace : WordTrace (prefixWord ++ tailWord_3992009) baseStart_3992009 baseEnd_3992009 := by
    simpa [prefixWord, tailWord_3992009, baseEnd_3992009] using wordTrace_append hprefix tailTrace_3992009
  have hstable : (prefixWord ++ tailWord_3992009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992009).length < 2 ^ (prefixWord ++ tailWord_3992009).sum := by decide
  have hdescent : baseEnd_3992009 < baseStart_3992009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992011 : List Nat := [1, 1, 1, 1, 3, 3, 1, 6, 2, 3]
def baseStart_3992011 : Nat := 118140960795 + 3992011 * 2 ^ 59
def prefixEnd_3992011 : Nat := 4983230072969 + 3 ^ 40 * 3992011 * 2
def baseEnd_3992011 : Nat := 1366546947357123981535721

theorem tailTrace_3992011 : CollatzResearch.WordTrace tailWord_3992011 prefixEnd_3992011 1366546947357123981535721 := by
  unfold tailWord_3992011
  simp only [CollatzResearch.WordTrace]
  refine ⟨145600602740633403044535887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97067068493755602029690591 145600602740633403044535887)
  ·
    refine ⟨218400904110950104566803831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145600602740633403044535887 218400904110950104566803831)
    ·
      refine ⟨327601356166425156850205747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218400904110950104566803831 327601356166425156850205747)
      ·
        refine ⟨491402034249637735275308621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327601356166425156850205747 491402034249637735275308621)
        ·
          refine ⟨184275762843614150728240733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 491402034249637735275308621 184275762843614150728240733)
          ·
            refine ⟨69103411066355306523090275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184275762843614150728240733 69103411066355306523090275)
            ·
              refine ⟨103655116599532959784635413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69103411066355306523090275 103655116599532959784635413)
              ·
                refine ⟨4858833590603107489904785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 103655116599532959784635413 4858833590603107489904785)
                ·
                  refine ⟨3644125192952330617428589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4858833590603107489904785 3644125192952330617428589)
                  ·
                    refine ⟨1366546947357123981535721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3644125192952330617428589 1366546947357123981535721)
                    ·
                      rfl

theorem cell22_3992011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 6, 2, 3].length) (baseStart_3992011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3992011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3992011 prefixEnd_3992011 := by exact prefixLift 3992011
  have htrace : WordTrace (prefixWord ++ tailWord_3992011) baseStart_3992011 baseEnd_3992011 := by
    simpa [prefixWord, tailWord_3992011, baseEnd_3992011] using wordTrace_append hprefix tailTrace_3992011
  have hstable : (prefixWord ++ tailWord_3992011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992011).length < 2 ^ (prefixWord ++ tailWord_3992011).sum := by decide
  have hdescent : baseEnd_3992011 < baseStart_3992011 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992069 : List Nat := [1, 3, 1, 1, 2, 2, 2, 3, 7]
def baseStart_3992069 : Nat := 118140960795 + 3992069 * 2 ^ 59
def prefixEnd_3992069 : Nat := 4983230072969 + 3 ^ 40 * 3992069 * 2
def baseEnd_3992069 : Nat := 455522267314143721195181

theorem tailTrace_3992069 : CollatzResearch.WordTrace tailWord_3992069 prefixEnd_3992069 455522267314143721195181 := by
  unfold tailWord_3992069
  simp only [CollatzResearch.WordTrace]
  refine ⟨145602718174423278950147261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97068478782948852633431507 145602718174423278950147261)
  ·
    refine ⟨54601019315408729606305223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145602718174423278950147261 54601019315408729606305223)
    ·
      refine ⟨81901528973113094409457835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54601019315408729606305223 81901528973113094409457835)
      ·
        refine ⟨122852293459669641614186753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81901528973113094409457835 122852293459669641614186753)
        ·
          refine ⟨92139220094752231210640065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122852293459669641614186753 92139220094752231210640065)
          ·
            refine ⟨69104415071064173407980049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92139220094752231210640065 69104415071064173407980049)
            ·
              refine ⟨51828311303298130055985037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69104415071064173407980049 51828311303298130055985037)
              ·
                refine ⟨19435616738736798770994389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51828311303298130055985037 19435616738736798770994389)
                ·
                  refine ⟨455522267314143721195181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19435616738736798770994389 455522267314143721195181)
                  ·
                    rfl

theorem cell22_3992069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 7].length) (baseStart_3992069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3992069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3992069 prefixEnd_3992069 := by exact prefixLift 3992069
  have htrace : WordTrace (prefixWord ++ tailWord_3992069) baseStart_3992069 baseEnd_3992069 := by
    simpa [prefixWord, tailWord_3992069, baseEnd_3992069] using wordTrace_append hprefix tailTrace_3992069
  have hstable : (prefixWord ++ tailWord_3992069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992069).length < 2 ^ (prefixWord ++ tailWord_3992069).sum := by decide
  have hdescent : baseEnd_3992069 < baseStart_3992069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992118 : List Nat := [5, 1, 2, 1, 2, 1, 1, 2, 2, 5]
def baseStart_3992118 : Nat := 118140960795 + 3992118 * 2 ^ 59
def prefixEnd_3992118 : Nat := 4983230072969 + 3 ^ 40 * 3992118 * 2
def baseEnd_3992118 : Nat := 1366583575643811369110393

theorem tailTrace_3992118 : CollatzResearch.WordTrace tailWord_3992118 prefixEnd_3992118 1366583575643811369110393 := by
  unfold tailWord_3992118
  simp only [CollatzResearch.WordTrace]
  refine ⟨9100281584452860019917563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97069670234163840212454005 9100281584452860019917563)
  ·
    refine ⟨13650422376679290029876345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9100281584452860019917563 13650422376679290029876345)
    ·
      refine ⟨10237816782509467522407259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13650422376679290029876345 10237816782509467522407259)
      ·
        refine ⟨15356725173764201283610889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10237816782509467522407259 15356725173764201283610889)
        ·
          refine ⟨11517543880323150962708167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15356725173764201283610889 11517543880323150962708167)
          ·
            refine ⟨17276315820484726444062251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11517543880323150962708167 17276315820484726444062251)
            ·
              refine ⟨25914473730727089666093377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17276315820484726444062251 25914473730727089666093377)
              ·
                refine ⟨19435855298045317249570033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25914473730727089666093377 19435855298045317249570033)
                ·
                  refine ⟨14576891473533987937177525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19435855298045317249570033 14576891473533987937177525)
                  ·
                    refine ⟨1366583575643811369110393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14576891473533987937177525 1366583575643811369110393)
                    ·
                      rfl

theorem cell22_3992118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_3992118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3992118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3992118 prefixEnd_3992118 := by exact prefixLift 3992118
  have htrace : WordTrace (prefixWord ++ tailWord_3992118) baseStart_3992118 baseEnd_3992118 := by
    simpa [prefixWord, tailWord_3992118, baseEnd_3992118] using wordTrace_append hprefix tailTrace_3992118
  have hstable : (prefixWord ++ tailWord_3992118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992118).length < 2 ^ (prefixWord ++ tailWord_3992118).sum := by decide
  have hdescent : baseEnd_3992118 < baseStart_3992118 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992158 : List Nat := [4, 4, 1, 2, 1, 2, 1, 3, 1, 3]
def baseStart_3992158 : Nat := 118140960795 + 3992158 * 2 ^ 59
def prefixEnd_3992158 : Nat := 4983230072969 + 3 ^ 40 * 3992158 * 2
def baseEnd_3992158 : Nat := 1366597268461264598110271

theorem tailTrace_3992158 : CollatzResearch.WordTrace tailWord_3992158 prefixEnd_3992158 1366597268461264598110271 := by
  unfold tailWord_3992158
  simp only [CollatzResearch.WordTrace]
  refine ⟨18200745533887605893767141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97070642847400564766758085 18200745533887605893767141)
  ·
    refine ⟨3412639787603926105081339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18200745533887605893767141 3412639787603926105081339)
    ·
      refine ⟨5118959681405889157622009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3412639787603926105081339 5118959681405889157622009)
      ·
        refine ⟨3839219761054416868216507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5118959681405889157622009 3839219761054416868216507)
        ·
          refine ⟨5758829641581625302324761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3839219761054416868216507 5758829641581625302324761)
          ·
            refine ⟨4319122231186218976743571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5758829641581625302324761 4319122231186218976743571)
            ·
              refine ⟨6478683346779328465115357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4319122231186218976743571 6478683346779328465115357)
              ·
                refine ⟨2429506255042248174418259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6478683346779328465115357 2429506255042248174418259)
                ·
                  refine ⟨3644259382563372261627389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2429506255042248174418259 3644259382563372261627389)
                  ·
                    refine ⟨1366597268461264598110271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3644259382563372261627389 1366597268461264598110271)
                    ·
                      rfl

theorem cell22_3992158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_3992158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3992158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3992158 prefixEnd_3992158 := by exact prefixLift 3992158
  have htrace : WordTrace (prefixWord ++ tailWord_3992158) baseStart_3992158 baseEnd_3992158 := by
    simpa [prefixWord, tailWord_3992158, baseEnd_3992158] using wordTrace_append hprefix tailTrace_3992158
  have hstable : (prefixWord ++ tailWord_3992158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992158).length < 2 ^ (prefixWord ++ tailWord_3992158).sum := by decide
  have hdescent : baseEnd_3992158 < baseStart_3992158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992161 : List Nat := [1, 2, 3, 1, 1, 4, 2, 1, 1, 6]
def baseStart_3992161 : Nat := 118140960795 + 3992161 * 2 ^ 59
def prefixEnd_3992161 : Nat := 4983230072969 + 3 ^ 40 * 3992161 * 2
def baseEnd_3992161 : Nat := 1366598295422573590285261

theorem tailTrace_3992161 : CollatzResearch.WordTrace tailWord_3992161 prefixEnd_3992161 1366598295422573590285261 := by
  unfold tailWord_3992161
  simp only [CollatzResearch.WordTrace]
  refine ⟨145606073690089978662496337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97070715793393319108330891 145606073690089978662496337)
  ·
    refine ⟨109204555267567483996872253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145606073690089978662496337 109204555267567483996872253)
    ·
      refine ⟨40951708225337806498827095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109204555267567483996872253 40951708225337806498827095)
      ·
        refine ⟨61427562338006709748240643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40951708225337806498827095 61427562338006709748240643)
        ·
          refine ⟨92141343507010064622360965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61427562338006709748240643 92141343507010064622360965)
          ·
            refine ⟨17276501907564387116692681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92141343507010064622360965 17276501907564387116692681)
            ·
              refine ⟨12957376430673290337519511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17276501907564387116692681 12957376430673290337519511)
              ·
                refine ⟨19436064646009935506279267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12957376430673290337519511 19436064646009935506279267)
                ·
                  refine ⟨29154096969014903259418901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19436064646009935506279267 29154096969014903259418901)
                  ·
                    refine ⟨1366598295422573590285261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29154096969014903259418901 1366598295422573590285261)
                    ·
                      rfl

theorem cell22_3992161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 6].length) (baseStart_3992161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3992161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3992161 prefixEnd_3992161 := by exact prefixLift 3992161
  have htrace : WordTrace (prefixWord ++ tailWord_3992161) baseStart_3992161 baseEnd_3992161 := by
    simpa [prefixWord, tailWord_3992161, baseEnd_3992161] using wordTrace_append hprefix tailTrace_3992161
  have hstable : (prefixWord ++ tailWord_3992161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992161).length < 2 ^ (prefixWord ++ tailWord_3992161).sum := by decide
  have hdescent : baseEnd_3992161 < baseStart_3992161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992182 : List Nat := [5, 1, 1, 2, 4, 1, 1, 1, 6]
def baseStart_3992182 : Nat := 118140960795 + 3992182 * 2 ^ 59
def prefixEnd_3992182 : Nat := 4983230072969 + 3 ^ 40 * 3992182 * 2
def baseEnd_3992182 : Nat := 455535161383912178503399

theorem tailTrace_3992182 : CollatzResearch.WordTrace tailWord_3992182 prefixEnd_3992182 455535161383912178503399 := by
  unfold tailWord_3992182
  simp only [CollatzResearch.WordTrace]
  refine ⟨9100427476438368703063175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97071226415342599499340533 9100427476438368703063175)
  ·
    refine ⟨13650641214657553054594763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9100427476438368703063175 13650641214657553054594763)
    ·
      refine ⟨20475961821986329581892145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13650641214657553054594763 20475961821986329581892145)
      ·
        refine ⟨15356971366489747186419109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20475961821986329581892145 15356971366489747186419109)
        ·
          refine ⟨2879432131216827597453583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15356971366489747186419109 2879432131216827597453583)
          ·
            refine ⟨4319148196825241396180375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2879432131216827597453583 4319148196825241396180375)
            ·
              refine ⟨6478722295237862094270563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4319148196825241396180375 6478722295237862094270563)
              ·
                refine ⟨9718083442856793141405845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6478722295237862094270563 9718083442856793141405845)
                ·
                  refine ⟨455535161383912178503399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9718083442856793141405845 455535161383912178503399)
                  ·
                    rfl

theorem cell22_3992182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 1, 6].length) (baseStart_3992182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3992182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3992182 prefixEnd_3992182 := by exact prefixLift 3992182
  have htrace : WordTrace (prefixWord ++ tailWord_3992182) baseStart_3992182 baseEnd_3992182 := by
    simpa [prefixWord, tailWord_3992182, baseEnd_3992182] using wordTrace_append hprefix tailTrace_3992182
  have hstable : (prefixWord ++ tailWord_3992182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992182).length < 2 ^ (prefixWord ++ tailWord_3992182).sum := by decide
  have hdescent : baseEnd_3992182 < baseStart_3992182 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992197 : List Nat := [1, 3, 1, 1, 4, 4, 2, 1, 2, 3]
def baseStart_3992197 : Nat := 118140960795 + 3992197 * 2 ^ 59
def prefixEnd_3992197 : Nat := 4983230072969 + 3 ^ 40 * 3992197 * 2
def baseEnd_3992197 : Nat := 1366610618958281496385151

theorem tailTrace_3992197 : CollatzResearch.WordTrace tailWord_3992197 prefixEnd_3992197 1366610618958281496385151 := by
  unfold tailWord_3992197
  simp only [CollatzResearch.WordTrace]
  refine ⟨145607386717959556810806845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97071591145306371207204563 145607386717959556810806845)
  ·
    refine ⟨54602770019234833804052567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145607386717959556810806845 54602770019234833804052567)
    ·
      refine ⟨81904155028852250706078851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54602770019234833804052567 81904155028852250706078851)
      ·
        refine ⟨122856232543278376059118277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81904155028852250706078851 122856232543278376059118277)
        ·
          refine ⟨23035543601864695511084677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122856232543278376059118277 23035543601864695511084677)
          ·
            refine ⟨4319164425349630408328377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23035543601864695511084677 4319164425349630408328377)
            ·
              refine ⟨3239373319012222806246283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4319164425349630408328377 3239373319012222806246283)
              ·
                refine ⟨4859059978518334209369425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3239373319012222806246283 4859059978518334209369425)
                ·
                  refine ⟨3644294983888750657027069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4859059978518334209369425 3644294983888750657027069)
                  ·
                    refine ⟨1366610618958281496385151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3644294983888750657027069 1366610618958281496385151)
                    ·
                      rfl

theorem cell22_3992197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 2, 1, 2, 3].length) (baseStart_3992197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3992197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3992197 prefixEnd_3992197 := by exact prefixLift 3992197
  have htrace : WordTrace (prefixWord ++ tailWord_3992197) baseStart_3992197 baseEnd_3992197 := by
    simpa [prefixWord, tailWord_3992197, baseEnd_3992197] using wordTrace_append hprefix tailTrace_3992197
  have hstable : (prefixWord ++ tailWord_3992197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992197).length < 2 ^ (prefixWord ++ tailWord_3992197).sum := by decide
  have hdescent : baseEnd_3992197 < baseStart_3992197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992221 : List Nat := [1, 4, 2, 1, 1, 1, 2, 1, 9]
def baseStart_3992221 : Nat := 118140960795 + 3992221 * 2 ^ 59
def prefixEnd_3992221 : Nat := 4983230072969 + 3 ^ 40 * 3992221 * 2
def baseEnd_3992221 : Nat := 455539611549584477928359

theorem tailTrace_3992221 : CollatzResearch.WordTrace tailWord_3992221 prefixEnd_3992221 455539611549584477928359 := by
  unfold tailWord_3992221
  simp only [CollatzResearch.WordTrace]
  refine ⟨145608262069872608909680517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97072174713248405939787011 145608262069872608909680517)
  ·
    refine ⟨27301549138101114170565097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145608262069872608909680517 27301549138101114170565097)
    ·
      refine ⟨20476161853575835627923823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27301549138101114170565097 20476161853575835627923823)
      ·
        refine ⟨30714242780363753441885735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20476161853575835627923823 30714242780363753441885735)
        ·
          refine ⟨46071364170545630162828603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30714242780363753441885735 46071364170545630162828603)
          ·
            refine ⟨69107046255818445244242905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46071364170545630162828603 69107046255818445244242905)
            ·
              refine ⟨51830284691863833933182179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69107046255818445244242905 51830284691863833933182179)
              ·
                refine ⟨77745427037795750899773269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51830284691863833933182179 77745427037795750899773269)
                ·
                  refine ⟨455539611549584477928359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 77745427037795750899773269 455539611549584477928359)
                  ·
                    rfl

theorem cell22_3992221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 9].length) (baseStart_3992221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3992221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3992221 prefixEnd_3992221 := by exact prefixLift 3992221
  have htrace : WordTrace (prefixWord ++ tailWord_3992221) baseStart_3992221 baseEnd_3992221 := by
    simpa [prefixWord, tailWord_3992221, baseEnd_3992221] using wordTrace_append hprefix tailTrace_3992221
  have hstable : (prefixWord ++ tailWord_3992221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992221).length < 2 ^ (prefixWord ++ tailWord_3992221).sum := by decide
  have hdescent : baseEnd_3992221 < baseStart_3992221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992253 : List Nat := [1, 4, 1, 2, 1, 4, 1, 1, 2, 5]
def baseStart_3992253 : Nat := 118140960795 + 3992253 * 2 ^ 59
def prefixEnd_3992253 : Nat := 4983230072969 + 3 ^ 40 * 3992253 * 2
def baseEnd_3992253 : Nat := 1366629788902716016984979

theorem tailTrace_3992253 : CollatzResearch.WordTrace tailWord_3992253 prefixEnd_3992253 1366629788902716016984979 := by
  unfold tailWord_3992253
  simp only [CollatzResearch.WordTrace]
  refine ⟨145609429205756678374845413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97072952803837785583230275 145609429205756678374845413)
  ·
    refine ⟨27301767976079377195283515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145609429205756678374845413 27301767976079377195283515)
    ·
      refine ⟨40952651964119065792925273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27301767976079377195283515 40952651964119065792925273)
      ·
        refine ⟨30714488973089299344693955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40952651964119065792925273 30714488973089299344693955)
        ·
          refine ⟨46071733459633949017040933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30714488973089299344693955 46071733459633949017040933)
          ·
            refine ⟨8638450023681365440695175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46071733459633949017040933 8638450023681365440695175)
            ·
              refine ⟨12957675035522048161042763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8638450023681365440695175 12957675035522048161042763)
              ·
                refine ⟨19436512553283072241564145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12957675035522048161042763 19436512553283072241564145)
                ·
                  refine ⟨14577384414962304181173109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19436512553283072241564145 14577384414962304181173109)
                  ·
                    refine ⟨1366629788902716016984979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14577384414962304181173109 1366629788902716016984979)
                    ·
                      rfl

theorem cell22_3992253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 2, 5].length) (baseStart_3992253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3992253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3992253 prefixEnd_3992253 := by exact prefixLift 3992253
  have htrace : WordTrace (prefixWord ++ tailWord_3992253) baseStart_3992253 baseEnd_3992253 := by
    simpa [prefixWord, tailWord_3992253, baseEnd_3992253] using wordTrace_append hprefix tailTrace_3992253
  have hstable : (prefixWord ++ tailWord_3992253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992253).length < 2 ^ (prefixWord ++ tailWord_3992253).sum := by decide
  have hdescent : baseEnd_3992253 < baseStart_3992253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992311 : List Nat := [1, 1, 3, 1, 1, 1, 3, 11]
def baseStart_3992311 : Nat := 118140960795 + 3992311 * 2 ^ 59
def prefixEnd_3992311 : Nat := 4983230072969 + 3 ^ 40 * 3992311 * 2
def baseEnd_3992311 : Nat := 151849960387558133226089

theorem tailTrace_3992311 : CollatzResearch.WordTrace tailWord_3992311 prefixEnd_3992311 151849960387558133226089 := by
  unfold tailWord_3992311
  simp only [CollatzResearch.WordTrace]
  refine ⟨145611544639546554280456787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97074363093031036186971191 145611544639546554280456787)
  ·
    refine ⟨218417316959319831420685181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145611544639546554280456787 218417316959319831420685181)
    ·
      refine ⟨81906493859744936782756943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218417316959319831420685181 81906493859744936782756943)
      ·
        refine ⟨122859740789617405174135415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81906493859744936782756943 122859740789617405174135415)
        ·
          refine ⟨184289611184426107761203123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122859740789617405174135415 184289611184426107761203123)
          ·
            refine ⟨276434416776639161641804685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184289611184426107761203123 276434416776639161641804685)
            ·
              refine ⟨103662906291239685615676757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 276434416776639161641804685 103662906291239685615676757)
              ·
                refine ⟨151849960387558133226089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 103662906291239685615676757 151849960387558133226089)
                ·
                  rfl

theorem cell22_3992311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 11].length) (baseStart_3992311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3992311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3992311 prefixEnd_3992311 := by exact prefixLift 3992311
  have htrace : WordTrace (prefixWord ++ tailWord_3992311) baseStart_3992311 baseEnd_3992311 := by
    simpa [prefixWord, tailWord_3992311, baseEnd_3992311] using wordTrace_append hprefix tailTrace_3992311
  have hstable : (prefixWord ++ tailWord_3992311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992311).length < 2 ^ (prefixWord ++ tailWord_3992311).sum := by decide
  have hdescent : baseEnd_3992311 < baseStart_3992311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992328 : List Nat := [2, 1, 3, 2, 2, 3, 1, 8]
def baseStart_3992328 : Nat := 118140960795 + 3992328 * 2 ^ 59
def prefixEnd_3992328 : Nat := 4983230072969 + 3 ^ 40 * 3992328 * 2
def baseEnd_3992328 : Nat := 151850606992826757928861

theorem tailTrace_3992328 : CollatzResearch.WordTrace tailWord_3992328 prefixEnd_3992328 151850606992826757928861 := by
  unfold tailWord_3992328
  simp only [CollatzResearch.WordTrace]
  refine ⟨72806082340242483091912819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97074776453656644122550425 72806082340242483091912819)
  ·
    refine ⟨109209123510363724637869229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72806082340242483091912819 109209123510363724637869229)
    ·
      refine ⟨40953421316386396739200961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109209123510363724637869229 40953421316386396739200961)
      ·
        refine ⟨30715065987289797554400721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40953421316386396739200961 30715065987289797554400721)
        ·
          refine ⟨23036299490467348165800541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30715065987289797554400721 23036299490467348165800541)
          ·
            refine ⟨8638612308925255562175203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23036299490467348165800541 8638612308925255562175203)
            ·
              refine ⟨12957918463387883343262805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8638612308925255562175203 12957918463387883343262805)
              ·
                refine ⟨151850606992826757928861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12957918463387883343262805 151850606992826757928861)
                ·
                  rfl

theorem cell22_3992328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 8].length) (baseStart_3992328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3992328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3992328 prefixEnd_3992328 := by exact prefixLift 3992328
  have htrace : WordTrace (prefixWord ++ tailWord_3992328) baseStart_3992328 baseEnd_3992328 := by
    simpa [prefixWord, tailWord_3992328, baseEnd_3992328] using wordTrace_append hprefix tailTrace_3992328
  have hstable : (prefixWord ++ tailWord_3992328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992328).length < 2 ^ (prefixWord ++ tailWord_3992328).sum := by decide
  have hdescent : baseEnd_3992328 < baseStart_3992328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992362 : List Nat := [3, 1, 4, 3, 1, 1, 2, 7]
def baseStart_3992362 : Nat := 118140960795 + 3992362 * 2 ^ 59
def prefixEnd_3992362 : Nat := 4983230072969 + 3 ^ 40 * 3992362 * 2
def baseEnd_3992362 : Nat := 151851900203364007334405

theorem tailTrace_3992362 : CollatzResearch.WordTrace tailWord_3992362 prefixEnd_3992362 151851900203364007334405 := by
  unfold tailWord_3992362
  simp only [CollatzResearch.WordTrace]
  refine ⟨36403351190590447497640835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97075603174907859993708893 36403351190590447497640835)
  ·
    refine ⟨54605026785885671246461253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36403351190590447497640835 54605026785885671246461253)
    ·
      refine ⟨10238442522353563358711485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54605026785885671246461253 10238442522353563358711485)
      ·
        refine ⟨3839415945882586259516807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10238442522353563358711485 3839415945882586259516807)
        ·
          refine ⟨5759123918823879389275211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3839415945882586259516807 5759123918823879389275211)
          ·
            refine ⟨8638685878235819083912817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5759123918823879389275211 8638685878235819083912817)
            ·
              refine ⟨6479014408676864312934613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8638685878235819083912817 6479014408676864312934613)
              ·
                refine ⟨151851900203364007334405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6479014408676864312934613 151851900203364007334405)
                ·
                  rfl

theorem cell22_3992362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 7].length) (baseStart_3992362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3992362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3992362 prefixEnd_3992362 := by exact prefixLift 3992362
  have htrace : WordTrace (prefixWord ++ tailWord_3992362) baseStart_3992362 baseEnd_3992362 := by
    simpa [prefixWord, tailWord_3992362, baseEnd_3992362] using wordTrace_append hprefix tailTrace_3992362
  have hstable : (prefixWord ++ tailWord_3992362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992362).length < 2 ^ (prefixWord ++ tailWord_3992362).sum := by decide
  have hdescent : baseEnd_3992362 < baseStart_3992362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992366 : List Nat := [4, 1, 3, 2, 1, 3, 2, 1, 2, 3]
def baseStart_3992366 : Nat := 118140960795 + 3992366 * 2 ^ 59
def prefixEnd_3992366 : Nat := 4983230072969 + 3 ^ 40 * 3992366 * 2
def baseEnd_3992366 : Nat := 1366668471112021388909633

theorem tailTrace_3992366 : CollatzResearch.WordTrace tailWord_3992366 prefixEnd_3992366 1366668471112021388909633 := by
  unfold tailWord_3992366
  simp only [CollatzResearch.WordTrace]
  refine ⟨18201693831793412334213619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97075700436231532449139301 18201693831793412334213619)
  ·
    refine ⟨27302540747690118501320429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18201693831793412334213619 27302540747690118501320429)
    ·
      refine ⟨10238452780383794437995161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27302540747690118501320429 10238452780383794437995161)
      ·
        refine ⟨7678839585287845828496371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10238452780383794437995161 7678839585287845828496371)
        ·
          refine ⟨11518259377931768742744557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7678839585287845828496371 11518259377931768742744557)
          ·
            refine ⟨4319347266724413278529209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11518259377931768742744557 4319347266724413278529209)
            ·
              refine ⟨3239510450043309958896907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4319347266724413278529209 3239510450043309958896907)
              ·
                refine ⟨4859265675064964938345361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3239510450043309958896907 4859265675064964938345361)
                ·
                  refine ⟨3644449256298723703759021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4859265675064964938345361 3644449256298723703759021)
                  ·
                    refine ⟨1366668471112021388909633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3644449256298723703759021 1366668471112021388909633)
                    ·
                      rfl

theorem cell22_3992366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_3992366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3992366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3992366 prefixEnd_3992366 := by exact prefixLift 3992366
  have htrace : WordTrace (prefixWord ++ tailWord_3992366) baseStart_3992366 baseEnd_3992366 := by
    simpa [prefixWord, tailWord_3992366, baseEnd_3992366] using wordTrace_append hprefix tailTrace_3992366
  have hstable : (prefixWord ++ tailWord_3992366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992366).length < 2 ^ (prefixWord ++ tailWord_3992366).sum := by decide
  have hdescent : baseEnd_3992366 < baseStart_3992366 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992420 : List Nat := [2, 3, 1, 1, 4, 1, 1, 2, 3, 4]
def baseStart_3992420 : Nat := 118140960795 + 3992420 * 2 ^ 59
def prefixEnd_3992420 : Nat := 4983230072969 + 3 ^ 40 * 3992420 * 2
def baseEnd_3992420 : Nat := 1366686956415583248059467

theorem tailTrace_3992420 : CollatzResearch.WordTrace tailWord_3992420 prefixEnd_3992420 1366686956415583248059467 := by
  unfold tailWord_3992420
  simp only [CollatzResearch.WordTrace]
  refine ⟨72807760098075832948087357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97077013464101110597449809 72807760098075832948087357)
  ·
    refine ⟨27302910036778437355532759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72807760098075832948087357 27302910036778437355532759)
    ·
      refine ⟨40954365055167656033299139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27302910036778437355532759 40954365055167656033299139)
      ·
        refine ⟨61431547582751484049948709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40954365055167656033299139 61431547582751484049948709)
        ·
          refine ⟨11518415171765903259365383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61431547582751484049948709 11518415171765903259365383)
          ·
            refine ⟨17277622757648854889048075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11518415171765903259365383 17277622757648854889048075)
            ·
              refine ⟨25916434136473282333572113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17277622757648854889048075 25916434136473282333572113)
              ·
                refine ⟨19437325602354961750179085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25916434136473282333572113 19437325602354961750179085)
                ·
                  refine ⟨7288997100883110656317157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19437325602354961750179085 7288997100883110656317157)
                  ·
                    refine ⟨1366686956415583248059467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7288997100883110656317157 1366686956415583248059467)
                    ·
                      rfl

theorem cell22_3992420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 3, 4].length) (baseStart_3992420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3992420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3992420 prefixEnd_3992420 := by exact prefixLift 3992420
  have htrace : WordTrace (prefixWord ++ tailWord_3992420) baseStart_3992420 baseEnd_3992420 := by
    simpa [prefixWord, tailWord_3992420, baseEnd_3992420] using wordTrace_append hprefix tailTrace_3992420
  have hstable : (prefixWord ++ tailWord_3992420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992420).length < 2 ^ (prefixWord ++ tailWord_3992420).sum := by decide
  have hdescent : baseEnd_3992420 < baseStart_3992420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992484 : List Nat := [2, 3, 1, 2, 1, 2, 5, 1, 2, 3]
def baseStart_3992484 : Nat := 118140960795 + 3992484 * 2 ^ 59
def prefixEnd_3992484 : Nat := 4983230072969 + 3 ^ 40 * 3992484 * 2
def baseEnd_3992484 : Nat := 1366708864923508414459271

theorem tailTrace_3992484 : CollatzResearch.WordTrace tailWord_3992484 prefixEnd_3992484 1366708864923508414459271 := by
  unfold tailWord_3992484
  simp only [CollatzResearch.WordTrace]
  refine ⟨72808927233959902413252253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97078569645279869884336337 72808927233959902413252253)
  ·
    refine ⟨27303347712734963404969595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72808927233959902413252253 27303347712734963404969595)
    ·
      refine ⟨40955021569102445107454393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27303347712734963404969595 40955021569102445107454393)
      ·
        refine ⟨30716266176826833830590795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40955021569102445107454393 30716266176826833830590795)
        ·
          refine ⟨46074399265240250745886193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30716266176826833830590795 46074399265240250745886193)
          ·
            refine ⟨34555799448930188059414645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46074399265240250745886193 34555799448930188059414645)
            ·
              refine ⟨3239606198337205130570123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34555799448930188059414645 3239606198337205130570123)
              ·
                refine ⟨4859409297505807695855185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3239606198337205130570123 4859409297505807695855185)
                ·
                  refine ⟨3644556973129355771891389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4859409297505807695855185 3644556973129355771891389)
                  ·
                    refine ⟨1366708864923508414459271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3644556973129355771891389 1366708864923508414459271)
                    ·
                      rfl

theorem cell22_3992484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 5, 1, 2, 3].length) (baseStart_3992484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3992484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3992484 prefixEnd_3992484 := by exact prefixLift 3992484
  have htrace : WordTrace (prefixWord ++ tailWord_3992484) baseStart_3992484 baseEnd_3992484 := by
    simpa [prefixWord, tailWord_3992484, baseEnd_3992484] using wordTrace_append hprefix tailTrace_3992484
  have hstable : (prefixWord ++ tailWord_3992484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992484).length < 2 ^ (prefixWord ++ tailWord_3992484).sum := by decide
  have hdescent : baseEnd_3992484 < baseStart_3992484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992495 : List Nat := [1, 1, 2, 1, 2, 2, 2, 3, 5, 3]
def baseStart_3992495 : Nat := 118140960795 + 3992495 * 2 ^ 59
def prefixEnd_3992495 : Nat := 4983230072969 + 3 ^ 40 * 3992495 * 2
def baseEnd_3992495 : Nat := 1366712630448308052434237

theorem tailTrace_3992495 : CollatzResearch.WordTrace tailWord_3992495 prefixEnd_3992495 1366712630448308052434237 := by
  unfold tailWord_3992495
  simp only [CollatzResearch.WordTrace]
  refine ⟨145618255670879953705154939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97078837113919969136769959 145618255670879953705154939)
  ·
    refine ⟨218427383506319930557732409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145618255670879953705154939 218427383506319930557732409)
    ·
      refine ⟨163820537629739947918299307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218427383506319930557732409 163820537629739947918299307)
      ·
        refine ⟨245730806444609921877448961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163820537629739947918299307 245730806444609921877448961)
        ·
          refine ⟨184298104833457441408086721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245730806444609921877448961 184298104833457441408086721)
          ·
            refine ⟨138223578625093081056065041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184298104833457441408086721 138223578625093081056065041)
            ·
              refine ⟨103667683968819810792048781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138223578625093081056065041 103667683968819810792048781)
              ·
                refine ⟨38875381488307429047018293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103667683968819810792048781 38875381488307429047018293)
                ·
                  refine ⟨3644567014528821473157965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38875381488307429047018293 3644567014528821473157965)
                  ·
                    refine ⟨1366712630448308052434237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3644567014528821473157965 1366712630448308052434237)
                    ·
                      rfl

theorem cell22_3992495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 5, 3].length) (baseStart_3992495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3992495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3992495 prefixEnd_3992495 := by exact prefixLift 3992495
  have htrace : WordTrace (prefixWord ++ tailWord_3992495) baseStart_3992495 baseEnd_3992495 := by
    simpa [prefixWord, tailWord_3992495, baseEnd_3992495] using wordTrace_append hprefix tailTrace_3992495
  have hstable : (prefixWord ++ tailWord_3992495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992495).length < 2 ^ (prefixWord ++ tailWord_3992495).sum := by decide
  have hdescent : baseEnd_3992495 < baseStart_3992495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992602 : List Nat := [3, 1, 1, 3, 1, 2, 4, 1, 1, 5]
def baseStart_3992602 : Nat := 118140960795 + 3992602 * 2 ^ 59
def prefixEnd_3992602 : Nat := 4983230072969 + 3 ^ 40 * 3992602 * 2
def baseEnd_3992602 : Nat := 1366749258734995440008909

theorem tailTrace_3992602 : CollatzResearch.WordTrace tailWord_3992602 prefixEnd_3992602 1366749258734995440008909 := by
  unfold tailWord_3992602
  simp only [CollatzResearch.WordTrace]
  refine ⟨36405539570373077744825015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97081438854328207319533373 36405539570373077744825015)
  ·
    refine ⟨54608309355559616617237523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36405539570373077744825015 54608309355559616617237523)
    ·
      refine ⟨81912464033339424925856285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54608309355559616617237523 81912464033339424925856285)
      ·
        refine ⟨30717174012502284347196107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81912464033339424925856285 30717174012502284347196107)
        ·
          refine ⟨46075761018753426520794161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30717174012502284347196107 46075761018753426520794161)
          ·
            refine ⟨34556820764065069890595621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46075761018753426520794161 34556820764065069890595621)
            ·
              refine ⟨6479403893262200604486679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34556820764065069890595621 6479403893262200604486679)
              ·
                refine ⟨9719105839893300906730019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6479403893262200604486679 9719105839893300906730019)
                ·
                  refine ⟨14578658759839951360095029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9719105839893300906730019 14578658759839951360095029)
                  ·
                    refine ⟨1366749258734995440008909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14578658759839951360095029 1366749258734995440008909)
                    ·
                      rfl

theorem cell22_3992602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 1, 1, 5].length) (baseStart_3992602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3992602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3992602 prefixEnd_3992602 := by exact prefixLift 3992602
  have htrace : WordTrace (prefixWord ++ tailWord_3992602) baseStart_3992602 baseEnd_3992602 := by
    simpa [prefixWord, tailWord_3992602, baseEnd_3992602] using wordTrace_append hprefix tailTrace_3992602
  have hstable : (prefixWord ++ tailWord_3992602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992602).length < 2 ^ (prefixWord ++ tailWord_3992602).sum := by decide
  have hdescent : baseEnd_3992602 < baseStart_3992602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992636 : List Nat := [2, 2, 2, 2, 2, 4, 1, 2, 2, 3]
def baseStart_3992636 : Nat := 118140960795 + 3992636 * 2 ^ 59
def prefixEnd_3992636 : Nat := 4983230072969 + 3 ^ 40 * 3992636 * 2
def baseEnd_3992636 : Nat := 1366760897629830684658805

theorem tailTrace_3992636 : CollatzResearch.WordTrace tailWord_3992636 prefixEnd_3992636 1366760897629830684658805 := by
  unfold tailWord_3992636
  simp only [CollatzResearch.WordTrace]
  refine ⟨72811699181684567393018881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97082265575579423190691841 72811699181684567393018881)
  ·
    refine ⟨54608774386263425544764161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72811699181684567393018881 54608774386263425544764161)
    ·
      refine ⟨40956580789697569158573121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54608774386263425544764161 40956580789697569158573121)
      ·
        refine ⟨30717435592273176868929841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40956580789697569158573121 30717435592273176868929841)
        ·
          refine ⟨23038076694204882651697381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30717435592273176868929841 23038076694204882651697381)
          ·
            refine ⟨4319639380163415497193259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23038076694204882651697381 4319639380163415497193259)
            ·
              refine ⟨6479459070245123245789889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4319639380163415497193259 6479459070245123245789889)
              ·
                refine ⟨4859594302683842434342417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6479459070245123245789889 4859594302683842434342417)
                ·
                  refine ⟨3644695727012881825756813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4859594302683842434342417 3644695727012881825756813)
                  ·
                    refine ⟨1366760897629830684658805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3644695727012881825756813 1366760897629830684658805)
                    ·
                      rfl

theorem cell22_3992636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 2, 2, 3].length) (baseStart_3992636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3992636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3992636 prefixEnd_3992636 := by exact prefixLift 3992636
  have htrace : WordTrace (prefixWord ++ tailWord_3992636) baseStart_3992636 baseEnd_3992636 := by
    simpa [prefixWord, tailWord_3992636, baseEnd_3992636] using wordTrace_append hprefix tailTrace_3992636
  have hstable : (prefixWord ++ tailWord_3992636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992636).length < 2 ^ (prefixWord ++ tailWord_3992636).sum := by decide
  have hdescent : baseEnd_3992636 < baseStart_3992636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992645 : List Nat := [1, 3, 1, 1, 1, 3, 2, 1, 1, 8]
def baseStart_3992645 : Nat := 118140960795 + 3992645 * 2 ^ 59
def prefixEnd_3992645 : Nat := 4983230072969 + 3 ^ 40 * 3992645 * 2
def baseEnd_3992645 : Nat := 1366763978513757661183777

theorem tailTrace_3992645 : CollatzResearch.WordTrace tailWord_3992645 prefixEnd_3992645 1366763978513757661183777 := by
  unfold tailWord_3992645
  simp only [CollatzResearch.WordTrace]
  refine ⟨145623726620336529323115389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97082484413557686215410259 145623726620336529323115389)
  ·
    refine ⟨54608897482626198496168271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145623726620336529323115389 54608897482626198496168271)
    ·
      refine ⟨81913346223939297744252407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54608897482626198496168271 81913346223939297744252407)
      ·
        refine ⟨122870019335908946616378611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81913346223939297744252407 122870019335908946616378611)
        ·
          refine ⟨184305029003863419924567917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122870019335908946616378611 184305029003863419924567917)
          ·
            refine ⟨69114385876448782471712969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184305029003863419924567917 69114385876448782471712969)
            ·
              refine ⟨51835789407336586853784727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69114385876448782471712969 51835789407336586853784727)
              ·
                refine ⟨77753684111004880280677091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51835789407336586853784727 77753684111004880280677091)
                ·
                  refine ⟨116630526166507320421015637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77753684111004880280677091 116630526166507320421015637)
                  ·
                    refine ⟨1366763978513757661183777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 116630526166507320421015637 1366763978513757661183777)
                    ·
                      rfl

theorem cell22_3992645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 8].length) (baseStart_3992645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3992645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3992645 prefixEnd_3992645 := by exact prefixLift 3992645
  have htrace : WordTrace (prefixWord ++ tailWord_3992645) baseStart_3992645 baseEnd_3992645 := by
    simpa [prefixWord, tailWord_3992645, baseEnd_3992645] using wordTrace_append hprefix tailTrace_3992645
  have hstable : (prefixWord ++ tailWord_3992645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992645).length < 2 ^ (prefixWord ++ tailWord_3992645).sum := by decide
  have hdescent : baseEnd_3992645 < baseStart_3992645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992653 : List Nat := [1, 6, 1, 1, 1, 3, 3, 1, 2, 3]
def baseStart_3992653 : Nat := 118140960795 + 3992653 * 2 ^ 59
def prefixEnd_3992653 : Nat := 4983230072969 + 3 ^ 40 * 3992653 * 2
def baseEnd_3992653 : Nat := 1366766717077248306983753

theorem tailTrace_3992653 : CollatzResearch.WordTrace tailWord_3992653 prefixEnd_3992653 1366766717077248306983753 := by
  unfold tailWord_3992653
  simp only [CollatzResearch.WordTrace]
  refine ⟨145624018404307546689406613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97082678936205031126271075 145624018404307546689406613)
  ·
    refine ⟨6826125862701916251065935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 145624018404307546689406613 6826125862701916251065935)
    ·
      refine ⟨10239188794052874376598903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6826125862701916251065935 10239188794052874376598903)
      ·
        refine ⟨15358783191079311564898355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10239188794052874376598903 15358783191079311564898355)
        ·
          refine ⟨23038174786618967347347533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15358783191079311564898355 23038174786618967347347533)
          ·
            refine ⟨8639315544982112755255325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23038174786618967347347533 8639315544982112755255325)
            ·
              refine ⟨3239743329368292283220747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8639315544982112755255325 3239743329368292283220747)
              ·
                refine ⟨4859614994052438424831121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3239743329368292283220747 4859614994052438424831121)
                ·
                  refine ⟨3644711245539328818623341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4859614994052438424831121 3644711245539328818623341)
                  ·
                    refine ⟨1366766717077248306983753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3644711245539328818623341 1366766717077248306983753)
                    ·
                      rfl

theorem cell22_3992653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_3992653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3992653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3992653 prefixEnd_3992653 := by exact prefixLift 3992653
  have htrace : WordTrace (prefixWord ++ tailWord_3992653) baseStart_3992653 baseEnd_3992653 := by
    simpa [prefixWord, tailWord_3992653, baseEnd_3992653] using wordTrace_append hprefix tailTrace_3992653
  have hstable : (prefixWord ++ tailWord_3992653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992653).length < 2 ^ (prefixWord ++ tailWord_3992653).sum := by decide
  have hdescent : baseEnd_3992653 < baseStart_3992653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
