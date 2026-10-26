import V185TrunkScan20Chunk133

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_813892 : List Nat := [2, 3, 4, 2, 1, 1, 1, 3, 3]
def baseStart_813892 : Nat := 118140960795 + 813892 * 2 ^ 59
def prefixEnd_813892 : Nat := 4983230072969 + 3 ^ 40 * 813892 * 2
def baseEnd_813892 : Nat := 371482486088208780006209

theorem tailTrace_813892 : CollatzResearch.WordTrace tailWord_813892 prefixEnd_813892 371482486088208780006209 := by
  unfold tailWord_813892
  simp only [CollatzResearch.WordTrace]
  refine ⟨14842539983707880266109965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19790053311610507021479953 14842539983707880266109965)
  ·
    refine ⟨5565952493890455099791237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14842539983707880266109965 5565952493890455099791237)
    ·
      refine ⟨1043616092604460331210857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5565952493890455099791237 1043616092604460331210857)
      ·
        refine ⟨782712069453345248408143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1043616092604460331210857 782712069453345248408143)
        ·
          refine ⟨1174068104180017872612215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 782712069453345248408143 1174068104180017872612215)
          ·
            refine ⟨1761102156270026808918323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1174068104180017872612215 1761102156270026808918323)
            ·
              refine ⟨2641653234405040213377485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1761102156270026808918323 2641653234405040213377485)
              ·
                refine ⟨990619962901890080016557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2641653234405040213377485 990619962901890080016557)
                ·
                  refine ⟨371482486088208780006209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 990619962901890080016557 371482486088208780006209)
                  ·
                    rfl

theorem cell20_813892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 3, 3].length) (baseStart_813892 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_813892 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_813892 prefixEnd_813892 := by exact prefixLift 813892
  have htrace : WordTrace (prefixWord ++ tailWord_813892) baseStart_813892 baseEnd_813892 := by
    simpa [prefixWord, tailWord_813892, baseEnd_813892] using wordTrace_append hprefix tailTrace_813892
  have hstable : (prefixWord ++ tailWord_813892).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813892).length < 2 ^ (prefixWord ++ tailWord_813892).sum := by decide
  have hdescent : baseEnd_813892 < baseStart_813892 := by decide
  rcases family_descends (prefixWord ++ tailWord_813892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813937 : List Nat := [1, 2, 2, 2, 1, 6, 2, 2, 2]
def baseStart_813937 : Nat := 118140960795 + 813937 * 2 ^ 59
def prefixEnd_813937 : Nat := 4983230072969 + 3 ^ 40 * 813937 * 2
def baseEnd_813937 : Nat := 371503025314388623506025

theorem tailTrace_813937 : CollatzResearch.WordTrace tailWord_813937 prefixEnd_813937 371503025314388623506025 := by
  unfold tailWord_813937
  simp only [CollatzResearch.WordTrace]
  refine ⟨29686721252252733217608065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19791147501501822145072043 29686721252252733217608065)
  ·
    refine ⟨22265040939189549913206049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29686721252252733217608065 22265040939189549913206049)
    ·
      refine ⟨16698780704392162434904537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22265040939189549913206049 16698780704392162434904537)
      ·
        refine ⟨12524085528294121826178403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16698780704392162434904537 12524085528294121826178403)
        ·
          refine ⟨18786128292441182739267605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12524085528294121826178403 18786128292441182739267605)
          ·
            refine ⟨880599763708180440903169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 18786128292441182739267605 880599763708180440903169)
            ·
              refine ⟨660449822781135330677377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 880599763708180440903169 660449822781135330677377)
              ·
                refine ⟨495337367085851498008033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 660449822781135330677377 495337367085851498008033)
                ·
                  refine ⟨371503025314388623506025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 495337367085851498008033 371503025314388623506025)
                  ·
                    rfl

theorem cell20_813937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 2, 2, 2].length) (baseStart_813937 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_813937 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_813937 prefixEnd_813937 := by exact prefixLift 813937
  have htrace : WordTrace (prefixWord ++ tailWord_813937) baseStart_813937 baseEnd_813937 := by
    simpa [prefixWord, tailWord_813937, baseEnd_813937] using wordTrace_append hprefix tailTrace_813937
  have hstable : (prefixWord ++ tailWord_813937).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813937).length < 2 ^ (prefixWord ++ tailWord_813937).sum := by decide
  have hdescent : baseEnd_813937 < baseStart_813937 := by decide
  rcases family_descends (prefixWord ++ tailWord_813937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813955 : List Nat := [1, 1, 1, 3, 4, 1, 1, 5, 3]
def baseStart_813955 : Nat := 118140960795 + 813955 * 2 ^ 59
def prefixEnd_813955 : Nat := 4983230072969 + 3 ^ 40 * 813955 * 2
def baseEnd_813955 : Nat := 371511241004860560905951

theorem tailTrace_813955 : CollatzResearch.WordTrace tailWord_813955 prefixEnd_813955 371511241004860560905951 := by
  unfold tailWord_813955
  simp only [CollatzResearch.WordTrace]
  refine ⟨29687377766187522291763319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19791585177458348194508879 29687377766187522291763319)
  ·
    refine ⟨44531066649281283437644979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29687377766187522291763319 44531066649281283437644979)
    ·
      refine ⟨66796599973921925156467469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44531066649281283437644979 66796599973921925156467469)
      ·
        refine ⟨25048724990220721933675301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66796599973921925156467469 25048724990220721933675301)
        ·
          refine ⟨4696635935666385362564119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25048724990220721933675301 4696635935666385362564119)
          ·
            refine ⟨7044953903499578043846179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4696635935666385362564119 7044953903499578043846179)
            ·
              refine ⟨10567430855249367065769269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7044953903499578043846179 10567430855249367065769269)
              ·
                refine ⟨990696642679628162415869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10567430855249367065769269 990696642679628162415869)
                ·
                  refine ⟨371511241004860560905951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 990696642679628162415869 371511241004860560905951)
                  ·
                    rfl

theorem cell20_813955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 5, 3].length) (baseStart_813955 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_813955 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_813955 prefixEnd_813955 := by exact prefixLift 813955
  have htrace : WordTrace (prefixWord ++ tailWord_813955) baseStart_813955 baseEnd_813955 := by
    simpa [prefixWord, tailWord_813955, baseEnd_813955] using wordTrace_append hprefix tailTrace_813955
  have hstable : (prefixWord ++ tailWord_813955).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813955).length < 2 ^ (prefixWord ++ tailWord_813955).sum := by decide
  have hdescent : baseEnd_813955 < baseStart_813955 := by decide
  rcases family_descends (prefixWord ++ tailWord_813955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_813986 : List Nat := [3, 3, 1, 2, 2, 2, 7]
def baseStart_813986 : Nat := 118140960795 + 813986 * 2 ^ 59
def prefixEnd_813986 : Nat := 4983230072969 + 3 ^ 40 * 813986 * 2
def baseEnd_813986 : Nat := 41280598916618025652499

theorem tailTrace_813986 : CollatzResearch.WordTrace tailWord_813986 prefixEnd_813986 41280598916618025652499 := by
  unfold tailWord_813986
  simp only [CollatzResearch.WordTrace]
  refine ⟨7422127107268803646535453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19792338952716809724094541 7422127107268803646535453)
  ·
    refine ⟨2783297665225801367450795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7422127107268803646535453 2783297665225801367450795)
    ·
      refine ⟨4174946497838702051176193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2783297665225801367450795 4174946497838702051176193)
      ·
        refine ⟨3131209873379026538382145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4174946497838702051176193 3131209873379026538382145)
        ·
          refine ⟨2348407405034269903786609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3131209873379026538382145 2348407405034269903786609)
          ·
            refine ⟨1761305553775702427839957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2348407405034269903786609 1761305553775702427839957)
            ·
              refine ⟨41280598916618025652499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1761305553775702427839957 41280598916618025652499)
              ·
                rfl

theorem cell20_813986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 7].length) (baseStart_813986 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_813986 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_813986 prefixEnd_813986 := by exact prefixLift 813986
  have htrace : WordTrace (prefixWord ++ tailWord_813986) baseStart_813986 baseEnd_813986 := by
    simpa [prefixWord, tailWord_813986, baseEnd_813986] using wordTrace_append hprefix tailTrace_813986
  have hstable : (prefixWord ++ tailWord_813986).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_813986).length < 2 ^ (prefixWord ++ tailWord_813986).sum := by decide
  have hdescent : baseEnd_813986 < baseStart_813986 := by decide
  rcases family_descends (prefixWord ++ tailWord_813986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814010 : List Nat := [3, 1, 1, 1, 2, 1, 7, 1, 3]
def baseStart_814010 : Nat := 118140960795 + 814010 * 2 ^ 59
def prefixEnd_814010 : Nat := 4983230072969 + 3 ^ 40 * 814010 * 2
def baseEnd_814010 : Nat := 371536344503524814072393

theorem tailTrace_814010 : CollatzResearch.WordTrace tailWord_814010 prefixEnd_814010 371536344503524814072393 := by
  unfold tailWord_814010
  simp only [CollatzResearch.WordTrace]
  refine ⟨7422345945247066671253871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19792922520658844456676989 7422345945247066671253871)
  ·
    refine ⟨11133518917870600006880807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7422345945247066671253871 11133518917870600006880807)
    ·
      refine ⟨16700278376805900010321211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11133518917870600006880807 16700278376805900010321211)
      ·
        refine ⟨25050417565208850015481817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16700278376805900010321211 25050417565208850015481817)
        ·
          refine ⟨18787813173906637511611363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25050417565208850015481817 18787813173906637511611363)
          ·
            refine ⟨28181719760859956267417045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18787813173906637511611363 28181719760859956267417045)
            ·
              refine ⟨660509056895155225017587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 28181719760859956267417045 660509056895155225017587)
              ·
                refine ⟨990763585342732837526381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 660509056895155225017587 990763585342732837526381)
                ·
                  refine ⟨371536344503524814072393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 990763585342732837526381 371536344503524814072393)
                  ·
                    rfl

theorem cell20_814010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 7, 1, 3].length) (baseStart_814010 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_814010 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_814010 prefixEnd_814010 := by exact prefixLift 814010
  have htrace : WordTrace (prefixWord ++ tailWord_814010) baseStart_814010 baseEnd_814010 := by
    simpa [prefixWord, tailWord_814010, baseEnd_814010] using wordTrace_append hprefix tailTrace_814010
  have hstable : (prefixWord ++ tailWord_814010).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814010).length < 2 ^ (prefixWord ++ tailWord_814010).sum := by decide
  have hdescent : baseEnd_814010 < baseStart_814010 := by decide
  rcases family_descends (prefixWord ++ tailWord_814010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814024 : List Nat := [2, 1, 3, 1, 5, 1, 1, 6]
def baseStart_814024 : Nat := 118140960795 + 814024 * 2 ^ 59
def prefixEnd_814024 : Nat := 4983230072969 + 3 ^ 40 * 814024 * 2
def baseEnd_814024 : Nat := 123847578161667662535223

theorem tailTrace_814024 : CollatzResearch.WordTrace tailWord_814024 prefixEnd_814024 123847578161667662535223 := by
  unfold tailWord_814024
  simp only [CollatzResearch.WordTrace]
  refine ⟨14844947201468773538012563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19793262935291698050683417 14844947201468773538012563)
  ·
    refine ⟨22267420802203160307018845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14844947201468773538012563 22267420802203160307018845)
    ·
      refine ⟨8350282800826185115132067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22267420802203160307018845 8350282800826185115132067)
      ·
        refine ⟨12525424201239277672698101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8350282800826185115132067 12525424201239277672698101)
        ·
          refine ⟨1174258518866182281815447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12525424201239277672698101 1174258518866182281815447)
          ·
            refine ⟨1761387778299273422723171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1174258518866182281815447 1761387778299273422723171)
            ·
              refine ⟨2642081667448910134084757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1761387778299273422723171 2642081667448910134084757)
              ·
                refine ⟨123847578161667662535223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2642081667448910134084757 123847578161667662535223)
                ·
                  rfl

theorem cell20_814024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 6].length) (baseStart_814024 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_814024 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_814024 prefixEnd_814024 := by exact prefixLift 814024
  have htrace : WordTrace (prefixWord ++ tailWord_814024) baseStart_814024 baseEnd_814024 := by
    simpa [prefixWord, tailWord_814024, baseEnd_814024] using wordTrace_append hprefix tailTrace_814024
  have hstable : (prefixWord ++ tailWord_814024).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814024).length < 2 ^ (prefixWord ++ tailWord_814024).sum := by decide
  have hdescent : baseEnd_814024 < baseStart_814024 := by decide
  rcases family_descends (prefixWord ++ tailWord_814024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814055 : List Nat := [1, 1, 5, 2, 2, 1, 3, 1, 4]
def baseStart_814055 : Nat := 118140960795 + 814055 * 2 ^ 59
def prefixEnd_814055 : Nat := 4983230072969 + 3 ^ 40 * 814055 * 2
def baseEnd_814055 : Nat := 371556883729704657572209

theorem tailTrace_814055 : CollatzResearch.WordTrace tailWord_814055 prefixEnd_814055 371556883729704657572209 := by
  unfold tailWord_814055
  simp only [CollatzResearch.WordTrace]
  refine ⟨29691025065825239370403619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19794016710550159580269079 29691025065825239370403619)
  ·
    refine ⟨44536537598737859055605429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29691025065825239370403619 44536537598737859055605429)
    ·
      refine ⟨4175300399881674286463009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44536537598737859055605429 4175300399881674286463009)
      ·
        refine ⟨3131475299911255714847257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4175300399881674286463009 3131475299911255714847257)
        ·
          refine ⟨2348606474933441786135443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3131475299911255714847257 2348606474933441786135443)
          ·
            refine ⟨3522909712400162679203165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2348606474933441786135443 3522909712400162679203165)
            ·
              refine ⟨1321091142150061004701187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3522909712400162679203165 1321091142150061004701187)
              ·
                refine ⟨1981636713225091507051781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1321091142150061004701187 1981636713225091507051781)
                ·
                  refine ⟨371556883729704657572209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1981636713225091507051781 371556883729704657572209)
                  ·
                    rfl

theorem cell20_814055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 1, 4].length) (baseStart_814055 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_814055 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_814055 prefixEnd_814055 := by exact prefixLift 814055
  have htrace : WordTrace (prefixWord ++ tailWord_814055) baseStart_814055 baseEnd_814055 := by
    simpa [prefixWord, tailWord_814055, baseEnd_814055] using wordTrace_append hprefix tailTrace_814055
  have hstable : (prefixWord ++ tailWord_814055).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814055).length < 2 ^ (prefixWord ++ tailWord_814055).sum := by decide
  have hdescent : baseEnd_814055 < baseStart_814055 := by decide
  rcases family_descends (prefixWord ++ tailWord_814055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814065 : List Nat := [1, 2, 2, 2, 4, 3, 2, 1, 3]
def baseStart_814065 : Nat := 118140960795 + 814065 * 2 ^ 59
def prefixEnd_814065 : Nat := 4983230072969 + 3 ^ 40 * 814065 * 2
def baseEnd_814065 : Nat := 371561448002189067238835

theorem tailTrace_814065 : CollatzResearch.WordTrace tailWord_814065 prefixEnd_814065 371561448002189067238835 := by
  unfold tailWord_814065
  simp only [CollatzResearch.WordTrace]
  refine ⟨29691389795789011078267649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19794259863859340718845099 29691389795789011078267649)
  ·
    refine ⟨22268542346841758308700737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29691389795789011078267649 22268542346841758308700737)
    ·
      refine ⟨16701406760131318731525553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22268542346841758308700737 16701406760131318731525553)
      ·
        refine ⟨12526055070098489048644165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16701406760131318731525553 12526055070098489048644165)
        ·
          refine ⟨2348635325643466696620781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12526055070098489048644165 2348635325643466696620781)
          ·
            refine ⟨880738247116300011232793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2348635325643466696620781 880738247116300011232793)
            ·
              refine ⟨660553685337225008424595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 880738247116300011232793 660553685337225008424595)
              ·
                refine ⟨990830528005837512636893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 660553685337225008424595 990830528005837512636893)
                ·
                  refine ⟨371561448002189067238835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 990830528005837512636893 371561448002189067238835)
                  ·
                    rfl

theorem cell20_814065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 2, 1, 3].length) (baseStart_814065 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_814065 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_814065 prefixEnd_814065 := by exact prefixLift 814065
  have htrace : WordTrace (prefixWord ++ tailWord_814065) baseStart_814065 baseEnd_814065 := by
    simpa [prefixWord, tailWord_814065, baseEnd_814065] using wordTrace_append hprefix tailTrace_814065
  have hstable : (prefixWord ++ tailWord_814065).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814065).length < 2 ^ (prefixWord ++ tailWord_814065).sum := by decide
  have hdescent : baseEnd_814065 < baseStart_814065 := by decide
  rcases family_descends (prefixWord ++ tailWord_814065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814162 : List Nat := [3, 2, 2, 1, 3, 1, 3, 2, 3]
def baseStart_814162 : Nat := 118140960795 + 814162 * 2 ^ 59
def prefixEnd_814162 : Nat := 4983230072969 + 3 ^ 40 * 814162 * 2
def baseEnd_814162 : Nat := 371605721445287841005105

theorem tailTrace_814162 : CollatzResearch.WordTrace tailWord_814162 prefixEnd_814162 371605721445287841005105 := by
  unfold tailWord_814162
  simp only [CollatzResearch.WordTrace]
  refine ⟨7423731919109399161137185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19796618450958397763032493 7423731919109399161137185)
  ·
    refine ⟨5567798939332049370852889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7423731919109399161137185 5567798939332049370852889)
    ·
      refine ⟨4175849204499037028139667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5567798939332049370852889 4175849204499037028139667)
      ·
        refine ⟨6263773806748555542209501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4175849204499037028139667 6263773806748555542209501)
        ·
          refine ⟨2348915177530708328328563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6263773806748555542209501 2348915177530708328328563)
          ·
            refine ⟨3523372766296062492492845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2348915177530708328328563 3523372766296062492492845)
            ·
              refine ⟨1321264787361023434684817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3523372766296062492492845 1321264787361023434684817)
              ·
                refine ⟨990948590520767576013613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1321264787361023434684817 990948590520767576013613)
                ·
                  refine ⟨371605721445287841005105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 990948590520767576013613 371605721445287841005105)
                  ·
                    rfl

theorem cell20_814162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 2, 3].length) (baseStart_814162 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_814162 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_814162 prefixEnd_814162 := by exact prefixLift 814162
  have htrace : WordTrace (prefixWord ++ tailWord_814162) baseStart_814162 baseEnd_814162 := by
    simpa [prefixWord, tailWord_814162, baseEnd_814162] using wordTrace_append hprefix tailTrace_814162
  have hstable : (prefixWord ++ tailWord_814162).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814162).length < 2 ^ (prefixWord ++ tailWord_814162).sum := by decide
  have hdescent : baseEnd_814162 < baseStart_814162 := by decide
  rcases family_descends (prefixWord ++ tailWord_814162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814204 : List Nat := [2, 2, 2, 1, 1, 3, 1, 1, 7]
def baseStart_814204 : Nat := 118140960795 + 814204 * 2 ^ 59
def prefixEnd_814204 : Nat := 4983230072969 + 3 ^ 40 * 814204 * 2
def baseEnd_814204 : Nat := 371624891389722361604933

theorem tailTrace_814204 : CollatzResearch.WordTrace tailWord_814204 prefixEnd_814204 371624891389722361604933 := by
  unfold tailWord_814204
  simp only [CollatzResearch.WordTrace]
  refine ⟨14848229771142718908788833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19797639694856958545051777 14848229771142718908788833)
  ·
    refine ⟨11136172328357039181591625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14848229771142718908788833 11136172328357039181591625)
    ·
      refine ⟨8352129246267779386193719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11136172328357039181591625 8352129246267779386193719)
      ·
        refine ⟨12528193869401669079290579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8352129246267779386193719 12528193869401669079290579)
        ·
          refine ⟨18792290804102503618935869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12528193869401669079290579 18792290804102503618935869)
          ·
            refine ⟨7047109051538438857100951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18792290804102503618935869 7047109051538438857100951)
            ·
              refine ⟨10570663577307658285651427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7047109051538438857100951 10570663577307658285651427)
              ·
                refine ⟨15855995365961487428477141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10570663577307658285651427 15855995365961487428477141)
                ·
                  refine ⟨371624891389722361604933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15855995365961487428477141 371624891389722361604933)
                  ·
                    rfl

theorem cell20_814204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_814204 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_814204 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_814204 prefixEnd_814204 := by exact prefixLift 814204
  have htrace : WordTrace (prefixWord ++ tailWord_814204) baseStart_814204 baseEnd_814204 := by
    simpa [prefixWord, tailWord_814204, baseEnd_814204] using wordTrace_append hprefix tailTrace_814204
  have hstable : (prefixWord ++ tailWord_814204).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814204).length < 2 ^ (prefixWord ++ tailWord_814204).sum := by decide
  have hdescent : baseEnd_814204 < baseStart_814204 := by decide
  rcases family_descends (prefixWord ++ tailWord_814204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814280 : List Nat := [2, 1, 3, 1, 2, 1, 2, 3, 5]
def baseStart_814280 : Nat := 118140960795 + 814280 * 2 ^ 59
def prefixEnd_814280 : Nat := 4983230072969 + 3 ^ 40 * 814280 * 2
def baseEnd_814280 : Nat := 371659579860603875071289

theorem tailTrace_814280 : CollatzResearch.WordTrace tailWord_814280 prefixEnd_814280 371659579860603875071289 := by
  unfold tailWord_814280
  simp only [CollatzResearch.WordTrace]
  refine ⟨14849615745005051398672147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19799487660006735198229529 14849615745005051398672147)
  ·
    refine ⟨22274423617507577098008221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14849615745005051398672147 22274423617507577098008221)
    ·
      refine ⟨8352908856565341411753083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22274423617507577098008221 8352908856565341411753083)
      ·
        refine ⟨12529363284848012117629625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8352908856565341411753083 12529363284848012117629625)
        ·
          refine ⟨9397022463636009088222219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12529363284848012117629625 9397022463636009088222219)
          ·
            refine ⟨14095533695454013632333329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9397022463636009088222219 14095533695454013632333329)
            ·
              refine ⟨10571650271590510224249997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14095533695454013632333329 10571650271590510224249997)
              ·
                refine ⟨3964368851846441334093749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10571650271590510224249997 3964368851846441334093749)
                ·
                  refine ⟨371659579860603875071289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3964368851846441334093749 371659579860603875071289)
                  ·
                    rfl

theorem cell20_814280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 5].length) (baseStart_814280 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_814280 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_814280 prefixEnd_814280 := by exact prefixLift 814280
  have htrace : WordTrace (prefixWord ++ tailWord_814280) baseStart_814280 baseEnd_814280 := by
    simpa [prefixWord, tailWord_814280, baseEnd_814280] using wordTrace_append hprefix tailTrace_814280
  have hstable : (prefixWord ++ tailWord_814280).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814280).length < 2 ^ (prefixWord ++ tailWord_814280).sum := by decide
  have hdescent : baseEnd_814280 < baseStart_814280 := by decide
  rcases family_descends (prefixWord ++ tailWord_814280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814304 : List Nat := [2, 1, 1, 3, 1, 5, 1, 2, 4]
def baseStart_814304 : Nat := 118140960795 + 814304 * 2 ^ 59
def prefixEnd_814304 : Nat := 4983230072969 + 3 ^ 40 * 814304 * 2
def baseEnd_814304 : Nat := 371670534114566458271191

theorem tailTrace_814304 : CollatzResearch.WordTrace tailWord_814304 prefixEnd_814304 371670534114566458271191 := by
  unfold tailWord_814304
  simp only [CollatzResearch.WordTrace]
  refine ⟨14850053420961577448108983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19800071227948769930811977 14850053420961577448108983)
  ·
    refine ⟨22275080131442366172163475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14850053420961577448108983 22275080131442366172163475)
    ·
      refine ⟨33412620197163549258245213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22275080131442366172163475 33412620197163549258245213)
      ·
        refine ⟨12529732573936330971841955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33412620197163549258245213 12529732573936330971841955)
        ·
          refine ⟨18794598860904496457762933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12529732573936330971841955 18794598860904496457762933)
          ·
            refine ⟨1761993643209796542915275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18794598860904496457762933 1761993643209796542915275)
            ·
              refine ⟨2642990464814694814372913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1761993643209796542915275 2642990464814694814372913)
              ·
                refine ⟨1982242848611021110779685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2642990464814694814372913 1982242848611021110779685)
                ·
                  refine ⟨371670534114566458271191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1982242848611021110779685 371670534114566458271191)
                  ·
                    rfl

theorem cell20_814304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 2, 4].length) (baseStart_814304 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_814304 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_814304 prefixEnd_814304 := by exact prefixLift 814304
  have htrace : WordTrace (prefixWord ++ tailWord_814304) baseStart_814304 baseEnd_814304 := by
    simpa [prefixWord, tailWord_814304, baseEnd_814304] using wordTrace_append hprefix tailTrace_814304
  have hstable : (prefixWord ++ tailWord_814304).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814304).length < 2 ^ (prefixWord ++ tailWord_814304).sum := by decide
  have hdescent : baseEnd_814304 < baseStart_814304 := by decide
  rcases family_descends (prefixWord ++ tailWord_814304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814324 : List Nat := [2, 6, 1, 2, 1, 1, 7]
def baseStart_814324 : Nat := 118140960795 + 814324 * 2 ^ 59
def prefixEnd_814324 : Nat := 4983230072969 + 3 ^ 40 * 814324 * 2
def baseEnd_814324 : Nat := 41297740295503919733827

theorem tailTrace_814324 : CollatzResearch.WordTrace tailWord_814324 prefixEnd_814324 41297740295503919733827 := by
  unfold tailWord_814324
  simp only [CollatzResearch.WordTrace]
  refine ⟨14850418150925349155973013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19800557534567132207964017 14850418150925349155973013)
  ·
    refine ⟨696113350824625741686235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 14850418150925349155973013 696113350824625741686235)
    ·
      refine ⟨1044170026236938612529353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 696113350824625741686235 1044170026236938612529353)
      ·
        refine ⟨783127519677703959397015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1044170026236938612529353 783127519677703959397015)
        ·
          refine ⟨1174691279516555939095523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 783127519677703959397015 1174691279516555939095523)
          ·
            refine ⟨1762036919274833908643285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1174691279516555939095523 1762036919274833908643285)
            ·
              refine ⟨41297740295503919733827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1762036919274833908643285 41297740295503919733827)
              ·
                rfl

theorem cell20_814324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 7].length) (baseStart_814324 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_814324 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_814324 prefixEnd_814324 := by exact prefixLift 814324
  have htrace : WordTrace (prefixWord ++ tailWord_814324) baseStart_814324 baseEnd_814324 := by
    simpa [prefixWord, tailWord_814324, baseEnd_814324] using wordTrace_append hprefix tailTrace_814324
  have hstable : (prefixWord ++ tailWord_814324).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814324).length < 2 ^ (prefixWord ++ tailWord_814324).sum := by decide
  have hdescent : baseEnd_814324 < baseStart_814324 := by decide
  rcases family_descends (prefixWord ++ tailWord_814324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814335 : List Nat := [1, 1, 2, 2, 1, 5, 3, 2, 3]
def baseStart_814335 : Nat := 118140960795 + 814335 * 2 ^ 59
def prefixEnd_814335 : Nat := 4983230072969 + 3 ^ 40 * 814335 * 2
def baseEnd_814335 : Nat := 371684683359268128237731

theorem tailTrace_814335 : CollatzResearch.WordTrace tailWord_814335 prefixEnd_814335 371684683359268128237731 := by
  unfold tailWord_814335
  simp only [CollatzResearch.WordTrace]
  refine ⟨29701237504810847190596459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19800825003207231460397639 29701237504810847190596459)
  ·
    refine ⟨44551856257216270785894689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29701237504810847190596459 44551856257216270785894689)
    ·
      refine ⟨33413892192912203089421017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44551856257216270785894689 33413892192912203089421017)
      ·
        refine ⟨25060419144684152317065763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33413892192912203089421017 25060419144684152317065763)
        ·
          refine ⟨37590628717026228475598645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25060419144684152317065763 37590628717026228475598645)
          ·
            refine ⟨3524121442221208919587373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37590628717026228475598645 3524121442221208919587373)
            ·
              refine ⟨1321545540832953344845265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3524121442221208919587373 1321545540832953344845265)
              ·
                refine ⟨991159155624715008633949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1321545540832953344845265 991159155624715008633949)
                ·
                  refine ⟨371684683359268128237731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 991159155624715008633949 371684683359268128237731)
                  ·
                    rfl

theorem cell20_814335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 2, 3].length) (baseStart_814335 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_814335 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_814335 prefixEnd_814335 := by exact prefixLift 814335
  have htrace : WordTrace (prefixWord ++ tailWord_814335) baseStart_814335 baseEnd_814335 := by
    simpa [prefixWord, tailWord_814335, baseEnd_814335] using wordTrace_append hprefix tailTrace_814335
  have hstable : (prefixWord ++ tailWord_814335).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814335).length < 2 ^ (prefixWord ++ tailWord_814335).sum := by decide
  have hdescent : baseEnd_814335 < baseStart_814335 := by decide
  rcases family_descends (prefixWord ++ tailWord_814335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814338 : List Nat := [3, 4, 1, 1, 3, 1, 2, 1, 4]
def baseStart_814338 : Nat := 118140960795 + 814338 * 2 ^ 59
def prefixEnd_814338 : Nat := 4983230072969 + 3 ^ 40 * 814338 * 2
def baseEnd_814338 : Nat := 371686052641013451137719

theorem tailTrace_814338 : CollatzResearch.WordTrace tailWord_814338 prefixEnd_814338 371686052641013451137719 := by
  unfold tailWord_814338
  simp only [CollatzResearch.WordTrace]
  refine ⟨7425336730949994675738917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19800897949199985801970445 7425336730949994675738917)
  ·
    refine ⟨1392250637053124001701047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7425336730949994675738917 1392250637053124001701047)
    ·
      refine ⟨2088375955579686002551571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1392250637053124001701047 2088375955579686002551571)
      ·
        refine ⟨3132563933369529003827357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2088375955579686002551571 3132563933369529003827357)
        ·
          refine ⟨1174711475013573376435259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3132563933369529003827357 1174711475013573376435259)
          ·
            refine ⟨1762067212520360064652889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1174711475013573376435259 1762067212520360064652889)
            ·
              refine ⟨1321550409390270048489667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1762067212520360064652889 1321550409390270048489667)
              ·
                refine ⟨1982325614085405072734501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1321550409390270048489667 1982325614085405072734501)
                ·
                  refine ⟨371686052641013451137719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1982325614085405072734501 371686052641013451137719)
                  ·
                    rfl

theorem cell20_814338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_814338 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_814338 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_814338 prefixEnd_814338 := by exact prefixLift 814338
  have htrace : WordTrace (prefixWord ++ tailWord_814338) baseStart_814338 baseEnd_814338 := by
    simpa [prefixWord, tailWord_814338, baseEnd_814338] using wordTrace_append hprefix tailTrace_814338
  have hstable : (prefixWord ++ tailWord_814338).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814338).length < 2 ^ (prefixWord ++ tailWord_814338).sum := by decide
  have hdescent : baseEnd_814338 < baseStart_814338 := by decide
  rcases family_descends (prefixWord ++ tailWord_814338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814376 : List Nat := [2, 1, 5, 1, 2, 1, 3, 3, 2]
def baseStart_814376 : Nat := 118140960795 + 814376 * 2 ^ 59
def prefixEnd_814376 : Nat := 4983230072969 + 3 ^ 40 * 814376 * 2
def baseEnd_814376 : Nat := 371703396876454207870897

theorem tailTrace_814376 : CollatzResearch.WordTrace tailWord_814376 prefixEnd_814376 371703396876454207870897 := by
  unfold tailWord_814376
  simp only [CollatzResearch.WordTrace]
  refine ⟨14851366448831155596419491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19801821931774874128559321 14851366448831155596419491)
  ·
    refine ⟨22277049673246733394629237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14851366448831155596419491 22277049673246733394629237)
    ·
      refine ⟨2088473406866881255746491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22277049673246733394629237 2088473406866881255746491)
      ·
        refine ⟨3132710110300321883619737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2088473406866881255746491 3132710110300321883619737)
        ·
          refine ⟨2349532582725241412714803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3132710110300321883619737 2349532582725241412714803)
          ·
            refine ⟨3524298874087862119072205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2349532582725241412714803 3524298874087862119072205)
            ·
              refine ⟨1321612077782948294652077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3524298874087862119072205 1321612077782948294652077)
              ·
                refine ⟨495604529168605610494529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1321612077782948294652077 495604529168605610494529)
                ·
                  refine ⟨371703396876454207870897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 495604529168605610494529 371703396876454207870897)
                  ·
                    rfl

theorem cell20_814376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 3, 2].length) (baseStart_814376 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_814376 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_814376 prefixEnd_814376 := by exact prefixLift 814376
  have htrace : WordTrace (prefixWord ++ tailWord_814376) baseStart_814376 baseEnd_814376 := by
    simpa [prefixWord, tailWord_814376, baseEnd_814376] using wordTrace_append hprefix tailTrace_814376
  have hstable : (prefixWord ++ tailWord_814376).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814376).length < 2 ^ (prefixWord ++ tailWord_814376).sum := by decide
  have hdescent : baseEnd_814376 < baseStart_814376 := by decide
  rcases family_descends (prefixWord ++ tailWord_814376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814387 : List Nat := [1, 1, 1, 2, 5, 4, 6]
def baseStart_814387 : Nat := 118140960795 + 814387 * 2 ^ 59
def prefixEnd_814387 : Nat := 4983230072969 + 3 ^ 40 * 814387 * 2
def baseEnd_814387 : Nat := 41300935286243006500465

theorem tailTrace_814387 : CollatzResearch.WordTrace tailWord_814387 prefixEnd_814387 41300935286243006500465 := by
  unfold tailWord_814387
  simp only [CollatzResearch.WordTrace]
  refine ⟨29703134100622460071489415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19802089400414973380992943 29703134100622460071489415)
  ·
    refine ⟨44554701150933690107234123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29703134100622460071489415 44554701150933690107234123)
    ·
      refine ⟨66832051726400535160851185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44554701150933690107234123 66832051726400535160851185)
      ·
        refine ⟨50124038794800401370638389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66832051726400535160851185 50124038794800401370638389)
        ·
          refine ⟨4699128637012537628497349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50124038794800401370638389 4699128637012537628497349)
          ·
            refine ⟨881086619439850805343253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4699128637012537628497349 881086619439850805343253)
            ·
              refine ⟨41300935286243006500465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 881086619439850805343253 41300935286243006500465)
              ·
                rfl

theorem cell20_814387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 6].length) (baseStart_814387 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_814387 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_814387 prefixEnd_814387 := by exact prefixLift 814387
  have htrace : WordTrace (prefixWord ++ tailWord_814387) baseStart_814387 baseEnd_814387 := by
    simpa [prefixWord, tailWord_814387, baseEnd_814387] using wordTrace_append hprefix tailTrace_814387
  have hstable : (prefixWord ++ tailWord_814387).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814387).length < 2 ^ (prefixWord ++ tailWord_814387).sum := by decide
  have hdescent : baseEnd_814387 < baseStart_814387 := by decide
  rcases family_descends (prefixWord ++ tailWord_814387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814393 : List Nat := [1, 2, 1, 6, 2, 1, 3, 2, 2]
def baseStart_814393 : Nat := 118140960795 + 814393 * 2 ^ 59
def prefixEnd_814393 : Nat := 4983230072969 + 3 ^ 40 * 814393 * 2
def baseEnd_814393 : Nat := 371711156139677704304161

theorem tailTrace_814393 : CollatzResearch.WordTrace tailWord_814393 prefixEnd_814393 371711156139677704304161 := by
  unfold tailWord_814393
  simp only [CollatzResearch.WordTrace]
  refine ⟨29703352938600723096207833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19802235292400482064138555 29703352938600723096207833)
  ·
    refine ⟨22277514703950542322155875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29703352938600723096207833 22277514703950542322155875)
    ·
      refine ⟨33416272055925813483233813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22277514703950542322155875 33416272055925813483233813)
      ·
        refine ⟨1566387752621522507026585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 33416272055925813483233813 1566387752621522507026585)
        ·
          refine ⟨1174790814466141880269939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1566387752621522507026585 1174790814466141880269939)
          ·
            refine ⟨1762186221699212820404909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1174790814466141880269939 1762186221699212820404909)
            ·
              refine ⟨660819833137204807651841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1762186221699212820404909 660819833137204807651841)
              ·
                refine ⟨495614874852903605738881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 660819833137204807651841 495614874852903605738881)
                ·
                  refine ⟨371711156139677704304161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 495614874852903605738881 371711156139677704304161)
                  ·
                    rfl

theorem cell20_814393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 3, 2, 2].length) (baseStart_814393 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_814393 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_814393 prefixEnd_814393 := by exact prefixLift 814393
  have htrace : WordTrace (prefixWord ++ tailWord_814393) baseStart_814393 baseEnd_814393 := by
    simpa [prefixWord, tailWord_814393, baseEnd_814393] using wordTrace_append hprefix tailTrace_814393
  have hstable : (prefixWord ++ tailWord_814393).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814393).length < 2 ^ (prefixWord ++ tailWord_814393).sum := by decide
  have hdescent : baseEnd_814393 < baseStart_814393 := by decide
  rcases family_descends (prefixWord ++ tailWord_814393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814394 : List Nat := [3, 1, 1, 1, 4, 1, 1, 3, 5]
def baseStart_814394 : Nat := 118140960795 + 814394 * 2 ^ 59
def prefixEnd_814394 : Nat := 4983230072969 + 3 ^ 40 * 814394 * 2
def baseEnd_814394 : Nat := 371711612566926145270823

theorem tailTrace_814394 : CollatzResearch.WordTrace tailWord_814394 prefixEnd_814394 371711612566926145270823 := by
  unfold tailWord_814394
  simp only [CollatzResearch.WordTrace]
  refine ⟨7425847352899275066748559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19802259607731400177996157 7425847352899275066748559)
  ·
    refine ⟨11138771029348912600122839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7425847352899275066748559 11138771029348912600122839)
    ·
      refine ⟨16708156544023368900184259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11138771029348912600122839 16708156544023368900184259)
      ·
        refine ⟨25062234816035053350276389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16708156544023368900184259 25062234816035053350276389)
        ·
          refine ⟨4699169028006572503176823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25062234816035053350276389 4699169028006572503176823)
          ·
            refine ⟨7048753542009858754765235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4699169028006572503176823 7048753542009858754765235)
            ·
              refine ⟨10573130313014788132147853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7048753542009858754765235 10573130313014788132147853)
              ·
                refine ⟨3964923867380545549555445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10573130313014788132147853 3964923867380545549555445)
                ·
                  refine ⟨371711612566926145270823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3964923867380545549555445 371711612566926145270823)
                  ·
                    rfl

theorem cell20_814394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 5].length) (baseStart_814394 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_814394 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_814394 prefixEnd_814394 := by exact prefixLift 814394
  have htrace : WordTrace (prefixWord ++ tailWord_814394) baseStart_814394 baseEnd_814394 := by
    simpa [prefixWord, tailWord_814394, baseEnd_814394] using wordTrace_append hprefix tailTrace_814394
  have hstable : (prefixWord ++ tailWord_814394).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814394).length < 2 ^ (prefixWord ++ tailWord_814394).sum := by decide
  have hdescent : baseEnd_814394 < baseStart_814394 := by decide
  rcases family_descends (prefixWord ++ tailWord_814394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814404 : List Nat := [2, 3, 4, 1, 1, 1, 1, 7]
def baseStart_814404 : Nat := 118140960795 + 814404 * 2 ^ 59
def prefixEnd_814404 : Nat := 4983230072969 + 3 ^ 40 * 814404 * 2
def baseEnd_814404 : Nat := 123905392279803518312483

theorem tailTrace_814404 : CollatzResearch.WordTrace tailWord_814404 prefixEnd_814404 123905392279803518312483 := by
  unfold tailWord_814404
  simp only [CollatzResearch.WordTrace]
  refine ⟨14851877070780435987429133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19802502761040581316572177 14851877070780435987429133)
  ·
    refine ⟨5569453901542663495285925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14851877070780435987429133 5569453901542663495285925)
    ·
      refine ⟨1044272606539249405366111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5569453901542663495285925 1044272606539249405366111)
      ·
        refine ⟨1566408909808874108049167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1044272606539249405366111 1566408909808874108049167)
        ·
          refine ⟨2349613364713311162073751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1566408909808874108049167 2349613364713311162073751)
          ·
            refine ⟨3524420047069966743110627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2349613364713311162073751 3524420047069966743110627)
            ·
              refine ⟨5286630070604950114665941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3524420047069966743110627 5286630070604950114665941)
              ·
                refine ⟨123905392279803518312483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5286630070604950114665941 123905392279803518312483)
                ·
                  rfl

theorem cell20_814404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 7].length) (baseStart_814404 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_814404 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_814404 prefixEnd_814404 := by exact prefixLift 814404
  have htrace : WordTrace (prefixWord ++ tailWord_814404) baseStart_814404 baseEnd_814404 := by
    simpa [prefixWord, tailWord_814404, baseEnd_814404] using wordTrace_append hprefix tailTrace_814404
  have hstable : (prefixWord ++ tailWord_814404).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814404).length < 2 ^ (prefixWord ++ tailWord_814404).sum := by decide
  have hdescent : baseEnd_814404 < baseStart_814404 := by decide
  rcases family_descends (prefixWord ++ tailWord_814404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814442 : List Nat := [3, 1, 3, 3, 3, 7]
def baseStart_814442 : Nat := 118140960795 + 814442 * 2 ^ 59
def prefixEnd_814442 : Nat := 4983230072969 + 3 ^ 40 * 814442 * 2
def baseEnd_814442 : Nat := 13767908187957455987801

theorem tailTrace_814442 : CollatzResearch.WordTrace tailWord_814442 prefixEnd_814442 13767908187957455987801 := by
  unfold tailWord_814442
  simp only [CollatzResearch.WordTrace]
  refine ⟨7426285028855801116185395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19803426743615469643161053 7426285028855801116185395)
  ·
    refine ⟨11139427543283701674278093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7426285028855801116185395 11139427543283701674278093)
    ·
      refine ⟨4177285328731388127854285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11139427543283701674278093 4177285328731388127854285)
      ·
        refine ⟨1566481998274270547945357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4177285328731388127854285 1566481998274270547945357)
        ·
          refine ⟨587430749352851455479509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1566481998274270547945357 587430749352851455479509)
          ·
            refine ⟨13767908187957455987801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 587430749352851455479509 13767908187957455987801)
            ·
              rfl

theorem cell20_814442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 7].length) (baseStart_814442 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_814442 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_814442 prefixEnd_814442 := by exact prefixLift 814442
  have htrace : WordTrace (prefixWord ++ tailWord_814442) baseStart_814442 baseEnd_814442 := by
    simpa [prefixWord, tailWord_814442, baseEnd_814442] using wordTrace_append hprefix tailTrace_814442
  have hstable : (prefixWord ++ tailWord_814442).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814442).length < 2 ^ (prefixWord ++ tailWord_814442).sum := by decide
  have hdescent : baseEnd_814442 < baseStart_814442 := by decide
  rcases family_descends (prefixWord ++ tailWord_814442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814504 : List Nat := [2, 1, 6, 1, 2, 1, 1, 1, 5]
def baseStart_814504 : Nat := 118140960795 + 814504 * 2 ^ 59
def prefixEnd_814504 : Nat := 4983230072969 + 3 ^ 40 * 814504 * 2
def baseEnd_814504 : Nat := 371761819564254651603707

theorem tailTrace_814504 : CollatzResearch.WordTrace tailWord_814504 prefixEnd_814504 371761819564254651603707 := by
  unfold tailWord_814504
  simp only [CollatzResearch.WordTrace]
  refine ⟨14853700720599294526749283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19804934294132392702332377 14853700720599294526749283)
  ·
    refine ⟨22280551080898941790123925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14853700720599294526749283 22280551080898941790123925)
    ·
      refine ⟨1044400831917137896412059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 22280551080898941790123925 1044400831917137896412059)
      ·
        refine ⟨1566601247875706844618089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1044400831917137896412059 1566601247875706844618089)
        ·
          refine ⟨1174950935906780133463567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1566601247875706844618089 1174950935906780133463567)
          ·
            refine ⟨1762426403860170200195351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1174950935906780133463567 1762426403860170200195351)
            ·
              refine ⟨2643639605790255300293027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1762426403860170200195351 2643639605790255300293027)
              ·
                refine ⟨3965459408685382950439541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2643639605790255300293027 3965459408685382950439541)
                ·
                  refine ⟨371761819564254651603707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3965459408685382950439541 371761819564254651603707)
                  ·
                    rfl

theorem cell20_814504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 5].length) (baseStart_814504 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_814504 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_814504 prefixEnd_814504 := by exact prefixLift 814504
  have htrace : WordTrace (prefixWord ++ tailWord_814504) baseStart_814504 baseEnd_814504 := by
    simpa [prefixWord, tailWord_814504, baseEnd_814504] using wordTrace_append hprefix tailTrace_814504
  have hstable : (prefixWord ++ tailWord_814504).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814504).length < 2 ^ (prefixWord ++ tailWord_814504).sum := by decide
  have hdescent : baseEnd_814504 < baseStart_814504 := by decide
  rcases family_descends (prefixWord ++ tailWord_814504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814539 : List Nat := [1, 1, 1, 1, 3, 3, 6, 4]
def baseStart_814539 : Nat := 118140960795 + 814539 * 2 ^ 59
def prefixEnd_814539 : Nat := 4983230072969 + 3 ^ 40 * 814539 * 2
def baseEnd_814539 : Nat := 123925931505983361812299

theorem tailTrace_814539 : CollatzResearch.WordTrace tailWord_814539 prefixEnd_814539 123925931505983361812299 := by
  unfold tailWord_814539
  simp only [CollatzResearch.WordTrace]
  refine ⟨29708677996071790031022671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19805785330714526687348447 29708677996071790031022671)
  ·
    refine ⟨44563016994107685046534007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29708677996071790031022671 44563016994107685046534007)
    ·
      refine ⟨66844525491161527569801011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44563016994107685046534007 66844525491161527569801011)
      ·
        refine ⟨100266788236742291354701517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66844525491161527569801011 100266788236742291354701517)
        ·
          refine ⟨37600045588778359258013069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100266788236742291354701517 37600045588778359258013069)
          ·
            refine ⟨14100017095791884721754901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37600045588778359258013069 14100017095791884721754901)
            ·
              refine ⟨660938301365244596332261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14100017095791884721754901 660938301365244596332261)
              ·
                refine ⟨123925931505983361812299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 660938301365244596332261 123925931505983361812299)
                ·
                  rfl

theorem cell20_814539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 6, 4].length) (baseStart_814539 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_814539 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_814539 prefixEnd_814539 := by exact prefixLift 814539
  have htrace : WordTrace (prefixWord ++ tailWord_814539) baseStart_814539 baseEnd_814539 := by
    simpa [prefixWord, tailWord_814539, baseEnd_814539] using wordTrace_append hprefix tailTrace_814539
  have hstable : (prefixWord ++ tailWord_814539).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814539).length < 2 ^ (prefixWord ++ tailWord_814539).sum := by decide
  have hdescent : baseEnd_814539 < baseStart_814539 := by decide
  rcases family_descends (prefixWord ++ tailWord_814539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814577 : List Nat := [1, 2, 2, 2, 3, 3, 2, 5]
def baseStart_814577 : Nat := 118140960795 + 814577 * 2 ^ 59
def prefixEnd_814577 : Nat := 4983230072969 + 3 ^ 40 * 814577 * 2
def baseEnd_814577 : Nat := 123931712917796947390025

theorem tailTrace_814577 : CollatzResearch.WordTrace tailWord_814577 prefixEnd_814577 123931712917796947390025 := by
  unfold tailWord_814577
  simp only [CollatzResearch.WordTrace]
  refine ⟨29710063969934122520905985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19806709313289415013937323 29710063969934122520905985)
  ·
    refine ⟨22282547977450591890679489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29710063969934122520905985 22282547977450591890679489)
    ·
      refine ⟨16711910983087943918009617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22282547977450591890679489 16711910983087943918009617)
      ·
        refine ⟨12533933237315957938507213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16711910983087943918009617 12533933237315957938507213)
        ·
          refine ⟨4700224963993484226940205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12533933237315957938507213 4700224963993484226940205)
          ·
            refine ⟨1762584361497556585102577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4700224963993484226940205 1762584361497556585102577)
            ·
              refine ⟨1321938271123167438826933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1762584361497556585102577 1321938271123167438826933)
              ·
                refine ⟨123931712917796947390025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1321938271123167438826933 123931712917796947390025)
                ·
                  rfl

theorem cell20_814577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 5].length) (baseStart_814577 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_814577 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_814577 prefixEnd_814577 := by exact prefixLift 814577
  have htrace : WordTrace (prefixWord ++ tailWord_814577) baseStart_814577 baseEnd_814577 := by
    simpa [prefixWord, tailWord_814577, baseEnd_814577] using wordTrace_append hprefix tailTrace_814577
  have hstable : (prefixWord ++ tailWord_814577).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814577).length < 2 ^ (prefixWord ++ tailWord_814577).sum := by decide
  have hdescent : baseEnd_814577 < baseStart_814577 := by decide
  rcases family_descends (prefixWord ++ tailWord_814577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814594 : List Nat := [3, 4, 1, 2, 1, 1, 2, 6]
def baseStart_814594 : Nat := 118140960795 + 814594 * 2 ^ 59
def prefixEnd_814594 : Nat := 4983230072969 + 3 ^ 40 * 814594 * 2
def baseEnd_814594 : Nat := 123934299338871446201113

theorem tailTrace_814594 : CollatzResearch.WordTrace tailWord_814594 prefixEnd_814594 123934299338871446201113 := by
  unfold tailWord_814594
  simp only [CollatzResearch.WordTrace]
  refine ⟨7427671002718133606068709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19807122673915022949516557 7427671002718133606068709)
  ·
    refine ⟨1392688313009650051137883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7427671002718133606068709 1392688313009650051137883)
    ·
      refine ⟨2089032469514475076706825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1392688313009650051137883 2089032469514475076706825)
      ·
        refine ⟨1566774352135856307530119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2089032469514475076706825 1566774352135856307530119)
        ·
          refine ⟨2350161528203784461295179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1566774352135856307530119 2350161528203784461295179)
          ·
            refine ⟨3525242292305676691942769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2350161528203784461295179 3525242292305676691942769)
            ·
              refine ⟨2643931719229257518957077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3525242292305676691942769 2643931719229257518957077)
              ·
                refine ⟨123934299338871446201113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2643931719229257518957077 123934299338871446201113)
                ·
                  rfl

theorem cell20_814594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 6].length) (baseStart_814594 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_814594 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_814594 prefixEnd_814594 := by exact prefixLift 814594
  have htrace : WordTrace (prefixWord ++ tailWord_814594) baseStart_814594 baseEnd_814594 := by
    simpa [prefixWord, tailWord_814594, baseEnd_814594] using wordTrace_append hprefix tailTrace_814594
  have hstable : (prefixWord ++ tailWord_814594).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814594).length < 2 ^ (prefixWord ++ tailWord_814594).sum := by decide
  have hdescent : baseEnd_814594 < baseStart_814594 := by decide
  rcases family_descends (prefixWord ++ tailWord_814594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814625 : List Nat := [1, 2, 3, 2, 2, 3, 1, 4, 2]
def baseStart_814625 : Nat := 118140960795 + 814625 * 2 ^ 59
def prefixEnd_814625 : Nat := 4983230072969 + 3 ^ 40 * 814625 * 2
def baseEnd_814625 : Nat := 371817047261316008569879

theorem tailTrace_814625 : CollatzResearch.WordTrace tailWord_814625 prefixEnd_814625 371817047261316008569879 := by
  unfold tailWord_814625
  simp only [CollatzResearch.WordTrace]
  refine ⟨29711814673760226718653329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19807876449173484479102219 29711814673760226718653329)
  ·
    refine ⟨22283861005320170038989997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29711814673760226718653329 22283861005320170038989997)
    ·
      refine ⟨8356447876995063764621249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22283861005320170038989997 8356447876995063764621249)
      ·
        refine ⟨6267335907746297823465937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8356447876995063764621249 6267335907746297823465937)
        ·
          refine ⟨4700501930809723367599453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6267335907746297823465937 4700501930809723367599453)
          ·
            refine ⟨1762688224053646262849795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4700501930809723367599453 1762688224053646262849795)
            ·
              refine ⟨2644032336080469394274693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1762688224053646262849795 2644032336080469394274693)
              ·
                refine ⟨495756063015088011426505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2644032336080469394274693 495756063015088011426505)
                ·
                  refine ⟨371817047261316008569879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 495756063015088011426505 371817047261316008569879)
                  ·
                    rfl

theorem cell20_814625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 4, 2].length) (baseStart_814625 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_814625 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_814625 prefixEnd_814625 := by exact prefixLift 814625
  have htrace : WordTrace (prefixWord ++ tailWord_814625) baseStart_814625 baseEnd_814625 := by
    simpa [prefixWord, tailWord_814625, baseEnd_814625] using wordTrace_append hprefix tailTrace_814625
  have hstable : (prefixWord ++ tailWord_814625).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814625).length < 2 ^ (prefixWord ++ tailWord_814625).sum := by decide
  have hdescent : baseEnd_814625 < baseStart_814625 := by decide
  rcases family_descends (prefixWord ++ tailWord_814625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814629 : List Nat := [1, 3, 1, 2, 2, 1, 1, 5, 4]
def baseStart_814629 : Nat := 118140960795 + 814629 * 2 ^ 59
def prefixEnd_814629 : Nat := 4983230072969 + 3 ^ 40 * 814629 * 2
def baseEnd_814629 : Nat := 371818872970309772436529

theorem tailTrace_814629 : CollatzResearch.WordTrace tailWord_814629 prefixEnd_814629 371818872970309772436529 := by
  unfold tailWord_814629
  simp only [CollatzResearch.WordTrace]
  refine ⟨29711960565745735401798941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19807973710497156934532627 29711960565745735401798941)
  ·
    refine ⟨11141985212154650775674603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29711960565745735401798941 11141985212154650775674603)
    ·
      refine ⟨16712977818231976163511905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11141985212154650775674603 16712977818231976163511905)
      ·
        refine ⟨12534733363673982122633929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16712977818231976163511905 12534733363673982122633929)
        ·
          refine ⟨9401050022755486591975447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12534733363673982122633929 9401050022755486591975447)
          ·
            refine ⟨14101575034133229887963171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9401050022755486591975447 14101575034133229887963171)
            ·
              refine ⟨21152362551199844831944757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14101575034133229887963171 21152362551199844831944757)
              ·
                refine ⟨1983033989174985452994821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21152362551199844831944757 1983033989174985452994821)
                ·
                  refine ⟨371818872970309772436529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1983033989174985452994821 371818872970309772436529)
                  ·
                    rfl

theorem cell20_814629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_814629 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_814629 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_814629 prefixEnd_814629 := by exact prefixLift 814629
  have htrace : WordTrace (prefixWord ++ tailWord_814629) baseStart_814629 baseEnd_814629 := by
    simpa [prefixWord, tailWord_814629, baseEnd_814629] using wordTrace_append hprefix tailTrace_814629
  have hstable : (prefixWord ++ tailWord_814629).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814629).length < 2 ^ (prefixWord ++ tailWord_814629).sum := by decide
  have hdescent : baseEnd_814629 < baseStart_814629 := by decide
  rcases family_descends (prefixWord ++ tailWord_814629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814684 : List Nat := [2, 2, 4, 1, 2, 1, 1, 3, 4]
def baseStart_814684 : Nat := 118140960795 + 814684 * 2 ^ 59
def prefixEnd_814684 : Nat := 4983230072969 + 3 ^ 40 * 814684 * 2
def baseEnd_814684 : Nat := 371843976468974025602971

theorem tailTrace_814684 : CollatzResearch.WordTrace tailWord_814684 prefixEnd_814684 371843976468974025602971 := by
  unfold tailWord_814684
  simp only [CollatzResearch.WordTrace]
  refine ⟨14856983290273239897525553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19809311053697653196700737 14856983290273239897525553)
  ·
    refine ⟨11142737467704929923144165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14856983290273239897525553 11142737467704929923144165)
    ·
      refine ⟨2089263275194674360589531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11142737467704929923144165 2089263275194674360589531)
      ·
        refine ⟨3133894912792011540884297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2089263275194674360589531 3133894912792011540884297)
        ·
          refine ⟨2350421184594008655663223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3133894912792011540884297 2350421184594008655663223)
          ·
            refine ⟨3525631776891012983494835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2350421184594008655663223 3525631776891012983494835)
            ·
              refine ⟨5288447665336519475242253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3525631776891012983494835 5288447665336519475242253)
              ·
                refine ⟨1983167874501194803215845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5288447665336519475242253 1983167874501194803215845)
                ·
                  refine ⟨371843976468974025602971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1983167874501194803215845 371843976468974025602971)
                  ·
                    rfl

theorem cell20_814684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 3, 4].length) (baseStart_814684 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_814684 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_814684 prefixEnd_814684 := by exact prefixLift 814684
  have htrace : WordTrace (prefixWord ++ tailWord_814684) baseStart_814684 baseEnd_814684 := by
    simpa [prefixWord, tailWord_814684, baseEnd_814684] using wordTrace_append hprefix tailTrace_814684
  have hstable : (prefixWord ++ tailWord_814684).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814684).length < 2 ^ (prefixWord ++ tailWord_814684).sum := by decide
  have hdescent : baseEnd_814684 < baseStart_814684 := by decide
  rcases family_descends (prefixWord ++ tailWord_814684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814753 : List Nat := [1, 2, 3, 3, 2, 2, 1, 3, 3]
def baseStart_814753 : Nat := 118140960795 + 814753 * 2 ^ 59
def prefixEnd_814753 : Nat := 4983230072969 + 3 ^ 40 * 814753 * 2
def baseEnd_814753 : Nat := 371875469949116452302689

theorem tailTrace_814753 : CollatzResearch.WordTrace tailWord_814753 prefixEnd_814753 371875469949116452302689 := by
  unfold tailWord_814753
  simp only [CollatzResearch.WordTrace]
  refine ⟨29716483217296504579312913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19810988811531003052875275 29716483217296504579312913)
  ·
    refine ⟨22287362412972378434484685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29716483217296504579312913 22287362412972378434484685)
    ·
      refine ⟨8357760904864641912931757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22287362412972378434484685 8357760904864641912931757)
      ·
        refine ⟨3134160339324240717349409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8357760904864641912931757 3134160339324240717349409)
        ·
          refine ⟨2350620254493180538012057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3134160339324240717349409 2350620254493180538012057)
          ·
            refine ⟨1762965190869885403509043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2350620254493180538012057 1762965190869885403509043)
            ·
              refine ⟨2644447786304828105263565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1762965190869885403509043 2644447786304828105263565)
              ·
                refine ⟨991667919864310539473837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2644447786304828105263565 991667919864310539473837)
                ·
                  refine ⟨371875469949116452302689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 991667919864310539473837 371875469949116452302689)
                  ·
                    rfl

theorem cell20_814753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 3, 3].length) (baseStart_814753 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_814753 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_814753 prefixEnd_814753 := by exact prefixLift 814753
  have htrace : WordTrace (prefixWord ++ tailWord_814753) baseStart_814753 baseEnd_814753 := by
    simpa [prefixWord, tailWord_814753, baseEnd_814753] using wordTrace_append hprefix tailTrace_814753
  have hstable : (prefixWord ++ tailWord_814753).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814753).length < 2 ^ (prefixWord ++ tailWord_814753).sum := by decide
  have hdescent : baseEnd_814753 < baseStart_814753 := by decide
  rcases family_descends (prefixWord ++ tailWord_814753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814786 : List Nat := [3, 5, 1, 2, 2, 1, 2, 2, 2]
def baseStart_814786 : Nat := 118140960795 + 814786 * 2 ^ 59
def prefixEnd_814786 : Nat := 4983230072969 + 3 ^ 40 * 814786 * 2
def baseEnd_814786 : Nat := 371890532048315004202555

theorem tailTrace_814786 : CollatzResearch.WordTrace tailWord_814786 prefixEnd_814786 371890532048315004202555 := by
  unfold tailWord_814786
  simp only [CollatzResearch.WordTrace]
  refine ⟨7429421706544237803816053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19811791217451300810176141 7429421706544237803816053)
  ·
    refine ⟨696508284988522294107755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7429421706544237803816053 696508284988522294107755)
    ·
      refine ⟨1044762427482783441161633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 696508284988522294107755 1044762427482783441161633)
      ·
        refine ⟨783571820612087580871225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1044762427482783441161633 783571820612087580871225)
        ·
          refine ⟨587678865459065685653419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 783571820612087580871225 587678865459065685653419)
          ·
            refine ⟨881518298188598528480129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 587678865459065685653419 881518298188598528480129)
            ·
              refine ⟨661138723641448896360097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 881518298188598528480129 661138723641448896360097)
              ·
                refine ⟨495854042731086672270073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 661138723641448896360097 495854042731086672270073)
                ·
                  refine ⟨371890532048315004202555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 495854042731086672270073 371890532048315004202555)
                  ·
                    rfl

theorem cell20_814786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_814786 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_814786 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_814786 prefixEnd_814786 := by exact prefixLift 814786
  have htrace : WordTrace (prefixWord ++ tailWord_814786) baseStart_814786 baseEnd_814786 := by
    simpa [prefixWord, tailWord_814786, baseEnd_814786] using wordTrace_append hprefix tailTrace_814786
  have hstable : (prefixWord ++ tailWord_814786).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814786).length < 2 ^ (prefixWord ++ tailWord_814786).sum := by decide
  have hdescent : baseEnd_814786 < baseStart_814786 := by decide
  rcases family_descends (prefixWord ++ tailWord_814786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814790 : List Nat := [6, 1, 2, 1, 1, 1, 4, 2, 2]
def baseStart_814790 : Nat := 118140960795 + 814790 * 2 ^ 59
def prefixEnd_814790 : Nat := 4983230072969 + 3 ^ 40 * 814790 * 2
def baseEnd_814790 : Nat := 371892357757308768069205

theorem tailTrace_814790 : CollatzResearch.WordTrace tailWord_814790 prefixEnd_814790 371892357757308768069205 := by
  unfold tailWord_814790
  simp only [CollatzResearch.WordTrace]
  refine ⟨928682272442576871825307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 19811888478774973265606549 928682272442576871825307)
  ·
    refine ⟨1393023408663865307737961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 928682272442576871825307 1393023408663865307737961)
    ·
      refine ⟨1044767556497898980803471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1393023408663865307737961 1044767556497898980803471)
      ·
        refine ⟨1567151334746848471205207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1044767556497898980803471 1567151334746848471205207)
        ·
          refine ⟨2350727002120272706807811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1567151334746848471205207 2350727002120272706807811)
          ·
            refine ⟨3526090503180409060211717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2350727002120272706807811 3526090503180409060211717)
            ·
              refine ⟨661141969346326698789697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3526090503180409060211717 661141969346326698789697)
              ·
                refine ⟨495856477009745024092273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 661141969346326698789697 495856477009745024092273)
                ·
                  refine ⟨371892357757308768069205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 495856477009745024092273 371892357757308768069205)
                  ·
                    rfl

theorem cell20_814790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_814790 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_814790 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_814790 prefixEnd_814790 := by exact prefixLift 814790
  have htrace : WordTrace (prefixWord ++ tailWord_814790) baseStart_814790 baseEnd_814790 := by
    simpa [prefixWord, tailWord_814790, baseEnd_814790] using wordTrace_append hprefix tailTrace_814790
  have hstable : (prefixWord ++ tailWord_814790).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814790).length < 2 ^ (prefixWord ++ tailWord_814790).sum := by decide
  have hdescent : baseEnd_814790 < baseStart_814790 := by decide
  rcases family_descends (prefixWord ++ tailWord_814790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814795 : List Nat := [1, 1, 1, 1, 3, 2, 1, 5, 5]
def baseStart_814795 : Nat := 118140960795 + 814795 * 2 ^ 59
def prefixEnd_814795 : Nat := 4983230072969 + 3 ^ 40 * 814795 * 2
def baseEnd_814795 : Nat := 371894639893550972902517

theorem tailTrace_814795 : CollatzResearch.WordTrace tailWord_814795 prefixEnd_814795 371894639893550972902517 := by
  unfold tailWord_814795
  simp only [CollatzResearch.WordTrace]
  refine ⟨29718015083144345752341839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19812010055429563834894559 29718015083144345752341839)
  ·
    refine ⟨44577022624716518628512759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29718015083144345752341839 44577022624716518628512759)
    ·
      refine ⟨66865533937074777942769139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44577022624716518628512759 66865533937074777942769139)
      ·
        refine ⟨100298300905612166914153709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66865533937074777942769139 100298300905612166914153709)
        ·
          refine ⟨37611862839604562592807641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100298300905612166914153709 37611862839604562592807641)
          ·
            refine ⟨28208897129703421944605731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37611862839604562592807641 28208897129703421944605731)
            ·
              refine ⟨42313345694555132916908597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28208897129703421944605731 42313345694555132916908597)
              ·
                refine ⟨3966876158864543710960181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42313345694555132916908597 3966876158864543710960181)
                ·
                  refine ⟨371894639893550972902517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3966876158864543710960181 371894639893550972902517)
                  ·
                    rfl

theorem cell20_814795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 5].length) (baseStart_814795 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_814795 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_814795 prefixEnd_814795 := by exact prefixLift 814795
  have htrace : WordTrace (prefixWord ++ tailWord_814795) baseStart_814795 baseEnd_814795 := by
    simpa [prefixWord, tailWord_814795, baseEnd_814795] using wordTrace_append hprefix tailTrace_814795
  have hstable : (prefixWord ++ tailWord_814795).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814795).length < 2 ^ (prefixWord ++ tailWord_814795).sum := by decide
  have hdescent : baseEnd_814795 < baseStart_814795 := by decide
  rcases family_descends (prefixWord ++ tailWord_814795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814826 : List Nat := [3, 1, 3, 1, 1, 1, 2, 8]
def baseStart_814826 : Nat := 118140960795 + 814826 * 2 ^ 59
def prefixEnd_814826 : Nat := 4983230072969 + 3 ^ 40 * 814826 * 2
def baseEnd_814826 : Nat := 123969596379417547623019

theorem tailTrace_814826 : CollatzResearch.WordTrace tailWord_814826 prefixEnd_814826 123969596379417547623019 := by
  unfold tailWord_814826
  simp only [CollatzResearch.WordTrace]
  refine ⟨7429786436508009511680083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19812763830688025364480221 7429786436508009511680083)
  ·
    refine ⟨11144679654762014267520125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7429786436508009511680083 11144679654762014267520125)
    ·
      refine ⟨4179254870535755350320047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11144679654762014267520125 4179254870535755350320047)
      ·
        refine ⟨6268882305803633025480071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4179254870535755350320047 6268882305803633025480071)
        ·
          refine ⟨9403323458705449538220107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6268882305803633025480071 9403323458705449538220107)
          ·
            refine ⟨14104985188058174307330161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9403323458705449538220107 14104985188058174307330161)
            ·
              refine ⟨10578738891043630730497621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14104985188058174307330161 10578738891043630730497621)
              ·
                refine ⟨123969596379417547623019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10578738891043630730497621 123969596379417547623019)
                ·
                  rfl

theorem cell20_814826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 8].length) (baseStart_814826 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_814826 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_814826 prefixEnd_814826 := by exact prefixLift 814826
  have htrace : WordTrace (prefixWord ++ tailWord_814826) baseStart_814826 baseEnd_814826 := by
    simpa [prefixWord, tailWord_814826, baseEnd_814826] using wordTrace_append hprefix tailTrace_814826
  have hstable : (prefixWord ++ tailWord_814826).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814826).length < 2 ^ (prefixWord ++ tailWord_814826).sum := by decide
  have hdescent : baseEnd_814826 < baseStart_814826 := by decide
  rcases family_descends (prefixWord ++ tailWord_814826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814881 : List Nat := [1, 2, 3, 2, 1, 3, 4, 4]
def baseStart_814881 : Nat := 118140960795 + 814881 * 2 ^ 59
def prefixEnd_814881 : Nat := 4983230072969 + 3 ^ 40 * 814881 * 2
def baseEnd_814881 : Nat := 123977964212305632011833

theorem tailTrace_814881 : CollatzResearch.WordTrace tailWord_814881 prefixEnd_814881 123977964212305632011833 := by
  unfold tailWord_814881
  simp only [CollatzResearch.WordTrace]
  refine ⟨29721151760832782439972497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19814101173888521626648331 29721151760832782439972497)
  ·
    refine ⟨22290863820624586829979373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29721151760832782439972497 22290863820624586829979373)
    ·
      refine ⟨8359073932734220061242265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22290863820624586829979373 8359073932734220061242265)
      ·
        refine ⟨6269305449550665045931699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8359073932734220061242265 6269305449550665045931699)
        ·
          refine ⟨9403958174325997568897549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6269305449550665045931699 9403958174325997568897549)
          ·
            refine ⟨3526484315372249088336581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9403958174325997568897549 3526484315372249088336581)
            ·
              refine ⟨661215809132296704063109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3526484315372249088336581 661215809132296704063109)
              ·
                refine ⟨123977964212305632011833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 661215809132296704063109 123977964212305632011833)
                ·
                  rfl

theorem cell20_814881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 4, 4].length) (baseStart_814881 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_814881 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_814881 prefixEnd_814881 := by exact prefixLift 814881
  have htrace : WordTrace (prefixWord ++ tailWord_814881) baseStart_814881 baseEnd_814881 := by
    simpa [prefixWord, tailWord_814881, baseEnd_814881] using wordTrace_append hprefix tailTrace_814881
  have hstable : (prefixWord ++ tailWord_814881).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814881).length < 2 ^ (prefixWord ++ tailWord_814881).sum := by decide
  have hdescent : baseEnd_814881 < baseStart_814881 := by decide
  rcases family_descends (prefixWord ++ tailWord_814881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814888 : List Nat := [2, 1, 5, 1, 1, 2, 1, 2, 5]
def baseStart_814888 : Nat := 118140960795 + 814888 * 2 ^ 59
def prefixEnd_814888 : Nat := 4983230072969 + 3 ^ 40 * 814888 * 2
def baseEnd_814888 : Nat := 371937087627655982802137

theorem tailTrace_814888 : CollatzResearch.WordTrace tailWord_814888 prefixEnd_814888 371937087627655982802137 := by
  unfold tailWord_814888
  simp only [CollatzResearch.WordTrace]
  refine ⟨14860703535903711317738659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19814271381204948423651545 14860703535903711317738659)
  ·
    refine ⟨22291055303855566976607989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14860703535903711317738659 22291055303855566976607989)
    ·
      refine ⟨2089786434736459404056999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22291055303855566976607989 2089786434736459404056999)
      ·
        refine ⟨3134679652104689106085499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2089786434736459404056999 3134679652104689106085499)
        ·
          refine ⟨4702019478157033659128249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3134679652104689106085499 4702019478157033659128249)
          ·
            refine ⟨3526514608617775244346187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4702019478157033659128249 3526514608617775244346187)
            ·
              refine ⟨5289771912926662866519281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3526514608617775244346187 5289771912926662866519281)
              ·
                refine ⟨3967328934694997149889461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5289771912926662866519281 3967328934694997149889461)
                ·
                  refine ⟨371937087627655982802137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3967328934694997149889461 371937087627655982802137)
                  ·
                    rfl

theorem cell20_814888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 5].length) (baseStart_814888 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_814888 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_814888 prefixEnd_814888 := by exact prefixLift 814888
  have htrace : WordTrace (prefixWord ++ tailWord_814888) baseStart_814888 baseEnd_814888 := by
    simpa [prefixWord, tailWord_814888, baseEnd_814888] using wordTrace_append hprefix tailTrace_814888
  have hstable : (prefixWord ++ tailWord_814888).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814888).length < 2 ^ (prefixWord ++ tailWord_814888).sum := by decide
  have hdescent : baseEnd_814888 < baseStart_814888 := by decide
  rcases family_descends (prefixWord ++ tailWord_814888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814918 : List Nat := [6, 1, 1, 2, 1, 3, 2, 1, 3]
def baseStart_814918 : Nat := 118140960795 + 814918 * 2 ^ 59
def prefixEnd_814918 : Nat := 4983230072969 + 3 ^ 40 * 814918 * 2
def baseEnd_814918 : Nat := 371950780445109211802015

theorem tailTrace_814918 : CollatzResearch.WordTrace tailWord_814918 prefixEnd_814918 371950780445109211802015 := by
  unfold tailWord_814918
  simp only [CollatzResearch.WordTrace]
  refine ⟨928828164428085554970919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 19815000841132491839379605 928828164428085554970919)
  ·
    refine ⟨1393242246642128332456379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 928828164428085554970919 1393242246642128332456379)
    ·
      refine ⟨2089863369963192498684569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1393242246642128332456379 2089863369963192498684569)
      ·
        refine ⟨1567397527472394374013427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2089863369963192498684569 1567397527472394374013427)
        ·
          refine ⟨2351096291208591561020141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1567397527472394374013427 2351096291208591561020141)
          ·
            refine ⟨881661109203221835382553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2351096291208591561020141 881661109203221835382553)
            ·
              refine ⟨661245831902416376536915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 881661109203221835382553 661245831902416376536915)
              ·
                refine ⟨991868747853624564805373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 661245831902416376536915 991868747853624564805373)
                ·
                  refine ⟨371950780445109211802015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 991868747853624564805373 371950780445109211802015)
                  ·
                    rfl

theorem cell20_814918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_814918 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_814918 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_814918 prefixEnd_814918 := by exact prefixLift 814918
  have htrace : WordTrace (prefixWord ++ tailWord_814918) baseStart_814918 baseEnd_814918 := by
    simpa [prefixWord, tailWord_814918, baseEnd_814918] using wordTrace_append hprefix tailTrace_814918
  have hstable : (prefixWord ++ tailWord_814918).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814918).length < 2 ^ (prefixWord ++ tailWord_814918).sum := by decide
  have hdescent : baseEnd_814918 < baseStart_814918 := by decide
  rcases family_descends (prefixWord ++ tailWord_814918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814974 : List Nat := [4, 2, 3, 1, 1, 1, 3, 5]
def baseStart_814974 : Nat := 118140960795 + 814974 * 2 ^ 59
def prefixEnd_814974 : Nat := 4983230072969 + 3 ^ 40 * 814974 * 2
def baseEnd_814974 : Nat := 123992113457007301978373

theorem tailTrace_814974 : CollatzResearch.WordTrace tailWord_814974 prefixEnd_814974 123992113457007301978373 := by
  unfold tailWord_814974
  simp only [CollatzResearch.WordTrace]
  refine ⟨3715567968686982415388497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19816362499663906215405317 3715567968686982415388497)
  ·
    refine ⟨2786675976515236811541373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3715567968686982415388497 2786675976515236811541373)
    ·
      refine ⟨1045003491193213804328015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2786675976515236811541373 1045003491193213804328015)
      ·
        refine ⟨1567505236789820706492023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1045003491193213804328015 1567505236789820706492023)
        ·
          refine ⟨2351257855184731059738035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1567505236789820706492023 2351257855184731059738035)
          ·
            refine ⟨3526886782777096589607053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2351257855184731059738035 3526886782777096589607053)
            ·
              refine ⟨1322582543541411221102645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3526886782777096589607053 1322582543541411221102645)
              ·
                refine ⟨123992113457007301978373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1322582543541411221102645 123992113457007301978373)
                ·
                  rfl

theorem cell20_814974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 5].length) (baseStart_814974 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_814974 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_814974 prefixEnd_814974 := by exact prefixLift 814974
  have htrace : WordTrace (prefixWord ++ tailWord_814974) baseStart_814974 baseEnd_814974 := by
    simpa [prefixWord, tailWord_814974, baseEnd_814974] using wordTrace_append hprefix tailTrace_814974
  have hstable : (prefixWord ++ tailWord_814974).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814974).length < 2 ^ (prefixWord ++ tailWord_814974).sum := by decide
  have hdescent : baseEnd_814974 < baseStart_814974 := by decide
  rcases family_descends (prefixWord ++ tailWord_814974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_814992 : List Nat := [2, 1, 1, 1, 1, 1, 2, 5, 6]
def baseStart_814992 : Nat := 118140960795 + 814992 * 2 ^ 59
def prefixEnd_814992 : Nat := 4983230072969 + 3 ^ 40 * 814992 * 2
def baseEnd_814992 : Nat := 371984556061493843335045

theorem tailTrace_814992 : CollatzResearch.WordTrace tailWord_814992 prefixEnd_814992 371984556061493843335045 := by
  unfold tailWord_814992
  simp only [CollatzResearch.WordTrace]
  refine ⟨14862600131715324198631615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19816800175620432264842153 14862600131715324198631615)
  ·
    refine ⟨22293900197572986297947423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14862600131715324198631615 22293900197572986297947423)
    ·
      refine ⟨33440850296359479446921135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22293900197572986297947423 33440850296359479446921135)
      ·
        refine ⟨50161275444539219170381703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33440850296359479446921135 50161275444539219170381703)
        ·
          refine ⟨75241913166808828755572555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50161275444539219170381703 75241913166808828755572555)
          ·
            refine ⟨112862869750213243133358833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75241913166808828755572555 112862869750213243133358833)
            ·
              refine ⟨84647152312659932350019125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112862869750213243133358833 84647152312659932350019125)
              ·
                refine ⟨7935670529311868657814293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 84647152312659932350019125 7935670529311868657814293)
                ·
                  refine ⟨371984556061493843335045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7935670529311868657814293 371984556061493843335045)
                  ·
                    rfl

theorem cell20_814992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 6].length) (baseStart_814992 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_814992 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_814992 prefixEnd_814992 := by exact prefixLift 814992
  have htrace : WordTrace (prefixWord ++ tailWord_814992) baseStart_814992 baseEnd_814992 := by
    simpa [prefixWord, tailWord_814992, baseEnd_814992] using wordTrace_append hprefix tailTrace_814992
  have hstable : (prefixWord ++ tailWord_814992).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_814992).length < 2 ^ (prefixWord ++ tailWord_814992).sum := by decide
  have hdescent : baseEnd_814992 < baseStart_814992 := by decide
  rcases family_descends (prefixWord ++ tailWord_814992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815005 : List Nat := [1, 4, 2, 1, 2, 3, 2, 3, 2]
def baseStart_815005 : Nat := 118140960795 + 815005 * 2 ^ 59
def prefixEnd_815005 : Nat := 4983230072969 + 3 ^ 40 * 815005 * 2
def baseEnd_815005 : Nat := 371990489615723575901659

theorem tailTrace_815005 : CollatzResearch.WordTrace tailWord_815005 prefixEnd_815005 371990489615723575901659 := by
  unfold tailWord_815005
  simp only [CollatzResearch.WordTrace]
  refine ⟨29725674412383551617486469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19817116274922367744990979 29725674412383551617486469)
  ·
    refine ⟨5573563952321915928278713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29725674412383551617486469 5573563952321915928278713)
    ·
      refine ⟨4180172964241436946209035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5573563952321915928278713 4180172964241436946209035)
      ·
        refine ⟨6270259446362155419313553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4180172964241436946209035 6270259446362155419313553)
        ·
          refine ⟨4702694584771616564485165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6270259446362155419313553 4702694584771616564485165)
          ·
            refine ⟨1763510469289356211681937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4702694584771616564485165 1763510469289356211681937)
            ·
              refine ⟨1322632851967017158761453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1763510469289356211681937 1322632851967017158761453)
              ·
                refine ⟨495987319487631434535545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1322632851967017158761453 495987319487631434535545)
                ·
                  refine ⟨371990489615723575901659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 495987319487631434535545 371990489615723575901659)
                  ·
                    rfl

theorem cell20_815005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 3, 2].length) (baseStart_815005 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_815005 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_815005 prefixEnd_815005 := by exact prefixLift 815005
  have htrace : WordTrace (prefixWord ++ tailWord_815005) baseStart_815005 baseEnd_815005 := by
    simpa [prefixWord, tailWord_815005, baseEnd_815005] using wordTrace_append hprefix tailTrace_815005
  have hstable : (prefixWord ++ tailWord_815005).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815005).length < 2 ^ (prefixWord ++ tailWord_815005).sum := by decide
  have hdescent : baseEnd_815005 < baseStart_815005 := by decide
  rcases family_descends (prefixWord ++ tailWord_815005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815023 : List Nat := [1, 1, 2, 1, 2, 2, 5, 1, 5]
def baseStart_815023 : Nat := 118140960795 + 815023 * 2 ^ 59
def prefixEnd_815023 : Nat := 4983230072969 + 3 ^ 40 * 815023 * 2
def baseEnd_815023 : Nat := 371998705306195513301585

theorem tailTrace_815023 : CollatzResearch.WordTrace tailWord_815023 prefixEnd_815023 371998705306195513301585 := by
  unfold tailWord_815023
  simp only [CollatzResearch.WordTrace]
  refine ⟨29726330926318340691641723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19817553950878893794427815 29726330926318340691641723)
  ·
    refine ⟨44589496389477511037462585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29726330926318340691641723 44589496389477511037462585)
    ·
      refine ⟨33442122292108133278096939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44589496389477511037462585 33442122292108133278096939)
      ·
        refine ⟨50163183438162199917145409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33442122292108133278096939 50163183438162199917145409)
        ·
          refine ⟨37622387578621649937859057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50163183438162199917145409 37622387578621649937859057)
          ·
            refine ⟨28216790683966237453394293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37622387578621649937859057 28216790683966237453394293)
            ·
              refine ⟨2645324126621834761255715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28216790683966237453394293 2645324126621834761255715)
              ·
                refine ⟨3967986189932752141883573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2645324126621834761255715 3967986189932752141883573)
                ·
                  refine ⟨371998705306195513301585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3967986189932752141883573 371998705306195513301585)
                  ·
                    rfl

theorem cell20_815023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 5].length) (baseStart_815023 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_815023 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_815023 prefixEnd_815023 := by exact prefixLift 815023
  have htrace : WordTrace (prefixWord ++ tailWord_815023) baseStart_815023 baseEnd_815023 := by
    simpa [prefixWord, tailWord_815023, baseEnd_815023] using wordTrace_append hprefix tailTrace_815023
  have hstable : (prefixWord ++ tailWord_815023).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815023).length < 2 ^ (prefixWord ++ tailWord_815023).sum := by decide
  have hdescent : baseEnd_815023 < baseStart_815023 := by decide
  rcases family_descends (prefixWord ++ tailWord_815023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815054 : List Nat := [4, 1, 1, 1, 2, 2, 3, 6]
def baseStart_815054 : Nat := 118140960795 + 815054 * 2 ^ 59
def prefixEnd_815054 : Nat := 4983230072969 + 3 ^ 40 * 815054 * 2
def baseEnd_815054 : Nat := 124004284850299061089375

theorem tailTrace_815054 : CollatzResearch.WordTrace tailWord_815054 prefixEnd_815054 124004284850299061089375 := by
  unfold tailWord_815054
  simp only [CollatzResearch.WordTrace]
  refine ⟨3715932698650754123252527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19818307726137355324013477 3715932698650754123252527)
  ·
    refine ⟨5573899047976131184878791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3715932698650754123252527 5573899047976131184878791)
    ·
      refine ⟨8360848571964196777318187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5573899047976131184878791 8360848571964196777318187)
      ·
        refine ⟨12541272857946295165977281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8360848571964196777318187 12541272857946295165977281)
        ·
          refine ⟨9405954643459721374482961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12541272857946295165977281 9405954643459721374482961)
          ·
            refine ⟨7054465982594791030862221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9405954643459721374482961 7054465982594791030862221)
            ·
              refine ⟨2645424743473046636573333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7054465982594791030862221 2645424743473046636573333)
              ·
                refine ⟨124004284850299061089375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2645424743473046636573333 124004284850299061089375)
                ·
                  rfl

theorem cell20_815054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_815054 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_815054 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_815054 prefixEnd_815054 := by exact prefixLift 815054
  have htrace : WordTrace (prefixWord ++ tailWord_815054) baseStart_815054 baseEnd_815054 := by
    simpa [prefixWord, tailWord_815054, baseEnd_815054] using wordTrace_append hprefix tailTrace_815054
  have hstable : (prefixWord ++ tailWord_815054).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815054).length < 2 ^ (prefixWord ++ tailWord_815054).sum := by decide
  have hdescent : baseEnd_815054 < baseStart_815054 := by decide
  rcases family_descends (prefixWord ++ tailWord_815054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815133 : List Nat := [1, 4, 2, 2, 2, 2, 2, 2, 3]
def baseStart_815133 : Nat := 118140960795 + 815133 * 2 ^ 59
def prefixEnd_815133 : Nat := 4983230072969 + 3 ^ 40 * 815133 * 2
def baseEnd_815133 : Nat := 372048912303524019634469

theorem tailTrace_815133 : CollatzResearch.WordTrace tailWord_815133 prefixEnd_815133 372048912303524019634469 := by
  unfold tailWord_815133
  simp only [CollatzResearch.WordTrace]
  refine ⟨29730342955919829478146053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19820228637279886318764035 29730342955919829478146053)
  ·
    refine ⟨5574439304234968027152385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29730342955919829478146053 5574439304234968027152385)
    ·
      refine ⟨4180829478176226020364289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5574439304234968027152385 4180829478176226020364289)
      ·
        refine ⟨3135622108632169515273217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4180829478176226020364289 3135622108632169515273217)
        ·
          refine ⟨2351716581474127136454913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3135622108632169515273217 2351716581474127136454913)
          ·
            refine ⟨1763787436105595352341185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2351716581474127136454913 1763787436105595352341185)
            ·
              refine ⟨1322840577079196514255889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1763787436105595352341185 1322840577079196514255889)
              ·
                refine ⟨992130432809397385691917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1322840577079196514255889 992130432809397385691917)
                ·
                  refine ⟨372048912303524019634469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 992130432809397385691917 372048912303524019634469)
                  ·
                    rfl

theorem cell20_815133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 2, 3].length) (baseStart_815133 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_815133 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_815133 prefixEnd_815133 := by exact prefixLift 815133
  have htrace : WordTrace (prefixWord ++ tailWord_815133) baseStart_815133 baseEnd_815133 := by
    simpa [prefixWord, tailWord_815133, baseEnd_815133] using wordTrace_append hprefix tailTrace_815133
  have hstable : (prefixWord ++ tailWord_815133).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815133).length < 2 ^ (prefixWord ++ tailWord_815133).sum := by decide
  have hdescent : baseEnd_815133 < baseStart_815133 := by decide
  rcases family_descends (prefixWord ++ tailWord_815133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815143 : List Nat := [1, 1, 7, 1, 3, 1, 1, 5]
def baseStart_815143 : Nat := 118140960795 + 815143 * 2 ^ 59
def prefixEnd_815143 : Nat := 4983230072969 + 3 ^ 40 * 815143 * 2
def baseEnd_815143 : Nat := 124017825525336143100365

theorem tailTrace_815143 : CollatzResearch.WordTrace tailWord_815143 prefixEnd_815143 124017825525336143100365 := by
  unfold tailWord_815143
  simp only [CollatzResearch.WordTrace]
  refine ⟨29730707685883601186010083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19820471790589067457340055 29730707685883601186010083)
  ·
    refine ⟨44596061528825401779015125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29730707685883601186010083 44596061528825401779015125)
    ·
      refine ⟨1045220192081845354195667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 44596061528825401779015125 1045220192081845354195667)
      ·
        refine ⟨1567830288122768031293501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1045220192081845354195667 1567830288122768031293501)
        ·
          refine ⟨587936358046038011735063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1567830288122768031293501 587936358046038011735063)
          ·
            refine ⟨881904537069057017602595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 587936358046038011735063 881904537069057017602595)
            ·
              refine ⟨1322856805603585526403893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 881904537069057017602595 1322856805603585526403893)
              ·
                refine ⟨124017825525336143100365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1322856805603585526403893 124017825525336143100365)
                ·
                  rfl

theorem cell20_815143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 5].length) (baseStart_815143 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_815143 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_815143 prefixEnd_815143 := by exact prefixLift 815143
  have htrace : WordTrace (prefixWord ++ tailWord_815143) baseStart_815143 baseEnd_815143 := by
    simpa [prefixWord, tailWord_815143, baseEnd_815143] using wordTrace_append hprefix tailTrace_815143
  have hstable : (prefixWord ++ tailWord_815143).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815143).length < 2 ^ (prefixWord ++ tailWord_815143).sum := by decide
  have hdescent : baseEnd_815143 < baseStart_815143 := by decide
  rcases family_descends (prefixWord ++ tailWord_815143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815151 : List Nat := [1, 1, 2, 1, 2, 1, 1, 11]
def baseStart_815151 : Nat := 118140960795 + 815151 * 2 ^ 59
def prefixEnd_815151 : Nat := 4983230072969 + 3 ^ 40 * 815151 * 2
def baseEnd_815151 : Nat := 124019042664665319011465

theorem tailTrace_815151 : CollatzResearch.WordTrace tailWord_815151 prefixEnd_815151 124019042664665319011465 := by
  unfold tailWord_815151
  simp only [CollatzResearch.WordTrace]
  refine ⟨29730999469854618552301307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19820666313236412368200871 29730999469854618552301307)
  ·
    refine ⟨44596499204781927828451961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29730999469854618552301307 44596499204781927828451961)
    ·
      refine ⟨33447374403586445871338971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44596499204781927828451961 33447374403586445871338971)
      ·
        refine ⟨50171061605379668807008457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33447374403586445871338971 50171061605379668807008457)
        ·
          refine ⟨37628296204034751605256343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50171061605379668807008457 37628296204034751605256343)
          ·
            refine ⟨56442444306052127407884515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37628296204034751605256343 56442444306052127407884515)
            ·
              refine ⟨84663666459078191111826773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56442444306052127407884515 84663666459078191111826773)
              ·
                refine ⟨124019042664665319011465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 84663666459078191111826773 124019042664665319011465)
                ·
                  rfl

theorem cell20_815151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 11].length) (baseStart_815151 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_815151 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_815151 prefixEnd_815151 := by exact prefixLift 815151
  have htrace : WordTrace (prefixWord ++ tailWord_815151) baseStart_815151 baseEnd_815151 := by
    simpa [prefixWord, tailWord_815151, baseEnd_815151] using wordTrace_append hprefix tailTrace_815151
  have hstable : (prefixWord ++ tailWord_815151).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815151).length < 2 ^ (prefixWord ++ tailWord_815151).sum := by decide
  have hdescent : baseEnd_815151 < baseStart_815151 := by decide
  rcases family_descends (prefixWord ++ tailWord_815151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815154 : List Nat := [3, 2, 1, 1, 2, 3, 2, 3, 3]
def baseStart_815154 : Nat := 118140960795 + 815154 * 2 ^ 59
def prefixEnd_815154 : Nat := 4983230072969 + 3 ^ 40 * 815154 * 2
def baseEnd_815154 : Nat := 372058497275741279934383

theorem tailTrace_815154 : CollatzResearch.WordTrace tailWord_815154 prefixEnd_815154 372058497275741279934383 := by
  unfold tailWord_815154
  simp only [CollatzResearch.WordTrace]
  refine ⟨7432777222210937516165129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19820739259229166709773677 7432777222210937516165129)
  ·
    refine ⟨5574582916658203137123847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7432777222210937516165129 5574582916658203137123847)
    ·
      refine ⟨8361874374987304705685771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5574582916658203137123847 8361874374987304705685771)
      ·
        refine ⟨12542811562480957058528657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8361874374987304705685771 12542811562480957058528657)
        ·
          refine ⟨9407108671860717793896493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12542811562480957058528657 9407108671860717793896493)
          ·
            refine ⟨3527665751947769172711185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9407108671860717793896493 3527665751947769172711185)
            ·
              refine ⟨2645749313960826879533389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3527665751947769172711185 2645749313960826879533389)
              ·
                refine ⟨992155992735310079825021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2645749313960826879533389 992155992735310079825021)
                ·
                  refine ⟨372058497275741279934383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 992155992735310079825021 372058497275741279934383)
                  ·
                    rfl

theorem cell20_815154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 3, 3].length) (baseStart_815154 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_815154 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_815154 prefixEnd_815154 := by exact prefixLift 815154
  have htrace : WordTrace (prefixWord ++ tailWord_815154) baseStart_815154 baseEnd_815154 := by
    simpa [prefixWord, tailWord_815154, baseEnd_815154] using wordTrace_append hprefix tailTrace_815154
  have hstable : (prefixWord ++ tailWord_815154).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815154).length < 2 ^ (prefixWord ++ tailWord_815154).sum := by decide
  have hdescent : baseEnd_815154 < baseStart_815154 := by decide
  rcases family_descends (prefixWord ++ tailWord_815154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815174 : List Nat := [6, 1, 1, 1, 1, 1, 4, 3, 2]
def baseStart_815174 : Nat := 118140960795 + 815174 * 2 ^ 59
def prefixEnd_815174 : Nat := 4983230072969 + 3 ^ 40 * 815174 * 2
def baseEnd_815174 : Nat := 372067625820710099267635

theorem tailTrace_815174 : CollatzResearch.WordTrace tailWord_815174 prefixEnd_815174 372067625820710099267635 := by
  unfold tailWord_815174
  simp only [CollatzResearch.WordTrace]
  refine ⟨929119948399102921262143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 19821225565847528986925717 929119948399102921262143)
  ·
    refine ⟨1393679922598654381893215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 929119948399102921262143 1393679922598654381893215)
    ·
      refine ⟨2090519883897981572839823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1393679922598654381893215 2090519883897981572839823)
      ·
        refine ⟨3135779825846972359259735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2090519883897981572839823 3135779825846972359259735)
        ·
          refine ⟨4703669738770458538889603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3135779825846972359259735 4703669738770458538889603)
          ·
            refine ⟨7055504608155687808334405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4703669738770458538889603 7055504608155687808334405)
            ·
              refine ⟨1322907114029191464062701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7055504608155687808334405 1322907114029191464062701)
              ·
                refine ⟨496090167760946799023513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1322907114029191464062701 496090167760946799023513)
                ·
                  refine ⟨372067625820710099267635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 496090167760946799023513 372067625820710099267635)
                  ·
                    rfl

theorem cell20_815174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_815174 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_815174 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_815174 prefixEnd_815174 := by exact prefixLift 815174
  have htrace : WordTrace (prefixWord ++ tailWord_815174) baseStart_815174 baseEnd_815174 := by
    simpa [prefixWord, tailWord_815174, baseEnd_815174] using wordTrace_append hprefix tailTrace_815174
  have hstable : (prefixWord ++ tailWord_815174).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815174).length < 2 ^ (prefixWord ++ tailWord_815174).sum := by decide
  have hdescent : baseEnd_815174 < baseStart_815174 := by decide
  rcases family_descends (prefixWord ++ tailWord_815174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815175 : List Nat := [1, 1, 4, 1, 3, 1, 2, 2, 5]
def baseStart_815175 : Nat := 118140960795 + 815175 * 2 ^ 59
def prefixEnd_815175 : Nat := 4983230072969 + 3 ^ 40 * 815175 * 2
def baseEnd_815175 : Nat := 372068082247958540234297

theorem tailTrace_815175 : CollatzResearch.WordTrace tailWord_815175 prefixEnd_815175 372068082247958540234297 := by
  unfold tailWord_815175
  simp only [CollatzResearch.WordTrace]
  refine ⟨29731874821767670651174979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19821249881178447100783319 29731874821767670651174979)
  ·
    refine ⟨44597812232651505976762469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29731874821767670651174979 44597812232651505976762469)
    ·
      refine ⟨8362089793622157370642963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44597812232651505976762469 8362089793622157370642963)
      ·
        refine ⟨12543134690433236055964445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8362089793622157370642963 12543134690433236055964445)
        ·
          refine ⟨4703675508912463520986667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12543134690433236055964445 4703675508912463520986667)
          ·
            refine ⟨7055513263368695281480001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4703675508912463520986667 7055513263368695281480001)
            ·
              refine ⟨5291634947526521461110001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7055513263368695281480001 5291634947526521461110001)
              ·
                refine ⟨3968726210644891095832501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5291634947526521461110001 3968726210644891095832501)
                ·
                  refine ⟨372068082247958540234297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3968726210644891095832501 372068082247958540234297)
                  ·
                    rfl

theorem cell20_815175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 5].length) (baseStart_815175 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_815175 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_815175 prefixEnd_815175 := by exact prefixLift 815175
  have htrace : WordTrace (prefixWord ++ tailWord_815175) baseStart_815175 baseEnd_815175 := by
    simpa [prefixWord, tailWord_815175, baseEnd_815175] using wordTrace_append hprefix tailTrace_815175
  have hstable : (prefixWord ++ tailWord_815175).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815175).length < 2 ^ (prefixWord ++ tailWord_815175).sum := by decide
  have hdescent : baseEnd_815175 < baseStart_815175 := by decide
  rcases family_descends (prefixWord ++ tailWord_815175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815192 : List Nat := [2, 1, 2, 2, 1, 4, 3, 2, 3]
def baseStart_815192 : Nat := 118140960795 + 815192 * 2 ^ 59
def prefixEnd_815192 : Nat := 4983230072969 + 3 ^ 40 * 815192 * 2
def baseEnd_815192 : Nat := 372075841511182036667561

theorem tailTrace_815192 : CollatzResearch.WordTrace tailWord_815192 prefixEnd_815192 372075841511182036667561 := by
  unfold tailWord_815192
  simp only [CollatzResearch.WordTrace]
  refine ⟨14866247431353041277271915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19821663241804055036362553 14866247431353041277271915)
  ·
    refine ⟨22299371147029561915907873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14866247431353041277271915 22299371147029561915907873)
    ·
      refine ⟨16724528360272171436930905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22299371147029561915907873 16724528360272171436930905)
      ·
        refine ⟨12543396270204128577698179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16724528360272171436930905 12543396270204128577698179)
        ·
          refine ⟨18815094405306192866547269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12543396270204128577698179 18815094405306192866547269)
          ·
            refine ⟨3527830200994911162477613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18815094405306192866547269 3527830200994911162477613)
            ·
              refine ⟨1322936325373091685929105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3527830200994911162477613 1322936325373091685929105)
              ·
                refine ⟨992202244029818764446829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1322936325373091685929105 992202244029818764446829)
                ·
                  refine ⟨372075841511182036667561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 992202244029818764446829 372075841511182036667561)
                  ·
                    rfl

theorem cell20_815192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 2, 3].length) (baseStart_815192 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_815192 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_815192 prefixEnd_815192 := by exact prefixLift 815192
  have htrace : WordTrace (prefixWord ++ tailWord_815192) baseStart_815192 baseEnd_815192 := by
    simpa [prefixWord, tailWord_815192, baseEnd_815192] using wordTrace_append hprefix tailTrace_815192
  have hstable : (prefixWord ++ tailWord_815192).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815192).length < 2 ^ (prefixWord ++ tailWord_815192).sum := by decide
  have hdescent : baseEnd_815192 < baseStart_815192 := by decide
  rcases family_descends (prefixWord ++ tailWord_815192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815223 : List Nat := [1, 1, 3, 1, 1, 7, 2, 4]
def baseStart_815223 : Nat := 118140960795 + 815223 * 2 ^ 59
def prefixEnd_815223 : Nat := 4983230072969 + 3 ^ 40 * 815223 * 2
def baseEnd_815223 : Nat := 124029996918627902211367

theorem tailTrace_815223 : CollatzResearch.WordTrace tailWord_815223 prefixEnd_815223 124029996918627902211367 := by
  unfold tailWord_815223
  simp only [CollatzResearch.WordTrace]
  refine ⟨29733625525593774848922323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19822417017062516565948215 29733625525593774848922323)
  ·
    refine ⟨44600438288390662273383485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29733625525593774848922323 44600438288390662273383485)
    ·
      refine ⟨16725164358146498352518807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44600438288390662273383485 16725164358146498352518807)
      ·
        refine ⟨25087746537219747528778211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16725164358146498352518807 25087746537219747528778211)
        ·
          refine ⟨37631619805829621293167317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25087746537219747528778211 37631619805829621293167317)
          ·
            refine ⟨881991089199131749058609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 37631619805829621293167317 881991089199131749058609)
            ·
              refine ⟨661493316899348811793957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 881991089199131749058609 661493316899348811793957)
              ·
                refine ⟨124029996918627902211367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 661493316899348811793957 124029996918627902211367)
                ·
                  rfl

theorem cell20_815223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 2, 4].length) (baseStart_815223 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_815223 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_815223 prefixEnd_815223 := by exact prefixLift 815223
  have htrace : WordTrace (prefixWord ++ tailWord_815223) baseStart_815223 baseEnd_815223 := by
    simpa [prefixWord, tailWord_815223, baseEnd_815223] using wordTrace_append hprefix tailTrace_815223
  have hstable : (prefixWord ++ tailWord_815223).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815223).length < 2 ^ (prefixWord ++ tailWord_815223).sum := by decide
  have hdescent : baseEnd_815223 < baseStart_815223 := by decide
  rcases family_descends (prefixWord ++ tailWord_815223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815251 : List Nat := [1, 1, 1, 2, 1, 2, 3, 6, 3]
def baseStart_815251 : Nat := 118140960795 + 815251 * 2 ^ 59
def prefixEnd_815251 : Nat := 4983230072969 + 3 ^ 40 * 815251 * 2
def baseEnd_815251 : Nat := 372102770718840053700653

theorem tailTrace_815251 : CollatzResearch.WordTrace tailWord_815251 prefixEnd_815251 372102770718840053700653 := by
  unfold tailWord_815251
  simp only [CollatzResearch.WordTrace]
  refine ⟨29734646769492335630941607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19823097846328223753961071 29734646769492335630941607)
  ·
    refine ⟨44601970154238503446412411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29734646769492335630941607 44601970154238503446412411)
    ·
      refine ⟨66902955231357755169618617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44601970154238503446412411 66902955231357755169618617)
      ·
        refine ⟨50177216423518316377213963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66902955231357755169618617 50177216423518316377213963)
        ·
          refine ⟨75265824635277474565820945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50177216423518316377213963 75265824635277474565820945)
          ·
            refine ⟨56449368476458105924365709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75265824635277474565820945 56449368476458105924365709)
            ·
              refine ⟨21168513178671789721637141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56449368476458105924365709 21168513178671789721637141)
              ·
                refine ⟨992274055250240143201741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21168513178671789721637141 992274055250240143201741)
                ·
                  refine ⟨372102770718840053700653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 992274055250240143201741 372102770718840053700653)
                  ·
                    rfl

theorem cell20_815251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 6, 3].length) (baseStart_815251 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_815251 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_815251 prefixEnd_815251 := by exact prefixLift 815251
  have htrace : WordTrace (prefixWord ++ tailWord_815251) baseStart_815251 baseEnd_815251 := by
    simpa [prefixWord, tailWord_815251, baseEnd_815251] using wordTrace_append hprefix tailTrace_815251
  have hstable : (prefixWord ++ tailWord_815251).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815251).length < 2 ^ (prefixWord ++ tailWord_815251).sum := by decide
  have hdescent : baseEnd_815251 < baseStart_815251 := by decide
  rcases family_descends (prefixWord ++ tailWord_815251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815306 : List Nat := [3, 1, 2, 1, 3, 1, 4, 2, 3]
def baseStart_815306 : Nat := 118140960795 + 815306 * 2 ^ 59
def prefixEnd_815306 : Nat := 4983230072969 + 3 ^ 40 * 815306 * 2
def baseEnd_815306 : Nat := 372127874217504306867095

theorem tailTrace_815306 : CollatzResearch.WordTrace tailWord_815306 prefixEnd_815306 372127874217504306867095 := by
  unfold tailWord_815306
  simp only [CollatzResearch.WordTrace]
  refine ⟨7434163196073270006048443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19824435189528720016129181 7434163196073270006048443)
  ·
    refine ⟨11151244794109905009072665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7434163196073270006048443 11151244794109905009072665)
    ·
      refine ⟨8363433595582428756804499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11151244794109905009072665 8363433595582428756804499)
      ·
        refine ⟨12545150393373643135206749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8363433595582428756804499 12545150393373643135206749)
        ·
          refine ⟨4704431397515116175702531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12545150393373643135206749 4704431397515116175702531)
          ·
            refine ⟨7056647096272674263553797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4704431397515116175702531 7056647096272674263553797)
            ·
              refine ⟨1323121330551126424416337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7056647096272674263553797 1323121330551126424416337)
              ·
                refine ⟨992340997913344818312253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1323121330551126424416337 992340997913344818312253)
                ·
                  refine ⟨372127874217504306867095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 992340997913344818312253 372127874217504306867095)
                  ·
                    rfl

theorem cell20_815306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 2, 3].length) (baseStart_815306 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_815306 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_815306 prefixEnd_815306 := by exact prefixLift 815306
  have htrace : WordTrace (prefixWord ++ tailWord_815306) baseStart_815306 baseEnd_815306 := by
    simpa [prefixWord, tailWord_815306, baseEnd_815306] using wordTrace_append hprefix tailTrace_815306
  have hstable : (prefixWord ++ tailWord_815306).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815306).length < 2 ^ (prefixWord ++ tailWord_815306).sum := by decide
  have hdescent : baseEnd_815306 < baseStart_815306 := by decide
  rcases family_descends (prefixWord ++ tailWord_815306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815320 : List Nat := [2, 1, 2, 2, 4, 1, 3, 5]
def baseStart_815320 : Nat := 118140960795 + 815320 * 2 ^ 59
def prefixEnd_815320 : Nat := 4983230072969 + 3 ^ 40 * 815320 * 2
def baseEnd_815320 : Nat := 124044754732994160133457

theorem tailTrace_815320 : CollatzResearch.WordTrace tailWord_815320 prefixEnd_815320 124044754732994160133457 := by
  unfold tailWord_815320
  simp only [CollatzResearch.WordTrace]
  refine ⟨14868581703121180207601707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19824775604161573610135609 14868581703121180207601707)
  ·
    refine ⟨22302872554681770311402561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14868581703121180207601707 22302872554681770311402561)
    ·
      refine ⟨16727154416011327733551921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22302872554681770311402561 16727154416011327733551921)
      ·
        refine ⟨12545365812008495800163941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16727154416011327733551921 12545365812008495800163941)
        ·
          refine ⟨2352256089751592962530739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12545365812008495800163941 2352256089751592962530739)
          ·
            refine ⟨3528384134627389443796109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2352256089751592962530739 3528384134627389443796109)
            ·
              refine ⟨1323144050485271041423541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3528384134627389443796109 1323144050485271041423541)
              ·
                refine ⟨124044754732994160133457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1323144050485271041423541 124044754732994160133457)
                ·
                  rfl

theorem cell20_815320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 5].length) (baseStart_815320 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_815320 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_815320 prefixEnd_815320 := by exact prefixLift 815320
  have htrace : WordTrace (prefixWord ++ tailWord_815320) baseStart_815320 baseEnd_815320 := by
    simpa [prefixWord, tailWord_815320, baseEnd_815320] using wordTrace_append hprefix tailTrace_815320
  have hstable : (prefixWord ++ tailWord_815320).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815320).length < 2 ^ (prefixWord ++ tailWord_815320).sum := by decide
  have hdescent : baseEnd_815320 < baseStart_815320 := by decide
  rcases family_descends (prefixWord ++ tailWord_815320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815358 : List Nat := [4, 2, 2, 1, 1, 1, 9]
def baseStart_815358 : Nat := 118140960795 + 815358 * 2 ^ 59
def prefixEnd_815358 : Nat := 4983230072969 + 3 ^ 40 * 815358 * 2
def baseEnd_815358 : Nat := 41350178714935915237061

theorem tailTrace_815358 : CollatzResearch.WordTrace tailWord_815358 prefixEnd_815358 41350178714935915237061 := by
  unfold tailWord_815358
  simp only [CollatzResearch.WordTrace]
  refine ⟨3717318672513086613135841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19825699586736461936724485 3717318672513086613135841)
  ·
    refine ⟨2787989004384814959851881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3717318672513086613135841 2787989004384814959851881)
    ·
      refine ⟨2090991753288611219888911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2787989004384814959851881 2090991753288611219888911)
      ·
        refine ⟨3136487629932916829833367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2090991753288611219888911 3136487629932916829833367)
        ·
          refine ⟨4704731444899375244750051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3136487629932916829833367 4704731444899375244750051)
          ·
            refine ⟨7057097167349062867125077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4704731444899375244750051 7057097167349062867125077)
            ·
              refine ⟨41350178714935915237061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7057097167349062867125077 41350178714935915237061)
              ·
                rfl

theorem cell20_815358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 9].length) (baseStart_815358 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_815358 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_815358 prefixEnd_815358 := by exact prefixLift 815358
  have htrace : WordTrace (prefixWord ++ tailWord_815358) baseStart_815358 baseEnd_815358 := by
    simpa [prefixWord, tailWord_815358, baseEnd_815358] using wordTrace_append hprefix tailTrace_815358
  have hstable : (prefixWord ++ tailWord_815358).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815358).length < 2 ^ (prefixWord ++ tailWord_815358).sum := by decide
  have hdescent : baseEnd_815358 < baseStart_815358 := by decide
  rcases family_descends (prefixWord ++ tailWord_815358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815365 : List Nat := [1, 3, 1, 1, 2, 1, 2, 6, 3]
def baseStart_815365 : Nat := 118140960795 + 815365 * 2 ^ 59
def prefixEnd_815365 : Nat := 4983230072969 + 3 ^ 40 * 815365 * 2
def baseEnd_815365 : Nat := 372154803425162323900187

theorem tailTrace_815365 : CollatzResearch.WordTrace tailWord_815365 prefixEnd_815365 372154803425162323900187 := by
  unfold tailWord_815365
  simp only [CollatzResearch.WordTrace]
  refine ⟨29738804691079333100591549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19825869794052888733727699 29738804691079333100591549)
  ·
    refine ⟨11152051759154749912721831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29738804691079333100591549 11152051759154749912721831)
    ·
      refine ⟨16728077638732124869082747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11152051759154749912721831 16728077638732124869082747)
      ·
        refine ⟨25092116458098187303624121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16728077638732124869082747 25092116458098187303624121)
        ·
          refine ⟨18819087343573640477718091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25092116458098187303624121 18819087343573640477718091)
          ·
            refine ⟨28228631015360460716577137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18819087343573640477718091 28228631015360460716577137)
            ·
              refine ⟨21171473261520345537432853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28228631015360460716577137 21171473261520345537432853)
              ·
                refine ⟨992412809133766197067165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21171473261520345537432853 992412809133766197067165)
                ·
                  refine ⟨372154803425162323900187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 992412809133766197067165 372154803425162323900187)
                  ·
                    rfl

theorem cell20_815365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 6, 3].length) (baseStart_815365 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_815365 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_815365 prefixEnd_815365 := by exact prefixLift 815365
  have htrace : WordTrace (prefixWord ++ tailWord_815365) baseStart_815365 baseEnd_815365 := by
    simpa [prefixWord, tailWord_815365, baseEnd_815365] using wordTrace_append hprefix tailTrace_815365
  have hstable : (prefixWord ++ tailWord_815365).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815365).length < 2 ^ (prefixWord ++ tailWord_815365).sum := by decide
  have hdescent : baseEnd_815365 < baseStart_815365 := by decide
  rcases family_descends (prefixWord ++ tailWord_815365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815368 : List Nat := [2, 1, 3, 2, 3, 1, 2, 4, 2]
def baseStart_815368 : Nat := 118140960795 + 815368 * 2 ^ 59
def prefixEnd_815368 : Nat := 4983230072969 + 3 ^ 40 * 815368 * 2
def baseEnd_815368 : Nat := 372156172706907646800175

theorem tailTrace_815368 : CollatzResearch.WordTrace tailWord_815368 prefixEnd_815368 372156172706907646800175 := by
  unfold tailWord_815368
  simp only [CollatzResearch.WordTrace]
  refine ⟨14869457055034232306475379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19825942740045643075300505 14869457055034232306475379)
  ·
    refine ⟨22304185582551348459713069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14869457055034232306475379 22304185582551348459713069)
    ·
      refine ⟨8364069593456755672392401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22304185582551348459713069 8364069593456755672392401)
      ·
        refine ⟨6273052195092566754294301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8364069593456755672392401 6273052195092566754294301)
        ·
          refine ⟨2352394573159712532860363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6273052195092566754294301 2352394573159712532860363)
          ·
            refine ⟨3528591859739568799290545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2352394573159712532860363 3528591859739568799290545)
            ·
              refine ⟨2646443894804676599467909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3528591859739568799290545 2646443894804676599467909)
              ·
                refine ⟨496208230275876862400233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2646443894804676599467909 496208230275876862400233)
                ·
                  refine ⟨372156172706907646800175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 496208230275876862400233 372156172706907646800175)
                  ·
                    rfl

theorem cell20_815368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 4, 2].length) (baseStart_815368 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_815368 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_815368 prefixEnd_815368 := by exact prefixLift 815368
  have htrace : WordTrace (prefixWord ++ tailWord_815368) baseStart_815368 baseEnd_815368 := by
    simpa [prefixWord, tailWord_815368, baseEnd_815368] using wordTrace_append hprefix tailTrace_815368
  have hstable : (prefixWord ++ tailWord_815368).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815368).length < 2 ^ (prefixWord ++ tailWord_815368).sum := by decide
  have hdescent : baseEnd_815368 < baseStart_815368 := by decide
  rcases family_descends (prefixWord ++ tailWord_815368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815396 : List Nat := [2, 3, 1, 3, 1, 3, 1, 6]
def baseStart_815396 : Nat := 118140960795 + 815396 * 2 ^ 59
def prefixEnd_815396 : Nat := 4983230072969 + 3 ^ 40 * 815396 * 2
def baseEnd_815396 : Nat := 124056317556621331288909

theorem tailTrace_815396 : CollatzResearch.WordTrace tailWord_815396 prefixEnd_815396 124056317556621331288909 := by
  unfold tailWord_815396
  simp only [CollatzResearch.WordTrace]
  refine ⟨14869967676983512697485021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19826623569311350263313361 14869967676983512697485021)
  ·
    refine ⟨5576237878868817261556883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14869967676983512697485021 5576237878868817261556883)
    ·
      refine ⟨8364356818303225892335325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5576237878868817261556883 8364356818303225892335325)
      ·
        refine ⟨3136633806863709709625747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8364356818303225892335325 3136633806863709709625747)
        ·
          refine ⟨4704950710295564564438621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3136633806863709709625747 4704950710295564564438621)
          ·
            refine ⟨1764356516360836711664483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4704950710295564564438621 1764356516360836711664483)
            ·
              refine ⟨2646534774541255067496725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1764356516360836711664483 2646534774541255067496725)
              ·
                refine ⟨124056317556621331288909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2646534774541255067496725 124056317556621331288909)
                ·
                  rfl

theorem cell20_815396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 6].length) (baseStart_815396 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_815396 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_815396 prefixEnd_815396 := by exact prefixLift 815396
  have htrace : WordTrace (prefixWord ++ tailWord_815396) baseStart_815396 baseEnd_815396 := by
    simpa [prefixWord, tailWord_815396, baseEnd_815396] using wordTrace_append hprefix tailTrace_815396
  have hstable : (prefixWord ++ tailWord_815396).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815396).length < 2 ^ (prefixWord ++ tailWord_815396).sum := by decide
  have hdescent : baseEnd_815396 < baseStart_815396 := by decide
  rcases family_descends (prefixWord ++ tailWord_815396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815402 : List Nat := [3, 1, 4, 2, 2, 2, 1, 3, 2]
def baseStart_815402 : Nat := 118140960795 + 815402 * 2 ^ 59
def prefixEnd_815402 : Nat := 4983230072969 + 3 ^ 40 * 815402 * 2
def baseEnd_815402 : Nat := 372171691233354639666703

theorem tailTrace_815402 : CollatzResearch.WordTrace tailWord_815402 prefixEnd_815402 372171691233354639666703 := by
  unfold tailWord_815402
  simp only [CollatzResearch.WordTrace]
  refine ⟨7435038547986322104922115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19826769461296858946458973 7435038547986322104922115)
  ·
    refine ⟨11152557821979483157383173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7435038547986322104922115 11152557821979483157383173)
    ·
      refine ⟨2091104591621153092009345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11152557821979483157383173 2091104591621153092009345)
      ·
        refine ⟨1568328443715864819007009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2091104591621153092009345 1568328443715864819007009)
        ·
          refine ⟨1176246332786898614255257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1568328443715864819007009 1176246332786898614255257)
          ·
            refine ⟨882184749590173960691443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1176246332786898614255257 882184749590173960691443)
            ·
              refine ⟨1323277124385260941037165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 882184749590173960691443 1323277124385260941037165)
              ·
                refine ⟨496228921644472852888937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1323277124385260941037165 496228921644472852888937)
                ·
                  refine ⟨372171691233354639666703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 496228921644472852888937 372171691233354639666703)
                  ·
                    rfl

theorem cell20_815402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 3, 2].length) (baseStart_815402 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_815402 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_815402 prefixEnd_815402 := by exact prefixLift 815402
  have htrace : WordTrace (prefixWord ++ tailWord_815402) baseStart_815402 baseEnd_815402 := by
    simpa [prefixWord, tailWord_815402, baseEnd_815402] using wordTrace_append hprefix tailTrace_815402
  have hstable : (prefixWord ++ tailWord_815402).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815402).length < 2 ^ (prefixWord ++ tailWord_815402).sum := by decide
  have hdescent : baseEnd_815402 < baseStart_815402 := by decide
  rcases family_descends (prefixWord ++ tailWord_815402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815427 : List Nat := [1, 1, 1, 3, 1, 3, 2, 6, 2]
def baseStart_815427 : Nat := 118140960795 + 815427 * 2 ^ 59
def prefixEnd_815427 : Nat := 4983230072969 + 3 ^ 40 * 815427 * 2
def baseEnd_815427 : Nat := 372183101914565663833267

theorem tailTrace_815427 : CollatzResearch.WordTrace tailWord_815427 prefixEnd_815427 372183101914565663833267 := by
  unfold tailWord_815427
  simp only [CollatzResearch.WordTrace]
  refine ⟨29741066016854717689348535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19827377344569811792899023 29741066016854717689348535)
  ·
    refine ⟨44611599025282076534022803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29741066016854717689348535 44611599025282076534022803)
    ·
      refine ⟨66917398537923114801034205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44611599025282076534022803 66917398537923114801034205)
      ·
        refine ⟨25094024451721168050387827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66917398537923114801034205 25094024451721168050387827)
        ·
          refine ⟨37641036677581752075581741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25094024451721168050387827 37641036677581752075581741)
          ·
            refine ⟨14115388754093157028343153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37641036677581752075581741 14115388754093157028343153)
            ·
              refine ⟨10586541565569867771257365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14115388754093157028343153 10586541565569867771257365)
              ·
                refine ⟨496244135886087551777689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10586541565569867771257365 496244135886087551777689)
                ·
                  refine ⟨372183101914565663833267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 496244135886087551777689 372183101914565663833267)
                  ·
                    rfl

theorem cell20_815427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 6, 2].length) (baseStart_815427 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_815427 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_815427 prefixEnd_815427 := by exact prefixLift 815427
  have htrace : WordTrace (prefixWord ++ tailWord_815427) baseStart_815427 baseEnd_815427 := by
    simpa [prefixWord, tailWord_815427, baseEnd_815427] using wordTrace_append hprefix tailTrace_815427
  have hstable : (prefixWord ++ tailWord_815427).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815427).length < 2 ^ (prefixWord ++ tailWord_815427).sum := by decide
  have hdescent : baseEnd_815427 < baseStart_815427 := by decide
  rcases family_descends (prefixWord ++ tailWord_815427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815455 : List Nat := [1, 1, 2, 3, 1, 2, 4, 6]
def baseStart_815455 : Nat := 118140960795 + 815455 * 2 ^ 59
def prefixEnd_815455 : Nat := 4983230072969 + 3 ^ 40 * 815455 * 2
def baseEnd_815455 : Nat := 124065293959174003633273

theorem tailTrace_815455 : CollatzResearch.WordTrace tailWord_815455 prefixEnd_815455 124065293959174003633273 := by
  unfold tailWord_815455
  simp only [CollatzResearch.WordTrace]
  refine ⟨29742087260753278471367819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19828058173835518980911879 29742087260753278471367819)
  ·
    refine ⟨44613130891129917707051729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29742087260753278471367819 44613130891129917707051729)
    ·
      refine ⟨33459848168347438280288797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44613130891129917707051729 33459848168347438280288797)
      ·
        refine ⟨12547443063130289355108299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33459848168347438280288797 12547443063130289355108299)
        ·
          refine ⟨18821164594695434032662449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12547443063130289355108299 18821164594695434032662449)
          ·
            refine ⟨14115873446021575524496837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18821164594695434032662449 14115873446021575524496837)
            ·
              refine ⟨2646726271129045410843157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14115873446021575524496837 2646726271129045410843157)
              ·
                refine ⟨124065293959174003633273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2646726271129045410843157 124065293959174003633273)
                ·
                  rfl

theorem cell20_815455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 6].length) (baseStart_815455 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_815455 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_815455 prefixEnd_815455 := by exact prefixLift 815455
  have htrace : WordTrace (prefixWord ++ tailWord_815455) baseStart_815455 baseEnd_815455 := by
    simpa [prefixWord, tailWord_815455, baseEnd_815455] using wordTrace_append hprefix tailTrace_815455
  have hstable : (prefixWord ++ tailWord_815455).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815455).length < 2 ^ (prefixWord ++ tailWord_815455).sum := by decide
  have hdescent : baseEnd_815455 < baseStart_815455 := by decide
  rcases family_descends (prefixWord ++ tailWord_815455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815465 : List Nat := [1, 2, 1, 1, 1, 3, 4, 5, 2]
def baseStart_815465 : Nat := 118140960795 + 815465 * 2 ^ 59
def prefixEnd_815465 : Nat := 4983230072969 + 3 ^ 40 * 815465 * 2
def baseEnd_815465 : Nat := 372200446150006420566445

theorem tailTrace_815465 : CollatzResearch.WordTrace tailWord_815465 prefixEnd_815465 372200446150006420566445 := by
  unfold tailWord_815465
  simp only [CollatzResearch.WordTrace]
  refine ⟨29742451990717050179231849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19828301327144700119487899 29742451990717050179231849)
  ·
    refine ⟨22306838993037787634423887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29742451990717050179231849 22306838993037787634423887)
    ·
      refine ⟨33460258489556681451635831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22306838993037787634423887 33460258489556681451635831)
      ·
        refine ⟨50190387734335022177453747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33460258489556681451635831 50190387734335022177453747)
        ·
          refine ⟨75285581601502533266180621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50190387734335022177453747 75285581601502533266180621)
          ·
            refine ⟨28232093100563449974817733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75285581601502533266180621 28232093100563449974817733)
            ·
              refine ⟨5293517456355646870278325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28232093100563449974817733 5293517456355646870278325)
              ·
                refine ⟨496267261533341894088593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5293517456355646870278325 496267261533341894088593)
                ·
                  refine ⟨372200446150006420566445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 496267261533341894088593 372200446150006420566445)
                  ·
                    rfl

theorem cell20_815465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 5, 2].length) (baseStart_815465 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_815465 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_815465 prefixEnd_815465 := by exact prefixLift 815465
  have htrace : WordTrace (prefixWord ++ tailWord_815465) baseStart_815465 baseEnd_815465 := by
    simpa [prefixWord, tailWord_815465, baseEnd_815465] using wordTrace_append hprefix tailTrace_815465
  have hstable : (prefixWord ++ tailWord_815465).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815465).length < 2 ^ (prefixWord ++ tailWord_815465).sum := by decide
  have hdescent : baseEnd_815465 < baseStart_815465 := by decide
  rcases family_descends (prefixWord ++ tailWord_815465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815478 : List Nat := [5, 1, 1, 4, 1, 1, 1, 4, 2]
def baseStart_815478 : Nat := 118140960795 + 815478 * 2 ^ 59
def prefixEnd_815478 : Nat := 4983230072969 + 3 ^ 40 * 815478 * 2
def baseEnd_815478 : Nat := 372206379704236153133059

theorem tailTrace_815478 : CollatzResearch.WordTrace tailWord_815478 prefixEnd_815478 372206379704236153133059 := by
  unfold tailWord_815478
  simp only [CollatzResearch.WordTrace]
  refine ⟨1858932883729372087465943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19828617426446635599636725 1858932883729372087465943)
  ·
    refine ⟨2788399325594058131198915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1858932883729372087465943 2788399325594058131198915)
    ·
      refine ⟨4182598988391087196798373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2788399325594058131198915 4182598988391087196798373)
      ·
        refine ⟨784237310323328849399695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4182598988391087196798373 784237310323328849399695)
        ·
          refine ⟨1176355965484993274099543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 784237310323328849399695 1176355965484993274099543)
          ·
            refine ⟨1764533948227489911149315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1176355965484993274099543 1764533948227489911149315)
            ·
              refine ⟨2646800922341234866723973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1764533948227489911149315 2646800922341234866723973)
              ·
                refine ⟨496275172938981537510745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2646800922341234866723973 496275172938981537510745)
                ·
                  refine ⟨372206379704236153133059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 496275172938981537510745 372206379704236153133059)
                  ·
                    rfl

theorem cell20_815478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 4, 2].length) (baseStart_815478 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_815478 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_815478 prefixEnd_815478 := by exact prefixLift 815478
  have htrace : WordTrace (prefixWord ++ tailWord_815478) baseStart_815478 baseEnd_815478 := by
    simpa [prefixWord, tailWord_815478, baseEnd_815478] using wordTrace_append hprefix tailTrace_815478
  have hstable : (prefixWord ++ tailWord_815478).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815478).length < 2 ^ (prefixWord ++ tailWord_815478).sum := by decide
  have hdescent : baseEnd_815478 < baseStart_815478 := by decide
  rcases family_descends (prefixWord ++ tailWord_815478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815489 : List Nat := [1, 2, 4, 3, 1, 3, 1, 5]
def baseStart_815489 : Nat := 118140960795 + 815489 * 2 ^ 59
def prefixEnd_815489 : Nat := 4983230072969 + 3 ^ 40 * 815489 * 2
def baseEnd_815489 : Nat := 124070466801323001255449

theorem tailTrace_815489 : CollatzResearch.WordTrace tailWord_815489 prefixEnd_815489 124070466801323001255449 := by
  unfold tailWord_815489
  simp only [CollatzResearch.WordTrace]
  refine ⟨29743327342630102278105521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19828884895086734852070347 29743327342630102278105521)
  ·
    refine ⟨22307495506972576708579141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29743327342630102278105521 22307495506972576708579141)
    ·
      refine ⟨4182655407557358132858589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22307495506972576708579141 4182655407557358132858589)
      ·
        refine ⟨1568495777834009299821971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4182655407557358132858589 1568495777834009299821971)
        ·
          refine ⟨2352743666751013949732957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1568495777834009299821971 2352743666751013949732957)
          ·
            refine ⟨882278875031630231149859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2352743666751013949732957 882278875031630231149859)
            ·
              refine ⟨1323418312547445346724789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 882278875031630231149859 1323418312547445346724789)
              ·
                refine ⟨124070466801323001255449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1323418312547445346724789 124070466801323001255449)
                ·
                  rfl

theorem cell20_815489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 5].length) (baseStart_815489 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_815489 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_815489 prefixEnd_815489 := by exact prefixLift 815489
  have htrace : WordTrace (prefixWord ++ tailWord_815489) baseStart_815489 baseEnd_815489 := by
    simpa [prefixWord, tailWord_815489, baseEnd_815489] using wordTrace_append hprefix tailTrace_815489
  have hstable : (prefixWord ++ tailWord_815489).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815489).length < 2 ^ (prefixWord ++ tailWord_815489).sum := by decide
  have hdescent : baseEnd_815489 < baseStart_815489 := by decide
  rcases family_descends (prefixWord ++ tailWord_815489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815520 : List Nat := [2, 1, 1, 4, 1, 4, 2, 3, 2]
def baseStart_815520 : Nat := 118140960795 + 815520 * 2 ^ 59
def prefixEnd_815520 : Nat := 4983230072969 + 3 ^ 40 * 815520 * 2
def baseEnd_815520 : Nat := 372225549648670673732887

theorem tailTrace_815520 : CollatzResearch.WordTrace tailWord_815520 prefixEnd_815520 372225549648670673732887 := by
  unfold tailWord_815520
  simp only [CollatzResearch.WordTrace]
  refine ⟨14872229002758897286242007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19829638670345196381656009 14872229002758897286242007)
  ·
    refine ⟨22308343504138345929363011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14872229002758897286242007 22308343504138345929363011)
    ·
      refine ⟨33462515256207518894044517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22308343504138345929363011 33462515256207518894044517)
      ·
        refine ⟨6274221610538909792633347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33462515256207518894044517 6274221610538909792633347)
        ·
          refine ⟨9411332415808364688950021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6274221610538909792633347 9411332415808364688950021)
          ·
            refine ⟨1764624827964068379178129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9411332415808364688950021 1764624827964068379178129)
            ·
              refine ⟨1323468620973051284383597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1764624827964068379178129 1323468620973051284383597)
              ·
                refine ⟨496300732864894231643849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1323468620973051284383597 496300732864894231643849)
                ·
                  refine ⟨372225549648670673732887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 496300732864894231643849 372225549648670673732887)
                  ·
                    rfl

theorem cell20_815520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 3, 2].length) (baseStart_815520 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_815520 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_815520 prefixEnd_815520 := by exact prefixLift 815520
  have htrace : WordTrace (prefixWord ++ tailWord_815520) baseStart_815520 baseEnd_815520 := by
    simpa [prefixWord, tailWord_815520, baseEnd_815520] using wordTrace_append hprefix tailTrace_815520
  have hstable : (prefixWord ++ tailWord_815520).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815520).length < 2 ^ (prefixWord ++ tailWord_815520).sum := by decide
  have hdescent : baseEnd_815520 < baseStart_815520 := by decide
  rcases family_descends (prefixWord ++ tailWord_815520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815530 : List Nat := [3, 1, 6, 1, 1, 1, 1, 1, 5]
def baseStart_815530 : Nat := 118140960795 + 815530 * 2 ^ 59
def prefixEnd_815530 : Nat := 4983230072969 + 3 ^ 40 * 815530 * 2
def baseEnd_815530 : Nat := 372230113921155083399513

theorem tailTrace_815530 : CollatzResearch.WordTrace tailWord_815530 prefixEnd_815530 372230113921155083399513 := by
  unfold tailWord_815530
  simp only [CollatzResearch.WordTrace]
  refine ⟨7436205683870391570087011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19829881823654377520232029 7436205683870391570087011)
  ·
    refine ⟨11154308525805587355130517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7436205683870391570087011 11154308525805587355130517)
    ·
      refine ⟨522858212147136907271743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 11154308525805587355130517 522858212147136907271743)
      ·
        refine ⟨784287318220705360907615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 522858212147136907271743 784287318220705360907615)
        ·
          refine ⟨1176430977331058041361423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 784287318220705360907615 1176430977331058041361423)
          ·
            refine ⟨1764646465996587062042135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1176430977331058041361423 1764646465996587062042135)
            ·
              refine ⟨2646969698994880593063203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1764646465996587062042135 2646969698994880593063203)
              ·
                refine ⟨3970454548492320889594805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2646969698994880593063203 3970454548492320889594805)
                ·
                  refine ⟨372230113921155083399513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3970454548492320889594805 372230113921155083399513)
                  ·
                    rfl

theorem cell20_815530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 5].length) (baseStart_815530 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_815530 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_815530 prefixEnd_815530 := by exact prefixLift 815530
  have htrace : WordTrace (prefixWord ++ tailWord_815530) baseStart_815530 baseEnd_815530 := by
    simpa [prefixWord, tailWord_815530, baseEnd_815530] using wordTrace_append hprefix tailTrace_815530
  have hstable : (prefixWord ++ tailWord_815530).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815530).length < 2 ^ (prefixWord ++ tailWord_815530).sum := by decide
  have hdescent : baseEnd_815530 < baseStart_815530 := by decide
  rcases family_descends (prefixWord ++ tailWord_815530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815562 : List Nat := [3, 1, 2, 1, 2, 2, 1, 4, 4]
def baseStart_815562 : Nat := 118140960795 + 815562 * 2 ^ 59
def prefixEnd_815562 : Nat := 4983230072969 + 3 ^ 40 * 815562 * 2
def baseEnd_815562 : Nat := 372244719593105194332715

theorem tailTrace_815562 : CollatzResearch.WordTrace tailWord_815562 prefixEnd_815562 372244719593105194332715 := by
  unfold tailWord_815562
  simp only [CollatzResearch.WordTrace]
  refine ⟨7436497467841408936378235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19830659914243757163675293 7436497467841408936378235)
  ·
    refine ⟨11154746201762113404567353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7436497467841408936378235 11154746201762113404567353)
    ·
      refine ⟨8366059651321585053425515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11154746201762113404567353 8366059651321585053425515)
      ·
        refine ⟨12549089476982377580138273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8366059651321585053425515 12549089476982377580138273)
        ·
          refine ⟨9411817107736783185103705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12549089476982377580138273 9411817107736783185103705)
          ·
            refine ⟨7058862830802587388827779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9411817107736783185103705 7058862830802587388827779)
            ·
              refine ⟨10588294246203881083241669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7058862830802587388827779 10588294246203881083241669)
              ·
                refine ⟨1985305171163227703107813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10588294246203881083241669 1985305171163227703107813)
                ·
                  refine ⟨372244719593105194332715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1985305171163227703107813 372244719593105194332715)
                  ·
                    rfl

theorem cell20_815562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 4, 4].length) (baseStart_815562 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_815562 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_815562 prefixEnd_815562 := by exact prefixLift 815562
  have htrace : WordTrace (prefixWord ++ tailWord_815562) baseStart_815562 baseEnd_815562 := by
    simpa [prefixWord, tailWord_815562, baseEnd_815562] using wordTrace_append hprefix tailTrace_815562
  have hstable : (prefixWord ++ tailWord_815562).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815562).length < 2 ^ (prefixWord ++ tailWord_815562).sum := by decide
  have hdescent : baseEnd_815562 < baseStart_815562 := by decide
  rcases family_descends (prefixWord ++ tailWord_815562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815596 : List Nat := [2, 2, 1, 1, 2, 1, 7, 2, 2]
def baseStart_815596 : Nat := 118140960795 + 815596 * 2 ^ 59
def prefixEnd_815596 : Nat := 4983230072969 + 3 ^ 40 * 815596 * 2
def baseEnd_815596 : Nat := 372260238119552187199243

theorem tailTrace_815596 : CollatzResearch.WordTrace tailWord_815596 prefixEnd_815596 372260238119552187199243 := by
  unfold tailWord_815596
  simp only [CollatzResearch.WordTrace]
  refine ⟨14873614976621229776125321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19831486635494973034833761 14873614976621229776125321)
  ·
    refine ⟨11155211232465922332093991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14873614976621229776125321 11155211232465922332093991)
    ·
      refine ⟨16732816848698883498140987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11155211232465922332093991 16732816848698883498140987)
      ·
        refine ⟨25099225273048325247211481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16732816848698883498140987 25099225273048325247211481)
        ·
          refine ⟨18824418954786243935408611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25099225273048325247211481 18824418954786243935408611)
          ·
            refine ⟨28236628432179365903112917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18824418954786243935408611 28236628432179365903112917)
            ·
              refine ⟨661795978879203888354209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 28236628432179365903112917 661795978879203888354209)
              ·
                refine ⟨496346984159402916265657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 661795978879203888354209 496346984159402916265657)
                ·
                  refine ⟨372260238119552187199243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 496346984159402916265657 372260238119552187199243)
                  ·
                    rfl

theorem cell20_815596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 7, 2, 2].length) (baseStart_815596 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_815596 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_815596 prefixEnd_815596 := by exact prefixLift 815596
  have htrace : WordTrace (prefixWord ++ tailWord_815596) baseStart_815596 baseEnd_815596 := by
    simpa [prefixWord, tailWord_815596, baseEnd_815596] using wordTrace_append hprefix tailTrace_815596
  have hstable : (prefixWord ++ tailWord_815596).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815596).length < 2 ^ (prefixWord ++ tailWord_815596).sum := by decide
  have hdescent : baseEnd_815596 < baseStart_815596 := by decide
  rcases family_descends (prefixWord ++ tailWord_815596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815645 : List Nat := [1, 4, 2, 2, 1, 10]
def baseStart_815645 : Nat := 118140960795 + 815645 * 2 ^ 59
def prefixEnd_815645 : Nat := 4983230072969 + 3 ^ 40 * 815645 * 2
def baseEnd_815645 : Nat := 13788244557582436835767

theorem tailTrace_815645 : CollatzResearch.WordTrace tailWord_815645 prefixEnd_815645 13788244557582436835767 := by
  unfold tailWord_815645
  simp only [CollatzResearch.WordTrace]
  refine ⟨29749017130064940920784389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19832678086709960613856259 29749017130064940920784389)
  ·
    refine ⟨5577940711887176422647073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29749017130064940920784389 5577940711887176422647073)
    ·
      refine ⟨4183455533915382316985305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5577940711887176422647073 4183455533915382316985305)
      ·
        refine ⟨3137591650436536737738979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4183455533915382316985305 3137591650436536737738979)
        ·
          refine ⟨4706387475654805106608469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3137591650436536737738979 4706387475654805106608469)
          ·
            refine ⟨13788244557582436835767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4706387475654805106608469 13788244557582436835767)
            ·
              rfl

theorem cell20_815645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 10].length) (baseStart_815645 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_815645 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_815645 prefixEnd_815645 := by exact prefixLift 815645
  have htrace : WordTrace (prefixWord ++ tailWord_815645) baseStart_815645 baseEnd_815645 := by
    simpa [prefixWord, tailWord_815645, baseEnd_815645] using wordTrace_append hprefix tailTrace_815645
  have hstable : (prefixWord ++ tailWord_815645).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815645).length < 2 ^ (prefixWord ++ tailWord_815645).sum := by decide
  have hdescent : baseEnd_815645 < baseStart_815645 := by decide
  rcases family_descends (prefixWord ++ tailWord_815645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815651 : List Nat := [1, 1, 1, 4, 4, 3, 2, 2, 2]
def baseStart_815651 : Nat := 118140960795 + 815651 * 2 ^ 59
def prefixEnd_815651 : Nat := 4983230072969 + 3 ^ 40 * 815651 * 2
def baseEnd_815651 : Nat := 372285341618216440365685

theorem tailTrace_815651 : CollatzResearch.WordTrace tailWord_815651 prefixEnd_815651 372285341618216440365685 := by
  unfold tailWord_815651
  simp only [CollatzResearch.WordTrace]
  refine ⟨29749235968043203945502807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19832823978695469297001871 29749235968043203945502807)
  ·
    refine ⟨44623853952064805918254211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29749235968043203945502807 44623853952064805918254211)
    ·
      refine ⟨66935780928097208877381317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44623853952064805918254211 66935780928097208877381317)
      ·
        refine ⟨12550458924018226664508997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66935780928097208877381317 12550458924018226664508997)
        ·
          refine ⟨2353211048253417499595437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12550458924018226664508997 2353211048253417499595437)
          ·
            refine ⟨882454143095031562348289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2353211048253417499595437 882454143095031562348289)
            ·
              refine ⟨661840607321273671761217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 882454143095031562348289 661840607321273671761217)
              ·
                refine ⟨496380455490955253820913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 661840607321273671761217 496380455490955253820913)
                ·
                  refine ⟨372285341618216440365685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 496380455490955253820913 372285341618216440365685)
                  ·
                    rfl

theorem cell20_815651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 2, 2, 2].length) (baseStart_815651 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_815651 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_815651 prefixEnd_815651 := by exact prefixLift 815651
  have htrace : WordTrace (prefixWord ++ tailWord_815651) baseStart_815651 baseEnd_815651 := by
    simpa [prefixWord, tailWord_815651, baseEnd_815651] using wordTrace_append hprefix tailTrace_815651
  have hstable : (prefixWord ++ tailWord_815651).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815651).length < 2 ^ (prefixWord ++ tailWord_815651).sum := by decide
  have hdescent : baseEnd_815651 < baseStart_815651 := by decide
  rcases family_descends (prefixWord ++ tailWord_815651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815659 : List Nat := [1, 1, 1, 1, 2, 1, 3, 2, 8]
def baseStart_815659 : Nat := 118140960795 + 815659 * 2 ^ 59
def prefixEnd_815659 : Nat := 4983230072969 + 3 ^ 40 * 815659 * 2
def baseEnd_815659 : Nat := 372288993036203968098985

theorem tailTrace_815659 : CollatzResearch.WordTrace tailWord_815659 prefixEnd_815659 372288993036203968098985 := by
  unfold tailWord_815659
  simp only [CollatzResearch.WordTrace]
  refine ⟨29749527752014221311794031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19833018501342814207862687 29749527752014221311794031)
  ·
    refine ⟨44624291628021331967691047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29749527752014221311794031 44624291628021331967691047)
    ·
      refine ⟨66936437442031997951536571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44624291628021331967691047 66936437442031997951536571)
      ·
        refine ⟨100404656163047996927304857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66936437442031997951536571 100404656163047996927304857)
        ·
          refine ⟨75303492122285997695478643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100404656163047996927304857 75303492122285997695478643)
          ·
            refine ⟨112955238183428996543217965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75303492122285997695478643 112955238183428996543217965)
            ·
              refine ⟨42358214318785873703706737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112955238183428996543217965 42358214318785873703706737)
              ·
                refine ⟨31768660739089405277780053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42358214318785873703706737 31768660739089405277780053)
                ·
                  refine ⟨372288993036203968098985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31768660739089405277780053 372288993036203968098985)
                  ·
                    rfl

theorem cell20_815659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 8].length) (baseStart_815659 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_815659 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_815659 prefixEnd_815659 := by exact prefixLift 815659
  have htrace : WordTrace (prefixWord ++ tailWord_815659) baseStart_815659 baseEnd_815659 := by
    simpa [prefixWord, tailWord_815659, baseEnd_815659] using wordTrace_append hprefix tailTrace_815659
  have hstable : (prefixWord ++ tailWord_815659).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815659).length < 2 ^ (prefixWord ++ tailWord_815659).sum := by decide
  have hdescent : baseEnd_815659 < baseStart_815659 := by decide
  rcases family_descends (prefixWord ++ tailWord_815659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815669 : List Nat := [1, 3, 3, 1, 1, 2, 1, 5, 3]
def baseStart_815669 : Nat := 118140960795 + 815669 * 2 ^ 59
def prefixEnd_815669 : Nat := 4983230072969 + 3 ^ 40 * 815669 * 2
def baseEnd_815669 : Nat := 372293557308688377765611

theorem tailTrace_815669 : CollatzResearch.WordTrace tailWord_815669 prefixEnd_815669 372293557308688377765611 := by
  unfold tailWord_815669
  simp only [CollatzResearch.WordTrace]
  refine ⟨29749892481977993019658061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19833261654651995346438707 29749892481977993019658061)
  ·
    refine ⟨11156209680741747382371773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29749892481977993019658061 11156209680741747382371773)
    ·
      refine ⟨4183578630278155268389415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11156209680741747382371773 4183578630278155268389415)
      ·
        refine ⟨6275367945417232902584123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4183578630278155268389415 6275367945417232902584123)
        ·
          refine ⟨9413051918125849353876185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6275367945417232902584123 9413051918125849353876185)
          ·
            refine ⟨7059788938594387015407139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9413051918125849353876185 7059788938594387015407139)
            ·
              refine ⟨10589683407891580523110709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7059788938594387015407139 10589683407891580523110709)
              ·
                refine ⟨992782819489835674041629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10589683407891580523110709 992782819489835674041629)
                ·
                  refine ⟨372293557308688377765611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 992782819489835674041629 372293557308688377765611)
                  ·
                    rfl

theorem cell20_815669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 5, 3].length) (baseStart_815669 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_815669 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_815669 prefixEnd_815669 := by exact prefixLift 815669
  have htrace : WordTrace (prefixWord ++ tailWord_815669) baseStart_815669 baseEnd_815669 := by
    simpa [prefixWord, tailWord_815669, baseEnd_815669] using wordTrace_append hprefix tailTrace_815669
  have hstable : (prefixWord ++ tailWord_815669).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815669).length < 2 ^ (prefixWord ++ tailWord_815669).sum := by decide
  have hdescent : baseEnd_815669 < baseStart_815669 := by decide
  rcases family_descends (prefixWord ++ tailWord_815669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815676 : List Nat := [2, 2, 2, 2, 3, 1, 1, 1, 6]
def baseStart_815676 : Nat := 118140960795 + 815676 * 2 ^ 59
def prefixEnd_815676 : Nat := 4983230072969 + 3 ^ 40 * 815676 * 2
def baseEnd_815676 : Nat := 372296752299427464532249

theorem tailTrace_815676 : CollatzResearch.WordTrace tailWord_815676 prefixEnd_815676 372296752299427464532249 := by
  unfold tailWord_815676
  simp only [CollatzResearch.WordTrace]
  refine ⟨14875073896476316607581441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19833431861968422143441921 14875073896476316607581441)
  ·
    refine ⟨11156305422357237455686081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14875073896476316607581441 11156305422357237455686081)
    ·
      refine ⟨8367229066767928091764561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11156305422357237455686081 8367229066767928091764561)
      ·
        refine ⟨6275421800075946068823421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8367229066767928091764561 6275421800075946068823421)
        ·
          refine ⟨2353283175028479775808783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6275421800075946068823421 2353283175028479775808783)
          ·
            refine ⟨3529924762542719663713175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2353283175028479775808783 3529924762542719663713175)
            ·
              refine ⟨5294887143814079495569763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3529924762542719663713175 5294887143814079495569763)
              ·
                refine ⟨7942330715721119243354645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5294887143814079495569763 7942330715721119243354645)
                ·
                  refine ⟨372296752299427464532249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7942330715721119243354645 372296752299427464532249)
                  ·
                    rfl

theorem cell20_815676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 6].length) (baseStart_815676 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_815676 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_815676 prefixEnd_815676 := by exact prefixLift 815676
  have htrace : WordTrace (prefixWord ++ tailWord_815676) baseStart_815676 baseEnd_815676 := by
    simpa [prefixWord, tailWord_815676, baseEnd_815676] using wordTrace_append hprefix tailTrace_815676
  have hstable : (prefixWord ++ tailWord_815676).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815676).length < 2 ^ (prefixWord ++ tailWord_815676).sum := by decide
  have hdescent : baseEnd_815676 < baseStart_815676 := by decide
  rcases family_descends (prefixWord ++ tailWord_815676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815734 : List Nat := [5, 1, 1, 2, 3, 2, 2, 4]
def baseStart_815734 : Nat := 118140960795 + 815734 * 2 ^ 59
def prefixEnd_815734 : Nat := 4983230072969 + 3 ^ 40 * 815734 * 2
def baseEnd_815734 : Nat := 124107741693279013532893

theorem tailTrace_815734 : CollatzResearch.WordTrace tailWord_815734 prefixEnd_815734 124107741693279013532893 := by
  unfold tailWord_815734
  simp only [CollatzResearch.WordTrace]
  refine ⟨1859516451671406820048391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19834842151161672747182837 1859516451671406820048391)
  ·
    refine ⟨2789274677507110230072587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1859516451671406820048391 2789274677507110230072587)
    ·
      refine ⟨4183912016260665345108881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2789274677507110230072587 4183912016260665345108881)
      ·
        refine ⟨3137934012195499008831661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4183912016260665345108881 3137934012195499008831661)
        ·
          refine ⟨1176725254573312128311873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3137934012195499008831661 1176725254573312128311873)
          ·
            refine ⟨882543940929984096233905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1176725254573312128311873 882543940929984096233905)
            ·
              refine ⟨661907955697488072175429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 882543940929984096233905 661907955697488072175429)
              ·
                refine ⟨124107741693279013532893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 661907955697488072175429 124107741693279013532893)
                ·
                  rfl

theorem cell20_815734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_815734 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_815734 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_815734 prefixEnd_815734 := by exact prefixLift 815734
  have htrace : WordTrace (prefixWord ++ tailWord_815734) baseStart_815734 baseEnd_815734 := by
    simpa [prefixWord, tailWord_815734, baseEnd_815734] using wordTrace_append hprefix tailTrace_815734
  have hstable : (prefixWord ++ tailWord_815734).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815734).length < 2 ^ (prefixWord ++ tailWord_815734).sum := by decide
  have hdescent : baseEnd_815734 < baseStart_815734 := by decide
  rcases family_descends (prefixWord ++ tailWord_815734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815748 : List Nat := [2, 3, 2, 1, 3, 1, 3, 3, 2]
def baseStart_815748 : Nat := 118140960795 + 815748 * 2 ^ 59
def prefixEnd_815748 : Nat := 4983230072969 + 3 ^ 40 * 815748 * 2
def baseEnd_815748 : Nat := 372329615061315214131955

theorem tailTrace_815748 : CollatzResearch.WordTrace tailWord_815748 prefixEnd_815748 372329615061315214131955 := by
  unfold tailWord_815748
  simp only [CollatzResearch.WordTrace]
  refine ⟨14876386924345894755891949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19835182565794526341189265 14876386924345894755891949)
  ·
    refine ⟨5578645096629710533459481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14876386924345894755891949 5578645096629710533459481)
    ·
      refine ⟨4183983822472282900094611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5578645096629710533459481 4183983822472282900094611)
      ·
        refine ⟨6275975733708424350141917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4183983822472282900094611 6275975733708424350141917)
        ·
          refine ⟨2353490900140659131303219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6275975733708424350141917 2353490900140659131303219)
          ·
            refine ⟨3530236350210988696954829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2353490900140659131303219 3530236350210988696954829)
            ·
              refine ⟨1323838631329120761358061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3530236350210988696954829 1323838631329120761358061)
              ·
                refine ⟨496439486748420285509273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1323838631329120761358061 496439486748420285509273)
                ·
                  refine ⟨372329615061315214131955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 496439486748420285509273 372329615061315214131955)
                  ·
                    rfl

theorem cell20_815748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 3, 2].length) (baseStart_815748 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_815748 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_815748 prefixEnd_815748 := by exact prefixLift 815748
  have htrace : WordTrace (prefixWord ++ tailWord_815748) baseStart_815748 baseEnd_815748 := by
    simpa [prefixWord, tailWord_815748, baseEnd_815748] using wordTrace_append hprefix tailTrace_815748
  have hstable : (prefixWord ++ tailWord_815748).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815748).length < 2 ^ (prefixWord ++ tailWord_815748).sum := by decide
  have hdescent : baseEnd_815748 < baseStart_815748 := by decide
  rcases family_descends (prefixWord ++ tailWord_815748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815776 : List Nat := [2, 1, 1, 4, 4, 1, 2, 5]
def baseStart_815776 : Nat := 118140960795 + 815776 * 2 ^ 59
def prefixEnd_815776 : Nat := 4983230072969 + 3 ^ 40 * 815776 * 2
def baseEnd_815776 : Nat := 124114131674757187066169

theorem tailTrace_815776 : CollatzResearch.WordTrace tailWord_815776 prefixEnd_815776 124114131674757187066169 := by
  unfold tailWord_815776
  simp only [CollatzResearch.WordTrace]
  refine ⟨14876897546295175146901591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19835863395060233529202121 14876897546295175146901591)
  ·
    refine ⟨22315346319442762720352387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14876897546295175146901591 22315346319442762720352387)
    ·
      refine ⟨33473019479164144080528581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22315346319442762720352387 33473019479164144080528581)
      ·
        refine ⟨6276191152343277015099109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33473019479164144080528581 6276191152343277015099109)
        ·
          refine ⟨1176785841064364440331083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6276191152343277015099109 1176785841064364440331083)
          ·
            refine ⟨1765178761596546660496625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1176785841064364440331083 1765178761596546660496625)
            ·
              refine ⟨1323884071197409995372469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1765178761596546660496625 1323884071197409995372469)
              ·
                refine ⟨124114131674757187066169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1323884071197409995372469 124114131674757187066169)
                ·
                  rfl

theorem cell20_815776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 5].length) (baseStart_815776 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_815776 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_815776 prefixEnd_815776 := by exact prefixLift 815776
  have htrace : WordTrace (prefixWord ++ tailWord_815776) baseStart_815776 baseEnd_815776 := by
    simpa [prefixWord, tailWord_815776, baseEnd_815776] using wordTrace_append hprefix tailTrace_815776
  have hstable : (prefixWord ++ tailWord_815776).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815776).length < 2 ^ (prefixWord ++ tailWord_815776).sum := by decide
  have hdescent : baseEnd_815776 < baseStart_815776 := by decide
  rcases family_descends (prefixWord ++ tailWord_815776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815849 : List Nat := [1, 2, 1, 1, 1, 2, 5, 1, 6]
def baseStart_815849 : Nat := 118140960795 + 815849 * 2 ^ 59
def prefixEnd_815849 : Nat := 4983230072969 + 3 ^ 40 * 815849 * 2
def baseEnd_815849 : Nat := 372375714213407751764875

theorem tailTrace_815849 : CollatzResearch.WordTrace tailWord_815849 prefixEnd_815849 372375714213407751764875 := by
  unfold tailWord_815849
  simp only [CollatzResearch.WordTrace]
  refine ⟨29756457621325883761210601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19837638414217255840807067 29756457621325883761210601)
  ·
    refine ⟨22317343215994412820907951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29756457621325883761210601 22317343215994412820907951)
    ·
      refine ⟨33476014823991619231361927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22317343215994412820907951 33476014823991619231361927)
      ·
        refine ⟨50214022235987428847042891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33476014823991619231361927 50214022235987428847042891)
        ·
          refine ⟨75321033353981143270564337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50214022235987428847042891 75321033353981143270564337)
          ·
            refine ⟨56490775015485857452923253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75321033353981143270564337 56490775015485857452923253)
            ·
              refine ⟨5296010157701799136211555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56490775015485857452923253 5296010157701799136211555)
              ·
                refine ⟨7944015236552698704317333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5296010157701799136211555 7944015236552698704317333)
                ·
                  refine ⟨372375714213407751764875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7944015236552698704317333 372375714213407751764875)
                  ·
                    rfl

theorem cell20_815849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 6].length) (baseStart_815849 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_815849 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_815849 prefixEnd_815849 := by exact prefixLift 815849
  have htrace : WordTrace (prefixWord ++ tailWord_815849) baseStart_815849 baseEnd_815849 := by
    simpa [prefixWord, tailWord_815849, baseEnd_815849] using wordTrace_append hprefix tailTrace_815849
  have hstable : (prefixWord ++ tailWord_815849).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815849).length < 2 ^ (prefixWord ++ tailWord_815849).sum := by decide
  have hdescent : baseEnd_815849 < baseStart_815849 := by decide
  rcases family_descends (prefixWord ++ tailWord_815849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815862 : List Nat := [5, 1, 1, 1, 1, 2, 4, 3, 2]
def baseStart_815862 : Nat := 118140960795 + 815862 * 2 ^ 59
def prefixEnd_815862 : Nat := 4983230072969 + 3 ^ 40 * 815862 * 2
def baseEnd_815862 : Nat := 372381647767637484331489

theorem tailTrace_815862 : CollatzResearch.WordTrace tailWord_815862 prefixEnd_815862 372381647767637484331489 := by
  unfold tailWord_815862
  simp only [CollatzResearch.WordTrace]
  refine ⟨1859808235642424186339615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19837954513519191320955893 1859808235642424186339615)
  ·
    refine ⟨2789712353463636279509423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1859808235642424186339615 2789712353463636279509423)
    ·
      refine ⟨4184568530195454419264135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2789712353463636279509423 4184568530195454419264135)
      ·
        refine ⟨6276852795293181628896203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4184568530195454419264135 6276852795293181628896203)
        ·
          refine ⟨9415279192939772443344305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6276852795293181628896203 9415279192939772443344305)
          ·
            refine ⟨7061459394704829332508229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9415279192939772443344305 7061459394704829332508229)
            ·
              refine ⟨1324023636507155499845293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7061459394704829332508229 1324023636507155499845293)
              ·
                refine ⟨496508863690183312441985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1324023636507155499845293 496508863690183312441985)
                ·
                  refine ⟨372381647767637484331489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 496508863690183312441985 372381647767637484331489)
                  ·
                    rfl

theorem cell20_815862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 3, 2].length) (baseStart_815862 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_815862 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_815862 prefixEnd_815862 := by exact prefixLift 815862
  have htrace : WordTrace (prefixWord ++ tailWord_815862) baseStart_815862 baseEnd_815862 := by
    simpa [prefixWord, tailWord_815862, baseEnd_815862] using wordTrace_append hprefix tailTrace_815862
  have hstable : (prefixWord ++ tailWord_815862).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815862).length < 2 ^ (prefixWord ++ tailWord_815862).sum := by decide
  have hdescent : baseEnd_815862 < baseStart_815862 := by decide
  rcases family_descends (prefixWord ++ tailWord_815862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815904 : List Nat := [2, 1, 1, 5, 1, 2, 2, 2, 4]
def baseStart_815904 : Nat := 118140960795 + 815904 * 2 ^ 59
def prefixEnd_815904 : Nat := 4983230072969 + 3 ^ 40 * 815904 * 2
def baseEnd_815904 : Nat := 372400817712072004931317

theorem tailTrace_815904 : CollatzResearch.WordTrace tailWord_815904 prefixEnd_815904 372400817712072004931317 := by
  unfold tailWord_815904
  simp only [CollatzResearch.WordTrace]
  refine ⟨14879231818063314077231383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19838975757417752102975177 14879231818063314077231383)
  ·
    refine ⟨22318847727094971115847075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14879231818063314077231383 22318847727094971115847075)
    ·
      refine ⟨33478271590642456673770613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22318847727094971115847075 33478271590642456673770613)
      ·
        refine ⟨3138587961622730313165995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33478271590642456673770613 3138587961622730313165995)
        ·
          refine ⟨4707881942434095469748993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3138587961622730313165995 4707881942434095469748993)
          ·
            refine ⟨3530911456825571602311745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4707881942434095469748993 3530911456825571602311745)
            ·
              refine ⟨2648183592619178701733809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3530911456825571602311745 2648183592619178701733809)
              ·
                refine ⟨1986137694464384026300357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2648183592619178701733809 1986137694464384026300357)
                ·
                  refine ⟨372400817712072004931317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1986137694464384026300357 372400817712072004931317)
                  ·
                    rfl

theorem cell20_815904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 2, 4].length) (baseStart_815904 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_815904 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_815904 prefixEnd_815904 := by exact prefixLift 815904
  have htrace : WordTrace (prefixWord ++ tailWord_815904) baseStart_815904 baseEnd_815904 := by
    simpa [prefixWord, tailWord_815904, baseEnd_815904] using wordTrace_append hprefix tailTrace_815904
  have hstable : (prefixWord ++ tailWord_815904).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815904).length < 2 ^ (prefixWord ++ tailWord_815904).sum := by decide
  have hdescent : baseEnd_815904 < baseStart_815904 := by decide
  rcases family_descends (prefixWord ++ tailWord_815904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_815990 : List Nat := [5, 1, 1, 3, 1, 1, 1, 4, 3]
def baseStart_815990 : Nat := 118140960795 + 815990 * 2 ^ 59
def prefixEnd_815990 : Nat := 4983230072969 + 3 ^ 40 * 815990 * 2
def baseEnd_815990 : Nat := 372440070455437928064299

theorem tailTrace_815990 : CollatzResearch.WordTrace tailWord_815990 prefixEnd_815990 372440070455437928064299 := by
  unfold tailWord_815990
  simp only [CollatzResearch.WordTrace]
  refine ⟨1860100019613441552630839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19841066875876709894728949 1860100019613441552630839)
  ·
    refine ⟨2790150029420162328946259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1860100019613441552630839 2790150029420162328946259)
    ·
      refine ⟨4185225044130243493419389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2790150029420162328946259 4185225044130243493419389)
      ·
        refine ⟨1569459391548841310032271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4185225044130243493419389 1569459391548841310032271)
        ·
          refine ⟨2354189087323261965048407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1569459391548841310032271 2354189087323261965048407)
          ·
            refine ⟨3531283630984892947572611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2354189087323261965048407 3531283630984892947572611)
            ·
              refine ⟨5296925446477339421358917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3531283630984892947572611 5296925446477339421358917)
              ·
                refine ⟨993173521214501141504797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5296925446477339421358917 993173521214501141504797)
                ·
                  refine ⟨372440070455437928064299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 993173521214501141504797 372440070455437928064299)
                  ·
                    rfl

theorem cell20_815990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_815990 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_815990 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_815990 prefixEnd_815990 := by exact prefixLift 815990
  have htrace : WordTrace (prefixWord ++ tailWord_815990) baseStart_815990 baseEnd_815990 := by
    simpa [prefixWord, tailWord_815990, baseEnd_815990] using wordTrace_append hprefix tailTrace_815990
  have hstable : (prefixWord ++ tailWord_815990).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_815990).length < 2 ^ (prefixWord ++ tailWord_815990).sum := by decide
  have hdescent : baseEnd_815990 < baseStart_815990 := by decide
  rcases family_descends (prefixWord ++ tailWord_815990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816049 : List Nat := [1, 2, 2, 4, 3, 1, 1, 1, 5]
def baseStart_816049 : Nat := 118140960795 + 816049 * 2 ^ 59
def prefixEnd_816049 : Nat := 4983230072969 + 3 ^ 40 * 816049 * 2
def baseEnd_816049 : Nat := 372466999663095945097391

theorem tailTrace_816049 : CollatzResearch.WordTrace tailWord_816049 prefixEnd_816049 372466999663095945097391 := by
  unfold tailWord_816049
  simp only [CollatzResearch.WordTrace]
  refine ⟨29763752220601317918491201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19842501480400878612327467 29763752220601317918491201)
  ·
    refine ⟨22322814165450988438868401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29763752220601317918491201 22322814165450988438868401)
    ·
      refine ⟨16742110624088241329151301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22322814165450988438868401 16742110624088241329151301)
      ·
        refine ⟨3139145742016545249215869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16742110624088241329151301 3139145742016545249215869)
        ·
          refine ⟨1177179653256204468455951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3139145742016545249215869 1177179653256204468455951)
          ·
            refine ⟨1765769479884306702683927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1177179653256204468455951 1765769479884306702683927)
            ·
              refine ⟨2648654219826460054025891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1765769479884306702683927 2648654219826460054025891)
              ·
                refine ⟨3972981329739690081038837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2648654219826460054025891 3972981329739690081038837)
                ·
                  refine ⟨372466999663095945097391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3972981329739690081038837 372466999663095945097391)
                  ·
                    rfl

theorem cell20_816049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 5].length) (baseStart_816049 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_816049 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_816049 prefixEnd_816049 := by exact prefixLift 816049
  have htrace : WordTrace (prefixWord ++ tailWord_816049) baseStart_816049 baseEnd_816049 := by
    simpa [prefixWord, tailWord_816049, baseEnd_816049] using wordTrace_append hprefix tailTrace_816049
  have hstable : (prefixWord ++ tailWord_816049).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816049).length < 2 ^ (prefixWord ++ tailWord_816049).sum := by decide
  have hdescent : baseEnd_816049 < baseStart_816049 := by decide
  rcases family_descends (prefixWord ++ tailWord_816049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816052 : List Nat := [2, 5, 2, 1, 1, 2, 2, 1, 4]
def baseStart_816052 : Nat := 118140960795 + 816052 * 2 ^ 59
def prefixEnd_816052 : Nat := 4983230072969 + 3 ^ 40 * 816052 * 2
def baseEnd_816052 : Nat := 372468368944841267997379

theorem tailTrace_816052 : CollatzResearch.WordTrace tailWord_816052 prefixEnd_816052 372468368944841267997379 := by
  unfold tailWord_816052
  simp only [CollatzResearch.WordTrace]
  refine ⟨14881930819795224715425205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19842574426393632953900273 14881930819795224715425205)
  ·
    refine ⟨1395181014355802317071113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14881930819795224715425205 1395181014355802317071113)
    ·
      refine ⟨1046385760766851737803335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1395181014355802317071113 1046385760766851737803335)
      ·
        refine ⟨1569578641150277606705003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1046385760766851737803335 1569578641150277606705003)
        ·
          refine ⟨2354367961725416410057505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1569578641150277606705003 2354367961725416410057505)
          ·
            refine ⟨1765775971294062307543129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2354367961725416410057505 1765775971294062307543129)
            ·
              refine ⟨1324331978470546730657347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1765775971294062307543129 1324331978470546730657347)
              ·
                refine ⟨1986497967705820095986021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1324331978470546730657347 1986497967705820095986021)
                ·
                  refine ⟨372468368944841267997379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1986497967705820095986021 372468368944841267997379)
                  ·
                    rfl

theorem cell20_816052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_816052 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_816052 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_816052 prefixEnd_816052 := by exact prefixLift 816052
  have htrace : WordTrace (prefixWord ++ tailWord_816052) baseStart_816052 baseEnd_816052 := by
    simpa [prefixWord, tailWord_816052, baseEnd_816052] using wordTrace_append hprefix tailTrace_816052
  have hstable : (prefixWord ++ tailWord_816052).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816052).length < 2 ^ (prefixWord ++ tailWord_816052).sum := by decide
  have hdescent : baseEnd_816052 < baseStart_816052 := by decide
  rcases family_descends (prefixWord ++ tailWord_816052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816056 : List Nat := [2, 1, 2, 1, 2, 5, 2, 1, 4]
def baseStart_816056 : Nat := 118140960795 + 816056 * 2 ^ 59
def prefixEnd_816056 : Nat := 4983230072969 + 3 ^ 40 * 816056 * 2
def baseEnd_816056 : Nat := 372470194653835031864029

theorem tailTrace_816056 : CollatzResearch.WordTrace tailWord_816056 prefixEnd_816056 372470194653835031864029 := by
  unfold tailWord_816056
  simp only [CollatzResearch.WordTrace]
  refine ⟨14882003765787979056998011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19842671687717305409330681 14882003765787979056998011)
  ·
    refine ⟨22323005648681968585497017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14882003765787979056998011 22323005648681968585497017)
    ·
      refine ⟨16742254236511476439122763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22323005648681968585497017 16742254236511476439122763)
      ·
        refine ⟨25113381354767214658684145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16742254236511476439122763 25113381354767214658684145)
        ·
          refine ⟨18835036016075410994013109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25113381354767214658684145 18835036016075410994013109)
          ·
            refine ⟨1765784626507069780688729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18835036016075410994013109 1765784626507069780688729)
            ·
              refine ⟨1324338469880302335516547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1765784626507069780688729 1324338469880302335516547)
              ·
                refine ⟨1986507704820453503274821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1324338469880302335516547 1986507704820453503274821)
                ·
                  refine ⟨372470194653835031864029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1986507704820453503274821 372470194653835031864029)
                  ·
                    rfl

theorem cell20_816056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 1, 4].length) (baseStart_816056 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_816056 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_816056 prefixEnd_816056 := by exact prefixLift 816056
  have htrace : WordTrace (prefixWord ++ tailWord_816056) baseStart_816056 baseEnd_816056 := by
    simpa [prefixWord, tailWord_816056, baseEnd_816056] using wordTrace_append hprefix tailTrace_816056
  have hstable : (prefixWord ++ tailWord_816056).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816056).length < 2 ^ (prefixWord ++ tailWord_816056).sum := by decide
  have hdescent : baseEnd_816056 < baseStart_816056 := by decide
  rcases family_descends (prefixWord ++ tailWord_816056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816090 : List Nat := [3, 1, 1, 2, 4, 3, 1, 3, 2]
def baseStart_816090 : Nat := 118140960795 + 816090 * 2 ^ 59
def prefixEnd_816090 : Nat := 4983230072969 + 3 ^ 40 * 816090 * 2
def baseEnd_816090 : Nat := 372485713180282024730557

theorem tailTrace_816090 : CollatzResearch.WordTrace tailWord_816090 prefixEnd_816090 372485713180282024730557 := by
  unfold tailWord_816090
  simp only [CollatzResearch.WordTrace]
  refine ⟨7441311903363195480183431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19843498408968521280489149 7441311903363195480183431)
  ·
    refine ⟨11161967855044793220275147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7441311903363195480183431 11161967855044793220275147)
    ·
      refine ⟨16742951782567189830412721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11161967855044793220275147 16742951782567189830412721)
      ·
        refine ⟨12557213836925392372809541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16742951782567189830412721 12557213836925392372809541)
        ·
          refine ⟨2354477594423511069901789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12557213836925392372809541 2354477594423511069901789)
          ·
            refine ⟨882929097908816651213171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2354477594423511069901789 882929097908816651213171)
            ·
              refine ⟨1324393646863224976819757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 882929097908816651213171 1324393646863224976819757)
              ·
                refine ⟨496647617573709366307409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1324393646863224976819757 496647617573709366307409)
                ·
                  refine ⟨372485713180282024730557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 496647617573709366307409 372485713180282024730557)
                  ·
                    rfl

theorem cell20_816090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 3, 2].length) (baseStart_816090 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_816090 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_816090 prefixEnd_816090 := by exact prefixLift 816090
  have htrace : WordTrace (prefixWord ++ tailWord_816090) baseStart_816090 baseEnd_816090 := by
    simpa [prefixWord, tailWord_816090, baseEnd_816090] using wordTrace_append hprefix tailTrace_816090
  have hstable : (prefixWord ++ tailWord_816090).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816090).length < 2 ^ (prefixWord ++ tailWord_816090).sum := by decide
  have hdescent : baseEnd_816090 < baseStart_816090 := by decide
  rcases family_descends (prefixWord ++ tailWord_816090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816117 : List Nat := [1, 3, 5, 2, 2, 1, 2, 1, 3]
def baseStart_816117 : Nat := 118140960795 + 816117 * 2 ^ 59
def prefixEnd_816117 : Nat := 4983230072969 + 3 ^ 40 * 816117 * 2
def baseEnd_816117 : Nat := 372498036715989930830447

theorem tailTrace_816117 : CollatzResearch.WordTrace tailWord_816117 prefixEnd_816117 372498036715989930830447 := by
  unfold tailWord_816117
  simp only [CollatzResearch.WordTrace]
  refine ⟨29766232384354965531966605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19844154922903310354644403 29766232384354965531966605)
  ·
    refine ⟨11162337144133112074487477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29766232384354965531966605 11162337144133112074487477)
    ·
      refine ⟨1046469107262479256983201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11162337144133112074487477 1046469107262479256983201)
      ·
        refine ⟨784851830446859442737401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1046469107262479256983201 784851830446859442737401)
        ·
          refine ⟨588638872835144582053051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 784851830446859442737401 588638872835144582053051)
          ·
            refine ⟨882958309252716873079577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 588638872835144582053051 882958309252716873079577)
            ·
              refine ⟨662218731939537654809683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 882958309252716873079577 662218731939537654809683)
              ·
                refine ⟨993328097909306482214525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 662218731939537654809683 993328097909306482214525)
                ·
                  refine ⟨372498036715989930830447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 993328097909306482214525 372498036715989930830447)
                  ·
                    rfl

theorem cell20_816117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 2, 1, 3].length) (baseStart_816117 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_816117 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_816117 prefixEnd_816117 := by exact prefixLift 816117
  have htrace : WordTrace (prefixWord ++ tailWord_816117) baseStart_816117 baseEnd_816117 := by
    simpa [prefixWord, tailWord_816117, baseEnd_816117] using wordTrace_append hprefix tailTrace_816117
  have hstable : (prefixWord ++ tailWord_816117).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816117).length < 2 ^ (prefixWord ++ tailWord_816117).sum := by decide
  have hdescent : baseEnd_816117 < baseStart_816117 := by decide
  rcases family_descends (prefixWord ++ tailWord_816117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816118 : List Nat := [5, 1, 1, 1, 3, 2, 2, 5]
def baseStart_816118 : Nat := 118140960795 + 816118 * 2 ^ 59
def prefixEnd_816118 : Nat := 4983230072969 + 3 ^ 40 * 816118 * 2
def baseEnd_816118 : Nat := 124166164381079457265703

theorem tailTrace_816118 : CollatzResearch.WordTrace tailWord_816118 prefixEnd_816118 124166164381079457265703 := by
  unfold tailWord_816118
  simp only [CollatzResearch.WordTrace]
  refine ⟨1860391803584458918922063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19844179238234228468502005 1860391803584458918922063)
  ·
    refine ⟨2790587705376688378383095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1860391803584458918922063 2790587705376688378383095)
    ·
      refine ⟨4185881558065032567574643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2790587705376688378383095 4185881558065032567574643)
      ·
        refine ⟨6278822337097548851361965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4185881558065032567574643 6278822337097548851361965)
        ·
          refine ⟨2354558376411580819260737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6278822337097548851361965 2354558376411580819260737)
          ·
            refine ⟨1765918782308685614445553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2354558376411580819260737 1765918782308685614445553)
            ·
              refine ⟨1324439086731514210834165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1765918782308685614445553 1324439086731514210834165)
              ·
                refine ⟨124166164381079457265703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1324439086731514210834165 124166164381079457265703)
                ·
                  rfl

theorem cell20_816118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_816118 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_816118 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_816118 prefixEnd_816118 := by exact prefixLift 816118
  have htrace : WordTrace (prefixWord ++ tailWord_816118) baseStart_816118 baseEnd_816118 := by
    simpa [prefixWord, tailWord_816118, baseEnd_816118] using wordTrace_append hprefix tailTrace_816118
  have hstable : (prefixWord ++ tailWord_816118).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816118).length < 2 ^ (prefixWord ++ tailWord_816118).sum := by decide
  have hdescent : baseEnd_816118 < baseStart_816118 := by decide
  rcases family_descends (prefixWord ++ tailWord_816118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816163 : List Nat := [1, 1, 1, 4, 3, 3, 2, 2, 3]
def baseStart_816163 : Nat := 118140960795 + 816163 * 2 ^ 59
def prefixEnd_816163 : Nat := 4983230072969 + 3 ^ 40 * 816163 * 2
def baseEnd_816163 : Nat := 372519032369418215296925

theorem tailTrace_816163 : CollatzResearch.WordTrace tailWord_816163 prefixEnd_816163 372519032369418215296925 := by
  unfold tailWord_816163
  simp only [CollatzResearch.WordTrace]
  refine ⟨29767910142188315388141143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19845273428125543592094095 29767910142188315388141143)
  ·
    refine ⟨44651865213282473082211715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29767910142188315388141143 44651865213282473082211715)
    ·
      refine ⟨66977797819923709623317573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44651865213282473082211715 66977797819923709623317573)
      ·
        refine ⟨12558337091235695554372045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66977797819923709623317573 12558337091235695554372045)
        ·
          refine ⟨4709376409213385832889517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12558337091235695554372045 4709376409213385832889517)
          ·
            refine ⟨1766016153455019687333569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4709376409213385832889517 1766016153455019687333569)
            ·
              refine ⟨1324512115091264765500177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1766016153455019687333569 1324512115091264765500177)
              ·
                refine ⟨993384086318448574125133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1324512115091264765500177 993384086318448574125133)
                ·
                  refine ⟨372519032369418215296925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 993384086318448574125133 372519032369418215296925)
                  ·
                    rfl

theorem cell20_816163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 2, 3].length) (baseStart_816163 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_816163 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_816163 prefixEnd_816163 := by exact prefixLift 816163
  have htrace : WordTrace (prefixWord ++ tailWord_816163) baseStart_816163 baseEnd_816163 := by
    simpa [prefixWord, tailWord_816163, baseEnd_816163] using wordTrace_append hprefix tailTrace_816163
  have hstable : (prefixWord ++ tailWord_816163).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816163).length < 2 ^ (prefixWord ++ tailWord_816163).sum := by decide
  have hdescent : baseEnd_816163 < baseStart_816163 := by decide
  rcases family_descends (prefixWord ++ tailWord_816163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816180 : List Nat := [2, 5, 1, 2, 1, 1, 2, 3, 3]
def baseStart_816180 : Nat := 118140960795 + 816180 * 2 ^ 59
def prefixEnd_816180 : Nat := 4983230072969 + 3 ^ 40 * 816180 * 2
def baseEnd_816180 : Nat := 372526791632641711730189

theorem tailTrace_816180 : CollatzResearch.WordTrace tailWord_816180 prefixEnd_816180 372526791632641711730189 := by
  unfold tailWord_816180
  simp only [CollatzResearch.WordTrace]
  refine ⟨14884265091563363645754997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19845686788751151527673329 14884265091563363645754997)
  ·
    refine ⟨1395399852334065341789531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14884265091563363645754997 1395399852334065341789531)
    ·
      refine ⟨2093099778501098012684297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1395399852334065341789531 2093099778501098012684297)
      ·
        refine ⟨1569824833875823509513223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2093099778501098012684297 1569824833875823509513223)
        ·
          refine ⟨2354737250813735264269835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1569824833875823509513223 2354737250813735264269835)
          ·
            refine ⟨3532105876220602896404753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2354737250813735264269835 3532105876220602896404753)
            ·
              refine ⟨2649079407165452172303565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3532105876220602896404753 2649079407165452172303565)
              ·
                refine ⟨993404777687044564613837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2649079407165452172303565 993404777687044564613837)
                ·
                  refine ⟨372526791632641711730189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 993404777687044564613837 372526791632641711730189)
                  ·
                    rfl

theorem cell20_816180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_816180 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_816180 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_816180 prefixEnd_816180 := by exact prefixLift 816180
  have htrace : WordTrace (prefixWord ++ tailWord_816180) baseStart_816180 baseEnd_816180 := by
    simpa [prefixWord, tailWord_816180, baseEnd_816180] using wordTrace_append hprefix tailTrace_816180
  have hstable : (prefixWord ++ tailWord_816180).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816180).length < 2 ^ (prefixWord ++ tailWord_816180).sum := by decide
  have hdescent : baseEnd_816180 < baseStart_816180 := by decide
  rcases family_descends (prefixWord ++ tailWord_816180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816214 : List Nat := [5, 2, 2, 1, 2, 2, 1, 2, 3]
def baseStart_816214 : Nat := 118140960795 + 816214 * 2 ^ 59
def prefixEnd_816214 : Nat := 4983230072969 + 3 ^ 40 * 816214 * 2
def baseEnd_816214 : Nat := 372542310159088704596717

theorem tailTrace_816214 : CollatzResearch.WordTrace tailWord_816214 prefixEnd_816214 372542310159088704596717 := by
  unfold tailWord_816214
  simp only [CollatzResearch.WordTrace]
  refine ⟨1860610641562721943640481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19846513510002367398831797 1860610641562721943640481)
  ·
    refine ⟨1395457981172041457730361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1860610641562721943640481 1395457981172041457730361)
    ·
      refine ⟨1046593485879031093297771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1395457981172041457730361 1046593485879031093297771)
      ·
        refine ⟨1569890228818546639946657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1046593485879031093297771 1569890228818546639946657)
        ·
          refine ⟨1177417671613909979959993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1569890228818546639946657 1177417671613909979959993)
          ·
            refine ⟨883063253710432484969995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1177417671613909979959993 883063253710432484969995)
            ·
              refine ⟨1324594880565648727454993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 883063253710432484969995 1324594880565648727454993)
              ·
                refine ⟨993446160424236545591245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1324594880565648727454993 993446160424236545591245)
                ·
                  refine ⟨372542310159088704596717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 993446160424236545591245 372542310159088704596717)
                  ·
                    rfl

theorem cell20_816214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_816214 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_816214 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_816214 prefixEnd_816214 := by exact prefixLift 816214
  have htrace : WordTrace (prefixWord ++ tailWord_816214) baseStart_816214 baseEnd_816214 := by
    simpa [prefixWord, tailWord_816214, baseEnd_816214] using wordTrace_append hprefix tailTrace_816214
  have hstable : (prefixWord ++ tailWord_816214).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816214).length < 2 ^ (prefixWord ++ tailWord_816214).sum := by decide
  have hdescent : baseEnd_816214 < baseStart_816214 := by decide
  rcases family_descends (prefixWord ++ tailWord_816214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816236 : List Nat := [2, 2, 1, 1, 3, 2, 2, 7]
def baseStart_816236 : Nat := 118140960795 + 816236 * 2 ^ 59
def prefixEnd_816236 : Nat := 4983230072969 + 3 ^ 40 * 816236 * 2
def baseEnd_816236 : Nat := 124184117186184801954431

theorem tailTrace_816236 : CollatzResearch.WordTrace tailWord_816236 prefixEnd_816236 124184117186184801954431 := by
  unfold tailWord_816236
  simp only [CollatzResearch.WordTrace]
  refine ⟨14885286335461924427774281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19847048447282565903699041 14885286335461924427774281)
  ·
    refine ⟨11163964751596443320830711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14885286335461924427774281 11163964751596443320830711)
    ·
      refine ⟨16745947127394664981246067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11163964751596443320830711 16745947127394664981246067)
      ·
        refine ⟨25118920691091997471869101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16745947127394664981246067 25118920691091997471869101)
        ·
          refine ⟨9419595259159499051950913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25118920691091997471869101 9419595259159499051950913)
          ·
            refine ⟨7064696444369624288963185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9419595259159499051950913 7064696444369624288963185)
            ·
              refine ⟨5298522333277218216722389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7064696444369624288963185 5298522333277218216722389)
              ·
                refine ⟨124184117186184801954431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5298522333277218216722389 124184117186184801954431)
                ·
                  rfl

theorem cell20_816236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 7].length) (baseStart_816236 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_816236 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_816236 prefixEnd_816236 := by exact prefixLift 816236
  have htrace : WordTrace (prefixWord ++ tailWord_816236) baseStart_816236 baseEnd_816236 := by
    simpa [prefixWord, tailWord_816236, baseEnd_816236] using wordTrace_append hprefix tailTrace_816236
  have hstable : (prefixWord ++ tailWord_816236).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816236).length < 2 ^ (prefixWord ++ tailWord_816236).sum := by decide
  have hdescent : baseEnd_816236 < baseStart_816236 := by decide
  rcases family_descends (prefixWord ++ tailWord_816236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816239 : List Nat := [1, 1, 2, 1, 3, 3, 5, 1, 3]
def baseStart_816239 : Nat := 118140960795 + 816239 * 2 ^ 59
def prefixEnd_816239 : Nat := 4983230072969 + 3 ^ 40 * 816239 * 2
def baseEnd_816239 : Nat := 372553720840299728763281

theorem tailTrace_816239 : CollatzResearch.WordTrace tailWord_816239 prefixEnd_816239 372553720840299728763281 := by
  unfold tailWord_816239
  simp only [CollatzResearch.WordTrace]
  refine ⟨29770682089912980367907771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19847121393275320245271847 29770682089912980367907771)
  ·
    refine ⟨44656023134869470551861657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29770682089912980367907771 44656023134869470551861657)
    ·
      refine ⟨33492017351152102913896243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44656023134869470551861657 33492017351152102913896243)
      ·
        refine ⟨50238026026728154370844365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33492017351152102913896243 50238026026728154370844365)
        ·
          refine ⟨18839259760023057889066637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50238026026728154370844365 18839259760023057889066637)
          ·
            refine ⟨7064722410008646708399989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18839259760023057889066637 7064722410008646708399989)
            ·
              refine ⟨662317725938310628912499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7064722410008646708399989 662317725938310628912499)
              ·
                refine ⟨993476588907465943368749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 662317725938310628912499 993476588907465943368749)
                ·
                  refine ⟨372553720840299728763281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 993476588907465943368749 372553720840299728763281)
                  ·
                    rfl

theorem cell20_816239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 5, 1, 3].length) (baseStart_816239 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_816239 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_816239 prefixEnd_816239 := by exact prefixLift 816239
  have htrace : WordTrace (prefixWord ++ tailWord_816239) baseStart_816239 baseEnd_816239 := by
    simpa [prefixWord, tailWord_816239, baseEnd_816239] using wordTrace_append hprefix tailTrace_816239
  have hstable : (prefixWord ++ tailWord_816239).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816239).length < 2 ^ (prefixWord ++ tailWord_816239).sum := by decide
  have hdescent : baseEnd_816239 < baseStart_816239 := by decide
  rcases family_descends (prefixWord ++ tailWord_816239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816246 : List Nat := [5, 1, 1, 2, 1, 1, 1, 4, 4]
def baseStart_816246 : Nat := 118140960795 + 816246 * 2 ^ 59
def prefixEnd_816246 : Nat := 4983230072969 + 3 ^ 40 * 816246 * 2
def baseEnd_816246 : Nat := 372556915831038815529919

theorem tailTrace_816246 : CollatzResearch.WordTrace tailWord_816246 prefixEnd_816246 372556915831038815529919 := by
  unfold tailWord_816246
  simp only [CollatzResearch.WordTrace]
  refine ⟨1860683587555476285213287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19847291600591747042275061 1860683587555476285213287)
  ·
    refine ⟨2791025381333214427819931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1860683587555476285213287 2791025381333214427819931)
    ·
      refine ⟨4186538071999821641729897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2791025381333214427819931 4186538071999821641729897)
      ·
        refine ⟨3139903553999866231297423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4186538071999821641729897 3139903553999866231297423)
        ·
          refine ⟨4709855330999799346946135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3139903553999866231297423 4709855330999799346946135)
          ·
            refine ⟨7064782996499699020419203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4709855330999799346946135 7064782996499699020419203)
            ·
              refine ⟨10597174494749548530628805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7064782996499699020419203 10597174494749548530628805)
              ·
                refine ⟨1986970217765540349492901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10597174494749548530628805 1986970217765540349492901)
                ·
                  refine ⟨372556915831038815529919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1986970217765540349492901 372556915831038815529919)
                  ·
                    rfl

theorem cell20_816246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_816246 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_816246 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_816246 prefixEnd_816246 := by exact prefixLift 816246
  have htrace : WordTrace (prefixWord ++ tailWord_816246) baseStart_816246 baseEnd_816246 := by
    simpa [prefixWord, tailWord_816246, baseEnd_816246] using wordTrace_append hprefix tailTrace_816246
  have hstable : (prefixWord ++ tailWord_816246).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816246).length < 2 ^ (prefixWord ++ tailWord_816246).sum := by decide
  have hdescent : baseEnd_816246 < baseStart_816246 := by decide
  rcases family_descends (prefixWord ++ tailWord_816246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816249 : List Nat := [1, 2, 1, 3, 6, 1, 2, 4]
def baseStart_816249 : Nat := 118140960795 + 816249 * 2 ^ 59
def prefixEnd_816249 : Nat := 4983230072969 + 3 ^ 40 * 816249 * 2
def baseEnd_816249 : Nat := 124186095037594712809969

theorem tailTrace_816249 : CollatzResearch.WordTrace tailWord_816249 prefixEnd_816249 124186095037594712809969 := by
  unfold tailWord_816249
  simp only [CollatzResearch.WordTrace]
  refine ⟨29771046819876752075771801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19847364546584501383847867 29771046819876752075771801)
  ·
    refine ⟨22328285114907564056828851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29771046819876752075771801 22328285114907564056828851)
    ·
      refine ⟨33492427672361346085243277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22328285114907564056828851 33492427672361346085243277)
      ·
        refine ⟨12559660377135504781966229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33492427672361346085243277 12559660377135504781966229)
        ·
          refine ⟨588734080178226786654667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12559660377135504781966229 588734080178226786654667)
          ·
            refine ⟨883101120267340179982001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 588734080178226786654667 883101120267340179982001)
            ·
              refine ⟨662325840200505134986501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 883101120267340179982001 662325840200505134986501)
              ·
                refine ⟨124186095037594712809969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 662325840200505134986501 124186095037594712809969)
                ·
                  rfl

theorem cell20_816249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 2, 4].length) (baseStart_816249 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_816249 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_816249 prefixEnd_816249 := by exact prefixLift 816249
  have htrace : WordTrace (prefixWord ++ tailWord_816249) baseStart_816249 baseEnd_816249 := by
    simpa [prefixWord, tailWord_816249, baseEnd_816249] using wordTrace_append hprefix tailTrace_816249
  have hstable : (prefixWord ++ tailWord_816249).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816249).length < 2 ^ (prefixWord ++ tailWord_816249).sum := by decide
  have hdescent : baseEnd_816249 < baseStart_816249 := by decide
  rcases family_descends (prefixWord ++ tailWord_816249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816260 : List Nat := [2, 3, 2, 1, 2, 2, 1, 2, 5]
def baseStart_816260 : Nat := 118140960795 + 816260 * 2 ^ 59
def prefixEnd_816260 : Nat := 4983230072969 + 3 ^ 40 * 816260 * 2
def baseEnd_816260 : Nat := 372563305812516989063195

theorem tailTrace_816260 : CollatzResearch.WordTrace tailWord_816260 prefixEnd_816260 372563305812516989063195 := by
  unfold tailWord_816260
  simp only [CollatzResearch.WordTrace]
  refine ⟨14885724011418450477211117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19847632015224600636281489 14885724011418450477211117)
  ·
    refine ⟨5582146504281918928954169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14885724011418450477211117 5582146504281918928954169)
    ·
      refine ⟨4186609878211439196715627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5582146504281918928954169 4186609878211439196715627)
      ·
        refine ⟨6279914817317158795073441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4186609878211439196715627 6279914817317158795073441)
        ·
          refine ⟨4709936112987869096305081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6279914817317158795073441 4709936112987869096305081)
          ·
            refine ⟨3532452084740901822228811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4709936112987869096305081 3532452084740901822228811)
            ·
              refine ⟨5298678127111352733343217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3532452084740901822228811 5298678127111352733343217)
              ·
                refine ⟨3974008595333514550007413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5298678127111352733343217 3974008595333514550007413)
                ·
                  refine ⟨372563305812516989063195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3974008595333514550007413 372563305812516989063195)
                  ·
                    rfl

theorem cell20_816260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_816260 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_816260 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_816260 prefixEnd_816260 := by exact prefixLift 816260
  have htrace : WordTrace (prefixWord ++ tailWord_816260) baseStart_816260 baseEnd_816260 := by
    simpa [prefixWord, tailWord_816260, baseEnd_816260] using wordTrace_append hprefix tailTrace_816260
  have hstable : (prefixWord ++ tailWord_816260).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816260).length < 2 ^ (prefixWord ++ tailWord_816260).sum := by decide
  have hdescent : baseEnd_816260 < baseStart_816260 := by decide
  rcases family_descends (prefixWord ++ tailWord_816260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816280 : List Nat := [2, 1, 2, 4, 2, 2, 3, 2, 2]
def baseStart_816280 : Nat := 118140960795 + 816280 * 2 ^ 59
def prefixEnd_816280 : Nat := 4983230072969 + 3 ^ 40 * 816280 * 2
def baseEnd_816280 : Nat := 372572434357485808396447

theorem tailTrace_816280 : CollatzResearch.WordTrace tailWord_816280 prefixEnd_816280 372572434357485808396447 := by
  unfold tailWord_816280
  simp only [CollatzResearch.WordTrace]
  refine ⟨14886088741382222185075147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19848118321842962913433529 14886088741382222185075147)
  ·
    refine ⟨22329133112073333277612721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14886088741382222185075147 22329133112073333277612721)
    ·
      refine ⟨16746849834054999958209541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22329133112073333277612721 16746849834054999958209541)
      ·
        refine ⟨3140034343885312492164289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16746849834054999958209541 3140034343885312492164289)
        ·
          refine ⟨2355025757913984369123217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3140034343885312492164289 2355025757913984369123217)
          ·
            refine ⟨1766269318435488276842413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2355025757913984369123217 1766269318435488276842413)
            ·
              refine ⟨662350994413308103815905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1766269318435488276842413 662350994413308103815905)
              ·
                refine ⟨496763245809981077861929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 662350994413308103815905 496763245809981077861929)
                ·
                  refine ⟨372572434357485808396447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 496763245809981077861929 372572434357485808396447)
                  ·
                    rfl

theorem cell20_816280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 3, 2, 2].length) (baseStart_816280 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_816280 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_816280 prefixEnd_816280 := by exact prefixLift 816280
  have htrace : WordTrace (prefixWord ++ tailWord_816280) baseStart_816280 baseEnd_816280 := by
    simpa [prefixWord, tailWord_816280, baseEnd_816280] using wordTrace_append hprefix tailTrace_816280
  have hstable : (prefixWord ++ tailWord_816280).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816280).length < 2 ^ (prefixWord ++ tailWord_816280).sum := by decide
  have hdescent : baseEnd_816280 < baseStart_816280 := by decide
  rcases family_descends (prefixWord ++ tailWord_816280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816284 : List Nat := [2, 2, 3, 2, 1, 2, 3, 1, 4]
def baseStart_816284 : Nat := 118140960795 + 816284 * 2 ^ 59
def prefixEnd_816284 : Nat := 4983230072969 + 3 ^ 40 * 816284 * 2
def baseEnd_816284 : Nat := 372574260066479572263097

theorem tailTrace_816284 : CollatzResearch.WordTrace tailWord_816284 prefixEnd_816284 372574260066479572263097 := by
  unfold tailWord_816284
  simp only [CollatzResearch.WordTrace]
  refine ⟨14886161687374976526647953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19848215583166635368863937 14886161687374976526647953)
  ·
    refine ⟨11164621265531232394985965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14886161687374976526647953 11164621265531232394985965)
    ·
      refine ⟨4186732974574212148119737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11164621265531232394985965 4186732974574212148119737)
      ·
        refine ⟨3140049730930659111089803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4186732974574212148119737 3140049730930659111089803)
        ·
          refine ⟨4710074596395988666634705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3140049730930659111089803 4710074596395988666634705)
          ·
            refine ⟨3532555947296991499976029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4710074596395988666634705 3532555947296991499976029)
            ·
              refine ⟨1324708480236371812491011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3532555947296991499976029 1324708480236371812491011)
              ·
                refine ⟨1987062720354557718736517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1324708480236371812491011 1987062720354557718736517)
                ·
                  refine ⟨372574260066479572263097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1987062720354557718736517 372574260066479572263097)
                  ·
                    rfl

theorem cell20_816284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 1, 4].length) (baseStart_816284 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_816284 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_816284 prefixEnd_816284 := by exact prefixLift 816284
  have htrace : WordTrace (prefixWord ++ tailWord_816284) baseStart_816284 baseEnd_816284 := by
    simpa [prefixWord, tailWord_816284, baseEnd_816284] using wordTrace_append hprefix tailTrace_816284
  have hstable : (prefixWord ++ tailWord_816284).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816284).length < 2 ^ (prefixWord ++ tailWord_816284).sum := by decide
  have hdescent : baseEnd_816284 < baseStart_816284 := by decide
  rcases family_descends (prefixWord ++ tailWord_816284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816290 : List Nat := [3, 3, 1, 3, 3, 1, 2, 1, 3]
def baseStart_816290 : Nat := 118140960795 + 816290 * 2 ^ 59
def prefixEnd_816290 : Nat := 4983230072969 + 3 ^ 40 * 816290 * 2
def baseEnd_816290 : Nat := 372576998629970218063073

theorem tailTrace_816290 : CollatzResearch.WordTrace tailWord_816290 prefixEnd_816290 372576998629970218063073 := by
  unfold tailWord_816290
  simp only [CollatzResearch.WordTrace]
  refine ⟨7443135553182054019503581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19848361475152144052009549 7443135553182054019503581)
  ·
    refine ⟨2791175832443270257313843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7443135553182054019503581 2791175832443270257313843)
    ·
      refine ⟨4186763748664905385970765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2791175832443270257313843 4186763748664905385970765)
      ·
        refine ⟨1570036405749339519739037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4186763748664905385970765 1570036405749339519739037)
        ·
          refine ⟨588763652156002319902139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1570036405749339519739037 588763652156002319902139)
          ·
            refine ⟨883145478234003479853209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 588763652156002319902139 883145478234003479853209)
            ·
              refine ⟨662359108675502609889907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 883145478234003479853209 662359108675502609889907)
              ·
                refine ⟨993538663013253914834861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 662359108675502609889907 993538663013253914834861)
                ·
                  refine ⟨372576998629970218063073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 993538663013253914834861 372576998629970218063073)
                  ·
                    rfl

theorem cell20_816290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 2, 1, 3].length) (baseStart_816290 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_816290 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_816290 prefixEnd_816290 := by exact prefixLift 816290
  have htrace : WordTrace (prefixWord ++ tailWord_816290) baseStart_816290 baseEnd_816290 := by
    simpa [prefixWord, tailWord_816290, baseEnd_816290] using wordTrace_append hprefix tailTrace_816290
  have hstable : (prefixWord ++ tailWord_816290).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816290).length < 2 ^ (prefixWord ++ tailWord_816290).sum := by decide
  have hdescent : baseEnd_816290 < baseStart_816290 := by decide
  rcases family_descends (prefixWord ++ tailWord_816290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816319 : List Nat := [1, 1, 2, 2, 2, 2, 2, 1, 7]
def baseStart_816319 : Nat := 118140960795 + 816319 * 2 ^ 59
def prefixEnd_816319 : Nat := 4983230072969 + 3 ^ 40 * 816319 * 2
def baseEnd_816319 : Nat := 372590235020175006096287

theorem tailTrace_816319 : CollatzResearch.WordTrace tailWord_816319 prefixEnd_816319 372590235020175006096287 := by
  unfold tailWord_816319
  simp only [CollatzResearch.WordTrace]
  refine ⟨29773599929623154030820011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19849066619748769353880007 29773599929623154030820011)
  ·
    refine ⟨44660399894434731046230017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29773599929623154030820011 44660399894434731046230017)
    ·
      refine ⟨33495299920826048284672513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44660399894434731046230017 33495299920826048284672513)
      ·
        refine ⟨25121474940619536213504385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33495299920826048284672513 25121474940619536213504385)
        ·
          refine ⟨18841106205464652160128289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25121474940619536213504385 18841106205464652160128289)
          ·
            refine ⟨14130829654098489120096217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18841106205464652160128289 14130829654098489120096217)
            ·
              refine ⟨10598122240573866840072163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14130829654098489120096217 10598122240573866840072163)
              ·
                refine ⟨15897183360860800260108245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10598122240573866840072163 15897183360860800260108245)
                ·
                  refine ⟨372590235020175006096287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15897183360860800260108245 372590235020175006096287)
                  ·
                    rfl

theorem cell20_816319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 7].length) (baseStart_816319 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_816319 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_816319 prefixEnd_816319 := by exact prefixLift 816319
  have htrace : WordTrace (prefixWord ++ tailWord_816319) baseStart_816319 baseEnd_816319 := by
    simpa [prefixWord, tailWord_816319, baseEnd_816319] using wordTrace_append hprefix tailTrace_816319
  have hstable : (prefixWord ++ tailWord_816319).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816319).length < 2 ^ (prefixWord ++ tailWord_816319).sum := by decide
  have hdescent : baseEnd_816319 < baseStart_816319 := by decide
  rcases family_descends (prefixWord ++ tailWord_816319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816342 : List Nat := [5, 2, 1, 2, 3, 1, 1, 5]
def baseStart_816342 : Nat := 118140960795 + 816342 * 2 ^ 59
def prefixEnd_816342 : Nat := 4983230072969 + 3 ^ 40 * 816342 * 2
def baseEnd_816342 : Nat := 124200244282296382776509

theorem tailTrace_816342 : CollatzResearch.WordTrace tailWord_816342 prefixEnd_816342 124200244282296382776509 := by
  unfold tailWord_816342
  simp only [CollatzResearch.WordTrace]
  refine ⟨1860902425533739309931705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19849625872359885972604853 1860902425533739309931705)
  ·
    refine ⟨1395676819150304482448779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1860902425533739309931705 1395676819150304482448779)
    ·
      refine ⟨2093515228725456723673169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1395676819150304482448779 2093515228725456723673169)
      ·
        refine ⟨1570136421544092542754877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2093515228725456723673169 1570136421544092542754877)
        ·
          refine ⟨588801158079034703533079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1570136421544092542754877 588801158079034703533079)
          ·
            refine ⟨883201737118552055299619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 588801158079034703533079 883201737118552055299619)
            ·
              refine ⟨1324802605677828082949429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 883201737118552055299619 1324802605677828082949429)
              ·
                refine ⟨124200244282296382776509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1324802605677828082949429 124200244282296382776509)
                ·
                  rfl

theorem cell20_816342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_816342 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_816342 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_816342 prefixEnd_816342 := by exact prefixLift 816342
  have htrace : WordTrace (prefixWord ++ tailWord_816342) baseStart_816342 baseEnd_816342 := by
    simpa [prefixWord, tailWord_816342, baseEnd_816342] using wordTrace_append hprefix tailTrace_816342
  have hstable : (prefixWord ++ tailWord_816342).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816342).length < 2 ^ (prefixWord ++ tailWord_816342).sum := by decide
  have hdescent : baseEnd_816342 < baseStart_816342 := by decide
  rcases family_descends (prefixWord ++ tailWord_816342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816374 : List Nat := [5, 1, 1, 1, 1, 1, 1, 4, 5]
def baseStart_816374 : Nat := 118140960795 + 816374 * 2 ^ 59
def prefixEnd_816374 : Nat := 4983230072969 + 3 ^ 40 * 816374 * 2
def baseEnd_816374 : Nat := 372615338518839259262729

theorem tailTrace_816374 : CollatzResearch.WordTrace tailWord_816374 prefixEnd_816374 372615338518839259262729 := by
  unfold tailWord_816374
  simp only [CollatzResearch.WordTrace]
  refine ⟨1860975371526493651504511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19850403962949265616048117 1860975371526493651504511)
  ·
    refine ⟨2791463057289740477256767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1860975371526493651504511 2791463057289740477256767)
    ·
      refine ⟨4187194585934610715885151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2791463057289740477256767 4187194585934610715885151)
      ·
        refine ⟨6280791878901916073827727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4187194585934610715885151 6280791878901916073827727)
        ·
          refine ⟨9421187818352874110741591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6280791878901916073827727 9421187818352874110741591)
          ·
            refine ⟨14131781727529311166112387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9421187818352874110741591 14131781727529311166112387)
            ·
              refine ⟨21197672591293966749168581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14131781727529311166112387 21197672591293966749168581)
              ·
                refine ⟨3974563610867618765469109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21197672591293966749168581 3974563610867618765469109)
                ·
                  refine ⟨372615338518839259262729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3974563610867618765469109 372615338518839259262729)
                  ·
                    rfl

theorem cell20_816374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_816374 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_816374 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_816374 prefixEnd_816374 := by exact prefixLift 816374
  have htrace : WordTrace (prefixWord ++ tailWord_816374) baseStart_816374 baseEnd_816374 := by
    simpa [prefixWord, tailWord_816374, baseEnd_816374] using wordTrace_append hprefix tailTrace_816374
  have hstable : (prefixWord ++ tailWord_816374).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816374).length < 2 ^ (prefixWord ++ tailWord_816374).sum := by decide
  have hdescent : baseEnd_816374 < baseStart_816374 := by decide
  rcases family_descends (prefixWord ++ tailWord_816374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816398 : List Nat := [4, 1, 1, 2, 1, 4, 2, 1, 4]
def baseStart_816398 : Nat := 118140960795 + 816398 * 2 ^ 59
def prefixEnd_816398 : Nat := 4983230072969 + 3 ^ 40 * 816398 * 2
def baseEnd_816398 : Nat := 372626292772801842462631

theorem tailTrace_816398 : CollatzResearch.WordTrace tailWord_816398 prefixEnd_816398 372626292772801842462631 := by
  unfold tailWord_816398
  simp only [CollatzResearch.WordTrace]
  refine ⟨3722060162042118815368231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19850987530891300348630565 3722060162042118815368231)
  ·
    refine ⟨5583090243063178223052347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3722060162042118815368231 5583090243063178223052347)
    ·
      refine ⟨8374635364594767334578521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5583090243063178223052347 8374635364594767334578521)
      ·
        refine ⟨6280976523446075500933891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8374635364594767334578521 6280976523446075500933891)
        ·
          refine ⟨9421464785169113251400837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6280976523446075500933891 9421464785169113251400837)
          ·
            refine ⟨1766524647219208734637657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9421464785169113251400837 1766524647219208734637657)
            ·
              refine ⟨1324893485414406550978243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1766524647219208734637657 1324893485414406550978243)
              ·
                refine ⟨1987340228121609826467365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1324893485414406550978243 1987340228121609826467365)
                ·
                  refine ⟨372626292772801842462631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1987340228121609826467365 372626292772801842462631)
                  ·
                    rfl

theorem cell20_816398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_816398 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_816398 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_816398 prefixEnd_816398 := by exact prefixLift 816398
  have htrace : WordTrace (prefixWord ++ tailWord_816398) baseStart_816398 baseEnd_816398 := by
    simpa [prefixWord, tailWord_816398, baseEnd_816398] using wordTrace_append hprefix tailTrace_816398
  have hstable : (prefixWord ++ tailWord_816398).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816398).length < 2 ^ (prefixWord ++ tailWord_816398).sum := by decide
  have hdescent : baseEnd_816398 < baseStart_816398 := by decide
  rcases family_descends (prefixWord ++ tailWord_816398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816412 : List Nat := [2, 2, 3, 1, 1, 1, 2, 5, 3]
def baseStart_816412 : Nat := 118140960795 + 816412 * 2 ^ 59
def prefixEnd_816412 : Nat := 4983230072969 + 3 ^ 40 * 816412 * 2
def baseEnd_816412 : Nat := 372632682754280015995907

theorem tailTrace_816412 : CollatzResearch.WordTrace tailWord_816412 prefixEnd_816412 372632682754280015995907 := by
  unfold tailWord_816412
  simp only [CollatzResearch.WordTrace]
  refine ⟨14888495959143115456977745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19851327945524153942636993 14888495959143115456977745)
  ·
    refine ⟨11166371969357336592733309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14888495959143115456977745 11166371969357336592733309)
    ·
      refine ⟨4187389488509001222274991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11166371969357336592733309 4187389488509001222274991)
      ·
        refine ⟨6281084232763501833412487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4187389488509001222274991 6281084232763501833412487)
        ·
          refine ⟨9421626349145252750118731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6281084232763501833412487 9421626349145252750118731)
          ·
            refine ⟨14132439523717879125178097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9421626349145252750118731 14132439523717879125178097)
            ·
              refine ⟨10599329642788409343883573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14132439523717879125178097 10599329642788409343883573)
              ·
                refine ⟨993687154011413375989085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10599329642788409343883573 993687154011413375989085)
                ·
                  refine ⟨372632682754280015995907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 993687154011413375989085 372632682754280015995907)
                  ·
                    rfl

theorem cell20_816412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 5, 3].length) (baseStart_816412 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_816412 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_816412 prefixEnd_816412 := by exact prefixLift 816412
  have htrace : WordTrace (prefixWord ++ tailWord_816412) baseStart_816412 baseEnd_816412 := by
    simpa [prefixWord, tailWord_816412, baseEnd_816412] using wordTrace_append hprefix tailTrace_816412
  have hstable : (prefixWord ++ tailWord_816412).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816412).length < 2 ^ (prefixWord ++ tailWord_816412).sum := by decide
  have hdescent : baseEnd_816412 < baseStart_816412 := by decide
  rcases family_descends (prefixWord ++ tailWord_816412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816419 : List Nat := [1, 1, 1, 4, 2, 3, 2, 2, 4]
def baseStart_816419 : Nat := 118140960795 + 816419 * 2 ^ 59
def prefixEnd_816419 : Nat := 4983230072969 + 3 ^ 40 * 816419 * 2
def baseEnd_816419 : Nat := 372635877745019102762545

theorem tailTrace_816419 : CollatzResearch.WordTrace tailWord_816419 prefixEnd_816419 372635877745019102762545 := by
  unfold tailWord_816419
  simp only [CollatzResearch.WordTrace]
  refine ⟨29777247229260871109460311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19851498152840580739640207 29777247229260871109460311)
  ·
    refine ⟨44665870843891306664190467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29777247229260871109460311 44665870843891306664190467)
    ·
      refine ⟨66998806265836959996285701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44665870843891306664190467 66998806265836959996285701)
      ·
        refine ⟨12562276174844429999303569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66998806265836959996285701 12562276174844429999303569)
        ·
          refine ⟨9421707131133322499477677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12562276174844429999303569 9421707131133322499477677)
          ·
            refine ⟨3533140174174995937304129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9421707131133322499477677 3533140174174995937304129)
            ·
              refine ⟨2649855130631246952978097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3533140174174995937304129 2649855130631246952978097)
              ·
                refine ⟨1987391347973435214733573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2649855130631246952978097 1987391347973435214733573)
                ·
                  refine ⟨372635877745019102762545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1987391347973435214733573 372635877745019102762545)
                  ·
                    rfl

theorem cell20_816419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 2, 4].length) (baseStart_816419 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_816419 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_816419 prefixEnd_816419 := by exact prefixLift 816419
  have htrace : WordTrace (prefixWord ++ tailWord_816419) baseStart_816419 baseEnd_816419 := by
    simpa [prefixWord, tailWord_816419, baseEnd_816419] using wordTrace_append hprefix tailTrace_816419
  have hstable : (prefixWord ++ tailWord_816419).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816419).length < 2 ^ (prefixWord ++ tailWord_816419).sum := by decide
  have hdescent : baseEnd_816419 < baseStart_816419 := by decide
  rcases family_descends (prefixWord ++ tailWord_816419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816429 : List Nat := [1, 5, 3, 1, 1, 1, 1, 2, 5]
def baseStart_816429 : Nat := 118140960795 + 816429 * 2 ^ 59
def prefixEnd_816429 : Nat := 4983230072969 + 3 ^ 40 * 816429 * 2
def baseEnd_816429 : Nat := 372640442017503512429171

theorem tailTrace_816429 : CollatzResearch.WordTrace tailWord_816429 prefixEnd_816429 372640442017503512429171 := by
  unfold tailWord_816429
  simp only [CollatzResearch.WordTrace]
  refine ⟨29777611959224642817324341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19851741306149761878216227 29777611959224642817324341)
  ·
    refine ⟨2791651121177310264124157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29777611959224642817324341 2791651121177310264124157)
    ·
      refine ⟨1046869170441491349046559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2791651121177310264124157 1046869170441491349046559)
      ·
        refine ⟨1570303755662237023569839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1046869170441491349046559 1570303755662237023569839)
        ·
          refine ⟨2355455633493355535354759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1570303755662237023569839 2355455633493355535354759)
          ·
            refine ⟨3533183450240033303032139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2355455633493355535354759 3533183450240033303032139)
            ·
              refine ⟨5299775175360049954548209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3533183450240033303032139 5299775175360049954548209)
              ·
                refine ⟨3974831381520037465911157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5299775175360049954548209 3974831381520037465911157)
                ·
                  refine ⟨372640442017503512429171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3974831381520037465911157 372640442017503512429171)
                  ·
                    rfl

theorem cell20_816429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_816429 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_816429 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_816429 prefixEnd_816429 := by exact prefixLift 816429
  have htrace : WordTrace (prefixWord ++ tailWord_816429) baseStart_816429 baseEnd_816429 := by
    simpa [prefixWord, tailWord_816429, baseEnd_816429] using wordTrace_append hprefix tailTrace_816429
  have hstable : (prefixWord ++ tailWord_816429).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816429).length < 2 ^ (prefixWord ++ tailWord_816429).sum := by decide
  have hdescent : baseEnd_816429 < baseStart_816429 := by decide
  rcases family_descends (prefixWord ++ tailWord_816429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816457 : List Nat := [1, 2, 1, 1, 2, 3, 5, 1, 4]
def baseStart_816457 : Nat := 118140960795 + 816457 * 2 ^ 59
def prefixEnd_816457 : Nat := 4983230072969 + 3 ^ 40 * 816457 * 2
def baseEnd_816457 : Nat := 372653221980459859495723

theorem tailTrace_816457 : CollatzResearch.WordTrace tailWord_816457 prefixEnd_816457 372653221980459859495723 := by
  unfold tailWord_816457
  simp only [CollatzResearch.WordTrace]
  refine ⟨29778633203123203599343625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19852422135415469066229083 29778633203123203599343625)
  ·
    refine ⟨22333974902342402699507719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29778633203123203599343625 22333974902342402699507719)
    ·
      refine ⟨33500962353513604049261579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22333974902342402699507719 33500962353513604049261579)
      ·
        refine ⟨50251443530270406073892369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33500962353513604049261579 50251443530270406073892369)
        ·
          refine ⟨37688582647702804555419277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50251443530270406073892369 37688582647702804555419277)
          ·
            refine ⟨14133218492888551708282229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37688582647702804555419277 14133218492888551708282229)
            ·
              refine ⟨1324989233708301722651459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14133218492888551708282229 1324989233708301722651459)
              ·
                refine ⟨1987483850562452583977189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1324989233708301722651459 1987483850562452583977189)
                ·
                  refine ⟨372653221980459859495723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1987483850562452583977189 372653221980459859495723)
                  ·
                    rfl

theorem cell20_816457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 1, 4].length) (baseStart_816457 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_816457 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_816457 prefixEnd_816457 := by exact prefixLift 816457
  have htrace : WordTrace (prefixWord ++ tailWord_816457) baseStart_816457 baseEnd_816457 := by
    simpa [prefixWord, tailWord_816457, baseEnd_816457] using wordTrace_append hprefix tailTrace_816457
  have hstable : (prefixWord ++ tailWord_816457).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816457).length < 2 ^ (prefixWord ++ tailWord_816457).sum := by decide
  have hdescent : baseEnd_816457 < baseStart_816457 := by decide
  rcases family_descends (prefixWord ++ tailWord_816457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816464 : List Nat := [2, 1, 1, 1, 1, 5, 4, 5]
def baseStart_816464 : Nat := 118140960795 + 816464 * 2 ^ 59
def prefixEnd_816464 : Nat := 4983230072969 + 3 ^ 40 * 816464 * 2
def baseEnd_816464 : Nat := 124218805657066315420787

theorem tailTrace_816464 : CollatzResearch.WordTrace tailWord_816464 prefixEnd_816464 124218805657066315420787 := by
  unfold tailWord_816464
  simp only [CollatzResearch.WordTrace]
  refine ⟨14889444257048921897424223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19852592342731895863232297 14889444257048921897424223)
  ·
    refine ⟨22334166385573382846136335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14889444257048921897424223 22334166385573382846136335)
    ·
      refine ⟨33501249578360074269204503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22334166385573382846136335 33501249578360074269204503)
      ·
        refine ⟨50251874367540111403806755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33501249578360074269204503 50251874367540111403806755)
        ·
          refine ⟨75377811551310167105710133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50251874367540111403806755 75377811551310167105710133)
          ·
            refine ⟨7066669832935328166160325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75377811551310167105710133 7066669832935328166160325)
            ·
              refine ⟨1325000593675374031155061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7066669832935328166160325 1325000593675374031155061)
              ·
                refine ⟨124218805657066315420787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1325000593675374031155061 124218805657066315420787)
                ·
                  rfl

theorem cell20_816464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 5].length) (baseStart_816464 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_816464 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_816464 prefixEnd_816464 := by exact prefixLift 816464
  have htrace : WordTrace (prefixWord ++ tailWord_816464) baseStart_816464 baseEnd_816464 := by
    simpa [prefixWord, tailWord_816464, baseEnd_816464] using wordTrace_append hprefix tailTrace_816464
  have hstable : (prefixWord ++ tailWord_816464).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816464).length < 2 ^ (prefixWord ++ tailWord_816464).sum := by decide
  have hdescent : baseEnd_816464 < baseStart_816464 := by decide
  rcases family_descends (prefixWord ++ tailWord_816464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816502 : List Nat := [5, 1, 1, 13]
def baseStart_816502 : Nat := 118140960795 + 816502 * 2 ^ 59
def prefixEnd_816502 : Nat := 4983230072969 + 3 ^ 40 * 816502 * 2
def baseEnd_816502 : Nat := 1533636877393579024673

theorem tailTrace_816502 : CollatzResearch.WordTrace tailWord_816502 prefixEnd_816502 1533636877393579024673 := by
  unfold tailWord_816502
  simp only [CollatzResearch.WordTrace]
  refine ⟨1861267155497511017795735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19853516325306784189821173 1861267155497511017795735)
  ·
    refine ⟨2791900733246266526693603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1861267155497511017795735 2791900733246266526693603)
    ·
      refine ⟨4187851099869399790040405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2791900733246266526693603 4187851099869399790040405)
      ·
        refine ⟨1533636877393579024673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 4187851099869399790040405 1533636877393579024673)
        ·
          rfl

theorem cell20_816502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 13].length) (baseStart_816502 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_816502 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_816502 prefixEnd_816502 := by exact prefixLift 816502
  have htrace : WordTrace (prefixWord ++ tailWord_816502) baseStart_816502 baseEnd_816502 := by
    simpa [prefixWord, tailWord_816502, baseEnd_816502] using wordTrace_append hprefix tailTrace_816502
  have hstable : (prefixWord ++ tailWord_816502).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816502).length < 2 ^ (prefixWord ++ tailWord_816502).sum := by decide
  have hdescent : baseEnd_816502 < baseStart_816502 := by decide
  rcases family_descends (prefixWord ++ tailWord_816502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816519 : List Nat := [1, 1, 4, 2, 2, 4, 1, 5]
def baseStart_816519 : Nat := 118140960795 + 816519 * 2 ^ 59
def prefixEnd_816519 : Nat := 4983230072969 + 3 ^ 40 * 816519 * 2
def baseEnd_816519 : Nat := 124227173489954399809601

theorem tailTrace_816519 : CollatzResearch.WordTrace tailWord_816519 prefixEnd_816519 124227173489954399809601 := by
  unfold tailWord_816519
  simp only [CollatzResearch.WordTrace]
  refine ⟨29780894528898588188100611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19853929685932392125400407 29780894528898588188100611)
  ·
    refine ⟨44671341793347882282150917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29780894528898588188100611 44671341793347882282150917)
    ·
      refine ⟨8375876586252727927903297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44671341793347882282150917 8375876586252727927903297)
      ·
        refine ⟨6281907439689545945927473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8375876586252727927903297 6281907439689545945927473)
        ·
          refine ⟨4711430579767159459445605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6281907439689545945927473 4711430579767159459445605)
          ·
            refine ⟨883393233706342398646051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4711430579767159459445605 883393233706342398646051)
            ·
              refine ⟨1325089850559513597969077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 883393233706342398646051 1325089850559513597969077)
              ·
                refine ⟨124227173489954399809601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1325089850559513597969077 124227173489954399809601)
                ·
                  rfl

theorem cell20_816519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 5].length) (baseStart_816519 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_816519 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_816519 prefixEnd_816519 := by exact prefixLift 816519
  have htrace : WordTrace (prefixWord ++ tailWord_816519) baseStart_816519 baseEnd_816519 := by
    simpa [prefixWord, tailWord_816519, baseEnd_816519] using wordTrace_append hprefix tailTrace_816519
  have hstable : (prefixWord ++ tailWord_816519).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816519).length < 2 ^ (prefixWord ++ tailWord_816519).sum := by decide
  have hdescent : baseEnd_816519 < baseStart_816519 := by decide
  rcases family_descends (prefixWord ++ tailWord_816519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816536 : List Nat := [2, 1, 2, 5, 2, 1, 3, 4]
def baseStart_816536 : Nat := 118140960795 + 816536 * 2 ^ 59
def prefixEnd_816536 : Nat := 4983230072969 + 3 ^ 40 * 816536 * 2
def baseEnd_816536 : Nat := 124229759911028898620689

theorem tailTrace_816536 : CollatzResearch.WordTrace tailWord_816536 prefixEnd_816536 124229759911028898620689 := by
  unfold tailWord_816536
  simp only [CollatzResearch.WordTrace]
  refine ⟨14890757284918500045734731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19854343046558000060979641 14890757284918500045734731)
  ·
    refine ⟨22336135927377750068602097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14890757284918500045734731 22336135927377750068602097)
    ·
      refine ⟨16752101945533312551451573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22336135927377750068602097 16752101945533312551451573)
      ·
        refine ⟨1570509557393748051698585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16752101945533312551451573 1570509557393748051698585)
        ·
          refine ⟨1177882168045311038773939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1570509557393748051698585 1177882168045311038773939)
          ·
            refine ⟨1766823252067966558160909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1177882168045311038773939 1766823252067966558160909)
            ·
              refine ⟨662558719525487459310341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1766823252067966558160909 662558719525487459310341)
              ·
                refine ⟨124229759911028898620689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 662558719525487459310341 124229759911028898620689)
                ·
                  rfl

theorem cell20_816536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 3, 4].length) (baseStart_816536 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_816536 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_816536 prefixEnd_816536 := by exact prefixLift 816536
  have htrace : WordTrace (prefixWord ++ tailWord_816536) baseStart_816536 baseEnd_816536 := by
    simpa [prefixWord, tailWord_816536, baseEnd_816536] using wordTrace_append hprefix tailTrace_816536
  have hstable : (prefixWord ++ tailWord_816536).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816536).length < 2 ^ (prefixWord ++ tailWord_816536).sum := by decide
  have hdescent : baseEnd_816536 < baseStart_816536 := by decide
  rcases family_descends (prefixWord ++ tailWord_816536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816547 : List Nat := [1, 1, 1, 4, 1, 3, 2, 2, 5]
def baseStart_816547 : Nat := 118140960795 + 816547 * 2 ^ 59
def prefixEnd_816547 : Nat := 4983230072969 + 3 ^ 40 * 816547 * 2
def baseEnd_816547 : Nat := 372694300432819546495355

theorem tailTrace_816547 : CollatzResearch.WordTrace tailWord_816547 prefixEnd_816547 372694300432819546495355 := by
  unfold tailWord_816547
  simp only [CollatzResearch.WordTrace]
  refine ⟨29781915772797148970119895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19854610515198099313413263 29781915772797148970119895)
  ·
    refine ⟨44672873659195723455179843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29781915772797148970119895 44672873659195723455179843)
    ·
      refine ⟨67009310488793585182769765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44672873659195723455179843 67009310488793585182769765)
      ·
        refine ⟨12564245716648797221769331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67009310488793585182769765 12564245716648797221769331)
        ·
          refine ⟨18846368574973195832653997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12564245716648797221769331 18846368574973195832653997)
          ·
            refine ⟨7067388215614948437245249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18846368574973195832653997 7067388215614948437245249)
            ·
              refine ⟨5300541161711211327933937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7067388215614948437245249 5300541161711211327933937)
              ·
                refine ⟨3975405871283408495950453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5300541161711211327933937 3975405871283408495950453)
                ·
                  refine ⟨372694300432819546495355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3975405871283408495950453 372694300432819546495355)
                  ·
                    rfl

theorem cell20_816547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 5].length) (baseStart_816547 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_816547 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_816547 prefixEnd_816547 := by exact prefixLift 816547
  have htrace : WordTrace (prefixWord ++ tailWord_816547) baseStart_816547 baseEnd_816547 := by
    simpa [prefixWord, tailWord_816547, baseEnd_816547] using wordTrace_append hprefix tailTrace_816547
  have hstable : (prefixWord ++ tailWord_816547).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816547).length < 2 ^ (prefixWord ++ tailWord_816547).sum := by decide
  have hdescent : baseEnd_816547 < baseStart_816547 := by decide
  rcases family_descends (prefixWord ++ tailWord_816547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816557 : List Nat := [1, 5, 2, 2, 1, 2, 7]
def baseStart_816557 : Nat := 118140960795 + 816557 * 2 ^ 59
def prefixEnd_816557 : Nat := 4983230072969 + 3 ^ 40 * 816557 * 2
def baseEnd_816557 : Nat := 41410984967255995129109

theorem tailTrace_816557 : CollatzResearch.WordTrace tailWord_816557 prefixEnd_816557 41410984967255995129109 := by
  unfold tailWord_816557
  simp only [CollatzResearch.WordTrace]
  refine ⟨29782280502760920677983925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19854853668507280451989283 29782280502760920677983925)
  ·
    refine ⟨2792088797133836313560993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29782280502760920677983925 2792088797133836313560993)
    ·
      refine ⟨2094066597850377235170745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2792088797133836313560993 2094066597850377235170745)
      ·
        refine ⟨1570549948387782926378059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2094066597850377235170745 1570549948387782926378059)
        ·
          refine ⟨2355824922581674389567089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1570549948387782926378059 2355824922581674389567089)
          ·
            refine ⟨1766868691936255792175317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2355824922581674389567089 1766868691936255792175317)
            ·
              refine ⟨41410984967255995129109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1766868691936255792175317 41410984967255995129109)
              ·
                rfl

theorem cell20_816557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 7].length) (baseStart_816557 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_816557 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_816557 prefixEnd_816557 := by exact prefixLift 816557
  have htrace : WordTrace (prefixWord ++ tailWord_816557) baseStart_816557 baseEnd_816557 := by
    simpa [prefixWord, tailWord_816557, baseEnd_816557] using wordTrace_append hprefix tailTrace_816557
  have hstable : (prefixWord ++ tailWord_816557).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816557).length < 2 ^ (prefixWord ++ tailWord_816557).sum := by decide
  have hdescent : baseEnd_816557 < baseStart_816557 := by decide
  rcases family_descends (prefixWord ++ tailWord_816557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816605 : List Nat := [1, 4, 3, 1, 1, 2, 3, 3, 2]
def baseStart_816605 : Nat := 118140960795 + 816605 * 2 ^ 59
def prefixEnd_816605 : Nat := 4983230072969 + 3 ^ 40 * 816605 * 2
def baseEnd_816605 : Nat := 372720773213229122561785

theorem tailTrace_816605 : CollatzResearch.WordTrace tailWord_816605 prefixEnd_816605 372720773213229122561785 := by
  unfold tailWord_816605
  simp only [CollatzResearch.WordTrace]
  refine ⟨29784031206587024875731269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19856020804391349917154179 29784031206587024875731269)
  ·
    refine ⟨5584505851235067164199613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29784031206587024875731269 5584505851235067164199613)
    ·
      refine ⟨2094189694213150186574855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5584505851235067164199613 2094189694213150186574855)
      ·
        refine ⟨3141284541319725279862283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2094189694213150186574855 3141284541319725279862283)
        ·
          refine ⟨4711926811979587919793425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3141284541319725279862283 4711926811979587919793425)
          ·
            refine ⟨3533945108984690939845069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4711926811979587919793425 3533945108984690939845069)
            ·
              refine ⟨1325229415869259102441901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3533945108984690939845069 1325229415869259102441901)
              ·
                refine ⟨496961030950972163415713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1325229415869259102441901 496961030950972163415713)
                ·
                  refine ⟨372720773213229122561785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 496961030950972163415713 372720773213229122561785)
                  ·
                    rfl

theorem cell20_816605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 3, 2].length) (baseStart_816605 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_816605 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_816605 prefixEnd_816605 := by exact prefixLift 816605
  have htrace : WordTrace (prefixWord ++ tailWord_816605) baseStart_816605 baseEnd_816605 := by
    simpa [prefixWord, tailWord_816605, baseEnd_816605] using wordTrace_append hprefix tailTrace_816605
  have hstable : (prefixWord ++ tailWord_816605).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816605).length < 2 ^ (prefixWord ++ tailWord_816605).sum := by decide
  have hdescent : baseEnd_816605 < baseStart_816605 := by decide
  rcases family_descends (prefixWord ++ tailWord_816605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816623 : List Nat := [1, 1, 2, 1, 4, 1, 4, 1, 5]
def baseStart_816623 : Nat := 118140960795 + 816623 * 2 ^ 59
def prefixEnd_816623 : Nat := 4983230072969 + 3 ^ 40 * 816623 * 2
def baseEnd_816623 : Nat := 372728988903701059961711

theorem tailTrace_816623 : CollatzResearch.WordTrace tailWord_816623 prefixEnd_816623 372728988903701059961711 := by
  unfold tailWord_816623
  simp only [CollatzResearch.WordTrace]
  refine ⟨29784687720521813949886523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19856458480347875966591015 29784687720521813949886523)
  ·
    refine ⟨44677031580782720924829785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29784687720521813949886523 44677031580782720924829785)
    ·
      refine ⟨33507773685587040693622339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44677031580782720924829785 33507773685587040693622339)
      ·
        refine ⟨50261660528380561040433509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33507773685587040693622339 50261660528380561040433509)
        ·
          refine ⟨9424061349071355195081283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50261660528380561040433509 9424061349071355195081283)
          ·
            refine ⟨14136092023607032792621925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9424061349071355195081283 14136092023607032792621925)
            ·
              refine ⟨2650517254426318648616611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14136092023607032792621925 2650517254426318648616611)
              ·
                refine ⟨3975775881639477972924917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2650517254426318648616611 3975775881639477972924917)
                ·
                  refine ⟨372728988903701059961711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3975775881639477972924917 372728988903701059961711)
                  ·
                    rfl

theorem cell20_816623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 5].length) (baseStart_816623 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_816623 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_816623 prefixEnd_816623 := by exact prefixLift 816623
  have htrace : WordTrace (prefixWord ++ tailWord_816623) baseStart_816623 baseEnd_816623 := by
    simpa [prefixWord, tailWord_816623, baseEnd_816623] using wordTrace_append hprefix tailTrace_816623
  have hstable : (prefixWord ++ tailWord_816623).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816623).length < 2 ^ (prefixWord ++ tailWord_816623).sum := by decide
  have hdescent : baseEnd_816623 < baseStart_816623 := by decide
  rcases family_descends (prefixWord ++ tailWord_816623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816626 : List Nat := [3, 2, 1, 4, 1, 1, 3, 1, 4]
def baseStart_816626 : Nat := 118140960795 + 816626 * 2 ^ 59
def prefixEnd_816626 : Nat := 4983230072969 + 3 ^ 40 * 816626 * 2
def baseEnd_816626 : Nat := 372730358185446382861699

theorem tailTrace_816626 : CollatzResearch.WordTrace tailWord_816626 prefixEnd_816626 372730358185446382861699 := by
  unfold tailWord_816626
  simp only [CollatzResearch.WordTrace]
  refine ⟨7446199284877736365561433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19856531426340630308163821 7446199284877736365561433)
  ·
    refine ⟨5584649463658302274171075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7446199284877736365561433 5584649463658302274171075)
    ·
      refine ⟨8376974195487453411256613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5584649463658302274171075 8376974195487453411256613)
      ·
        refine ⟨1570682661653897514610615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8376974195487453411256613 1570682661653897514610615)
        ·
          refine ⟨2356023992480846271915923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1570682661653897514610615 2356023992480846271915923)
          ·
            refine ⟨3534035988721269407873885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2356023992480846271915923 3534035988721269407873885)
            ·
              refine ⟨1325263495770476027952707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3534035988721269407873885 1325263495770476027952707)
              ·
                refine ⟨1987895243655714041929061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1325263495770476027952707 1987895243655714041929061)
                ·
                  refine ⟨372730358185446382861699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1987895243655714041929061 372730358185446382861699)
                  ·
                    rfl

theorem cell20_816626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_816626 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_816626 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_816626 prefixEnd_816626 := by exact prefixLift 816626
  have htrace : WordTrace (prefixWord ++ tailWord_816626) baseStart_816626 baseEnd_816626 := by
    simpa [prefixWord, tailWord_816626, baseEnd_816626] using wordTrace_append hprefix tailTrace_816626
  have hstable : (prefixWord ++ tailWord_816626).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816626).length < 2 ^ (prefixWord ++ tailWord_816626).sum := by decide
  have hdescent : baseEnd_816626 < baseStart_816626 := by decide
  rcases family_descends (prefixWord ++ tailWord_816626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816670 : List Nat := [4, 3, 3, 1, 1, 1, 2, 2, 3]
def baseStart_816670 : Nat := 118140960795 + 816670 * 2 ^ 59
def prefixEnd_816670 : Nat := 4983230072969 + 3 ^ 40 * 816670 * 2
def baseEnd_816670 : Nat := 372750440984377785394853

theorem tailTrace_816670 : CollatzResearch.WordTrace tailWord_816670 prefixEnd_816670 372750440984377785394853 := by
  unfold tailWord_816670
  simp only [CollatzResearch.WordTrace]
  refine ⟨3723300243918942622105933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19857601300901027317898309 3723300243918942622105933)
  ·
    refine ⟨1396237591469603483289725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3723300243918942622105933 1396237591469603483289725)
    ·
      refine ⟨523589096801101306233647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1396237591469603483289725 523589096801101306233647)
      ·
        refine ⟨785383645201651959350471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 523589096801101306233647 785383645201651959350471)
        ·
          refine ⟨1178075467802477939025707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 785383645201651959350471 1178075467802477939025707)
          ·
            refine ⟨1767113201703716908538561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1178075467802477939025707 1767113201703716908538561)
            ·
              refine ⟨1325334901277787681403921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1767113201703716908538561 1325334901277787681403921)
              ·
                refine ⟨994001175958340761052941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1325334901277787681403921 994001175958340761052941)
                ·
                  refine ⟨372750440984377785394853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 994001175958340761052941 372750440984377785394853)
                  ·
                    rfl

theorem cell20_816670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_816670 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_816670 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_816670 prefixEnd_816670 := by exact prefixLift 816670
  have htrace : WordTrace (prefixWord ++ tailWord_816670) baseStart_816670 baseEnd_816670 := by
    simpa [prefixWord, tailWord_816670, baseEnd_816670] using wordTrace_append hprefix tailTrace_816670
  have hstable : (prefixWord ++ tailWord_816670).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816670).length < 2 ^ (prefixWord ++ tailWord_816670).sum := by decide
  have hdescent : baseEnd_816670 < baseStart_816670 := by decide
  rcases family_descends (prefixWord ++ tailWord_816670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816675 : List Nat := [1, 1, 1, 4, 13]
def baseStart_816675 : Nat := 118140960795 + 816675 * 2 ^ 59
def prefixEnd_816675 : Nat := 4983230072969 + 3 ^ 40 * 816675 * 2
def baseEnd_816675 : Nat := 4601885470624938150965

theorem tailTrace_816675 : CollatzResearch.WordTrace tailWord_816675 prefixEnd_816675 4601885470624938150965 := by
  unfold tailWord_816675
  simp only [CollatzResearch.WordTrace]
  refine ⟨29786584316333426830779479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19857722877555617887186319 29786584316333426830779479)
  ·
    refine ⟨44679876474500140246169219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29786584316333426830779479 44679876474500140246169219)
    ·
      refine ⟨67019814711750210369253829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44679876474500140246169219 67019814711750210369253829)
      ·
        refine ⟨12566215258453164444235093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67019814711750210369253829 12566215258453164444235093)
        ·
          refine ⟨4601885470624938150965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 12566215258453164444235093 4601885470624938150965)
          ·
            rfl

theorem cell20_816675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 13].length) (baseStart_816675 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_816675 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_816675 prefixEnd_816675 := by exact prefixLift 816675
  have htrace : WordTrace (prefixWord ++ tailWord_816675) baseStart_816675 baseEnd_816675 := by
    simpa [prefixWord, tailWord_816675, baseEnd_816675] using wordTrace_append hprefix tailTrace_816675
  have hstable : (prefixWord ++ tailWord_816675).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816675).length < 2 ^ (prefixWord ++ tailWord_816675).sum := by decide
  have hdescent : baseEnd_816675 < baseStart_816675 := by decide
  rcases family_descends (prefixWord ++ tailWord_816675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816713 : List Nat := [1, 2, 1, 1, 2, 2, 1, 10]
def baseStart_816713 : Nat := 118140960795 + 816713 * 2 ^ 59
def prefixEnd_816713 : Nat := 4983230072969 + 3 ^ 40 * 816713 * 2
def baseEnd_816713 : Nat := 124256689118686915653781

theorem tailTrace_816713 : CollatzResearch.WordTrace tailWord_816713 prefixEnd_816713 124256689118686915653781 := by
  unfold tailWord_816713
  simp only [CollatzResearch.WordTrace]
  refine ⟨29787970290195759320662793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19858646860130506213775195 29787970290195759320662793)
  ·
    refine ⟨22340977717646819490497095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29787970290195759320662793 22340977717646819490497095)
    ·
      refine ⟨33511466576470229235745643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22340977717646819490497095 33511466576470229235745643)
      ·
        refine ⟨50267199864705343853618465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33511466576470229235745643 50267199864705343853618465)
        ·
          refine ⟨37700399898529007890213849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50267199864705343853618465 37700399898529007890213849)
          ·
            refine ⟨28275299923896755917660387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37700399898529007890213849 28275299923896755917660387)
            ·
              refine ⟨42412949885845133876490581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28275299923896755917660387 42412949885845133876490581)
              ·
                refine ⟨124256689118686915653781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 42412949885845133876490581 124256689118686915653781)
                ·
                  rfl

theorem cell20_816713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 10].length) (baseStart_816713 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_816713 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_816713 prefixEnd_816713 := by exact prefixLift 816713
  have htrace : WordTrace (prefixWord ++ tailWord_816713) baseStart_816713 baseEnd_816713 := by
    simpa [prefixWord, tailWord_816713, baseEnd_816713] using wordTrace_append hprefix tailTrace_816713
  have hstable : (prefixWord ++ tailWord_816713).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816713).length < 2 ^ (prefixWord ++ tailWord_816713).sum := by decide
  have hdescent : baseEnd_816713 < baseStart_816713 := by decide
  rcases family_descends (prefixWord ++ tailWord_816713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816737 : List Nat := [1, 2, 3, 1, 1, 3, 3, 1, 5]
def baseStart_816737 : Nat := 118140960795 + 816737 * 2 ^ 59
def prefixEnd_816737 : Nat := 4983230072969 + 3 ^ 40 * 816737 * 2
def baseEnd_816737 : Nat := 372781021610023330161245

theorem tailTrace_816737 : CollatzResearch.WordTrace tailWord_816737 prefixEnd_816737 372781021610023330161245 := by
  unfold tailWord_816737
  simp only [CollatzResearch.WordTrace]
  refine ⟨29788845642108811419536465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19859230428072540946357643 29788845642108811419536465)
  ·
    refine ⟨22341634231581608564652349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29788845642108811419536465 22341634231581608564652349)
    ·
      refine ⟨8378112836843103211744631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22341634231581608564652349 8378112836843103211744631)
      ·
        refine ⟨12567169255264654817616947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8378112836843103211744631 12567169255264654817616947)
        ·
          refine ⟨18850753882896982226425421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12567169255264654817616947 18850753882896982226425421)
          ·
            refine ⟨7069032706086368334909533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18850753882896982226425421 7069032706086368334909533)
            ·
              refine ⟨2650887264782388125591075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7069032706086368334909533 2650887264782388125591075)
              ·
                refine ⟨3976330897173582188386613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2650887264782388125591075 3976330897173582188386613)
                ·
                  refine ⟨372781021610023330161245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3976330897173582188386613 372781021610023330161245)
                  ·
                    rfl

theorem cell20_816737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 5].length) (baseStart_816737 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_816737 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_816737 prefixEnd_816737 := by exact prefixLift 816737
  have htrace : WordTrace (prefixWord ++ tailWord_816737) baseStart_816737 baseEnd_816737 := by
    simpa [prefixWord, tailWord_816737, baseEnd_816737] using wordTrace_append hprefix tailTrace_816737
  have hstable : (prefixWord ++ tailWord_816737).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816737).length < 2 ^ (prefixWord ++ tailWord_816737).sum := by decide
  have hdescent : baseEnd_816737 < baseStart_816737 := by decide
  rcases family_descends (prefixWord ++ tailWord_816737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816740 : List Nat := [2, 3, 1, 1, 2, 3, 2, 4, 2]
def baseStart_816740 : Nat := 118140960795 + 816740 * 2 ^ 59
def prefixEnd_816740 : Nat := 4983230072969 + 3 ^ 40 * 816740 * 2
def baseEnd_816740 : Nat := 372782390891768653061233

theorem tailTrace_816740 : CollatzResearch.WordTrace tailWord_816740 prefixEnd_816740 372782390891768653061233 := by
  unfold tailWord_816740
  simp only [CollatzResearch.WordTrace]
  refine ⟨14894477530548971465947837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19859303374065295287930449 14894477530548971465947837)
  ·
    refine ⟨5585429073955864299730439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14894477530548971465947837 5585429073955864299730439)
    ·
      refine ⟨8378143610933796449595659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5585429073955864299730439 8378143610933796449595659)
      ·
        refine ⟨12567215416400694674393489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8378143610933796449595659 12567215416400694674393489)
        ·
          refine ⟨9425411562300521005795117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12567215416400694674393489 9425411562300521005795117)
          ·
            refine ⟨3534529335862695377173169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9425411562300521005795117 3534529335862695377173169)
            ·
              refine ⟨2650897001897021532879877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3534529335862695377173169 2650897001897021532879877)
              ·
                refine ⟨497043187855691537414977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2650897001897021532879877 497043187855691537414977)
                ·
                  refine ⟨372782390891768653061233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 497043187855691537414977 372782390891768653061233)
                  ·
                    rfl

theorem cell20_816740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 4, 2].length) (baseStart_816740 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_816740 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_816740 prefixEnd_816740 := by exact prefixLift 816740
  have htrace : WordTrace (prefixWord ++ tailWord_816740) baseStart_816740 baseEnd_816740 := by
    simpa [prefixWord, tailWord_816740, baseEnd_816740] using wordTrace_append hprefix tailTrace_816740
  have hstable : (prefixWord ++ tailWord_816740).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816740).length < 2 ^ (prefixWord ++ tailWord_816740).sum := by decide
  have hdescent : baseEnd_816740 < baseStart_816740 := by decide
  rcases family_descends (prefixWord ++ tailWord_816740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816750 : List Nat := [4, 1, 2, 2, 3, 1, 3, 1, 3]
def baseStart_816750 : Nat := 118140960795 + 816750 * 2 ^ 59
def prefixEnd_816750 : Nat := 4983230072969 + 3 ^ 40 * 816750 * 2
def baseEnd_816750 : Nat := 372786955164253062727859

theorem tailTrace_816750 : CollatzResearch.WordTrace tailWord_816750 prefixEnd_816750 372786955164253062727859 := by
  unfold tailWord_816750
  simp only [CollatzResearch.WordTrace]
  refine ⟨3723664973882714329969963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19859546527374476426506469 3723664973882714329969963)
  ·
    refine ⟨5585497460824071494954945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3723664973882714329969963 5585497460824071494954945)
    ·
      refine ⟨4189123095618053621216209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5585497460824071494954945 4189123095618053621216209)
      ·
        refine ⟨3141842321713540215912157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4189123095618053621216209 3141842321713540215912157)
        ·
          refine ⟨1178190870642577580967059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3141842321713540215912157 1178190870642577580967059)
          ·
            refine ⟨1767286305963866371450589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1178190870642577580967059 1767286305963866371450589)
            ·
              refine ⟨662732364736449889293971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1767286305963866371450589 662732364736449889293971)
              ·
                refine ⟨994098547104674833940957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 662732364736449889293971 994098547104674833940957)
                ·
                  refine ⟨372786955164253062727859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 994098547104674833940957 372786955164253062727859)
                  ·
                    rfl

theorem cell20_816750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 3, 1, 3].length) (baseStart_816750 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_816750 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_816750 prefixEnd_816750 := by exact prefixLift 816750
  have htrace : WordTrace (prefixWord ++ tailWord_816750) baseStart_816750 baseEnd_816750 := by
    simpa [prefixWord, tailWord_816750, baseEnd_816750] using wordTrace_append hprefix tailTrace_816750
  have hstable : (prefixWord ++ tailWord_816750).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816750).length < 2 ^ (prefixWord ++ tailWord_816750).sum := by decide
  have hdescent : baseEnd_816750 < baseStart_816750 := by decide
  rcases family_descends (prefixWord ++ tailWord_816750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816751 : List Nat := [1, 1, 2, 1, 3, 2, 1, 9]
def baseStart_816751 : Nat := 118140960795 + 816751 * 2 ^ 59
def prefixEnd_816751 : Nat := 4983230072969 + 3 ^ 40 * 816751 * 2
def baseEnd_816751 : Nat := 124262470530500501231507

theorem tailTrace_816751 : CollatzResearch.WordTrace tailWord_816751 prefixEnd_816751 124262470530500501231507 := by
  unfold tailWord_816751
  simp only [CollatzResearch.WordTrace]
  refine ⟨29789356264058091810546107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19859570842705394540364071 29789356264058091810546107)
  ·
    refine ⟨44684034396087137715819161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29789356264058091810546107 44684034396087137715819161)
    ·
      refine ⟨33513025797065353286864371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44684034396087137715819161 33513025797065353286864371)
      ·
        refine ⟨50269538695598029930296557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33513025797065353286864371 50269538695598029930296557)
        ·
          refine ⟨18851077010849261223861209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50269538695598029930296557 18851077010849261223861209)
          ·
            refine ⟨14138307758136945917895907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18851077010849261223861209 14138307758136945917895907)
            ·
              refine ⟨21207461637205418876843861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14138307758136945917895907 21207461637205418876843861)
              ·
                refine ⟨124262470530500501231507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21207461637205418876843861 124262470530500501231507)
                ·
                  rfl

theorem cell20_816751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 9].length) (baseStart_816751 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_816751 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_816751 prefixEnd_816751 := by exact prefixLift 816751
  have htrace : WordTrace (prefixWord ++ tailWord_816751) baseStart_816751 baseEnd_816751 := by
    simpa [prefixWord, tailWord_816751, baseEnd_816751] using wordTrace_append hprefix tailTrace_816751
  have hstable : (prefixWord ++ tailWord_816751).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816751).length < 2 ^ (prefixWord ++ tailWord_816751).sum := by decide
  have hdescent : baseEnd_816751 < baseStart_816751 := by decide
  rcases family_descends (prefixWord ++ tailWord_816751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816775 : List Nat := [1, 1, 4, 2, 1, 3, 1, 2, 5]
def baseStart_816775 : Nat := 118140960795 + 816775 * 2 ^ 59
def prefixEnd_816775 : Nat := 4983230072969 + 3 ^ 40 * 816775 * 2
def baseEnd_816775 : Nat := 372798365845464086894423

theorem tailTrace_816775 : CollatzResearch.WordTrace tailWord_816775 prefixEnd_816775 372798365845464086894423 := by
  unfold tailWord_816775
  simp only [CollatzResearch.WordTrace]
  refine ⟨29790231615971143909419779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19860154410647429272946519 29790231615971143909419779)
  ·
    refine ⟨44685347423956715864129669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29790231615971143909419779 44685347423956715864129669)
    ·
      refine ⟨8378502641991884224524313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44685347423956715864129669 8378502641991884224524313)
      ·
        refine ⟨6283876981493913168393235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8378502641991884224524313 6283876981493913168393235)
        ·
          refine ⟨9425815472240869752589853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6283876981493913168393235 9425815472240869752589853)
          ·
            refine ⟨3534680802090326157221195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9425815472240869752589853 3534680802090326157221195)
            ·
              refine ⟨5302021203135489235831793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3534680802090326157221195 5302021203135489235831793)
              ·
                refine ⟨3976515902351616926873845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5302021203135489235831793 3976515902351616926873845)
                ·
                  refine ⟨372798365845464086894423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3976515902351616926873845 372798365845464086894423)
                  ·
                    rfl

theorem cell20_816775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 5].length) (baseStart_816775 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_816775 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_816775 prefixEnd_816775 := by exact prefixLift 816775
  have htrace : WordTrace (prefixWord ++ tailWord_816775) baseStart_816775 baseEnd_816775 := by
    simpa [prefixWord, tailWord_816775, baseEnd_816775] using wordTrace_append hprefix tailTrace_816775
  have hstable : (prefixWord ++ tailWord_816775).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816775).length < 2 ^ (prefixWord ++ tailWord_816775).sum := by decide
  have hdescent : baseEnd_816775 < baseStart_816775 := by decide
  rcases family_descends (prefixWord ++ tailWord_816775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816802 : List Nat := [3, 3, 1, 4, 1, 1, 2, 5]
def baseStart_816802 : Nat := 118140960795 + 816802 * 2 ^ 59
def prefixEnd_816802 : Nat := 4983230072969 + 3 ^ 40 * 816802 * 2
def baseEnd_816802 : Nat := 124270229793723997664771

theorem tailTrace_816802 : CollatzResearch.WordTrace tailWord_816802 prefixEnd_816802 124270229793723997664771 := by
  unfold tailWord_816802
  simp only [CollatzResearch.WordTrace]
  refine ⟨7447804096718331880163165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19860810924582218347101773 7447804096718331880163165)
  ·
    refine ⟨2792926536269374455061187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7447804096718331880163165 2792926536269374455061187)
    ·
      refine ⟨4189389804404061682591781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2792926536269374455061187 4189389804404061682591781)
      ·
        refine ⟨785510588325761565485959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4189389804404061682591781 785510588325761565485959)
        ·
          refine ⟨1178265882488642348228939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 785510588325761565485959 1178265882488642348228939)
          ·
            refine ⟨1767398823732963522343409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1178265882488642348228939 1767398823732963522343409)
            ·
              refine ⟨1325549117799722641757557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1767398823732963522343409 1325549117799722641757557)
              ·
                refine ⟨124270229793723997664771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1325549117799722641757557 124270229793723997664771)
                ·
                  rfl

theorem cell20_816802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 5].length) (baseStart_816802 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_816802 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_816802 prefixEnd_816802 := by exact prefixLift 816802
  have htrace : WordTrace (prefixWord ++ tailWord_816802) baseStart_816802 baseEnd_816802 := by
    simpa [prefixWord, tailWord_816802, baseEnd_816802] using wordTrace_append hprefix tailTrace_816802
  have hstable : (prefixWord ++ tailWord_816802).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816802).length < 2 ^ (prefixWord ++ tailWord_816802).sum := by decide
  have hdescent : baseEnd_816802 < baseStart_816802 := by decide
  rcases family_descends (prefixWord ++ tailWord_816802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816844 : List Nat := [2, 2, 1, 5, 2, 8]
def baseStart_816844 : Nat := 118140960795 + 816844 * 2 ^ 59
def prefixEnd_816844 : Nat := 4983230072969 + 3 ^ 40 * 816844 * 2
def baseEnd_816844 : Nat := 13808513308355796799783

theorem tailTrace_816844 : CollatzResearch.WordTrace tailWord_816844 prefixEnd_816844 13808513308355796799783 := by
  unfold tailWord_816844
  simp only [CollatzResearch.WordTrace]
  refine ⟨14896374126360584346840793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19861832168480779129121057 14896374126360584346840793)
  ·
    refine ⟨11172280594770438260130595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14896374126360584346840793 11172280594770438260130595)
    ·
      refine ⟨16758420892155657390195893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11172280594770438260130595 16758420892155657390195893)
      ·
        refine ⟨1571101958639592880330865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16758420892155657390195893 1571101958639592880330865)
        ·
          refine ⟨1178326468979694660248149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1571101958639592880330865 1178326468979694660248149)
          ·
            refine ⟨13808513308355796799783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1178326468979694660248149 13808513308355796799783)
            ·
              rfl

theorem cell20_816844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 8].length) (baseStart_816844 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_816844 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_816844 prefixEnd_816844 := by exact prefixLift 816844
  have htrace : WordTrace (prefixWord ++ tailWord_816844) baseStart_816844 baseEnd_816844 := by
    simpa [prefixWord, tailWord_816844, baseEnd_816844] using wordTrace_append hprefix tailTrace_816844
  have hstable : (prefixWord ++ tailWord_816844).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816844).length < 2 ^ (prefixWord ++ tailWord_816844).sum := by decide
  have hdescent : baseEnd_816844 < baseStart_816844 := by decide
  rcases family_descends (prefixWord ++ tailWord_816844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816850 : List Nat := [3, 2, 2, 2, 2, 3, 2, 2, 2]
def baseStart_816850 : Nat := 118140960795 + 816850 * 2 ^ 59
def prefixEnd_816850 : Nat := 4983230072969 + 3 ^ 40 * 816850 * 2
def baseEnd_816850 : Nat := 372832597889097159394117

theorem tailTrace_816850 : CollatzResearch.WordTrace tailWord_816850 prefixEnd_816850 372832597889097159394117 := by
  unfold tailWord_816850
  simp only [CollatzResearch.WordTrace]
  refine ⟨7448241772674857929600001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19861978060466287812266669 7448241772674857929600001)
  ·
    refine ⟨5586181329506143447200001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7448241772674857929600001 5586181329506143447200001)
    ·
      refine ⟨4189635997129607585400001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5586181329506143447200001 4189635997129607585400001)
      ·
        refine ⟨3142226997847205689050001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4189635997129607585400001 3142226997847205689050001)
        ·
          refine ⟨2356670248385404266787501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3142226997847205689050001 2356670248385404266787501)
          ·
            refine ⟨883751343144526600045313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2356670248385404266787501 883751343144526600045313)
            ·
              refine ⟨662813507358394950033985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 883751343144526600045313 662813507358394950033985)
              ·
                refine ⟨497110130518796212525489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 662813507358394950033985 497110130518796212525489)
                ·
                  refine ⟨372832597889097159394117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 497110130518796212525489 372832597889097159394117)
                  ·
                    rfl

theorem cell20_816850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 2, 2, 2].length) (baseStart_816850 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_816850 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_816850 prefixEnd_816850 := by exact prefixLift 816850
  have htrace : WordTrace (prefixWord ++ tailWord_816850) baseStart_816850 baseEnd_816850 := by
    simpa [prefixWord, tailWord_816850, baseEnd_816850] using wordTrace_append hprefix tailTrace_816850
  have hstable : (prefixWord ++ tailWord_816850).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816850).length < 2 ^ (prefixWord ++ tailWord_816850).sum := by decide
  have hdescent : baseEnd_816850 < baseStart_816850 := by decide
  rcases family_descends (prefixWord ++ tailWord_816850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816892 : List Nat := [2, 2, 2, 1, 3, 1, 4, 3, 2]
def baseStart_816892 : Nat := 118140960795 + 816892 * 2 ^ 59
def prefixEnd_816892 : Nat := 4983230072969 + 3 ^ 40 * 816892 * 2
def baseEnd_816892 : Nat := 372851767833531679993945

theorem tailTrace_816892 : CollatzResearch.WordTrace tailWord_816892 prefixEnd_816892 372851767833531679993945 := by
  unfold tailWord_816892
  simp only [CollatzResearch.WordTrace]
  refine ⟨14897249478273636445714465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19862999304364848594285953 14897249478273636445714465)
  ·
    refine ⟨11172937108705227334285849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14897249478273636445714465 11172937108705227334285849)
    ·
      refine ⟨8379702831528920500714387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11172937108705227334285849 8379702831528920500714387)
      ·
        refine ⟨12569554247293380751071581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8379702831528920500714387 12569554247293380751071581)
        ·
          refine ⟨4713582842735017781651843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12569554247293380751071581 4713582842735017781651843)
          ·
            refine ⟨7070374264102526672477765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4713582842735017781651843 7070374264102526672477765)
            ·
              refine ⟨1325695174519223751089581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7070374264102526672477765 1325695174519223751089581)
              ·
                refine ⟨497135690444708906658593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1325695174519223751089581 497135690444708906658593)
                ·
                  refine ⟨372851767833531679993945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 497135690444708906658593 372851767833531679993945)
                  ·
                    rfl

theorem cell20_816892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 3, 2].length) (baseStart_816892 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_816892 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_816892 prefixEnd_816892 := by exact prefixLift 816892
  have htrace : WordTrace (prefixWord ++ tailWord_816892) baseStart_816892 baseEnd_816892 := by
    simpa [prefixWord, tailWord_816892, baseEnd_816892] using wordTrace_append hprefix tailTrace_816892
  have hstable : (prefixWord ++ tailWord_816892).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816892).length < 2 ^ (prefixWord ++ tailWord_816892).sum := by decide
  have hdescent : baseEnd_816892 < baseStart_816892 := by decide
  rcases family_descends (prefixWord ++ tailWord_816892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816906 : List Nat := [3, 1, 2, 2, 1, 3, 3, 2, 3]
def baseStart_816906 : Nat := 118140960795 + 816906 * 2 ^ 59
def prefixEnd_816906 : Nat := 4983230072969 + 3 ^ 40 * 816906 * 2
def baseEnd_816906 : Nat := 372858157815009853527221

theorem tailTrace_816906 : CollatzResearch.WordTrace tailWord_816906 prefixEnd_816906 372858157815009853527221 := by
  unfold tailWord_816906
  simp only [CollatzResearch.WordTrace]
  refine ⟨7448752394624138320609643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19863339718997702188292381 7448752394624138320609643)
  ·
    refine ⟨11173128591936207480914465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7448752394624138320609643 11173128591936207480914465)
    ·
      refine ⟨8379846443952155610685849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11173128591936207480914465 8379846443952155610685849)
      ·
        refine ⟨6284884832964116708014387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8379846443952155610685849 6284884832964116708014387)
        ·
          refine ⟨9427327249446175062021581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6284884832964116708014387 9427327249446175062021581)
          ·
            refine ⟨3535247718542315648258093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9427327249446175062021581 3535247718542315648258093)
            ·
              refine ⟨1325717894453368368096785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3535247718542315648258093 1325717894453368368096785)
              ·
                refine ⟨994288420840026276072589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1325717894453368368096785 994288420840026276072589)
                ·
                  refine ⟨372858157815009853527221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 994288420840026276072589 372858157815009853527221)
                  ·
                    rfl

theorem cell20_816906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 2, 3].length) (baseStart_816906 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_816906 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_816906 prefixEnd_816906 := by exact prefixLift 816906
  have htrace : WordTrace (prefixWord ++ tailWord_816906) baseStart_816906 baseEnd_816906 := by
    simpa [prefixWord, tailWord_816906, baseEnd_816906] using wordTrace_append hprefix tailTrace_816906
  have hstable : (prefixWord ++ tailWord_816906).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816906).length < 2 ^ (prefixWord ++ tailWord_816906).sum := by decide
  have hdescent : baseEnd_816906 < baseStart_816906 := by decide
  rcases family_descends (prefixWord ++ tailWord_816906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816947 : List Nat := [1, 1, 1, 2, 7, 2, 1, 3, 2]
def baseStart_816947 : Nat := 118140960795 + 816947 * 2 ^ 59
def prefixEnd_816947 : Nat := 4983230072969 + 3 ^ 40 * 816947 * 2
def baseEnd_816947 : Nat := 372876871332195933160387

theorem tailTrace_816947 : CollatzResearch.WordTrace tailWord_816947 prefixEnd_816947 372876871332195933160387 := by
  unfold tailWord_816947
  simp only [CollatzResearch.WordTrace]
  refine ⟨29796504971348017284681095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19864336647565344856454063 29796504971348017284681095)
  ·
    refine ⟨44694757457022025927021643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29796504971348017284681095 44694757457022025927021643)
    ·
      refine ⟨67042136185533038890532465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44694757457022025927021643 67042136185533038890532465)
      ·
        refine ⟨50281602139149779167899349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67042136185533038890532465 50281602139149779167899349)
        ·
          refine ⟨1178475050136322949247641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 50281602139149779167899349 1178475050136322949247641)
          ·
            refine ⟨883856287602242211935731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1178475050136322949247641 883856287602242211935731)
            ·
              refine ⟨1325784431403363317903597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 883856287602242211935731 1325784431403363317903597)
              ·
                refine ⟨497169161776261244213849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1325784431403363317903597 497169161776261244213849)
                ·
                  refine ⟨372876871332195933160387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 497169161776261244213849 372876871332195933160387)
                  ·
                    rfl

theorem cell20_816947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 3, 2].length) (baseStart_816947 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_816947 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_816947 prefixEnd_816947 := by exact prefixLift 816947
  have htrace : WordTrace (prefixWord ++ tailWord_816947) baseStart_816947 baseEnd_816947 := by
    simpa [prefixWord, tailWord_816947, baseEnd_816947] using wordTrace_append hprefix tailTrace_816947
  have hstable : (prefixWord ++ tailWord_816947).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816947).length < 2 ^ (prefixWord ++ tailWord_816947).sum := by decide
  have hdescent : baseEnd_816947 < baseStart_816947 := by decide
  rcases family_descends (prefixWord ++ tailWord_816947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816951 : List Nat := [1, 1, 3, 1, 2, 1, 2, 7, 2]
def baseStart_816951 : Nat := 118140960795 + 816951 * 2 ^ 59
def prefixEnd_816951 : Nat := 4983230072969 + 3 ^ 40 * 816951 * 2
def baseEnd_816951 : Nat := 372878697041189697027037

theorem tailTrace_816951 : CollatzResearch.WordTrace tailWord_816951 prefixEnd_816951 372878697041189697027037 := by
  unfold tailWord_816951
  simp only [CollatzResearch.WordTrace]
  refine ⟨29796650863333525967826707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19864433908889017311884471 29796650863333525967826707)
  ·
    refine ⟨44694976295000288951740061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29796650863333525967826707 44694976295000288951740061)
    ·
      refine ⟨16760616110625108356902523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44694976295000288951740061 16760616110625108356902523)
      ·
        refine ⟨25140924165937662535353785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16760616110625108356902523 25140924165937662535353785)
        ·
          refine ⟨18855693124453246901515339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25140924165937662535353785 18855693124453246901515339)
          ·
            refine ⟨28283539686679870352273009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18855693124453246901515339 28283539686679870352273009)
            ·
              refine ⟨21212654765009902764204757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28283539686679870352273009 21212654765009902764204757)
              ·
                refine ⟨497171596054919596036049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 21212654765009902764204757 497171596054919596036049)
                ·
                  refine ⟨372878697041189697027037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 497171596054919596036049 372878697041189697027037)
                  ·
                    rfl

theorem cell20_816951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 7, 2].length) (baseStart_816951 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_816951 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_816951 prefixEnd_816951 := by exact prefixLift 816951
  have htrace : WordTrace (prefixWord ++ tailWord_816951) baseStart_816951 baseEnd_816951 := by
    simpa [prefixWord, tailWord_816951, baseEnd_816951] using wordTrace_append hprefix tailTrace_816951
  have hstable : (prefixWord ++ tailWord_816951).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816951).length < 2 ^ (prefixWord ++ tailWord_816951).sum := by decide
  have hdescent : baseEnd_816951 < baseStart_816951 := by decide
  rcases family_descends (prefixWord ++ tailWord_816951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816958 : List Nat := [4, 2, 1, 2, 2, 1, 8]
def baseStart_816958 : Nat := 118140960795 + 816958 * 2 ^ 59
def prefixEnd_816958 : Nat := 4983230072969 + 3 ^ 40 * 816958 * 2
def baseEnd_816958 : Nat := 41431321336880975977075

theorem tailTrace_816958 : CollatzResearch.WordTrace tailWord_816958 prefixEnd_816958 41431321336880975977075 := by
  unfold tailWord_816958
  simp only [CollatzResearch.WordTrace]
  refine ⟨3724613271788520770416441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19864604116205444108887685 3724613271788520770416441)
  ·
    refine ⟨2793459953841390577812331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3724613271788520770416441 2793459953841390577812331)
    ·
      refine ⟨4190189930762085866718497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2793459953841390577812331 4190189930762085866718497)
      ·
        refine ⟨3142642448071564400038873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4190189930762085866718497 3142642448071564400038873)
        ·
          refine ⟨2356981836053673300029155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3142642448071564400038873 2356981836053673300029155)
          ·
            refine ⟨3535472754080509950043733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2356981836053673300029155 3535472754080509950043733)
            ·
              refine ⟨41431321336880975977075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3535472754080509950043733 41431321336880975977075)
              ·
                rfl

theorem cell20_816958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 8].length) (baseStart_816958 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_816958 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_816958 prefixEnd_816958 := by exact prefixLift 816958
  have htrace : WordTrace (prefixWord ++ tailWord_816958) baseStart_816958 baseEnd_816958 := by
    simpa [prefixWord, tailWord_816958, baseEnd_816958] using wordTrace_append hprefix tailTrace_816958
  have hstable : (prefixWord ++ tailWord_816958).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816958).length < 2 ^ (prefixWord ++ tailWord_816958).sum := by decide
  have hdescent : baseEnd_816958 < baseStart_816958 := by decide
  rcases family_descends (prefixWord ++ tailWord_816958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_816965 : List Nat := [1, 3, 1, 1, 1, 2, 4, 4, 3]
def baseStart_816965 : Nat := 118140960795 + 816965 * 2 ^ 59
def prefixEnd_816965 : Nat := 4983230072969 + 3 ^ 40 * 816965 * 2
def baseEnd_816965 : Nat := 372885087022667870560313

theorem tailTrace_816965 : CollatzResearch.WordTrace tailWord_816965 prefixEnd_816965 372885087022667870560313 := by
  unfold tailWord_816965
  simp only [CollatzResearch.WordTrace]
  refine ⟨29797161485282806358836349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19864774323521870905890899 29797161485282806358836349)
  ·
    refine ⟨11173935556981052384563631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29797161485282806358836349 11173935556981052384563631)
    ·
      refine ⟨16760903335471578576845447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11173935556981052384563631 16760903335471578576845447)
      ·
        refine ⟨25141355003207367865268171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16760903335471578576845447 25141355003207367865268171)
        ·
          refine ⟨37712032504811051797902257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25141355003207367865268171 37712032504811051797902257)
          ·
            refine ⟨28284024378608288848426693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37712032504811051797902257 28284024378608288848426693)
            ·
              refine ⟨5303254570989054159080005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28284024378608288848426693 5303254570989054159080005)
              ·
                refine ⟨994360232060447654827501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5303254570989054159080005 994360232060447654827501)
                ·
                  refine ⟨372885087022667870560313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 994360232060447654827501 372885087022667870560313)
                  ·
                    rfl

theorem cell20_816965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 4, 3].length) (baseStart_816965 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_816965 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_816965 prefixEnd_816965 := by exact prefixLift 816965
  have htrace : WordTrace (prefixWord ++ tailWord_816965) baseStart_816965 baseEnd_816965 := by
    simpa [prefixWord, tailWord_816965, baseEnd_816965] using wordTrace_append hprefix tailTrace_816965
  have hstable : (prefixWord ++ tailWord_816965).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_816965).length < 2 ^ (prefixWord ++ tailWord_816965).sum := by decide
  have hdescent : baseEnd_816965 < baseStart_816965 := by decide
  rcases family_descends (prefixWord ++ tailWord_816965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817041 : List Nat := [1, 2, 2, 1, 1, 1, 6, 3, 3]
def baseStart_817041 : Nat := 118140960795 + 817041 * 2 ^ 59
def prefixEnd_817041 : Nat := 4983230072969 + 3 ^ 40 * 817041 * 2
def baseEnd_817041 : Nat := 372919775493549384026669

theorem tailTrace_817041 : CollatzResearch.WordTrace tailWord_817041 prefixEnd_817041 372919775493549384026669 := by
  unfold tailWord_817041
  simp only [CollatzResearch.WordTrace]
  refine ⟨29799933433007471338602977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19866622288671647559068651 29799933433007471338602977)
  ·
    refine ⟨22349950074755603503952233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29799933433007471338602977 22349950074755603503952233)
    ·
      refine ⟨16762462556066702627964175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22349950074755603503952233 16762462556066702627964175)
      ·
        refine ⟨25143693834100053941946263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16762462556066702627964175 25143693834100053941946263)
        ·
          refine ⟨37715540751150080912919395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25143693834100053941946263 37715540751150080912919395)
          ·
            refine ⟨56573311126725121369379093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37715540751150080912919395 56573311126725121369379093)
            ·
              refine ⟨2651873959065240064189645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 56573311126725121369379093 2651873959065240064189645)
              ·
                refine ⟨994452734649465024071117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2651873959065240064189645 994452734649465024071117)
                ·
                  refine ⟨372919775493549384026669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 994452734649465024071117 372919775493549384026669)
                  ·
                    rfl

theorem cell20_817041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 3, 3].length) (baseStart_817041 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_817041 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_817041 prefixEnd_817041 := by exact prefixLift 817041
  have htrace : WordTrace (prefixWord ++ tailWord_817041) baseStart_817041 baseEnd_817041 := by
    simpa [prefixWord, tailWord_817041, baseEnd_817041] using wordTrace_append hprefix tailTrace_817041
  have hstable : (prefixWord ++ tailWord_817041).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817041).length < 2 ^ (prefixWord ++ tailWord_817041).sum := by decide
  have hdescent : baseEnd_817041 < baseStart_817041 := by decide
  rcases family_descends (prefixWord ++ tailWord_817041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817106 : List Nat := [3, 2, 2, 3, 2, 2, 2, 4]
def baseStart_817106 : Nat := 118140960795 + 817106 * 2 ^ 59
def prefixEnd_817106 : Nat := 4983230072969 + 3 ^ 40 * 817106 * 2
def baseEnd_817106 : Nat := 124316481088232682286579

theorem tailTrace_817106 : CollatzResearch.WordTrace tailWord_817106 prefixEnd_817106 124316481088232682286579 := by
  unfold tailWord_817106
  simp only [CollatzResearch.WordTrace]
  refine ⟨7450576044442996859929793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19868202785181324959812781 7450576044442996859929793)
  ·
    refine ⟨5587932033332247644947345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7450576044442996859929793 5587932033332247644947345)
    ·
      refine ⟨4190949024999185733710509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5587932033332247644947345 4190949024999185733710509)
      ·
        refine ⟨1571605884374694650141441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4190949024999185733710509 1571605884374694650141441)
        ·
          refine ⟨1178704413281020987606081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1571605884374694650141441 1178704413281020987606081)
          ·
            refine ⟨884028309960765740704561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1178704413281020987606081 884028309960765740704561)
            ·
              refine ⟨663021232470574305528421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 884028309960765740704561 663021232470574305528421)
              ·
                refine ⟨124316481088232682286579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 663021232470574305528421 124316481088232682286579)
                ·
                  rfl

theorem cell20_817106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 2, 4].length) (baseStart_817106 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_817106 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_817106 prefixEnd_817106 := by exact prefixLift 817106
  have htrace : WordTrace (prefixWord ++ tailWord_817106) baseStart_817106 baseEnd_817106 := by
    simpa [prefixWord, tailWord_817106, baseEnd_817106] using wordTrace_append hprefix tailTrace_817106
  have hstable : (prefixWord ++ tailWord_817106).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817106).length < 2 ^ (prefixWord ++ tailWord_817106).sum := by decide
  have hdescent : baseEnd_817106 < baseStart_817106 := by decide
  rcases family_descends (prefixWord ++ tailWord_817106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817127 : List Nat := [1, 1, 5, 2, 4, 1, 6]
def baseStart_817127 : Nat := 118140960795 + 817127 * 2 ^ 59
def prefixEnd_817127 : Nat := 4983230072969 + 3 ^ 40 * 817127 * 2
def baseEnd_817127 : Nat := 41439892026323923017739

theorem tailTrace_817127 : CollatzResearch.WordTrace tailWord_817127 prefixEnd_817127 41439892026323923017739 := by
  unfold tailWord_817127
  simp only [CollatzResearch.WordTrace]
  refine ⟨29803070110695908026233635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19868713407130605350822423 29803070110695908026233635)
  ·
    refine ⟨44704605166043862039350453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29803070110695908026233635 44704605166043862039350453)
    ·
      refine ⟨4191056734316612066189105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44704605166043862039350453 4191056734316612066189105)
      ·
        refine ⟨3143292550737459049641829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4191056734316612066189105 3143292550737459049641829)
        ·
          refine ⟨589367353263273571807843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3143292550737459049641829 589367353263273571807843)
          ·
            refine ⟨884051029894910357711765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 589367353263273571807843 884051029894910357711765)
            ·
              refine ⟨41439892026323923017739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 884051029894910357711765 41439892026323923017739)
              ·
                rfl

theorem cell20_817127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 6].length) (baseStart_817127 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_817127 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_817127 prefixEnd_817127 := by exact prefixLift 817127
  have htrace : WordTrace (prefixWord ++ tailWord_817127) baseStart_817127 baseEnd_817127 := by
    simpa [prefixWord, tailWord_817127, baseEnd_817127] using wordTrace_append hprefix tailTrace_817127
  have hstable : (prefixWord ++ tailWord_817127).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817127).length < 2 ^ (prefixWord ++ tailWord_817127).sum := by decide
  have hdescent : baseEnd_817127 < baseStart_817127 := by decide
  rcases family_descends (prefixWord ++ tailWord_817127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817137 : List Nat := [1, 2, 2, 2, 5, 1, 3, 2, 2]
def baseStart_817137 : Nat := 118140960795 + 817137 * 2 ^ 59
def prefixEnd_817137 : Nat := 4983230072969 + 3 ^ 40 * 817137 * 2
def baseEnd_817137 : Nat := 372963592509399716826277

theorem tailTrace_817137 : CollatzResearch.WordTrace tailWord_817137 prefixEnd_817137 372963592509399716826277 := by
  unfold tailWord_817137
  simp only [CollatzResearch.WordTrace]
  refine ⟨29803434840659679734097665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19868956560439786489398443 29803434840659679734097665)
  ·
    refine ⟨22352576130494759800573249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29803434840659679734097665 22352576130494759800573249)
    ·
      refine ⟨16764432097871069850429937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22352576130494759800573249 16764432097871069850429937)
      ·
        refine ⟨12573324073403302387822453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16764432097871069850429937 12573324073403302387822453)
        ·
          refine ⟨1178749131881559598858355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12573324073403302387822453 1178749131881559598858355)
          ·
            refine ⟨1768123697822339398287533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1178749131881559598858355 1768123697822339398287533)
            ·
              refine ⟨663046386683377274357825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1768123697822339398287533 663046386683377274357825)
              ·
                refine ⟨497284790012532955768369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 663046386683377274357825 497284790012532955768369)
                ·
                  refine ⟨372963592509399716826277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 497284790012532955768369 372963592509399716826277)
                  ·
                    rfl

theorem cell20_817137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 3, 2, 2].length) (baseStart_817137 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_817137 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_817137 prefixEnd_817137 := by exact prefixLift 817137
  have htrace : WordTrace (prefixWord ++ tailWord_817137) baseStart_817137 baseEnd_817137 := by
    simpa [prefixWord, tailWord_817137, baseEnd_817137] using wordTrace_append hprefix tailTrace_817137
  have hstable : (prefixWord ++ tailWord_817137).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817137).length < 2 ^ (prefixWord ++ tailWord_817137).sum := by decide
  have hdescent : baseEnd_817137 < baseStart_817137 := by decide
  rcases family_descends (prefixWord ++ tailWord_817137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817207 : List Nat := [1, 1, 3, 1, 2, 2, 5, 5]
def baseStart_817207 : Nat := 118140960795 + 817207 * 2 ^ 59
def prefixEnd_817207 : Nat := 4983230072969 + 3 ^ 40 * 817207 * 2
def baseEnd_817207 : Nat := 124331847472263528164219

theorem tailTrace_817207 : CollatzResearch.WordTrace tailWord_817207 prefixEnd_817207 124331847472263528164219 := by
  unfold tailWord_817207
  simp only [CollatzResearch.WordTrace]
  refine ⟨29805987950406081689145875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19870658633604054459430583 29805987950406081689145875)
  ·
    refine ⟨44708981925609122533718813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29805987950406081689145875 44708981925609122533718813)
    ·
      refine ⟨16765868222103420950144555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44708981925609122533718813 16765868222103420950144555)
      ·
        refine ⟨25148802333155131425216833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16765868222103420950144555 25148802333155131425216833)
        ·
          refine ⟨18861601749866348568912625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25148802333155131425216833 18861601749866348568912625)
          ·
            refine ⟨14146201312399761426684469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18861601749866348568912625 14146201312399761426684469)
            ·
              refine ⟨1326206373037477633751669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14146201312399761426684469 1326206373037477633751669)
              ·
                refine ⟨124331847472263528164219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1326206373037477633751669 124331847472263528164219)
                ·
                  rfl

theorem cell20_817207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 5].length) (baseStart_817207 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_817207 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_817207 prefixEnd_817207 := by exact prefixLift 817207
  have htrace : WordTrace (prefixWord ++ tailWord_817207) baseStart_817207 baseEnd_817207 := by
    simpa [prefixWord, tailWord_817207, baseEnd_817207] using wordTrace_append hprefix tailTrace_817207
  have hstable : (prefixWord ++ tailWord_817207).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817207).length < 2 ^ (prefixWord ++ tailWord_817207).sum := by decide
  have hdescent : baseEnd_817207 < baseStart_817207 := by decide
  rcases family_descends (prefixWord ++ tailWord_817207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817217 : List Nat := [1, 2, 5, 1, 2, 2, 1, 2, 4]
def baseStart_817217 : Nat := 118140960795 + 817217 * 2 ^ 59
def prefixEnd_817217 : Nat := 4983230072969 + 3 ^ 40 * 817217 * 2
def baseEnd_817217 : Nat := 373000106689274994159283

theorem tailTrace_817217 : CollatzResearch.WordTrace tailWord_817217 prefixEnd_817217 373000106689274994159283 := by
  unfold tailWord_817217
  simp only [CollatzResearch.WordTrace]
  refine ⟨29806352680369853397009905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19870901786913235598006603 29806352680369853397009905)
  ·
    refine ⟨22354764510277390047757429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29806352680369853397009905 22354764510277390047757429)
    ·
      refine ⟨2095759172838505316977259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22354764510277390047757429 2095759172838505316977259)
      ·
        refine ⟨3143638759257757975465889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2095759172838505316977259 3143638759257757975465889)
        ·
          refine ⟨2357729069443318481599417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3143638759257757975465889 2357729069443318481599417)
          ·
            refine ⟨1768296802082488861199563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2357729069443318481599417 1768296802082488861199563)
            ·
              refine ⟨2652445203123733291799345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1768296802082488861199563 2652445203123733291799345)
              ·
                refine ⟨1989333902342799968849509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2652445203123733291799345 1989333902342799968849509)
                ·
                  refine ⟨373000106689274994159283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1989333902342799968849509 373000106689274994159283)
                  ·
                    rfl

theorem cell20_817217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 2, 4].length) (baseStart_817217 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_817217 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_817217 prefixEnd_817217 := by exact prefixLift 817217
  have htrace : WordTrace (prefixWord ++ tailWord_817217) baseStart_817217 baseEnd_817217 := by
    simpa [prefixWord, tailWord_817217, baseEnd_817217] using wordTrace_append hprefix tailTrace_817217
  have hstable : (prefixWord ++ tailWord_817217).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817217).length < 2 ^ (prefixWord ++ tailWord_817217).sum := by decide
  have hdescent : baseEnd_817217 < baseStart_817217 := by decide
  rcases family_descends (prefixWord ++ tailWord_817217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817248 : List Nat := [2, 1, 1, 3, 2, 5, 1, 2, 3]
def baseStart_817248 : Nat := 118140960795 + 817248 * 2 ^ 59
def prefixEnd_817248 : Nat := 4983230072969 + 3 ^ 40 * 817248 * 2
def baseEnd_817248 : Nat := 373014255933976664125823

theorem tailTrace_817248 : CollatzResearch.WordTrace tailWord_817248 prefixEnd_817248 373014255933976664125823 := by
  unfold tailWord_817248
  simp only [CollatzResearch.WordTrace]
  refine ⟨14903741671628772845694199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19871655562171697127592265 14903741671628772845694199)
  ·
    refine ⟨22355612507443159268541299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14903741671628772845694199 22355612507443159268541299)
    ·
      refine ⟨33533418761164738902811949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22355612507443159268541299 33533418761164738902811949)
      ·
        refine ⟨12575032035436777088554481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33533418761164738902811949 12575032035436777088554481)
        ·
          refine ⟨9431274026577582816415861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12575032035436777088554481 9431274026577582816415861)
          ·
            refine ⟨884181939991648389038987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9431274026577582816415861 884181939991648389038987)
            ·
              refine ⟨1326272909987472583558481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 884181939991648389038987 1326272909987472583558481)
              ·
                refine ⟨994704682490604437668861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1326272909987472583558481 994704682490604437668861)
                ·
                  refine ⟨373014255933976664125823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 994704682490604437668861 373014255933976664125823)
                  ·
                    rfl

theorem cell20_817248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 2, 3].length) (baseStart_817248 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_817248 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_817248 prefixEnd_817248 := by exact prefixLift 817248
  have htrace : WordTrace (prefixWord ++ tailWord_817248) baseStart_817248 baseEnd_817248 := by
    simpa [prefixWord, tailWord_817248, baseEnd_817248] using wordTrace_append hprefix tailTrace_817248
  have hstable : (prefixWord ++ tailWord_817248).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817248).length < 2 ^ (prefixWord ++ tailWord_817248).sum := by decide
  have hdescent : baseEnd_817248 < baseStart_817248 := by decide
  rcases family_descends (prefixWord ++ tailWord_817248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817255 : List Nat := [1, 1, 5, 1, 1, 2, 1, 6, 2]
def baseStart_817255 : Nat := 118140960795 + 817255 * 2 ^ 59
def prefixEnd_817255 : Nat := 4983230072969 + 3 ^ 40 * 817255 * 2
def baseEnd_817255 : Nat := 373017450924715750892461

theorem tailTrace_817255 : CollatzResearch.WordTrace tailWord_817255 prefixEnd_817255 373017450924715750892461 := by
  unfold tailWord_817255
  simp only [CollatzResearch.WordTrace]
  refine ⟨29807738654232185886893219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19871825769488123924595479 29807738654232185886893219)
  ·
    refine ⟨44711607981348278830339829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29807738654232185886893219 44711607981348278830339829)
    ·
      refine ⟨4191713248251401140344359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44711607981348278830339829 4191713248251401140344359)
      ·
        refine ⟨6287569872377101710516539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4191713248251401140344359 6287569872377101710516539)
        ·
          refine ⟨9431354808565652565774809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6287569872377101710516539 9431354808565652565774809)
          ·
            refine ⟨7073516106424239424331107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9431354808565652565774809 7073516106424239424331107)
            ·
              refine ⟨10610274159636359136496661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7073516106424239424331107 10610274159636359136496661)
              ·
                refine ⟨497356601232954334523281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10610274159636359136496661 497356601232954334523281)
                ·
                  refine ⟨373017450924715750892461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 497356601232954334523281 373017450924715750892461)
                  ·
                    rfl

theorem cell20_817255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 6, 2].length) (baseStart_817255 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_817255 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_817255 prefixEnd_817255 := by exact prefixLift 817255
  have htrace : WordTrace (prefixWord ++ tailWord_817255) baseStart_817255 baseEnd_817255 := by
    simpa [prefixWord, tailWord_817255, baseEnd_817255] using wordTrace_append hprefix tailTrace_817255
  have hstable : (prefixWord ++ tailWord_817255).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817255).length < 2 ^ (prefixWord ++ tailWord_817255).sum := by decide
  have hdescent : baseEnd_817255 < baseStart_817255 := by decide
  rcases family_descends (prefixWord ++ tailWord_817255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817276 : List Nat := [2, 2, 2, 1, 1, 4, 2, 2, 4]
def baseStart_817276 : Nat := 118140960795 + 817276 * 2 ^ 59
def prefixEnd_817276 : Nat := 4983230072969 + 3 ^ 40 * 817276 * 2
def baseEnd_817276 : Nat := 373027035896933011192375

theorem tailTrace_817276 : CollatzResearch.WordTrace tailWord_817276 prefixEnd_817276 373027035896933011192375 := by
  unfold tailWord_817276
  simp only [CollatzResearch.WordTrace]
  refine ⟨14904252293578053236703841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19872336391437404315605121 14904252293578053236703841)
  ·
    refine ⟨11178189220183539927527881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14904252293578053236703841 11178189220183539927527881)
    ·
      refine ⟨8383641915137654945645911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11178189220183539927527881 8383641915137654945645911)
      ·
        refine ⟨12575462872706482418468867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8383641915137654945645911 12575462872706482418468867)
        ·
          refine ⟨18863194309059723627703301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12575462872706482418468867 18863194309059723627703301)
          ·
            refine ⟨3536848932948698180194369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18863194309059723627703301 3536848932948698180194369)
            ·
              refine ⟨2652636699711523635145777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3536848932948698180194369 2652636699711523635145777)
              ·
                refine ⟨1989477524783642726359333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2652636699711523635145777 1989477524783642726359333)
                ·
                  refine ⟨373027035896933011192375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1989477524783642726359333 373027035896933011192375)
                  ·
                    rfl

theorem cell20_817276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 2, 4].length) (baseStart_817276 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_817276 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_817276 prefixEnd_817276 := by exact prefixLift 817276
  have htrace : WordTrace (prefixWord ++ tailWord_817276) baseStart_817276 baseEnd_817276 := by
    simpa [prefixWord, tailWord_817276, baseEnd_817276] using wordTrace_append hprefix tailTrace_817276
  have hstable : (prefixWord ++ tailWord_817276).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817276).length < 2 ^ (prefixWord ++ tailWord_817276).sum := by decide
  have hdescent : baseEnd_817276 < baseStart_817276 := by decide
  rcases family_descends (prefixWord ++ tailWord_817276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817283 : List Nat := [1, 1, 1, 3, 3, 4, 1, 6]
def baseStart_817283 : Nat := 118140960795 + 817283 * 2 ^ 59
def prefixEnd_817283 : Nat := 4983230072969 + 3 ^ 40 * 817283 * 2
def baseEnd_817283 : Nat := 124343410295890699319671

theorem tailTrace_817283 : CollatzResearch.WordTrace tailWord_817283 prefixEnd_817283 124343410295890699319671 := by
  unfold tailWord_817283
  simp only [CollatzResearch.WordTrace]
  refine ⟨29808759898130746668912503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19872506598753831112608335 29808759898130746668912503)
  ·
    refine ⟨44713139847196120003368755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29808759898130746668912503 44713139847196120003368755)
    ·
      refine ⟨67069709770794180005053133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44713139847196120003368755 67069709770794180005053133)
      ·
        refine ⟨25151141164047817501894925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67069709770794180005053133 25151141164047817501894925)
        ·
          refine ⟨9431677936517931563210597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25151141164047817501894925 9431677936517931563210597)
          ·
            refine ⟨1768439613097112168101987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9431677936517931563210597 1768439613097112168101987)
            ·
              refine ⟨2652659419645668252152981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1768439613097112168101987 2652659419645668252152981)
              ·
                refine ⟨124343410295890699319671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2652659419645668252152981 124343410295890699319671)
                ·
                  rfl

theorem cell20_817283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 6].length) (baseStart_817283 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_817283 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_817283 prefixEnd_817283 := by exact prefixLift 817283
  have htrace : WordTrace (prefixWord ++ tailWord_817283) baseStart_817283 baseEnd_817283 := by
    simpa [prefixWord, tailWord_817283, baseEnd_817283] using wordTrace_append hprefix tailTrace_817283
  have hstable : (prefixWord ++ tailWord_817283).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817283).length < 2 ^ (prefixWord ++ tailWord_817283).sum := by decide
  have hdescent : baseEnd_817283 < baseStart_817283 := by decide
  rcases family_descends (prefixWord ++ tailWord_817283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817302 : List Nat := [5, 3, 2, 1, 2, 1, 1, 1, 4]
def baseStart_817302 : Nat := 118140960795 + 817302 * 2 ^ 59
def prefixEnd_817302 : Nat := 4983230072969 + 3 ^ 40 * 817302 * 2
def baseEnd_817302 : Nat := 373038903005392476325603

theorem tailTrace_817302 : CollatzResearch.WordTrace tailWord_817302 prefixEnd_817302 373038903005392476325603 := by
  unfold tailWord_817302
  simp only [CollatzResearch.WordTrace]
  refine ⟨1863090805316369557115885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19872968590041275275902773 1863090805316369557115885)
  ·
    refine ⟨698659051993638583918457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1863090805316369557115885 698659051993638583918457)
    ·
      refine ⟨523994288995228937938843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 698659051993638583918457 523994288995228937938843)
      ·
        refine ⟨785991433492843406908265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 523994288995228937938843 785991433492843406908265)
        ·
          refine ⟨589493575119632555181199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 785991433492843406908265 589493575119632555181199)
          ·
            refine ⟨884240362679448832771799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 589493575119632555181199 884240362679448832771799)
            ·
              refine ⟨1326360544019173249157699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 884240362679448832771799 1326360544019173249157699)
              ·
                refine ⟨1989540816028759873736549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1326360544019173249157699 1989540816028759873736549)
                ·
                  refine ⟨373038903005392476325603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1989540816028759873736549 373038903005392476325603)
                  ·
                    rfl

theorem cell20_817302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_817302 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_817302 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_817302 prefixEnd_817302 := by exact prefixLift 817302
  have htrace : WordTrace (prefixWord ++ tailWord_817302) baseStart_817302 baseEnd_817302 := by
    simpa [prefixWord, tailWord_817302, baseEnd_817302] using wordTrace_append hprefix tailTrace_817302
  have hstable : (prefixWord ++ tailWord_817302).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817302).length < 2 ^ (prefixWord ++ tailWord_817302).sum := by decide
  have hdescent : baseEnd_817302 < baseStart_817302 := by decide
  rcases family_descends (prefixWord ++ tailWord_817302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817362 : List Nat := [3, 2, 2, 2, 1, 3, 2, 2, 3]
def baseStart_817362 : Nat := 118140960795 + 817362 * 2 ^ 59
def prefixEnd_817362 : Nat := 4983230072969 + 3 ^ 40 * 817362 * 2
def baseEnd_817362 : Nat := 373066288640298934325357

theorem tailTrace_817362 : CollatzResearch.WordTrace tailWord_817362 prefixEnd_817362 373066288640298934325357 := by
  unfold tailWord_817362
  simp only [CollatzResearch.WordTrace]
  refine ⟨7452910316211135790259585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19874427509896362107358893 7452910316211135790259585)
  ·
    refine ⟨5589682737158351842694689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7452910316211135790259585 5589682737158351842694689)
    ·
      refine ⟨4192262052868763882021017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5589682737158351842694689 4192262052868763882021017)
      ·
        refine ⟨3144196539651572911515763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4192262052868763882021017 3144196539651572911515763)
        ·
          refine ⟨4716294809477359367273645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3144196539651572911515763 4716294809477359367273645)
          ·
            refine ⟨1768610553554009762727617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4716294809477359367273645 1768610553554009762727617)
            ·
              refine ⟨1326457915165507322045713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1768610553554009762727617 1326457915165507322045713)
              ·
                refine ⟨994843436374130491534285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1326457915165507322045713 994843436374130491534285)
                ·
                  refine ⟨373066288640298934325357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 994843436374130491534285 373066288640298934325357)
                  ·
                    rfl

theorem cell20_817362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 2, 3].length) (baseStart_817362 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_817362 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_817362 prefixEnd_817362 := by exact prefixLift 817362
  have htrace : WordTrace (prefixWord ++ tailWord_817362) baseStart_817362 baseEnd_817362 := by
    simpa [prefixWord, tailWord_817362, baseEnd_817362] using wordTrace_append hprefix tailTrace_817362
  have hstable : (prefixWord ++ tailWord_817362).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817362).length < 2 ^ (prefixWord ++ tailWord_817362).sum := by decide
  have hdescent : baseEnd_817362 < baseStart_817362 := by decide
  rcases family_descends (prefixWord ++ tailWord_817362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817372 : List Nat := [2, 2, 5, 2, 1, 2, 1, 5]
def baseStart_817372 : Nat := 118140960795 + 817372 * 2 ^ 59
def prefixEnd_817372 : Nat := 4983230072969 + 3 ^ 40 * 817372 * 2
def baseEnd_817372 : Nat := 124356950970927781330661

theorem tailTrace_817372 : CollatzResearch.WordTrace tailWord_817372 prefixEnd_817372 124356950970927781330661 := by
  unfold tailWord_817372
  simp only [CollatzResearch.WordTrace]
  refine ⟨14906002997404157434451185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19874670663205543245934913 14906002997404157434451185)
  ·
    refine ⟨11179502248053118075838389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14906002997404157434451185 11179502248053118075838389)
    ·
      refine ⟨1048078335754979819609849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11179502248053118075838389 1048078335754979819609849)
      ·
        refine ⟨786058751816234864707387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1048078335754979819609849 786058751816234864707387)
        ·
          refine ⟨1179088127724352297061081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 786058751816234864707387 1179088127724352297061081)
          ·
            refine ⟨884316095793264222795811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1179088127724352297061081 884316095793264222795811)
            ·
              refine ⟨1326474143689896334193717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 884316095793264222795811 1326474143689896334193717)
              ·
                refine ⟨124356950970927781330661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1326474143689896334193717 124356950970927781330661)
                ·
                  rfl

theorem cell20_817372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 5].length) (baseStart_817372 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_817372 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_817372 prefixEnd_817372 := by exact prefixLift 817372
  have htrace : WordTrace (prefixWord ++ tailWord_817372) baseStart_817372 baseEnd_817372 := by
    simpa [prefixWord, tailWord_817372, baseEnd_817372] using wordTrace_append hprefix tailTrace_817372
  have hstable : (prefixWord ++ tailWord_817372).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817372).length < 2 ^ (prefixWord ++ tailWord_817372).sum := by decide
  have hdescent : baseEnd_817372 < baseStart_817372 := by decide
  rcases family_descends (prefixWord ++ tailWord_817372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817407 : List Nat := [1, 1, 2, 2, 1, 4, 4, 3, 2]
def baseStart_817407 : Nat := 118140960795 + 817407 * 2 ^ 59
def prefixEnd_817407 : Nat := 4983230072969 + 3 ^ 40 * 817407 * 2
def baseEnd_817407 : Nat := 373086827866478777825173

theorem tailTrace_817407 : CollatzResearch.WordTrace tailWord_817407 prefixEnd_817407 373086827866478777825173 := by
  unfold tailWord_817407
  simp only [CollatzResearch.WordTrace]
  refine ⟨29813282549681515846426475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19875521699787677230950983 29813282549681515846426475)
  ·
    refine ⟨44719923824522273769639713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29813282549681515846426475 44719923824522273769639713)
    ·
      refine ⟨33539942868391705327229785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44719923824522273769639713 33539942868391705327229785)
      ·
        refine ⟨25154957151293778995422339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33539942868391705327229785 25154957151293778995422339)
        ·
          refine ⟨37732435726940668493133509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25154957151293778995422339 37732435726940668493133509)
          ·
            refine ⟨7074831698801375342462533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37732435726940668493133509 7074831698801375342462533)
            ·
              refine ⟨1326530943525257876711725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7074831698801375342462533 1326530943525257876711725)
              ·
                refine ⟨497449103821971703766897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1326530943525257876711725 497449103821971703766897)
                ·
                  refine ⟨373086827866478777825173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 497449103821971703766897 373086827866478777825173)
                  ·
                    rfl

theorem cell20_817407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 3, 2].length) (baseStart_817407 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_817407 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_817407 prefixEnd_817407 := by exact prefixLift 817407
  have htrace : WordTrace (prefixWord ++ tailWord_817407) baseStart_817407 baseEnd_817407 := by
    simpa [prefixWord, tailWord_817407, baseEnd_817407] using wordTrace_append hprefix tailTrace_817407
  have hstable : (prefixWord ++ tailWord_817407).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817407).length < 2 ^ (prefixWord ++ tailWord_817407).sum := by decide
  have hdescent : baseEnd_817407 < baseStart_817407 := by decide
  rcases family_descends (prefixWord ++ tailWord_817407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817411 : List Nat := [1, 1, 1, 3, 2, 3, 1, 2, 6]
def baseStart_817411 : Nat := 118140960795 + 817411 * 2 ^ 59
def prefixEnd_817411 : Nat := 4983230072969 + 3 ^ 40 * 817411 * 2
def baseEnd_817411 : Nat := 373088653575472541691823

theorem tailTrace_817411 : CollatzResearch.WordTrace tailWord_817411 prefixEnd_817411 373088653575472541691823 := by
  unfold tailWord_817411
  simp only [CollatzResearch.WordTrace]
  refine ⟨29813428441667024529572087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19875618961111349686381391 29813428441667024529572087)
  ·
    refine ⟨44720142662500536794358131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29813428441667024529572087 44720142662500536794358131)
    ·
      refine ⟨67080213993750805191537197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44720142662500536794358131 67080213993750805191537197)
      ·
        refine ⟨25155080247656551946826449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67080213993750805191537197 25155080247656551946826449)
        ·
          refine ⟨18866310185742413960119837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25155080247656551946826449 18866310185742413960119837)
          ·
            refine ⟨7074866319653405235044939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18866310185742413960119837 7074866319653405235044939)
            ·
              refine ⟨10612299479480107852567409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7074866319653405235044939 10612299479480107852567409)
              ·
                refine ⟨7959224609610080889425557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10612299479480107852567409 7959224609610080889425557)
                ·
                  refine ⟨373088653575472541691823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7959224609610080889425557 373088653575472541691823)
                  ·
                    rfl

theorem cell20_817411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 6].length) (baseStart_817411 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_817411 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_817411 prefixEnd_817411 := by exact prefixLift 817411
  have htrace : WordTrace (prefixWord ++ tailWord_817411) baseStart_817411 baseEnd_817411 := by
    simpa [prefixWord, tailWord_817411, baseEnd_817411] using wordTrace_append hprefix tailTrace_817411
  have hstable : (prefixWord ++ tailWord_817411).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817411).length < 2 ^ (prefixWord ++ tailWord_817411).sum := by decide
  have hdescent : baseEnd_817411 < baseStart_817411 := by decide
  rcases family_descends (prefixWord ++ tailWord_817411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817448 : List Nat := [2, 1, 5, 1, 4, 1, 2, 4]
def baseStart_817448 : Nat := 118140960795 + 817448 * 2 ^ 59
def prefixEnd_817448 : Nat := 4983230072969 + 3 ^ 40 * 817448 * 2
def baseEnd_817448 : Nat := 124368513794554952486113

theorem tailTrace_817448 : CollatzResearch.WordTrace tailWord_817448 prefixEnd_817448 124368513794554952486113 := by
  unfold tailWord_817448
  simp only [CollatzResearch.WordTrace]
  refine ⟨14907388971266489924334499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19876518628355319899112665 14907388971266489924334499)
  ·
    refine ⟨22361083456899734886501749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14907388971266489924334499 22361083456899734886501749)
    ·
      refine ⟨2096351574084350145609539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22361083456899734886501749 2096351574084350145609539)
      ·
        refine ⟨3144527361126525218414309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2096351574084350145609539 3144527361126525218414309)
        ·
          refine ⟨589598880211223478452683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3144527361126525218414309 589598880211223478452683)
          ·
            refine ⟨884398320316835217679025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 589598880211223478452683 884398320316835217679025)
            ·
              refine ⟨663298740237626413259269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 884398320316835217679025 663298740237626413259269)
              ·
                refine ⟨124368513794554952486113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 663298740237626413259269 124368513794554952486113)
                ·
                  rfl

theorem cell20_817448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 2, 4].length) (baseStart_817448 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_817448 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_817448 prefixEnd_817448 := by exact prefixLift 817448
  have htrace : WordTrace (prefixWord ++ tailWord_817448) baseStart_817448 baseEnd_817448 := by
    simpa [prefixWord, tailWord_817448, baseEnd_817448] using wordTrace_append hprefix tailTrace_817448
  have hstable : (prefixWord ++ tailWord_817448).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817448).length < 2 ^ (prefixWord ++ tailWord_817448).sum := by decide
  have hdescent : baseEnd_817448 < baseStart_817448 := by decide
  rcases family_descends (prefixWord ++ tailWord_817448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817480 : List Nat := [2, 1, 3, 1, 1, 2, 4, 1, 5]
def baseStart_817480 : Nat := 118140960795 + 817480 * 2 ^ 59
def prefixEnd_817480 : Nat := 4983230072969 + 3 ^ 40 * 817480 * 2
def baseEnd_817480 : Nat := 373120147055614968391541

theorem tailTrace_817480 : CollatzResearch.WordTrace tailWord_817480 prefixEnd_817480 373120147055614968391541 := by
  unfold tailWord_817480
  simp only [CollatzResearch.WordTrace]
  refine ⟨14907972539208524656916947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19877296718944699542555929 14907972539208524656916947)
  ·
    refine ⟨22361958808812786985375421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14907972539208524656916947 22361958808812786985375421)
    ·
      refine ⟨8385734553304795119515783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22361958808812786985375421 8385734553304795119515783)
      ·
        refine ⟨12578601829957192679273675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8385734553304795119515783 12578601829957192679273675)
        ·
          refine ⟨18867902744935789018910513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12578601829957192679273675 18867902744935789018910513)
          ·
            refine ⟨14150927058701841764182885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18867902744935789018910513 14150927058701841764182885)
            ·
              refine ⟨2653298823506595330784291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14150927058701841764182885 2653298823506595330784291)
              ·
                refine ⟨3979948235259892996176437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2653298823506595330784291 3979948235259892996176437)
                ·
                  refine ⟨373120147055614968391541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3979948235259892996176437 373120147055614968391541)
                  ·
                    rfl

theorem cell20_817480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 5].length) (baseStart_817480 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_817480 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_817480 prefixEnd_817480 := by exact prefixLift 817480
  have htrace : WordTrace (prefixWord ++ tailWord_817480) baseStart_817480 baseEnd_817480 := by
    simpa [prefixWord, tailWord_817480, baseEnd_817480] using wordTrace_append hprefix tailTrace_817480
  have hstable : (prefixWord ++ tailWord_817480).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817480).length < 2 ^ (prefixWord ++ tailWord_817480).sum := by decide
  have hdescent : baseEnd_817480 < baseStart_817480 := by decide
  rcases family_descends (prefixWord ++ tailWord_817480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817487 : List Nat := [1, 1, 2, 1, 1, 2, 1, 7, 4]
def baseStart_817487 : Nat := 118140960795 + 817487 * 2 ^ 59
def prefixEnd_817487 : Nat := 4983230072969 + 3 ^ 40 * 817487 * 2
def baseEnd_817487 : Nat := 373123342046354055158179

theorem tailTrace_817487 : CollatzResearch.WordTrace tailWord_817487 prefixEnd_817487 373123342046354055158179 := by
  unfold tailWord_817487
  simp only [CollatzResearch.WordTrace]
  refine ⟨29816200389391689509338715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19877466926261126339559143 29816200389391689509338715)
  ·
    refine ⟨44724300584087534264008073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29816200389391689509338715 44724300584087534264008073)
    ·
      refine ⟨33543225438065650698006055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44724300584087534264008073 33543225438065650698006055)
      ·
        refine ⟨50314838157098476047009083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33543225438065650698006055 50314838157098476047009083)
        ·
          refine ⟨75472257235647714070513625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50314838157098476047009083 75472257235647714070513625)
          ·
            refine ⟨56604192926735785552885219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75472257235647714070513625 56604192926735785552885219)
            ·
              refine ⟨84906289390103678329327829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56604192926735785552885219 84906289390103678329327829)
              ·
                refine ⟨1989991157580554960843621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 84906289390103678329327829 1989991157580554960843621)
                ·
                  refine ⟨373123342046354055158179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1989991157580554960843621 373123342046354055158179)
                  ·
                    rfl

theorem cell20_817487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 7, 4].length) (baseStart_817487 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_817487 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_817487 prefixEnd_817487 := by exact prefixLift 817487
  have htrace : WordTrace (prefixWord ++ tailWord_817487) baseStart_817487 baseEnd_817487 := by
    simpa [prefixWord, tailWord_817487, baseEnd_817487] using wordTrace_append hprefix tailTrace_817487
  have hstable : (prefixWord ++ tailWord_817487).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817487).length < 2 ^ (prefixWord ++ tailWord_817487).sum := by decide
  have hdescent : baseEnd_817487 < baseStart_817487 := by decide
  rcases family_descends (prefixWord ++ tailWord_817487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817493 : List Nat := [1, 3, 2, 2, 4, 2, 2, 1, 3]
def baseStart_817493 : Nat := 118140960795 + 817493 * 2 ^ 59
def prefixEnd_817493 : Nat := 4983230072969 + 3 ^ 40 * 817493 * 2
def baseEnd_817493 : Nat := 373126080609844700958155

theorem tailTrace_817493 : CollatzResearch.WordTrace tailWord_817493 prefixEnd_817493 373126080609844700958155 := by
  unfold tailWord_817493
  simp only [CollatzResearch.WordTrace]
  refine ⟨29816419227369952534057133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19877612818246635022704755 29816419227369952534057133)
  ·
    refine ⟨11181157210263732200271425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29816419227369952534057133 11181157210263732200271425)
    ·
      refine ⟨8385867907697799150203569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11181157210263732200271425 8385867907697799150203569)
      ·
        refine ⟨6289400930773349362652677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8385867907697799150203569 6289400930773349362652677)
        ·
          refine ⟨1179262674520003005497377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6289400930773349362652677 1179262674520003005497377)
          ·
            refine ⟨884447005890002254123033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1179262674520003005497377 884447005890002254123033)
            ·
              refine ⟨663335254417501690592275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 884447005890002254123033 663335254417501690592275)
              ·
                refine ⟨995002881626252535888413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 663335254417501690592275 995002881626252535888413)
                ·
                  refine ⟨373126080609844700958155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 995002881626252535888413 373126080609844700958155)
                  ·
                    rfl

theorem cell20_817493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 2, 1, 3].length) (baseStart_817493 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_817493 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_817493 prefixEnd_817493 := by exact prefixLift 817493
  have htrace : WordTrace (prefixWord ++ tailWord_817493) baseStart_817493 baseEnd_817493 := by
    simpa [prefixWord, tailWord_817493, baseEnd_817493] using wordTrace_append hprefix tailTrace_817493
  have hstable : (prefixWord ++ tailWord_817493).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817493).length < 2 ^ (prefixWord ++ tailWord_817493).sum := by decide
  have hdescent : baseEnd_817493 < baseStart_817493 := by decide
  rcases family_descends (prefixWord ++ tailWord_817493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817511 : List Nat := [1, 1, 5, 1, 3, 1, 2, 6]
def baseStart_817511 : Nat := 118140960795 + 817511 * 2 ^ 59
def prefixEnd_817511 : Nat := 4983230072969 + 3 ^ 40 * 817511 * 2
def baseEnd_817511 : Nat := 124378098766772212786027

theorem tailTrace_817511 : CollatzResearch.WordTrace tailWord_817511 prefixEnd_817511 124378098766772212786027 := by
  unfold tailWord_817511
  simp only [CollatzResearch.WordTrace]
  refine ⟨29817075741304741608212387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19878050494203161072141591 29817075741304741608212387)
  ·
    refine ⟨44725613611957112412318581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29817075741304741608212387 44725613611957112412318581)
    ·
      refine ⟨4193026276120979288654867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44725613611957112412318581 4193026276120979288654867)
      ·
        refine ⟨6289539414181468932982301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4193026276120979288654867 6289539414181468932982301)
        ·
          refine ⟨2358577280318050849868363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6289539414181468932982301 2358577280318050849868363)
          ·
            refine ⟨3537865920477076274802545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2358577280318050849868363 3537865920477076274802545)
            ·
              refine ⟨2653399440357807206101909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3537865920477076274802545 2653399440357807206101909)
              ·
                refine ⟨124378098766772212786027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2653399440357807206101909 124378098766772212786027)
                ·
                  rfl

theorem cell20_817511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 6].length) (baseStart_817511 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_817511 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_817511 prefixEnd_817511 := by exact prefixLift 817511
  have htrace : WordTrace (prefixWord ++ tailWord_817511) baseStart_817511 baseEnd_817511 := by
    simpa [prefixWord, tailWord_817511, baseEnd_817511] using wordTrace_append hprefix tailTrace_817511
  have hstable : (prefixWord ++ tailWord_817511).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817511).length < 2 ^ (prefixWord ++ tailWord_817511).sum := by decide
  have hdescent : baseEnd_817511 < baseStart_817511 := by decide
  rcases family_descends (prefixWord ++ tailWord_817511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817576 : List Nat := [2, 1, 6, 1, 1, 1, 1, 5, 2]
def baseStart_817576 : Nat := 118140960795 + 817576 * 2 ^ 59
def prefixEnd_817576 : Nat := 4983230072969 + 3 ^ 40 * 817576 * 2
def baseEnd_817576 : Nat := 373163964071465301191149

theorem tailTrace_817576 : CollatzResearch.WordTrace tailWord_817576 prefixEnd_817576 373163964071465301191149 := by
  unfold tailWord_817576
  simp only [CollatzResearch.WordTrace]
  refine ⟨14909723243034628854664291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19879630990712838472885721 14909723243034628854664291)
  ·
    refine ⟨22364584864551943281996437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14909723243034628854664291 22364584864551943281996437)
    ·
      refine ⟨1048339915525872341343583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 22364584864551943281996437 1048339915525872341343583)
      ·
        refine ⟨1572509873288808512015375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1048339915525872341343583 1572509873288808512015375)
        ·
          refine ⟨2358764809933212768023063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1572509873288808512015375 2358764809933212768023063)
          ·
            refine ⟨3538147214899819152034595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2358764809933212768023063 3538147214899819152034595)
            ·
              refine ⟨5307220822349728728051893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3538147214899819152034595 5307220822349728728051893)
              ·
                refine ⟨497551952095287068254865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5307220822349728728051893 497551952095287068254865)
                ·
                  refine ⟨373163964071465301191149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 497551952095287068254865 373163964071465301191149)
                  ·
                    rfl

theorem cell20_817576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 5, 2].length) (baseStart_817576 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_817576 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_817576 prefixEnd_817576 := by exact prefixLift 817576
  have htrace : WordTrace (prefixWord ++ tailWord_817576) baseStart_817576 baseEnd_817576 := by
    simpa [prefixWord, tailWord_817576, baseEnd_817576] using wordTrace_append hprefix tailTrace_817576
  have hstable : (prefixWord ++ tailWord_817576).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817576).length < 2 ^ (prefixWord ++ tailWord_817576).sum := by decide
  have hdescent : baseEnd_817576 < baseStart_817576 := by decide
  rcases family_descends (prefixWord ++ tailWord_817576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817597 : List Nat := [1, 4, 1, 2, 2, 2, 2, 4, 2]
def baseStart_817597 : Nat := 118140960795 + 817597 * 2 ^ 59
def prefixEnd_817597 : Nat := 4983230072969 + 3 ^ 40 * 817597 * 2
def baseEnd_817597 : Nat := 373173549043682561491063

theorem tailTrace_817597 : CollatzResearch.WordTrace tailWord_817597 prefixEnd_817597 373173549043682561491063 := by
  unfold tailWord_817597
  simp only [CollatzResearch.WordTrace]
  refine ⟨29820212418993178295843045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19880141612662118863895363 29820212418993178295843045)
  ·
    refine ⟨5591289828561220930470571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29820212418993178295843045 5591289828561220930470571)
    ·
      refine ⟨8386934742841831395705857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5591289828561220930470571 8386934742841831395705857)
      ·
        refine ⟨6290201057131373546779393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8386934742841831395705857 6290201057131373546779393)
        ·
          refine ⟨4717650792848530160084545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6290201057131373546779393 4717650792848530160084545)
          ·
            refine ⟨3538238094636397620063409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4717650792848530160084545 3538238094636397620063409)
            ·
              refine ⟨2653678570977298215047557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3538238094636397620063409 2653678570977298215047557)
              ·
                refine ⟨497564732058243415321417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2653678570977298215047557 497564732058243415321417)
                ·
                  refine ⟨373173549043682561491063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 497564732058243415321417 373173549043682561491063)
                  ·
                    rfl

theorem cell20_817597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 4, 2].length) (baseStart_817597 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_817597 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_817597 prefixEnd_817597 := by exact prefixLift 817597
  have htrace : WordTrace (prefixWord ++ tailWord_817597) baseStart_817597 baseEnd_817597 := by
    simpa [prefixWord, tailWord_817597, baseEnd_817597] using wordTrace_append hprefix tailTrace_817597
  have hstable : (prefixWord ++ tailWord_817597).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817597).length < 2 ^ (prefixWord ++ tailWord_817597).sum := by decide
  have hdescent : baseEnd_817597 < baseStart_817597 := by decide
  rcases family_descends (prefixWord ++ tailWord_817597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817703 : List Nat := [1, 1, 7, 2, 2, 1, 2, 2, 2]
def baseStart_817703 : Nat := 118140960795 + 817703 * 2 ^ 59
def prefixEnd_817703 : Nat := 4983230072969 + 3 ^ 40 * 817703 * 2
def baseEnd_817703 : Nat := 373221930332017303957297

theorem tailTrace_817703 : CollatzResearch.WordTrace tailWord_817703 prefixEnd_817703 373221930332017303957297 := by
  unfold tailWord_817703
  simp only [CollatzResearch.WordTrace]
  refine ⟨29824078556609158399201763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19882719037739438932801175 29824078556609158399201763)
  ·
    refine ⟨44736117834913737598802645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29824078556609158399201763 44736117834913737598802645)
    ·
      refine ⟨1048502761755790724971937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 44736117834913737598802645 1048502761755790724971937)
      ·
        refine ⟨786377071316843043728953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1048502761755790724971937 786377071316843043728953)
        ·
          refine ⟨589782803487632282796715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 786377071316843043728953 589782803487632282796715)
          ·
            refine ⟨884674205231448424195073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 589782803487632282796715 884674205231448424195073)
            ·
              refine ⟨663505653923586318146305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 884674205231448424195073 663505653923586318146305)
              ·
                refine ⟨497629240442689738609729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 663505653923586318146305 497629240442689738609729)
                ·
                  refine ⟨373221930332017303957297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 497629240442689738609729 373221930332017303957297)
                  ·
                    rfl

theorem cell20_817703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 2, 2, 2].length) (baseStart_817703 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_817703 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_817703 prefixEnd_817703 := by exact prefixLift 817703
  have htrace : WordTrace (prefixWord ++ tailWord_817703) baseStart_817703 baseEnd_817703 := by
    simpa [prefixWord, tailWord_817703, baseEnd_817703] using wordTrace_append hprefix tailTrace_817703
  have hstable : (prefixWord ++ tailWord_817703).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817703).length < 2 ^ (prefixWord ++ tailWord_817703).sum := by decide
  have hdescent : baseEnd_817703 < baseStart_817703 := by decide
  rcases family_descends (prefixWord ++ tailWord_817703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817704 : List Nat := [2, 1, 5, 2, 1, 2, 2, 2, 3]
def baseStart_817704 : Nat := 118140960795 + 817704 * 2 ^ 59
def prefixEnd_817704 : Nat := 4983230072969 + 3 ^ 40 * 817704 * 2
def baseEnd_817704 : Nat := 373222386759265744923959

theorem tailTrace_817704 : CollatzResearch.WordTrace tailWord_817704 prefixEnd_817704 373222386759265744923959 := by
  unfold tailWord_817704
  simp only [CollatzResearch.WordTrace]
  refine ⟨14912057514802767784994083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19882743353070357046658777 14912057514802767784994083)
  ·
    refine ⟨22368086272204151677491125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14912057514802767784994083 22368086272204151677491125)
    ·
      refine ⟨2097008088019139219764793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22368086272204151677491125 2097008088019139219764793)
      ·
        refine ⟨1572756066014354414823595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2097008088019139219764793 1572756066014354414823595)
        ·
          refine ⟨2359134099021531622235393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1572756066014354414823595 2359134099021531622235393)
          ·
            refine ⟨1769350574266148716676545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2359134099021531622235393 1769350574266148716676545)
            ·
              refine ⟨1327012930699611537507409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1769350574266148716676545 1327012930699611537507409)
              ·
                refine ⟨995259698024708653130557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1327012930699611537507409 995259698024708653130557)
                ·
                  refine ⟨373222386759265744923959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 995259698024708653130557 373222386759265744923959)
                  ·
                    rfl

theorem cell20_817704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 2, 3].length) (baseStart_817704 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_817704 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_817704 prefixEnd_817704 := by exact prefixLift 817704
  have htrace : WordTrace (prefixWord ++ tailWord_817704) baseStart_817704 baseEnd_817704 := by
    simpa [prefixWord, tailWord_817704, baseEnd_817704] using wordTrace_append hprefix tailTrace_817704
  have hstable : (prefixWord ++ tailWord_817704).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817704).length < 2 ^ (prefixWord ++ tailWord_817704).sum := by decide
  have hdescent : baseEnd_817704 < baseStart_817704 := by decide
  rcases family_descends (prefixWord ++ tailWord_817704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817715 : List Nat := [1, 1, 1, 2, 4, 2, 2, 3, 4]
def baseStart_817715 : Nat := 118140960795 + 817715 * 2 ^ 59
def prefixEnd_817715 : Nat := 4983230072969 + 3 ^ 40 * 817715 * 2
def baseEnd_817715 : Nat := 373227407458998595557247

theorem tailTrace_817715 : CollatzResearch.WordTrace tailWord_817715 prefixEnd_817715 373227407458998595557247 := by
  unfold tailWord_817715
  simp only [CollatzResearch.WordTrace]
  refine ⟨29824516232565684448638599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19883010821710456299092399 29824516232565684448638599)
  ·
    refine ⟨44736774348848526672957899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29824516232565684448638599 44736774348848526672957899)
    ·
      refine ⟨67105161523272790009436849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44736774348848526672957899 67105161523272790009436849)
      ·
        refine ⟨50328871142454592507077637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67105161523272790009436849 50328871142454592507077637)
        ·
          refine ⟨9436663339210236095077057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50328871142454592507077637 9436663339210236095077057)
          ·
            refine ⟨7077497504407677071307793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9436663339210236095077057 7077497504407677071307793)
            ·
              refine ⟨5308123128305757803480845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7077497504407677071307793 5308123128305757803480845)
              ·
                refine ⟨1990546173114659176305317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5308123128305757803480845 1990546173114659176305317)
                ·
                  refine ⟨373227407458998595557247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1990546173114659176305317 373227407458998595557247)
                  ·
                    rfl

theorem cell20_817715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 3, 4].length) (baseStart_817715 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_817715 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_817715 prefixEnd_817715 := by exact prefixLift 817715
  have htrace : WordTrace (prefixWord ++ tailWord_817715) baseStart_817715 baseEnd_817715 := by
    simpa [prefixWord, tailWord_817715, baseEnd_817715] using wordTrace_append hprefix tailTrace_817715
  have hstable : (prefixWord ++ tailWord_817715).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817715).length < 2 ^ (prefixWord ++ tailWord_817715).sum := by decide
  have hdescent : baseEnd_817715 < baseStart_817715 := by decide
  rcases family_descends (prefixWord ++ tailWord_817715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817718 : List Nat := [5, 1, 2, 1, 2, 1, 3, 5]
def baseStart_817718 : Nat := 118140960795 + 817718 * 2 ^ 59
def prefixEnd_817718 : Nat := 4983230072969 + 3 ^ 40 * 817718 * 2
def baseEnd_817718 : Nat := 124409592246914639485745

theorem tailTrace_817718 : CollatzResearch.WordTrace tailWord_817718 prefixEnd_817718 124409592246914639485745 := by
  unfold tailWord_817718
  simp only [CollatzResearch.WordTrace]
  refine ⟨1864039103222175997562363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19883083767703210640665205 1864039103222175997562363)
  ·
    refine ⟨2796058654833263996343545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1864039103222175997562363 2796058654833263996343545)
    ·
      refine ⟨2097043991124947997257659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2796058654833263996343545 2097043991124947997257659)
      ·
        refine ⟨3145565986687421995886489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2097043991124947997257659 3145565986687421995886489)
        ·
          refine ⟨2359174490015566496914867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3145565986687421995886489 2359174490015566496914867)
          ·
            refine ⟨3538761735023349745372301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2359174490015566496914867 3538761735023349745372301)
            ·
              refine ⟨1327035650633756154514613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3538761735023349745372301 1327035650633756154514613)
              ·
                refine ⟨124409592246914639485745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1327035650633756154514613 124409592246914639485745)
                ·
                  rfl

theorem cell20_817718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_817718 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_817718 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_817718 prefixEnd_817718 := by exact prefixLift 817718
  have htrace : WordTrace (prefixWord ++ tailWord_817718) baseStart_817718 baseEnd_817718 := by
    simpa [prefixWord, tailWord_817718, baseEnd_817718] using wordTrace_append hprefix tailTrace_817718
  have hstable : (prefixWord ++ tailWord_817718).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817718).length < 2 ^ (prefixWord ++ tailWord_817718).sum := by decide
  have hdescent : baseEnd_817718 < baseStart_817718 := by decide
  rcases family_descends (prefixWord ++ tailWord_817718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817725 : List Nat := [1, 4, 1, 3, 2, 1, 2, 3, 3]
def baseStart_817725 : Nat := 118140960795 + 817725 * 2 ^ 59
def prefixEnd_817725 : Nat := 4983230072969 + 3 ^ 40 * 817725 * 2
def baseEnd_817725 : Nat := 373231971731483005223873

theorem tailTrace_817725 : CollatzResearch.WordTrace tailWord_817725 prefixEnd_817725 373231971731483005223873 := by
  unfold tailWord_817725
  simp only [CollatzResearch.WordTrace]
  refine ⟨29824880962529456156502629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19883253975019637437668419 29824880962529456156502629)
  ·
    refine ⟨5592165180474273029344243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29824880962529456156502629 5592165180474273029344243)
    ·
      refine ⟨8388247770711409544016365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5592165180474273029344243 8388247770711409544016365)
      ·
        refine ⟨3145592914016778579006137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8388247770711409544016365 3145592914016778579006137)
        ·
          refine ⟨2359194685512583934254603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3145592914016778579006137 2359194685512583934254603)
          ·
            refine ⟨3538792028268875901381905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2359194685512583934254603 3538792028268875901381905)
            ·
              refine ⟨2654094021201656926036429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3538792028268875901381905 2654094021201656926036429)
              ·
                refine ⟨995285257950621347263661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2654094021201656926036429 995285257950621347263661)
                ·
                  refine ⟨373231971731483005223873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 995285257950621347263661 373231971731483005223873)
                  ·
                    rfl

theorem cell20_817725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 3, 3].length) (baseStart_817725 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_817725 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_817725 prefixEnd_817725 := by exact prefixLift 817725
  have htrace : WordTrace (prefixWord ++ tailWord_817725) baseStart_817725 baseEnd_817725 := by
    simpa [prefixWord, tailWord_817725, baseEnd_817725] using wordTrace_append hprefix tailTrace_817725
  have hstable : (prefixWord ++ tailWord_817725).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817725).length < 2 ^ (prefixWord ++ tailWord_817725).sum := by decide
  have hdescent : baseEnd_817725 < baseStart_817725 := by decide
  rcases family_descends (prefixWord ++ tailWord_817725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817746 : List Nat := [3, 2, 2, 1, 2, 1, 2, 2, 5]
def baseStart_817746 : Nat := 118140960795 + 817746 * 2 ^ 59
def prefixEnd_817746 : Nat := 4983230072969 + 3 ^ 40 * 817746 * 2
def baseEnd_817746 : Nat := 373241556703700265523787

theorem tailTrace_817746 : CollatzResearch.WordTrace tailWord_817746 prefixEnd_817746 373241556703700265523787 := by
  unfold tailWord_817746
  simp only [CollatzResearch.WordTrace]
  refine ⟨7456411723863344185754273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19883764596968917828678061 7456411723863344185754273)
  ·
    refine ⟨5592308792897508139315705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7456411723863344185754273 5592308792897508139315705)
    ·
      refine ⟨4194231594673131104486779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5592308792897508139315705 4194231594673131104486779)
      ·
        refine ⟨6291347392009696656730169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4194231594673131104486779 6291347392009696656730169)
        ·
          refine ⟨4718510544007272492547627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6291347392009696656730169 4718510544007272492547627)
          ·
            refine ⟨7077765816010908738821441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4718510544007272492547627 7077765816010908738821441)
            ·
              refine ⟨5308324362008181554116081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7077765816010908738821441 5308324362008181554116081)
              ·
                refine ⟨3981243271506136165587061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5308324362008181554116081 3981243271506136165587061)
                ·
                  refine ⟨373241556703700265523787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3981243271506136165587061 373241556703700265523787)
                  ·
                    rfl

theorem cell20_817746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_817746 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_817746 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_817746 prefixEnd_817746 := by exact prefixLift 817746
  have htrace : WordTrace (prefixWord ++ tailWord_817746) baseStart_817746 baseEnd_817746 := by
    simpa [prefixWord, tailWord_817746, baseEnd_817746] using wordTrace_append hprefix tailTrace_817746
  have hstable : (prefixWord ++ tailWord_817746).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817746).length < 2 ^ (prefixWord ++ tailWord_817746).sum := by decide
  have hdescent : baseEnd_817746 < baseStart_817746 := by decide
  rcases family_descends (prefixWord ++ tailWord_817746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817770 : List Nat := [3, 1, 3, 2, 1, 1, 4, 1, 4]
def baseStart_817770 : Nat := 118140960795 + 817770 * 2 ^ 59
def prefixEnd_817770 : Nat := 4983230072969 + 3 ^ 40 * 817770 * 2
def baseEnd_817770 : Nat := 373252510957662848723689

theorem tailTrace_817770 : CollatzResearch.WordTrace tailWord_817770 prefixEnd_817770 373252510957662848723689 := by
  unfold tailWord_817770
  simp only [CollatzResearch.WordTrace]
  refine ⟨7456630561841607210472691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19884348164910952561260509 7456630561841607210472691)
  ·
    refine ⟨11184945842762410815709037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7456630561841607210472691 11184945842762410815709037)
    ·
      refine ⟨4194354691035904055890889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11184945842762410815709037 4194354691035904055890889)
      ·
        refine ⟨3145766018276928041918167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4194354691035904055890889 3145766018276928041918167)
        ·
          refine ⟨4718649027415392062877251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3145766018276928041918167 4718649027415392062877251)
          ·
            refine ⟨7077973541123088094315877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4718649027415392062877251 7077973541123088094315877)
            ·
              refine ⟨1327120038960579017684227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7077973541123088094315877 1327120038960579017684227)
              ·
                refine ⟨1990680058440868526526341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1327120038960579017684227 1990680058440868526526341)
                ·
                  refine ⟨373252510957662848723689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1990680058440868526526341 373252510957662848723689)
                  ·
                    rfl

theorem cell20_817770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 1, 4].length) (baseStart_817770 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_817770 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_817770 prefixEnd_817770 := by exact prefixLift 817770
  have htrace : WordTrace (prefixWord ++ tailWord_817770) baseStart_817770 baseEnd_817770 := by
    simpa [prefixWord, tailWord_817770, baseEnd_817770] using wordTrace_append hprefix tailTrace_817770
  have hstable : (prefixWord ++ tailWord_817770).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817770).length < 2 ^ (prefixWord ++ tailWord_817770).sum := by decide
  have hdescent : baseEnd_817770 < baseStart_817770 := by decide
  rcases family_descends (prefixWord ++ tailWord_817770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817825 : List Nat := [1, 2, 3, 3, 3, 2, 1, 1, 4]
def baseStart_817825 : Nat := 118140960795 + 817825 * 2 ^ 59
def prefixEnd_817825 : Nat := 4983230072969 + 3 ^ 40 * 817825 * 2
def baseEnd_817825 : Nat := 373277614456327101890131

theorem tailTrace_817825 : CollatzResearch.WordTrace tailWord_817825 prefixEnd_817825 373277614456327101890131 := by
  unfold tailWord_817825
  simp only [CollatzResearch.WordTrace]
  refine ⟨29828528262167173235142929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19885685508111448823428619 29828528262167173235142929)
  ·
    refine ⟨22371396196625379926357197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29828528262167173235142929 22371396196625379926357197)
    ·
      refine ⟨8389273573734517472383949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22371396196625379926357197 8389273573734517472383949)
      ·
        refine ⟨3145977590150444052143981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8389273573734517472383949 3145977590150444052143981)
        ·
          refine ⟨1179741596306416519553993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3145977590150444052143981 1179741596306416519553993)
          ·
            refine ⟨884806197229812389665495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1179741596306416519553993 884806197229812389665495)
            ·
              refine ⟨1327209295844718584498243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 884806197229812389665495 1327209295844718584498243)
              ·
                refine ⟨1990813943767077876747365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1327209295844718584498243 1990813943767077876747365)
                ·
                  refine ⟨373277614456327101890131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1990813943767077876747365 373277614456327101890131)
                  ·
                    rfl

theorem cell20_817825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 1, 4].length) (baseStart_817825 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_817825 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_817825 prefixEnd_817825 := by exact prefixLift 817825
  have htrace : WordTrace (prefixWord ++ tailWord_817825) baseStart_817825 baseEnd_817825 := by
    simpa [prefixWord, tailWord_817825, baseEnd_817825] using wordTrace_append hprefix tailTrace_817825
  have hstable : (prefixWord ++ tailWord_817825).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817825).length < 2 ^ (prefixWord ++ tailWord_817825).sum := by decide
  have hdescent : baseEnd_817825 < baseStart_817825 := by decide
  rcases family_descends (prefixWord ++ tailWord_817825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817839 : List Nat := [1, 1, 2, 1, 2, 5, 4, 1, 3]
def baseStart_817839 : Nat := 118140960795 + 817839 * 2 ^ 59
def prefixEnd_817839 : Nat := 4983230072969 + 3 ^ 40 * 817839 * 2
def baseEnd_817839 : Nat := 373284004437805275423407

theorem tailTrace_817839 : CollatzResearch.WordTrace tailWord_817839 prefixEnd_817839 373284004437805275423407 := by
  unfold tailWord_817839
  simp only [CollatzResearch.WordTrace]
  refine ⟨29829038884116453626152571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19886025922744302417435047 29829038884116453626152571)
  ·
    refine ⟨44743558326174680439228857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29829038884116453626152571 44743558326174680439228857)
    ·
      refine ⟨33557668744631010329421643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44743558326174680439228857 33557668744631010329421643)
      ·
        refine ⟨50336503116946515494132465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33557668744631010329421643 50336503116946515494132465)
        ·
          refine ⟨37752377337709886620599349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50336503116946515494132465 37752377337709886620599349)
          ·
            refine ⟨3539285375410301870681189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37752377337709886620599349 3539285375410301870681189)
            ·
              refine ⟨663616007889431600752723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3539285375410301870681189 663616007889431600752723)
              ·
                refine ⟨995424011834147401129085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 663616007889431600752723 995424011834147401129085)
                ·
                  refine ⟨373284004437805275423407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 995424011834147401129085 373284004437805275423407)
                  ·
                    rfl

theorem cell20_817839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 4, 1, 3].length) (baseStart_817839 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_817839 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_817839 prefixEnd_817839 := by exact prefixLift 817839
  have htrace : WordTrace (prefixWord ++ tailWord_817839) baseStart_817839 baseEnd_817839 := by
    simpa [prefixWord, tailWord_817839, baseEnd_817839] using wordTrace_append hprefix tailTrace_817839
  have hstable : (prefixWord ++ tailWord_817839).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817839).length < 2 ^ (prefixWord ++ tailWord_817839).sum := by decide
  have hdescent : baseEnd_817839 < baseStart_817839 := by decide
  rcases family_descends (prefixWord ++ tailWord_817839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817874 : List Nat := [3, 2, 2, 2, 11]
def baseStart_817874 : Nat := 118140960795 + 817874 * 2 ^ 59
def prefixEnd_817874 : Nat := 4983230072969 + 3 ^ 40 * 817874 * 2
def baseEnd_817874 : Nat := 4608641720882724805637

theorem tailTrace_817874 : CollatzResearch.WordTrace tailWord_817874 prefixEnd_817874 4608641720882724805637 := by
  unfold tailWord_817874
  simp only [CollatzResearch.WordTrace]
  refine ⟨7457578859747413650919169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19886876959326436402451117 7457578859747413650919169)
  ·
    refine ⟨5593184144810560238189377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7457578859747413650919169 5593184144810560238189377)
    ·
      refine ⟨4194888108607920178642033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5593184144810560238189377 4194888108607920178642033)
      ·
        refine ⟨3146166081455940133981525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4194888108607920178642033 3146166081455940133981525)
        ·
          refine ⟨4608641720882724805637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3146166081455940133981525 4608641720882724805637)
          ·
            rfl

theorem cell20_817874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 11].length) (baseStart_817874 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_817874 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_817874 prefixEnd_817874 := by exact prefixLift 817874
  have htrace : WordTrace (prefixWord ++ tailWord_817874) baseStart_817874 baseEnd_817874 := by
    simpa [prefixWord, tailWord_817874, baseEnd_817874] using wordTrace_append hprefix tailTrace_817874
  have hstable : (prefixWord ++ tailWord_817874).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817874).length < 2 ^ (prefixWord ++ tailWord_817874).sum := by decide
  have hdescent : baseEnd_817874 < baseStart_817874 := by decide
  rcases family_descends (prefixWord ++ tailWord_817874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817876 : List Nat := [2, 4, 1, 3, 3, 1, 2, 2, 2]
def baseStart_817876 : Nat := 118140960795 + 817876 * 2 ^ 59
def prefixEnd_817876 : Nat := 4983230072969 + 3 ^ 40 * 817876 * 2
def baseEnd_817876 : Nat := 373300892245997591189923

theorem tailTrace_817876 : CollatzResearch.WordTrace tailWord_817876 prefixEnd_817876 373300892245997591189923 := by
  unfold tailWord_817876
  simp only [CollatzResearch.WordTrace]
  refine ⟨14915194192491204472624741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19886925589988272630166321 14915194192491204472624741)
  ·
    refine ⟨2796598911092100838617139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14915194192491204472624741 2796598911092100838617139)
    ·
      refine ⟨4194898366638151257925709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2796598911092100838617139 4194898366638151257925709)
      ·
        refine ⟨1573086887489306721722141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4194898366638151257925709 1573086887489306721722141)
        ·
          refine ⟨589907582808490020645803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1573086887489306721722141 589907582808490020645803)
          ·
            refine ⟨884861374212735030968705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 589907582808490020645803 884861374212735030968705)
            ·
              refine ⟨663646030659551273226529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 884861374212735030968705 663646030659551273226529)
              ·
                refine ⟨497734522994663454919897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 663646030659551273226529 497734522994663454919897)
                ·
                  refine ⟨373300892245997591189923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 497734522994663454919897 373300892245997591189923)
                  ·
                    rfl

theorem cell20_817876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 2, 2, 2].length) (baseStart_817876 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_817876 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_817876 prefixEnd_817876 := by exact prefixLift 817876
  have htrace : WordTrace (prefixWord ++ tailWord_817876) baseStart_817876 baseEnd_817876 := by
    simpa [prefixWord, tailWord_817876, baseEnd_817876] using wordTrace_append hprefix tailTrace_817876
  have hstable : (prefixWord ++ tailWord_817876).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817876).length < 2 ^ (prefixWord ++ tailWord_817876).sum := by decide
  have hdescent : baseEnd_817876 < baseStart_817876 := by decide
  rcases family_descends (prefixWord ++ tailWord_817876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817880 : List Nat := [2, 1, 2, 2, 3, 4, 2, 2, 2]
def baseStart_817880 : Nat := 118140960795 + 817880 * 2 ^ 59
def prefixEnd_817880 : Nat := 4983230072969 + 3 ^ 40 * 817880 * 2
def baseEnd_817880 : Nat := 373302717954991355056573

theorem tailTrace_817880 : CollatzResearch.WordTrace tailWord_817880 prefixEnd_817880 373302717954991355056573 := by
  unfold tailWord_817880
  simp only [CollatzResearch.WordTrace]
  refine ⟨14915267138483958814197547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19887022851311945085596729 14915267138483958814197547)
  ·
    refine ⟨22372900707725938221296321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14915267138483958814197547 22372900707725938221296321)
    ·
      refine ⟨16779675530794453665972241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22372900707725938221296321 16779675530794453665972241)
      ·
        refine ⟨12584756648095840249479181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16779675530794453665972241 12584756648095840249479181)
        ·
          refine ⟨4719283743035940093554693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12584756648095840249479181 4719283743035940093554693)
          ·
            refine ⟨884865701819238767541505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4719283743035940093554693 884865701819238767541505)
            ·
              refine ⟨663649276364429075656129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 884865701819238767541505 663649276364429075656129)
              ·
                refine ⟨497736957273321806742097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 663649276364429075656129 497736957273321806742097)
                ·
                  refine ⟨373302717954991355056573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 497736957273321806742097 373302717954991355056573)
                  ·
                    rfl

theorem cell20_817880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 2, 2, 2].length) (baseStart_817880 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_817880 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_817880 prefixEnd_817880 := by exact prefixLift 817880
  have htrace : WordTrace (prefixWord ++ tailWord_817880) baseStart_817880 baseEnd_817880 := by
    simpa [prefixWord, tailWord_817880, baseEnd_817880] using wordTrace_append hprefix tailTrace_817880
  have hstable : (prefixWord ++ tailWord_817880).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817880).length < 2 ^ (prefixWord ++ tailWord_817880).sum := by decide
  have hdescent : baseEnd_817880 < baseStart_817880 := by decide
  rcases family_descends (prefixWord ++ tailWord_817880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817891 : List Nat := [1, 1, 1, 7, 1, 1, 3, 5]
def baseStart_817891 : Nat := 118140960795 + 817891 * 2 ^ 59
def prefixEnd_817891 : Nat := 4983230072969 + 3 ^ 40 * 817891 * 2
def baseEnd_817891 : Nat := 124435912884908068563287

theorem tailTrace_817891 : CollatzResearch.WordTrace tailWord_817891 prefixEnd_817891 124435912884908068563287 := by
  unfold tailWord_817891
  simp only [CollatzResearch.WordTrace]
  refine ⟨29830935479928066507045527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19887290319952044338030351 29830935479928066507045527)
  ·
    refine ⟨44746403219892099760568291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29830935479928066507045527 44746403219892099760568291)
    ·
      refine ⟨67119604829838149640852437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44746403219892099760568291 67119604829838149640852437)
      ·
        refine ⟨1573115738199331632207479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 67119604829838149640852437 1573115738199331632207479)
        ·
          refine ⟨2359673607298997448311219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1573115738199331632207479 2359673607298997448311219)
          ·
            refine ⟨3539510410948496172466829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2359673607298997448311219 3539510410948496172466829)
            ·
              refine ⟨1327316404105686064675061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3539510410948496172466829 1327316404105686064675061)
              ·
                refine ⟨124435912884908068563287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1327316404105686064675061 124435912884908068563287)
                ·
                  rfl

theorem cell20_817891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 5].length) (baseStart_817891 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_817891 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_817891 prefixEnd_817891 := by exact prefixLift 817891
  have htrace : WordTrace (prefixWord ++ tailWord_817891) baseStart_817891 baseEnd_817891 := by
    simpa [prefixWord, tailWord_817891, baseEnd_817891] using wordTrace_append hprefix tailTrace_817891
  have hstable : (prefixWord ++ tailWord_817891).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817891).length < 2 ^ (prefixWord ++ tailWord_817891).sum := by decide
  have hdescent : baseEnd_817891 < baseStart_817891 := by decide
  rcases family_descends (prefixWord ++ tailWord_817891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817905 : List Nat := [1, 2, 2, 2, 2, 2, 3, 2, 4]
def baseStart_817905 : Nat := 118140960795 + 817905 * 2 ^ 59
def prefixEnd_817905 : Nat := 4983230072969 + 3 ^ 40 * 817905 * 2
def baseEnd_817905 : Nat := 373314128636202379223137

theorem tailTrace_817905 : CollatzResearch.WordTrace tailWord_817905 prefixEnd_817905 373314128636202379223137 := by
  unfold tailWord_817905
  simp only [CollatzResearch.WordTrace]
  refine ⟨29831446101877346898055169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19887630734584897932036779 29831446101877346898055169)
  ·
    refine ⟨22373584576408010173541377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29831446101877346898055169 22373584576408010173541377)
    ·
      refine ⟨16780188432306007630156033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22373584576408010173541377 16780188432306007630156033)
      ·
        refine ⟨12585141324229505722617025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16780188432306007630156033 12585141324229505722617025)
        ·
          refine ⟨9438855993172129291962769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12585141324229505722617025 9438855993172129291962769)
          ·
            refine ⟨7079141994879096968972077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9438855993172129291962769 7079141994879096968972077)
            ·
              refine ⟨2654678248079661363364529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7079141994879096968972077 2654678248079661363364529)
              ·
                refine ⟨1991008686059746022523397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2654678248079661363364529 1991008686059746022523397)
                ·
                  refine ⟨373314128636202379223137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1991008686059746022523397 373314128636202379223137)
                  ·
                    rfl

theorem cell20_817905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 2, 4].length) (baseStart_817905 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_817905 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_817905 prefixEnd_817905 := by exact prefixLift 817905
  have htrace : WordTrace (prefixWord ++ tailWord_817905) baseStart_817905 baseEnd_817905 := by
    simpa [prefixWord, tailWord_817905, baseEnd_817905] using wordTrace_append hprefix tailTrace_817905
  have hstable : (prefixWord ++ tailWord_817905).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817905).length < 2 ^ (prefixWord ++ tailWord_817905).sum := by decide
  have hdescent : baseEnd_817905 < baseStart_817905 := by decide
  rcases family_descends (prefixWord ++ tailWord_817905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817918 : List Nat := [4, 2, 2, 1, 2, 2, 2, 3, 2]
def baseStart_817918 : Nat := 118140960795 + 817918 * 2 ^ 59
def prefixEnd_817918 : Nat := 4983230072969 + 3 ^ 40 * 817918 * 2
def baseEnd_817918 : Nat := 373320062190432111789751

theorem tailTrace_817918 : CollatzResearch.WordTrace tailWord_817918 prefixEnd_817918 373320062190432111789751 := by
  unfold tailWord_817918
  simp only [CollatzResearch.WordTrace]
  refine ⟨3728990031353781264784801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19887946833886833412185605 3728990031353781264784801)
  ·
    refine ⟨2796742523515335948588601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3728990031353781264784801 2796742523515335948588601)
    ·
      refine ⟨2097556892636501961441451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2796742523515335948588601 2097556892636501961441451)
      ·
        refine ⟨3146335338954752942162177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2097556892636501961441451 3146335338954752942162177)
        ·
          refine ⟨2359751504216064706621633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3146335338954752942162177 2359751504216064706621633)
          ·
            refine ⟨1769813628162048529966225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2359751504216064706621633 1769813628162048529966225)
            ·
              refine ⟨1327360221121536397474669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1769813628162048529966225 1327360221121536397474669)
              ·
                refine ⟨497760082920576149053001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1327360221121536397474669 497760082920576149053001)
                ·
                  refine ⟨373320062190432111789751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 497760082920576149053001 373320062190432111789751)
                  ·
                    rfl

theorem cell20_817918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 3, 2].length) (baseStart_817918 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_817918 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_817918 prefixEnd_817918 := by exact prefixLift 817918
  have htrace : WordTrace (prefixWord ++ tailWord_817918) baseStart_817918 baseEnd_817918 := by
    simpa [prefixWord, tailWord_817918, baseEnd_817918] using wordTrace_append hprefix tailTrace_817918
  have hstable : (prefixWord ++ tailWord_817918).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817918).length < 2 ^ (prefixWord ++ tailWord_817918).sum := by decide
  have hdescent : baseEnd_817918 < baseStart_817918 := by decide
  rcases family_descends (prefixWord ++ tailWord_817918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817919 : List Nat := [1, 1, 2, 2, 1, 3, 1, 4, 5]
def baseStart_817919 : Nat := 118140960795 + 817919 * 2 ^ 59
def prefixEnd_817919 : Nat := 4983230072969 + 3 ^ 40 * 817919 * 2
def baseEnd_817919 : Nat := 373320518617680552756413

theorem tailTrace_817919 : CollatzResearch.WordTrace tailWord_817919 prefixEnd_817919 373320518617680552756413 := by
  unfold tailWord_817919
  simp only [CollatzResearch.WordTrace]
  refine ⟨29831956723826627289064811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19887971149217751526043207 29831956723826627289064811)
  ·
    refine ⟨44747935085739940933597217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29831956723826627289064811 44747935085739940933597217)
    ·
      refine ⟨33560951314304955700197913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44747935085739940933597217 33560951314304955700197913)
      ·
        refine ⟨25170713485728716775148435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33560951314304955700197913 25170713485728716775148435)
        ·
          refine ⟨37756070228593075162722653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25170713485728716775148435 37756070228593075162722653)
          ·
            refine ⟨14158526335722403186020995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37756070228593075162722653 14158526335722403186020995)
            ·
              refine ⟨21237789503583604779031493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14158526335722403186020995 21237789503583604779031493)
              ·
                refine ⟨3982085531921925896068405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21237789503583604779031493 3982085531921925896068405)
                ·
                  refine ⟨373320518617680552756413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3982085531921925896068405 373320518617680552756413)
                  ·
                    rfl

theorem cell20_817919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 5].length) (baseStart_817919 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_817919 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_817919 prefixEnd_817919 := by exact prefixLift 817919
  have htrace : WordTrace (prefixWord ++ tailWord_817919) baseStart_817919 baseEnd_817919 := by
    simpa [prefixWord, tailWord_817919, baseEnd_817919] using wordTrace_append hprefix tailTrace_817919
  have hstable : (prefixWord ++ tailWord_817919).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817919).length < 2 ^ (prefixWord ++ tailWord_817919).sum := by decide
  have hdescent : baseEnd_817919 < baseStart_817919 := by decide
  rcases family_descends (prefixWord ++ tailWord_817919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817949 : List Nat := [1, 4, 2, 4, 1, 1, 3, 1, 3]
def baseStart_817949 : Nat := 118140960795 + 817949 * 2 ^ 59
def prefixEnd_817949 : Nat := 4983230072969 + 3 ^ 40 * 817949 * 2
def baseEnd_817949 : Nat := 373334211435133781756291

theorem tailTrace_817949 : CollatzResearch.WordTrace tailWord_817949 prefixEnd_817949 373334211435133781756291 := by
  unfold tailWord_817949
  simp only [CollatzResearch.WordTrace]
  refine ⟨29833050913717942412656901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19888700609145294941771267 29833050913717942412656901)
  ·
    refine ⟨5593697046322114202373169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29833050913717942412656901 5593697046322114202373169)
    ·
      refine ⟨4195272784741585651779877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5593697046322114202373169 4195272784741585651779877)
      ·
        refine ⟨786613647139047309708727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4195272784741585651779877 786613647139047309708727)
        ·
          refine ⟨1179920470708570964563091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 786613647139047309708727 1179920470708570964563091)
          ·
            refine ⟨1769880706062856446844637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1179920470708570964563091 1769880706062856446844637)
            ·
              refine ⟨663705264773571167566739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1769880706062856446844637 663705264773571167566739)
              ·
                refine ⟨995557897160356751350109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 663705264773571167566739 995557897160356751350109)
                ·
                  refine ⟨373334211435133781756291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 995557897160356751350109 373334211435133781756291)
                  ·
                    rfl

theorem cell20_817949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 3, 1, 3].length) (baseStart_817949 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_817949 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_817949 prefixEnd_817949 := by exact prefixLift 817949
  have htrace : WordTrace (prefixWord ++ tailWord_817949) baseStart_817949 baseEnd_817949 := by
    simpa [prefixWord, tailWord_817949, baseEnd_817949] using wordTrace_append hprefix tailTrace_817949
  have hstable : (prefixWord ++ tailWord_817949).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817949).length < 2 ^ (prefixWord ++ tailWord_817949).sum := by decide
  have hdescent : baseEnd_817949 < baseStart_817949 := by decide
  rcases family_descends (prefixWord ++ tailWord_817949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817953 : List Nat := [1, 2, 3, 2, 1, 2, 5, 1, 3]
def baseStart_817953 : Nat := 118140960795 + 817953 * 2 ^ 59
def prefixEnd_817953 : Nat := 4983230072969 + 3 ^ 40 * 817953 * 2
def baseEnd_817953 : Nat := 373336037144127545622941

theorem tailTrace_817953 : CollatzResearch.WordTrace tailWord_817953 prefixEnd_817953 373336037144127545622941 := by
  unfold tailWord_817953
  simp only [CollatzResearch.WordTrace]
  refine ⟨29833196805703451095802513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19888797870468967397201675 29833196805703451095802513)
  ·
    refine ⟨22374897604277588321851885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29833196805703451095802513 22374897604277588321851885)
    ·
      refine ⟨8390586601604095620694457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22374897604277588321851885 8390586601604095620694457)
      ·
        refine ⟨6292939951203071715520843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8390586601604095620694457 6292939951203071715520843)
        ·
          refine ⟨9439409926804607573281265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6292939951203071715520843 9439409926804607573281265)
          ·
            refine ⟨7079557445103455679960949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9439409926804607573281265 7079557445103455679960949)
            ·
              refine ⟨663708510478448969996339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7079557445103455679960949 663708510478448969996339)
              ·
                refine ⟨995562765717673454994509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 663708510478448969996339 995562765717673454994509)
                ·
                  refine ⟨373336037144127545622941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 995562765717673454994509 373336037144127545622941)
                  ·
                    rfl

theorem cell20_817953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 5, 1, 3].length) (baseStart_817953 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_817953 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_817953 prefixEnd_817953 := by exact prefixLift 817953
  have htrace : WordTrace (prefixWord ++ tailWord_817953) baseStart_817953 baseEnd_817953 := by
    simpa [prefixWord, tailWord_817953, baseEnd_817953] using wordTrace_append hprefix tailTrace_817953
  have hstable : (prefixWord ++ tailWord_817953).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817953).length < 2 ^ (prefixWord ++ tailWord_817953).sum := by decide
  have hdescent : baseEnd_817953 < baseStart_817953 := by decide
  rcases family_descends (prefixWord ++ tailWord_817953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817990 : List Nat := [6, 1, 1, 2, 2, 1, 3, 2, 2]
def baseStart_817990 : Nat := 118140960795 + 817990 * 2 ^ 59
def prefixEnd_817990 : Nat := 4983230072969 + 3 ^ 40 * 817990 * 2
def baseEnd_817990 : Nat := 373352924952319861389457

theorem tailTrace_817990 : CollatzResearch.WordTrace tailWord_817990 prefixEnd_817990 373352924952319861389457 := by
  unfold tailWord_817990
  simp only [CollatzResearch.WordTrace]
  refine ⟨932329572080293950465607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 19889697537712937609932949 932329572080293950465607)
  ·
    refine ⟨1398494358120440925698411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 932329572080293950465607 1398494358120440925698411)
    ·
      refine ⟨2097741537180661388547617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1398494358120440925698411 2097741537180661388547617)
      ·
        refine ⟨1573306152885496041410713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2097741537180661388547617 1573306152885496041410713)
        ·
          refine ⟨1179979614664122031058035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1573306152885496041410713 1179979614664122031058035)
          ·
            refine ⟨1769969421996183046587053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1179979614664122031058035 1769969421996183046587053)
            ·
              refine ⟨663738533248568642470145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1769969421996183046587053 663738533248568642470145)
              ·
                refine ⟨497803899936426481852609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 663738533248568642470145 497803899936426481852609)
                ·
                  refine ⟨373352924952319861389457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 497803899936426481852609 373352924952319861389457)
                  ·
                    rfl

theorem cell20_817990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_817990 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_817990 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_817990 prefixEnd_817990 := by exact prefixLift 817990
  have htrace : WordTrace (prefixWord ++ tailWord_817990) baseStart_817990 baseEnd_817990 := by
    simpa [prefixWord, tailWord_817990, baseEnd_817990] using wordTrace_append hprefix tailTrace_817990
  have hstable : (prefixWord ++ tailWord_817990).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817990).length < 2 ^ (prefixWord ++ tailWord_817990).sum := by decide
  have hdescent : baseEnd_817990 < baseStart_817990 := by decide
  rcases family_descends (prefixWord ++ tailWord_817990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_817998 : List Nat := [4, 1, 1, 1, 1, 1, 1, 8, 2]
def baseStart_817998 : Nat := 118140960795 + 817998 * 2 ^ 59
def prefixEnd_817998 : Nat := 4983230072969 + 3 ^ 40 * 817998 * 2
def baseEnd_817998 : Nat := 373356576370307389122757

theorem tailTrace_817998 : CollatzResearch.WordTrace tailWord_817998 prefixEnd_817998 373356576370307389122757 := by
  unfold tailWord_817998
  simp only [CollatzResearch.WordTrace]
  refine ⟨3729354761317552972648831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19889892060360282520793765 3729354761317552972648831)
  ·
    refine ⟨5594032141976329458973247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3729354761317552972648831 5594032141976329458973247)
    ·
      refine ⟨8391048212964494188459871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5594032141976329458973247 8391048212964494188459871)
      ·
        refine ⟨12586572319446741282689807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8391048212964494188459871 12586572319446741282689807)
        ·
          refine ⟨18879858479170111924034711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12586572319446741282689807 18879858479170111924034711)
          ·
            refine ⟨28319787718755167886052067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18879858479170111924034711 28319787718755167886052067)
            ·
              refine ⟨42479681578132751829078101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28319787718755167886052067 42479681578132751829078101)
              ·
                refine ⟨497808768493743185497009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 42479681578132751829078101 497808768493743185497009)
                ·
                  refine ⟨373356576370307389122757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 497808768493743185497009 373356576370307389122757)
                  ·
                    rfl

theorem cell20_817998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 8, 2].length) (baseStart_817998 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_817998 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_817998 prefixEnd_817998 := by exact prefixLift 817998
  have htrace : WordTrace (prefixWord ++ tailWord_817998) baseStart_817998 baseEnd_817998 := by
    simpa [prefixWord, tailWord_817998, baseEnd_817998] using wordTrace_append hprefix tailTrace_817998
  have hstable : (prefixWord ++ tailWord_817998).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_817998).length < 2 ^ (prefixWord ++ tailWord_817998).sum := by decide
  have hdescent : baseEnd_817998 < baseStart_817998 := by decide
  rcases family_descends (prefixWord ++ tailWord_817998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818040 : List Nat := [2, 1, 2, 1, 1, 1, 1, 3, 8]
def baseStart_818040 : Nat := 118140960795 + 818040 * 2 ^ 59
def prefixEnd_818040 : Nat := 4983230072969 + 3 ^ 40 * 818040 * 2
def baseEnd_818040 : Nat := 373375746314741909722585

theorem tailTrace_818040 : CollatzResearch.WordTrace tailWord_818040 prefixEnd_818040 373375746314741909722585 := by
  unfold tailWord_818040
  simp only [CollatzResearch.WordTrace]
  refine ⟨14918184978194132477109787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19890913304258843302813049 14918184978194132477109787)
  ·
    refine ⟨22377277467291198715664681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14918184978194132477109787 22377277467291198715664681)
    ·
      refine ⟨16782958100468399036748511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22377277467291198715664681 16782958100468399036748511)
      ·
        refine ⟨25174437150702598555122767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16782958100468399036748511 25174437150702598555122767)
        ·
          refine ⟨37761655726053897832684151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25174437150702598555122767 37761655726053897832684151)
          ·
            refine ⟨56642483589080846749026227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37761655726053897832684151 56642483589080846749026227)
            ·
              refine ⟨84963725383621270123539341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56642483589080846749026227 84963725383621270123539341)
              ·
                refine ⟨31861397018857976296327253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84963725383621270123539341 31861397018857976296327253)
                ·
                  refine ⟨373375746314741909722585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31861397018857976296327253 373375746314741909722585)
                  ·
                    rfl

theorem cell20_818040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 8].length) (baseStart_818040 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_818040 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_818040 prefixEnd_818040 := by exact prefixLift 818040
  have htrace : WordTrace (prefixWord ++ tailWord_818040) baseStart_818040 baseEnd_818040 := by
    simpa [prefixWord, tailWord_818040, baseEnd_818040] using wordTrace_append hprefix tailTrace_818040
  have hstable : (prefixWord ++ tailWord_818040).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818040).length < 2 ^ (prefixWord ++ tailWord_818040).sum := by decide
  have hdescent : baseEnd_818040 < baseStart_818040 := by decide
  rcases family_descends (prefixWord ++ tailWord_818040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818053 : List Nat := [1, 3, 1, 1, 3, 3, 4, 2, 2]
def baseStart_818053 : Nat := 118140960795 + 818053 * 2 ^ 59
def prefixEnd_818053 : Nat := 4983230072969 + 3 ^ 40 * 818053 * 2
def baseEnd_818053 : Nat := 373381679868971642289199

theorem tailTrace_818053 : CollatzResearch.WordTrace tailWord_818053 prefixEnd_818053 373381679868971642289199 := by
  unfold tailWord_818053
  simp only [CollatzResearch.WordTrace]
  refine ⟨29836844105341168174442813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19891229403560778782961875 29836844105341168174442813)
  ·
    refine ⟨11188816539502938065416055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29836844105341168174442813 11188816539502938065416055)
    ·
      refine ⟨16783224809254407098124083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11188816539502938065416055 16783224809254407098124083)
      ·
        refine ⟨25174837213881610647186125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16783224809254407098124083 25174837213881610647186125)
        ·
          refine ⟨9440563955205603992694797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25174837213881610647186125 9440563955205603992694797)
          ·
            refine ⟨3540211483202101497260549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9440563955205603992694797 3540211483202101497260549)
            ·
              refine ⟨663789653100394030736353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3540211483202101497260549 663789653100394030736353)
              ·
                refine ⟨497842239825295523052265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 663789653100394030736353 497842239825295523052265)
                ·
                  refine ⟨373381679868971642289199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 497842239825295523052265 373381679868971642289199)
                  ·
                    rfl

theorem cell20_818053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 4, 2, 2].length) (baseStart_818053 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_818053 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_818053 prefixEnd_818053 := by exact prefixLift 818053
  have htrace : WordTrace (prefixWord ++ tailWord_818053) baseStart_818053 baseEnd_818053 := by
    simpa [prefixWord, tailWord_818053, baseEnd_818053] using wordTrace_append hprefix tailTrace_818053
  have hstable : (prefixWord ++ tailWord_818053).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818053).length < 2 ^ (prefixWord ++ tailWord_818053).sum := by decide
  have hdescent : baseEnd_818053 < baseStart_818053 := by decide
  rcases family_descends (prefixWord ++ tailWord_818053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818070 : List Nat := [5, 3, 1, 1, 1, 2, 1, 2, 4]
def baseStart_818070 : Nat := 118140960795 + 818070 * 2 ^ 59
def prefixEnd_818070 : Nat := 4983230072969 + 3 ^ 40 * 818070 * 2
def baseEnd_818070 : Nat := 373389439132195138722463

theorem tailTrace_818070 : CollatzResearch.WordTrace tailWord_818070 prefixEnd_818070 373389439132195138722463 := by
  unfold tailWord_818070
  simp only [CollatzResearch.WordTrace]
  refine ⟨1864841509142473754863229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19891642764186386718541109 1864841509142473754863229)
  ·
    refine ⟨699315565928427658073711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1864841509142473754863229 699315565928427658073711)
    ·
      refine ⟨1048973348892641487110567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 699315565928427658073711 1048973348892641487110567)
      ·
        refine ⟨1573460023338962230665851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1048973348892641487110567 1573460023338962230665851)
        ·
          refine ⟨2360190035008443345998777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1573460023338962230665851 2360190035008443345998777)
          ·
            refine ⟨1770142526256332509499083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2360190035008443345998777 1770142526256332509499083)
            ·
              refine ⟨2655213789384498764248625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1770142526256332509499083 2655213789384498764248625)
              ·
                refine ⟨1991410342038374073186469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2655213789384498764248625 1991410342038374073186469)
                ·
                  refine ⟨373389439132195138722463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1991410342038374073186469 373389439132195138722463)
                  ·
                    rfl

theorem cell20_818070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_818070 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_818070 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_818070 prefixEnd_818070 := by exact prefixLift 818070
  have htrace : WordTrace (prefixWord ++ tailWord_818070) baseStart_818070 baseEnd_818070 := by
    simpa [prefixWord, tailWord_818070, baseEnd_818070] using wordTrace_append hprefix tailTrace_818070
  have hstable : (prefixWord ++ tailWord_818070).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818070).length < 2 ^ (prefixWord ++ tailWord_818070).sum := by decide
  have hdescent : baseEnd_818070 < baseStart_818070 := by decide
  rcases family_descends (prefixWord ++ tailWord_818070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818074 : List Nat := [3, 1, 1, 4, 3, 1, 1, 2, 4]
def baseStart_818074 : Nat := 118140960795 + 818074 * 2 ^ 59
def prefixEnd_818074 : Nat := 4983230072969 + 3 ^ 40 * 818074 * 2
def baseEnd_818074 : Nat := 373391264841188902589113

theorem tailTrace_818074 : CollatzResearch.WordTrace tailWord_818074 prefixEnd_818074 373391264841188902589113 := by
  unfold tailWord_818074
  simp only [CollatzResearch.WordTrace]
  refine ⟨7459402509566272190239319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19891740025510059173971517 7459402509566272190239319)
  ·
    refine ⟨11189103764349408285358979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7459402509566272190239319 11189103764349408285358979)
    ·
      refine ⟨16783655646524112428038469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11189103764349408285358979 16783655646524112428038469)
      ·
        refine ⟨3146935433723271080257213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16783655646524112428038469 3146935433723271080257213)
        ·
          refine ⟨1180100787646226655096455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3146935433723271080257213 1180100787646226655096455)
          ·
            refine ⟨1770151181469339982644683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1180100787646226655096455 1770151181469339982644683)
            ·
              refine ⟨2655226772204009973967025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1770151181469339982644683 2655226772204009973967025)
              ·
                refine ⟨1991420079153007480475269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2655226772204009973967025 1991420079153007480475269)
                ·
                  refine ⟨373391264841188902589113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1991420079153007480475269 373391264841188902589113)
                  ·
                    rfl

theorem cell20_818074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 2, 4].length) (baseStart_818074 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_818074 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_818074 prefixEnd_818074 := by exact prefixLift 818074
  have htrace : WordTrace (prefixWord ++ tailWord_818074) baseStart_818074 baseEnd_818074 := by
    simpa [prefixWord, tailWord_818074, baseEnd_818074] using wordTrace_append hprefix tailTrace_818074
  have hstable : (prefixWord ++ tailWord_818074).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818074).length < 2 ^ (prefixWord ++ tailWord_818074).sum := by decide
  have hdescent : baseEnd_818074 < baseStart_818074 := by decide
  rcases family_descends (prefixWord ++ tailWord_818074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818105 : List Nat := [1, 2, 1, 4, 2, 4, 1, 2, 3]
def baseStart_818105 : Nat := 118140960795 + 818105 * 2 ^ 59
def prefixEnd_818105 : Nat := 4983230072969 + 3 ^ 40 * 818105 * 2
def baseEnd_818105 : Nat := 373405414085890572555653

theorem tailTrace_818105 : CollatzResearch.WordTrace tailWord_818105 prefixEnd_818105 373405414085890572555653 := by
  unfold tailWord_818105
  simp only [CollatzResearch.WordTrace]
  refine ⟨29838740701152781055335769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19892493800768520703557179 29838740701152781055335769)
  ·
    refine ⟨22379055525864585791501827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29838740701152781055335769 22379055525864585791501827)
    ·
      refine ⟨33568583288796878687252741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22379055525864585791501827 33568583288796878687252741)
      ·
        refine ⟨6294109366649414753859889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33568583288796878687252741 6294109366649414753859889)
        ·
          refine ⟨4720582024987061065394917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6294109366649414753859889 4720582024987061065394917)
          ·
            refine ⟨885109129685073949761547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4720582024987061065394917 885109129685073949761547)
            ·
              refine ⟨1327663694527610924642321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 885109129685073949761547 1327663694527610924642321)
              ·
                refine ⟨995747770895708193481741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1327663694527610924642321 995747770895708193481741)
                ·
                  refine ⟨373405414085890572555653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 995747770895708193481741 373405414085890572555653)
                  ·
                    rfl

theorem cell20_818105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 2, 3].length) (baseStart_818105 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_818105 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_818105 prefixEnd_818105 := by exact prefixLift 818105
  have htrace : WordTrace (prefixWord ++ tailWord_818105) baseStart_818105 baseEnd_818105 := by
    simpa [prefixWord, tailWord_818105, baseEnd_818105] using wordTrace_append hprefix tailTrace_818105
  have hstable : (prefixWord ++ tailWord_818105).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818105).length < 2 ^ (prefixWord ++ tailWord_818105).sum := by decide
  have hdescent : baseEnd_818105 < baseStart_818105 := by decide
  rcases family_descends (prefixWord ++ tailWord_818105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818112 : List Nat := [2, 1, 1, 2, 3, 3, 2, 4, 2]
def baseStart_818112 : Nat := 118140960795 + 818112 * 2 ^ 59
def prefixEnd_818112 : Nat := 4983230072969 + 3 ^ 40 * 818112 * 2
def baseEnd_818112 : Nat := 373408609076629659322291

theorem tailTrace_818112 : CollatzResearch.WordTrace tailWord_818112 prefixEnd_818112 373408609076629659322291 := by
  unfold tailWord_818112
  simp only [CollatzResearch.WordTrace]
  refine ⟨14919498006063710625420295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19892664008084947500560393 14919498006063710625420295)
  ·
    refine ⟨22379247009095565938130443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14919498006063710625420295 22379247009095565938130443)
    ·
      refine ⟨33568870513643348907195665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22379247009095565938130443 33568870513643348907195665)
      ·
        refine ⟨25176652885232511680396749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33568870513643348907195665 25176652885232511680396749)
        ·
          refine ⟨9441244831962191880148781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25176652885232511680396749 9441244831962191880148781)
          ·
            refine ⟨3540466811985821955055793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9441244831962191880148781 3540466811985821955055793)
            ·
              refine ⟨2655350108989366466291845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3540466811985821955055793 2655350108989366466291845)
              ·
                refine ⟨497878145435506212429721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2655350108989366466291845 497878145435506212429721)
                ·
                  refine ⟨373408609076629659322291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 497878145435506212429721 373408609076629659322291)
                  ·
                    rfl

theorem cell20_818112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 4, 2].length) (baseStart_818112 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_818112 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_818112 prefixEnd_818112 := by exact prefixLift 818112
  have htrace : WordTrace (prefixWord ++ tailWord_818112) baseStart_818112 baseEnd_818112 := by
    simpa [prefixWord, tailWord_818112, baseEnd_818112] using wordTrace_append hprefix tailTrace_818112
  have hstable : (prefixWord ++ tailWord_818112).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818112).length < 2 ^ (prefixWord ++ tailWord_818112).sum := by decide
  have hdescent : baseEnd_818112 < baseStart_818112 := by decide
  rcases family_descends (prefixWord ++ tailWord_818112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818146 : List Nat := [3, 3, 3, 1, 1, 1, 3, 3, 2]
def baseStart_818146 : Nat := 118140960795 + 818146 * 2 ^ 59
def prefixEnd_818146 : Nat := 4983230072969 + 3 ^ 40 * 818146 * 2
def baseEnd_818146 : Nat := 373424127603076652188819

theorem tailTrace_818146 : CollatzResearch.WordTrace tailWord_818146 prefixEnd_818146 373424127603076652188819 := by
  unfold tailWord_818146
  simp only [CollatzResearch.WordTrace]
  refine ⟨7460059023501061264394573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19893490729336163371718861 7460059023501061264394573)
  ·
    refine ⟨2797522133812897974147965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7460059023501061264394573 2797522133812897974147965)
    ·
      refine ⟨1049070800179836740305487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2797522133812897974147965 1049070800179836740305487)
      ·
        refine ⟨1573606200269755110458231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1049070800179836740305487 1573606200269755110458231)
        ·
          refine ⟨2360409300404632665687347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1573606200269755110458231 2360409300404632665687347)
          ·
            refine ⟨3540613950606948998531021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2360409300404632665687347 3540613950606948998531021)
            ·
              refine ⟨1327730231477605874449133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3540613950606948998531021 1327730231477605874449133)
              ·
                refine ⟨497898836804102202918425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1327730231477605874449133 497898836804102202918425)
                ·
                  refine ⟨373424127603076652188819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 497898836804102202918425 373424127603076652188819)
                  ·
                    rfl

theorem cell20_818146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 3, 2].length) (baseStart_818146 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_818146 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_818146 prefixEnd_818146 := by exact prefixLift 818146
  have htrace : WordTrace (prefixWord ++ tailWord_818146) baseStart_818146 baseEnd_818146 := by
    simpa [prefixWord, tailWord_818146, baseEnd_818146] using wordTrace_append hprefix tailTrace_818146
  have hstable : (prefixWord ++ tailWord_818146).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818146).length < 2 ^ (prefixWord ++ tailWord_818146).sum := by decide
  have hdescent : baseEnd_818146 < baseStart_818146 := by decide
  rcases family_descends (prefixWord ++ tailWord_818146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818147 : List Nat := [1, 1, 1, 6, 1, 1, 1, 1, 7]
def baseStart_818147 : Nat := 118140960795 + 818147 * 2 ^ 59
def prefixEnd_818147 : Nat := 4983230072969 + 3 ^ 40 * 818147 * 2
def baseEnd_818147 : Nat := 373424584030325093155481

theorem tailTrace_818147 : CollatzResearch.WordTrace tailWord_818147 prefixEnd_818147 373424584030325093155481 := by
  unfold tailWord_818147
  simp only [CollatzResearch.WordTrace]
  refine ⟨29840272567000622228364695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19893515044667081485576463 29840272567000622228364695)
  ·
    refine ⟨44760408850500933342547043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29840272567000622228364695 44760408850500933342547043)
    ·
      refine ⟨67140613275751400013820565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44760408850500933342547043 67140613275751400013820565)
      ·
        refine ⟨3147216247300846875647839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 67140613275751400013820565 3147216247300846875647839)
        ·
          refine ⟨4720824370951270313471759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3147216247300846875647839 4720824370951270313471759)
          ·
            refine ⟨7081236556426905470207639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4720824370951270313471759 7081236556426905470207639)
            ·
              refine ⟨10621854834640358205311459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7081236556426905470207639 10621854834640358205311459)
              ·
                refine ⟨15932782251960537307967189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10621854834640358205311459 15932782251960537307967189)
                ·
                  refine ⟨373424584030325093155481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15932782251960537307967189 373424584030325093155481)
                  ·
                    rfl

theorem cell20_818147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 7].length) (baseStart_818147 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_818147 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_818147 prefixEnd_818147 := by exact prefixLift 818147
  have htrace : WordTrace (prefixWord ++ tailWord_818147) baseStart_818147 baseEnd_818147 := by
    simpa [prefixWord, tailWord_818147, baseEnd_818147] using wordTrace_append hprefix tailTrace_818147
  have hstable : (prefixWord ++ tailWord_818147).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818147).length < 2 ^ (prefixWord ++ tailWord_818147).sum := by decide
  have hdescent : baseEnd_818147 < baseStart_818147 := by decide
  rcases family_descends (prefixWord ++ tailWord_818147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818174 : List Nat := [4, 2, 2, 2, 2, 1, 2, 5]
def baseStart_818174 : Nat := 118140960795 + 818174 * 2 ^ 59
def prefixEnd_818174 : Nat := 4983230072969 + 3 ^ 40 * 818174 * 2
def baseEnd_818174 : Nat := 124478969188677666418457

theorem tailTrace_818174 : CollatzResearch.WordTrace tailWord_818174 prefixEnd_818174 124478969188677666418457 := by
  unfold tailWord_818174
  simp only [CollatzResearch.WordTrace]
  refine ⟨3730157167237850729949697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19894171558601870559731717 3730157167237850729949697)
  ·
    refine ⟨2797617875428388047462273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3730157167237850729949697 2797617875428388047462273)
    ·
      refine ⟨2098213406571291035596705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2797617875428388047462273 2098213406571291035596705)
      ·
        refine ⟨1573660054928468276697529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2098213406571291035596705 1573660054928468276697529)
        ·
          refine ⟨1180245041196351207523147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1573660054928468276697529 1180245041196351207523147)
          ·
            refine ⟨1770367561794526811284721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1180245041196351207523147 1770367561794526811284721)
            ·
              refine ⟨1327775671345895108463541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1770367561794526811284721 1327775671345895108463541)
              ·
                refine ⟨124478969188677666418457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1327775671345895108463541 124478969188677666418457)
                ·
                  rfl

theorem cell20_818174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 5].length) (baseStart_818174 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_818174 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_818174 prefixEnd_818174 := by exact prefixLift 818174
  have htrace : WordTrace (prefixWord ++ tailWord_818174) baseStart_818174 baseEnd_818174 := by
    simpa [prefixWord, tailWord_818174, baseEnd_818174] using wordTrace_append hprefix tailTrace_818174
  have hstable : (prefixWord ++ tailWord_818174).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818174).length < 2 ^ (prefixWord ++ tailWord_818174).sum := by decide
  have hdescent : baseEnd_818174 < baseStart_818174 := by decide
  rcases family_descends (prefixWord ++ tailWord_818174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818226 : List Nat := [3, 2, 1, 1, 2, 2, 3, 4, 2]
def baseStart_818226 : Nat := 118140960795 + 818226 * 2 ^ 59
def prefixEnd_818226 : Nat := 4983230072969 + 3 ^ 40 * 818226 * 2
def baseEnd_818226 : Nat := 373460641782951929521825

theorem tailTrace_818226 : CollatzResearch.WordTrace tailWord_818226 prefixEnd_818226 373460641782951929521825 := by
  unfold tailWord_818226
  simp only [CollatzResearch.WordTrace]
  refine ⟨7460788483428604680122633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19895435955809612480327021 7460788483428604680122633)
  ·
    refine ⟨5595591362571453510091975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7460788483428604680122633 5595591362571453510091975)
    ·
      refine ⟨8393387043857180265137963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5595591362571453510091975 8393387043857180265137963)
      ·
        refine ⟨12590080565785770397706945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8393387043857180265137963 12590080565785770397706945)
        ·
          refine ⟨9442560424339327798280209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12590080565785770397706945 9442560424339327798280209)
          ·
            refine ⟨7081920318254495848710157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9442560424339327798280209 7081920318254495848710157)
            ·
              refine ⟨2655720119345435943266309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7081920318254495848710157 2655720119345435943266309)
              ·
                refine ⟨497947522377269239362433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2655720119345435943266309 497947522377269239362433)
                ·
                  refine ⟨373460641782951929521825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 497947522377269239362433 373460641782951929521825)
                  ·
                    rfl

theorem cell20_818226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 4, 2].length) (baseStart_818226 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_818226 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_818226 prefixEnd_818226 := by exact prefixLift 818226
  have htrace : WordTrace (prefixWord ++ tailWord_818226) baseStart_818226 baseEnd_818226 := by
    simpa [prefixWord, tailWord_818226, baseEnd_818226] using wordTrace_append hprefix tailTrace_818226
  have hstable : (prefixWord ++ tailWord_818226).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818226).length < 2 ^ (prefixWord ++ tailWord_818226).sum := by decide
  have hdescent : baseEnd_818226 < baseStart_818226 := by decide
  rcases family_descends (prefixWord ++ tailWord_818226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818233 : List Nat := [1, 2, 1, 5, 2, 3, 1, 5]
def baseStart_818233 : Nat := 118140960795 + 818233 * 2 ^ 59
def prefixEnd_818233 : Nat := 4983230072969 + 3 ^ 40 * 818233 * 2
def baseEnd_818233 : Nat := 124487945591230338762821

theorem tailTrace_818233 : CollatzResearch.WordTrace tailWord_818233 prefixEnd_818233 124487945591230338762821 := by
  unfold tailWord_818233
  simp only [CollatzResearch.WordTrace]
  refine ⟨29843409244689058915995353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19895606163126039277330235 29843409244689058915995353)
  ·
    refine ⟨22382556933516794186996515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29843409244689058915995353 22382556933516794186996515)
    ·
      refine ⟨33573835400275191280494773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22382556933516794186996515 33573835400275191280494773)
      ·
        refine ⟨3147547068775799182546385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33573835400275191280494773 3147547068775799182546385)
        ·
          refine ⟨2360660301581849386909789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3147547068775799182546385 2360660301581849386909789)
          ·
            refine ⟨885247613093193520091171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2360660301581849386909789 885247613093193520091171)
            ·
              refine ⟨1327871419639790280136757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 885247613093193520091171 1327871419639790280136757)
              ·
                refine ⟨124487945591230338762821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1327871419639790280136757 124487945591230338762821)
                ·
                  rfl

theorem cell20_818233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 5].length) (baseStart_818233 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_818233 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_818233 prefixEnd_818233 := by exact prefixLift 818233
  have htrace : WordTrace (prefixWord ++ tailWord_818233) baseStart_818233 baseEnd_818233 := by
    simpa [prefixWord, tailWord_818233, baseEnd_818233] using wordTrace_append hprefix tailTrace_818233
  have hstable : (prefixWord ++ tailWord_818233).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818233).length < 2 ^ (prefixWord ++ tailWord_818233).sum := by decide
  have hdescent : baseEnd_818233 < baseStart_818233 := by decide
  rcases family_descends (prefixWord ++ tailWord_818233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818247 : List Nat := [1, 1, 4, 1, 3, 3, 1, 2, 4]
def baseStart_818247 : Nat := 118140960795 + 818247 * 2 ^ 59
def prefixEnd_818247 : Nat := 4983230072969 + 3 ^ 40 * 818247 * 2
def baseEnd_818247 : Nat := 373470226755169189821739

theorem tailTrace_818247 : CollatzResearch.WordTrace tailWord_818247 prefixEnd_818247 373470226755169189821739 := by
  unfold tailWord_818247
  simp only [CollatzResearch.WordTrace]
  refine ⟨29843919866638339307004995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19895946577758892871336663 29843919866638339307004995)
  ·
    refine ⟨44765879799957508960507493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29843919866638339307004995 44765879799957508960507493)
    ·
      refine ⟨8393602462492032930095155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44765879799957508960507493 8393602462492032930095155)
      ·
        refine ⟨12590403693738049395142733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8393602462492032930095155 12590403693738049395142733)
        ·
          refine ⟨4721401385151768523178525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12590403693738049395142733 4721401385151768523178525)
          ·
            refine ⟨1770525519431913196191947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4721401385151768523178525 1770525519431913196191947)
            ·
              refine ⟨2655788279147869794287921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1770525519431913196191947 2655788279147869794287921)
              ·
                refine ⟨1991841209360902345715941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2655788279147869794287921 1991841209360902345715941)
                ·
                  refine ⟨373470226755169189821739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1991841209360902345715941 373470226755169189821739)
                  ·
                    rfl

theorem cell20_818247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 2, 4].length) (baseStart_818247 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_818247 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_818247 prefixEnd_818247 := by exact prefixLift 818247
  have htrace : WordTrace (prefixWord ++ tailWord_818247) baseStart_818247 baseEnd_818247 := by
    simpa [prefixWord, tailWord_818247, baseEnd_818247] using wordTrace_append hprefix tailTrace_818247
  have hstable : (prefixWord ++ tailWord_818247).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818247).length < 2 ^ (prefixWord ++ tailWord_818247).sum := by decide
  have hdescent : baseEnd_818247 < baseStart_818247 := by decide
  rcases family_descends (prefixWord ++ tailWord_818247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818261 : List Nat := [1, 3, 2, 2, 1, 2, 2, 2, 5]
def baseStart_818261 : Nat := 118140960795 + 818261 * 2 ^ 59
def prefixEnd_818261 : Nat := 4983230072969 + 3 ^ 40 * 818261 * 2
def baseEnd_818261 : Nat := 373476616736647363355015

theorem tailTrace_818261 : CollatzResearch.WordTrace tailWord_818261 prefixEnd_818261 373476616736647363355015 := by
  unfold tailWord_818261
  simp only [CollatzResearch.WordTrace]
  refine ⟨29844430488587619698014637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19896286992391746465343091 29844430488587619698014637)
  ·
    refine ⟨11191661433220357386755489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29844430488587619698014637 11191661433220357386755489)
    ·
      refine ⟨8393746074915268040066617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11191661433220357386755489 8393746074915268040066617)
      ·
        refine ⟨6295309556186451030049963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8393746074915268040066617 6295309556186451030049963)
        ·
          refine ⟨9442964334279676545074945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6295309556186451030049963 9442964334279676545074945)
          ·
            refine ⟨7082223250709757408806209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9442964334279676545074945 7082223250709757408806209)
            ·
              refine ⟨5311667438032318056604657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7082223250709757408806209 5311667438032318056604657)
              ·
                refine ⟨3983750578524238542453493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5311667438032318056604657 3983750578524238542453493)
                ·
                  refine ⟨373476616736647363355015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3983750578524238542453493 373476616736647363355015)
                  ·
                    rfl

theorem cell20_818261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 5].length) (baseStart_818261 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_818261 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_818261 prefixEnd_818261 := by exact prefixLift 818261
  have htrace : WordTrace (prefixWord ++ tailWord_818261) baseStart_818261 baseEnd_818261 := by
    simpa [prefixWord, tailWord_818261, baseEnd_818261] using wordTrace_append hprefix tailTrace_818261
  have hstable : (prefixWord ++ tailWord_818261).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818261).length < 2 ^ (prefixWord ++ tailWord_818261).sum := by decide
  have hdescent : baseEnd_818261 < baseStart_818261 := by decide
  rcases family_descends (prefixWord ++ tailWord_818261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818264 : List Nat := [2, 1, 2, 2, 1, 3, 4, 3, 2]
def baseStart_818264 : Nat := 118140960795 + 818264 * 2 ^ 59
def prefixEnd_818264 : Nat := 4983230072969 + 3 ^ 40 * 818264 * 2
def baseEnd_818264 : Nat := 373477986018392686255003

theorem tailTrace_818264 : CollatzResearch.WordTrace tailWord_818264 prefixEnd_818264 373477986018392686255003 := by
  unfold tailWord_818264
  simp only [CollatzResearch.WordTrace]
  refine ⟨14922269953788375605186923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19896359938384500806915897 14922269953788375605186923)
  ·
    refine ⟨22383404930682563407780385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14922269953788375605186923 22383404930682563407780385)
    ·
      refine ⟨16787553698011922555835289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22383404930682563407780385 16787553698011922555835289)
      ·
        refine ⟨12590665273508941916876467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16787553698011922555835289 12590665273508941916876467)
        ·
          refine ⟨18885997910263412875314701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12590665273508941916876467 18885997910263412875314701)
          ·
            refine ⟨7082249216348779828243013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18885997910263412875314701 7082249216348779828243013)
            ·
              refine ⟨1327921728065396217795565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7082249216348779828243013 1327921728065396217795565)
              ·
                refine ⟨497970648024523581673337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1327921728065396217795565 497970648024523581673337)
                ·
                  refine ⟨373477986018392686255003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 497970648024523581673337 373477986018392686255003)
                  ·
                    rfl

theorem cell20_818264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 3, 2].length) (baseStart_818264 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_818264 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_818264 prefixEnd_818264 := by exact prefixLift 818264
  have htrace : WordTrace (prefixWord ++ tailWord_818264) baseStart_818264 baseEnd_818264 := by
    simpa [prefixWord, tailWord_818264, baseEnd_818264] using wordTrace_append hprefix tailTrace_818264
  have hstable : (prefixWord ++ tailWord_818264).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818264).length < 2 ^ (prefixWord ++ tailWord_818264).sum := by decide
  have hdescent : baseEnd_818264 < baseStart_818264 := by decide
  rcases family_descends (prefixWord ++ tailWord_818264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818274 : List Nat := [3, 3, 2, 2, 1, 3, 1, 2, 3]
def baseStart_818274 : Nat := 118140960795 + 818274 * 2 ^ 59
def prefixEnd_818274 : Nat := 4983230072969 + 3 ^ 40 * 818274 * 2
def baseEnd_818274 : Nat := 373482550290877095921629

theorem tailTrace_818274 : CollatzResearch.WordTrace tailWord_818274 prefixEnd_818274 373482550290877095921629 := by
  unfold tailWord_818274
  simp only [CollatzResearch.WordTrace]
  refine ⟨7461226159385130729559469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19896603091693681945491917 7461226159385130729559469)
  ·
    refine ⟨2797959809769424023584801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7461226159385130729559469 2797959809769424023584801)
    ·
      refine ⟨2098469857327068017688601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2797959809769424023584801 2098469857327068017688601)
      ·
        refine ⟨1573852392995301013266451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2098469857327068017688601 1573852392995301013266451)
        ·
          refine ⟨2360778589492951519899677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1573852392995301013266451 2360778589492951519899677)
          ·
            refine ⟨885291971059856819962379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2360778589492951519899677 885291971059856819962379)
            ·
              refine ⟨1327937956589785229943569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 885291971059856819962379 1327937956589785229943569)
              ·
                refine ⟨995953467442338922457677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1327937956589785229943569 995953467442338922457677)
                ·
                  refine ⟨373482550290877095921629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 995953467442338922457677 373482550290877095921629)
                  ·
                    rfl

theorem cell20_818274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_818274 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_818274 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_818274 prefixEnd_818274 := by exact prefixLift 818274
  have htrace : WordTrace (prefixWord ++ tailWord_818274) baseStart_818274 baseEnd_818274 := by
    simpa [prefixWord, tailWord_818274, baseEnd_818274] using wordTrace_append hprefix tailTrace_818274
  have hstable : (prefixWord ++ tailWord_818274).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818274).length < 2 ^ (prefixWord ++ tailWord_818274).sum := by decide
  have hdescent : baseEnd_818274 < baseStart_818274 := by decide
  rcases family_descends (prefixWord ++ tailWord_818274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818285 : List Nat := [1, 5, 1, 1, 2, 2, 1, 3, 4]
def baseStart_818285 : Nat := 118140960795 + 818285 * 2 ^ 59
def prefixEnd_818285 : Nat := 4983230072969 + 3 ^ 40 * 818285 * 2
def baseEnd_818285 : Nat := 373487570990609946554917

theorem tailTrace_818285 : CollatzResearch.WordTrace tailWord_818285 prefixEnd_818285 373487570990609946554917 := by
  unfold tailWord_818285
  simp only [CollatzResearch.WordTrace]
  refine ⟨29845305840500671796888309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19896870560333781197925539 29845305840500671796888309)
  ·
    refine ⟨2797997422546937980958279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29845305840500671796888309 2797997422546937980958279)
    ·
      refine ⟨4196996133820406971437419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2797997422546937980958279 4196996133820406971437419)
      ·
        refine ⟨6295494200730610457156129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4196996133820406971437419 6295494200730610457156129)
        ·
          refine ⟨4721620650547957842867097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6295494200730610457156129 4721620650547957842867097)
          ·
            refine ⟨3541215487910968382150323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4721620650547957842867097 3541215487910968382150323)
            ·
              refine ⟨5311823231866452573225485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3541215487910968382150323 5311823231866452573225485)
              ·
                refine ⟨1991933711949919714959557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5311823231866452573225485 1991933711949919714959557)
                ·
                  refine ⟨373487570990609946554917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1991933711949919714959557 373487570990609946554917)
                  ·
                    rfl

theorem cell20_818285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_818285 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_818285 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_818285 prefixEnd_818285 := by exact prefixLift 818285
  have htrace : WordTrace (prefixWord ++ tailWord_818285) baseStart_818285 baseEnd_818285 := by
    simpa [prefixWord, tailWord_818285, baseEnd_818285] using wordTrace_append hprefix tailTrace_818285
  have hstable : (prefixWord ++ tailWord_818285).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818285).length < 2 ^ (prefixWord ++ tailWord_818285).sum := by decide
  have hdescent : baseEnd_818285 < baseStart_818285 := by decide
  rcases family_descends (prefixWord ++ tailWord_818285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818299 : List Nat := [1, 1, 1, 1, 1, 4, 1, 7, 3]
def baseStart_818299 : Nat := 118140960795 + 818299 * 2 ^ 59
def prefixEnd_818299 : Nat := 4983230072969 + 3 ^ 40 * 818299 * 2
def baseEnd_818299 : Nat := 373493960972088120088193

theorem tailTrace_818299 : CollatzResearch.WordTrace tailWord_818299 prefixEnd_818299 373493960972088120088193 := by
  unfold tailWord_818299
  simp only [CollatzResearch.WordTrace]
  refine ⟨29845816462449952187897951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19897210974966634791931967 29845816462449952187897951)
  ·
    refine ⟨44768724693674928281846927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29845816462449952187897951 44768724693674928281846927)
    ·
      refine ⟨67153087040512392422770391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44768724693674928281846927 67153087040512392422770391)
      ·
        refine ⟨100729630560768588634155587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67153087040512392422770391 100729630560768588634155587)
        ·
          refine ⟨151094445841152882951233381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100729630560768588634155587 151094445841152882951233381)
          ·
            refine ⟨28330208595216165553356259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 151094445841152882951233381 28330208595216165553356259)
            ·
              refine ⟨42495312892824248330034389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28330208595216165553356259 42495312892824248330034389)
              ·
                refine ⟨995983895925568320235181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 42495312892824248330034389 995983895925568320235181)
                ·
                  refine ⟨373493960972088120088193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 995983895925568320235181 373493960972088120088193)
                  ·
                    rfl

theorem cell20_818299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 7, 3].length) (baseStart_818299 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_818299 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_818299 prefixEnd_818299 := by exact prefixLift 818299
  have htrace : WordTrace (prefixWord ++ tailWord_818299) baseStart_818299 baseEnd_818299 := by
    simpa [prefixWord, tailWord_818299, baseEnd_818299] using wordTrace_append hprefix tailTrace_818299
  have hstable : (prefixWord ++ tailWord_818299).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818299).length < 2 ^ (prefixWord ++ tailWord_818299).sum := by decide
  have hdescent : baseEnd_818299 < baseStart_818299 := by decide
  rcases family_descends (prefixWord ++ tailWord_818299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818330 : List Nat := [3, 1, 1, 5, 1, 1, 8]
def baseStart_818330 : Nat := 118140960795 + 818330 * 2 ^ 59
def prefixEnd_818330 : Nat := 4983230072969 + 3 ^ 40 * 818330 * 2
def baseEnd_818330 : Nat := 41500901135198865561637

theorem tailTrace_818330 : CollatzResearch.WordTrace tailWord_818330 prefixEnd_818330 41500901135198865561637 := by
  unfold tailWord_818330
  simp only [CollatzResearch.WordTrace]
  refine ⟨7461736781334411120569111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19897964750225096321517629 7461736781334411120569111)
  ·
    refine ⟨11192605172001616680853667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7461736781334411120569111 11192605172001616680853667)
    ·
      refine ⟨16788907758002425021280501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11192605172001616680853667 16788907758002425021280501)
      ·
        refine ⟨1573960102312727345745047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16788907758002425021280501 1573960102312727345745047)
        ·
          refine ⟨2360940153469091018617571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1573960102312727345745047 2360940153469091018617571)
          ·
            refine ⟨3541410230203636527926357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2360940153469091018617571 3541410230203636527926357)
            ·
              refine ⟨41500901135198865561637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3541410230203636527926357 41500901135198865561637)
              ·
                rfl

theorem cell20_818330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 8].length) (baseStart_818330 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_818330 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_818330 prefixEnd_818330 := by exact prefixLift 818330
  have htrace : WordTrace (prefixWord ++ tailWord_818330) baseStart_818330 baseEnd_818330 := by
    simpa [prefixWord, tailWord_818330, baseEnd_818330] using wordTrace_append hprefix tailTrace_818330
  have hstable : (prefixWord ++ tailWord_818330).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818330).length < 2 ^ (prefixWord ++ tailWord_818330).sum := by decide
  have hdescent : baseEnd_818330 < baseStart_818330 := by decide
  rcases family_descends (prefixWord ++ tailWord_818330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818337 : List Nat := [1, 2, 3, 3, 1, 1, 1, 3, 5]
def baseStart_818337 : Nat := 118140960795 + 818337 * 2 ^ 59
def prefixEnd_818337 : Nat := 4983230072969 + 3 ^ 40 * 818337 * 2
def baseEnd_818337 : Nat := 373511305207528876821371

theorem tailTrace_818337 : CollatzResearch.WordTrace tailWord_818337 prefixEnd_818337 373511305207528876821371 := by
  unfold tailWord_818337
  simp only [CollatzResearch.WordTrace]
  refine ⟨29847202436312284677781265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19898134957541523118520843 29847202436312284677781265)
  ·
    refine ⟨22385401827234213508335949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29847202436312284677781265 22385401827234213508335949)
    ·
      refine ⟨8394525685212830065625981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22385401827234213508335949 8394525685212830065625981)
      ·
        refine ⟨3147947131954811274609743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8394525685212830065625981 3147947131954811274609743)
        ·
          refine ⟨4721920697932216911914615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3147947131954811274609743 4721920697932216911914615)
          ·
            refine ⟨7082881046898325367871923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4721920697932216911914615 7082881046898325367871923)
            ·
              refine ⟨10624321570347488051807885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7082881046898325367871923 10624321570347488051807885)
              ·
                refine ⟨3984120588880308019427957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10624321570347488051807885 3984120588880308019427957)
                ·
                  refine ⟨373511305207528876821371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3984120588880308019427957 373511305207528876821371)
                  ·
                    rfl

theorem cell20_818337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 5].length) (baseStart_818337 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_818337 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_818337 prefixEnd_818337 := by exact prefixLift 818337
  have htrace : WordTrace (prefixWord ++ tailWord_818337) baseStart_818337 baseEnd_818337 := by
    simpa [prefixWord, tailWord_818337, baseEnd_818337] using wordTrace_append hprefix tailTrace_818337
  have hstable : (prefixWord ++ tailWord_818337).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818337).length < 2 ^ (prefixWord ++ tailWord_818337).sum := by decide
  have hdescent : baseEnd_818337 < baseStart_818337 := by decide
  rcases family_descends (prefixWord ++ tailWord_818337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818340 : List Nat := [2, 3, 1, 2, 3, 3, 1, 1, 4]
def baseStart_818340 : Nat := 118140960795 + 818340 * 2 ^ 59
def prefixEnd_818340 : Nat := 4983230072969 + 3 ^ 40 * 818340 * 2
def baseEnd_818340 : Nat := 373512674489274199721359

theorem tailTrace_818340 : CollatzResearch.WordTrace tailWord_818340 prefixEnd_818340 373512674489274199721359 := by
  unfold tailWord_818340
  simp only [CollatzResearch.WordTrace]
  refine ⟨14923655927650708095070237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19898207903534277460093649 14923655927650708095070237)
  ·
    refine ⟨5596370972869015535651339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14923655927650708095070237 5596370972869015535651339)
    ·
      refine ⟨8394556459303523303477009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5596370972869015535651339 8394556459303523303477009)
      ·
        refine ⟨6295917344477642477607757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8394556459303523303477009 6295917344477642477607757)
        ·
          refine ⟨2360969004179115929102909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6295917344477642477607757 2360969004179115929102909)
          ·
            refine ⟨885363376567168473413591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2360969004179115929102909 885363376567168473413591)
            ·
              refine ⟨1328045064850752710120387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 885363376567168473413591 1328045064850752710120387)
              ·
                refine ⟨1992067597276129065180581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1328045064850752710120387 1992067597276129065180581)
                ·
                  refine ⟨373512674489274199721359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1992067597276129065180581 373512674489274199721359)
                  ·
                    rfl

theorem cell20_818340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 1, 4].length) (baseStart_818340 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_818340 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_818340 prefixEnd_818340 := by exact prefixLift 818340
  have htrace : WordTrace (prefixWord ++ tailWord_818340) baseStart_818340 baseEnd_818340 := by
    simpa [prefixWord, tailWord_818340, baseEnd_818340] using wordTrace_append hprefix tailTrace_818340
  have hstable : (prefixWord ++ tailWord_818340).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818340).length < 2 ^ (prefixWord ++ tailWord_818340).sum := by decide
  have hdescent : baseEnd_818340 < baseStart_818340 := by decide
  rcases family_descends (prefixWord ++ tailWord_818340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818351 : List Nat := [1, 1, 2, 1, 2, 3, 3, 7]
def baseStart_818351 : Nat := 118140960795 + 818351 * 2 ^ 59
def prefixEnd_818351 : Nat := 4983230072969 + 3 ^ 40 * 818351 * 2
def baseEnd_818351 : Nat := 124505898396335683451549

theorem tailTrace_818351 : CollatzResearch.WordTrace tailWord_818351 prefixEnd_818351 124505898396335683451549 := by
  unfold tailWord_818351
  simp only [CollatzResearch.WordTrace]
  refine ⟨29847713058261565068790907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19898475372174376712527271 29847713058261565068790907)
  ·
    refine ⟨44771569587392347603186361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29847713058261565068790907 44771569587392347603186361)
    ·
      refine ⟨33578677190544260702389771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44771569587392347603186361 33578677190544260702389771)
      ·
        refine ⟨50368015785816391053584657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33578677190544260702389771 50368015785816391053584657)
        ·
          refine ⟨37776011839362293290188493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50368015785816391053584657 37776011839362293290188493)
          ·
            refine ⟨14166004439760859983820685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37776011839362293290188493 14166004439760859983820685)
            ·
              refine ⟨5312251664910322493932757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14166004439760859983820685 5312251664910322493932757)
              ·
                refine ⟨124505898396335683451549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5312251664910322493932757 124505898396335683451549)
                ·
                  rfl

theorem cell20_818351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 7].length) (baseStart_818351 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_818351 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_818351 prefixEnd_818351 := by exact prefixLift 818351
  have htrace : WordTrace (prefixWord ++ tailWord_818351) baseStart_818351 baseEnd_818351 := by
    simpa [prefixWord, tailWord_818351, baseEnd_818351] using wordTrace_append hprefix tailTrace_818351
  have hstable : (prefixWord ++ tailWord_818351).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818351).length < 2 ^ (prefixWord ++ tailWord_818351).sum := by decide
  have hdescent : baseEnd_818351 < baseStart_818351 := by decide
  rcases family_descends (prefixWord ++ tailWord_818351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818354 : List Nat := [3, 2, 1, 1, 1, 5, 1, 3, 3]
def baseStart_818354 : Nat := 118140960795 + 818354 * 2 ^ 59
def prefixEnd_818354 : Nat := 4983230072969 + 3 ^ 40 * 818354 * 2
def baseEnd_818354 : Nat := 373519064470752373254635

theorem tailTrace_818354 : CollatzResearch.WordTrace tailWord_818354 prefixEnd_818354 373519064470752373254635 := by
  unfold tailWord_818354
  simp only [CollatzResearch.WordTrace]
  refine ⟨7461955619312674145287529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19898548318167131054100077 7461955619312674145287529)
  ·
    refine ⟨5596466714484505608965647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7461955619312674145287529 5596466714484505608965647)
    ·
      refine ⟨8394700071726758413448471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5596466714484505608965647 8394700071726758413448471)
      ·
        refine ⟨12592050107590137620172707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8394700071726758413448471 12592050107590137620172707)
        ·
          refine ⟨18888075161385206430259061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12592050107590137620172707 18888075161385206430259061)
          ·
            refine ⟨1770757046379863102836787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18888075161385206430259061 1770757046379863102836787)
            ·
              refine ⟨2656135569569794654255181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1770757046379863102836787 2656135569569794654255181)
              ·
                refine ⟨996050838588672995345693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2656135569569794654255181 996050838588672995345693)
                ·
                  refine ⟨373519064470752373254635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 996050838588672995345693 373519064470752373254635)
                  ·
                    rfl

theorem cell20_818354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 3, 3].length) (baseStart_818354 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_818354 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_818354 prefixEnd_818354 := by exact prefixLift 818354
  have htrace : WordTrace (prefixWord ++ tailWord_818354) baseStart_818354 baseEnd_818354 := by
    simpa [prefixWord, tailWord_818354, baseEnd_818354] using wordTrace_append hprefix tailTrace_818354
  have hstable : (prefixWord ++ tailWord_818354).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818354).length < 2 ^ (prefixWord ++ tailWord_818354).sum := by decide
  have hdescent : baseEnd_818354 < baseStart_818354 := by decide
  rcases family_descends (prefixWord ++ tailWord_818354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818388 : List Nat := [2, 4, 1, 4, 1, 1, 2, 2, 3]
def baseStart_818388 : Nat := 118140960795 + 818388 * 2 ^ 59
def prefixEnd_818388 : Nat := 4983230072969 + 3 ^ 40 * 818388 * 2
def baseEnd_818388 : Nat := 373534582997199366121163

theorem tailTrace_818388 : CollatzResearch.WordTrace tailWord_818388 prefixEnd_818388 373534582997199366121163 := by
  unfold tailWord_818388
  simp only [CollatzResearch.WordTrace]
  refine ⟨14924531279563760193943909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19899375039418346925258545 14924531279563760193943909)
  ·
    refine ⟨2798349614918205036364483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14924531279563760193943909 2798349614918205036364483)
    ·
      refine ⟨4197524422377307554546725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2798349614918205036364483 4197524422377307554546725)
      ·
        refine ⟨787035829195745166477511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4197524422377307554546725 787035829195745166477511)
        ·
          refine ⟨1180553743793617749716267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 787035829195745166477511 1180553743793617749716267)
          ·
            refine ⟨1770830615690426624574401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1180553743793617749716267 1770830615690426624574401)
            ·
              refine ⟨1328122961767819968430801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1770830615690426624574401 1328122961767819968430801)
              ·
                refine ⟨996092221325864976323101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1328122961767819968430801 996092221325864976323101)
                ·
                  refine ⟨373534582997199366121163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 996092221325864976323101 373534582997199366121163)
                  ·
                    rfl

theorem cell20_818388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_818388 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_818388 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_818388 prefixEnd_818388 := by exact prefixLift 818388
  have htrace : WordTrace (prefixWord ++ tailWord_818388) baseStart_818388 baseEnd_818388 := by
    simpa [prefixWord, tailWord_818388, baseEnd_818388] using wordTrace_append hprefix tailTrace_818388
  have hstable : (prefixWord ++ tailWord_818388).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818388).length < 2 ^ (prefixWord ++ tailWord_818388).sum := by decide
  have hdescent : baseEnd_818388 < baseStart_818388 := by decide
  rcases family_descends (prefixWord ++ tailWord_818388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818465 : List Nat := [1, 2, 3, 2, 1, 1, 1, 9]
def baseStart_818465 : Nat := 118140960795 + 818465 * 2 ^ 59
def prefixEnd_818465 : Nat := 4983230072969 + 3 ^ 40 * 818465 * 2
def baseEnd_818465 : Nat := 124523242631776440184727

theorem tailTrace_818465 : CollatzResearch.WordTrace tailWord_818465 prefixEnd_818465 124523242631776440184727 := by
  unfold tailWord_818465
  simp only [CollatzResearch.WordTrace]
  refine ⟨29851870979848562538440849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19901247319899041692293899 29851870979848562538440849)
  ·
    refine ⟨22388903234886421903830637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29851870979848562538440849 22388903234886421903830637)
    ·
      refine ⟨8395838713082408213936489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22388903234886421903830637 8395838713082408213936489)
      ·
        refine ⟨6296879034811806160452367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8395838713082408213936489 6296879034811806160452367)
        ·
          refine ⟨9445318552217709240678551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6296879034811806160452367 9445318552217709240678551)
          ·
            refine ⟨14167977828326563861017827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9445318552217709240678551 14167977828326563861017827)
            ·
              refine ⟨21251966742489845791526741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14167977828326563861017827 21251966742489845791526741)
              ·
                refine ⟨124523242631776440184727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21251966742489845791526741 124523242631776440184727)
                ·
                  rfl

theorem cell20_818465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 9].length) (baseStart_818465 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_818465 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_818465 prefixEnd_818465 := by exact prefixLift 818465
  have htrace : WordTrace (prefixWord ++ tailWord_818465) baseStart_818465 baseEnd_818465 := by
    simpa [prefixWord, tailWord_818465, baseEnd_818465] using wordTrace_append hprefix tailTrace_818465
  have hstable : (prefixWord ++ tailWord_818465).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818465).length < 2 ^ (prefixWord ++ tailWord_818465).sum := by decide
  have hdescent : baseEnd_818465 < baseStart_818465 := by decide
  rcases family_descends (prefixWord ++ tailWord_818465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818482 : List Nat := [3, 2, 1, 1, 4, 2, 1, 6]
def baseStart_818482 : Nat := 118140960795 + 818482 * 2 ^ 59
def prefixEnd_818482 : Nat := 4983230072969 + 3 ^ 40 * 818482 * 2
def baseEnd_818482 : Nat := 124525829052850938995815

theorem tailTrace_818482 : CollatzResearch.WordTrace tailWord_818482 prefixEnd_818482 124525829052850938995815 := by
  unfold tailWord_818482
  simp only [CollatzResearch.WordTrace]
  refine ⟨7463122755196743610452425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19901660680524649627873133 7463122755196743610452425)
  ·
    refine ⟨5597342066397557707839319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7463122755196743610452425 5597342066397557707839319)
    ·
      refine ⟨8396013099596336561758979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5597342066397557707839319 8396013099596336561758979)
      ·
        refine ⟨12594019649394504842638469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8396013099596336561758979 12594019649394504842638469)
        ·
          refine ⟨2361378684261469657994713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12594019649394504842638469 2361378684261469657994713)
          ·
            refine ⟨1771034013196102243496035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2361378684261469657994713 1771034013196102243496035)
            ·
              refine ⟨2656551019794153365244053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1771034013196102243496035 2656551019794153365244053)
              ·
                refine ⟨124525829052850938995815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2656551019794153365244053 124525829052850938995815)
                ·
                  rfl

theorem cell20_818482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 6].length) (baseStart_818482 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_818482 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_818482 prefixEnd_818482 := by exact prefixLift 818482
  have htrace : WordTrace (prefixWord ++ tailWord_818482) baseStart_818482 baseEnd_818482 := by
    simpa [prefixWord, tailWord_818482, baseEnd_818482] using wordTrace_append hprefix tailTrace_818482
  have hstable : (prefixWord ++ tailWord_818482).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818482).length < 2 ^ (prefixWord ++ tailWord_818482).sum := by decide
  have hdescent : baseEnd_818482 < baseStart_818482 := by decide
  rcases family_descends (prefixWord ++ tailWord_818482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818492 : List Nat := [2, 2, 2, 2, 1, 3, 3, 3, 2]
def baseStart_818492 : Nat := 118140960795 + 818492 * 2 ^ 59
def prefixEnd_818492 : Nat := 4983230072969 + 3 ^ 40 * 818492 * 2
def baseEnd_818492 : Nat := 373582051431037226654071

theorem tailTrace_818492 : CollatzResearch.WordTrace tailWord_818492 prefixEnd_818492 373582051431037226654071 := by
  unfold tailWord_818492
  simp only [CollatzResearch.WordTrace]
  refine ⟨14926427875375373074836865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19901903833833830766449153 14926427875375373074836865)
  ·
    refine ⟨11194820906531529806127649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14926427875375373074836865 11194820906531529806127649)
    ·
      refine ⟨8396115679898647354595737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11194820906531529806127649 8396115679898647354595737)
      ·
        refine ⟨6297086759923985515946803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8396115679898647354595737 6297086759923985515946803)
        ·
          refine ⟨9445630139885978273920205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6297086759923985515946803 9445630139885978273920205)
          ·
            refine ⟨3542111302457241852720077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9445630139885978273920205 3542111302457241852720077)
            ·
              refine ⟨1328291738421465694770029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3542111302457241852720077 1328291738421465694770029)
              ·
                refine ⟨498109401908049635538761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1328291738421465694770029 498109401908049635538761)
                ·
                  refine ⟨373582051431037226654071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 498109401908049635538761 373582051431037226654071)
                  ·
                    rfl

theorem cell20_818492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 3, 2].length) (baseStart_818492 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_818492 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_818492 prefixEnd_818492 := by exact prefixLift 818492
  have htrace : WordTrace (prefixWord ++ tailWord_818492) baseStart_818492 baseEnd_818492 := by
    simpa [prefixWord, tailWord_818492, baseEnd_818492] using wordTrace_append hprefix tailTrace_818492
  have hstable : (prefixWord ++ tailWord_818492).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818492).length < 2 ^ (prefixWord ++ tailWord_818492).sum := by decide
  have hdescent : baseEnd_818492 < baseStart_818492 := by decide
  rcases family_descends (prefixWord ++ tailWord_818492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818503 : List Nat := [1, 1, 4, 1, 2, 3, 8]
def baseStart_818503 : Nat := 118140960795 + 818503 * 2 ^ 59
def prefixEnd_818503 : Nat := 4983230072969 + 3 ^ 40 * 818503 * 2
def baseEnd_818503 : Nat := 41509674681196675254151

theorem tailTrace_818503 : CollatzResearch.WordTrace tailWord_818503 prefixEnd_818503 41509674681196675254151 := by
  unfold tailWord_818503
  simp only [CollatzResearch.WordTrace]
  refine ⟨29853256953710895028324163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19902171302473930018882775 29853256953710895028324163)
  ·
    refine ⟨44779885430566342542486245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29853256953710895028324163 44779885430566342542486245)
    ·
      refine ⟨8396228518231189226716171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44779885430566342542486245 8396228518231189226716171)
      ·
        refine ⟨12594342777346783840074257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8396228518231189226716171 12594342777346783840074257)
        ·
          refine ⟨9445757083010087880055693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12594342777346783840074257 9445757083010087880055693)
          ·
            refine ⟨3542158906128782955020885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9445757083010087880055693 3542158906128782955020885)
            ·
              refine ⟨41509674681196675254151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3542158906128782955020885 41509674681196675254151)
              ·
                rfl

theorem cell20_818503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 8].length) (baseStart_818503 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_818503 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_818503 prefixEnd_818503 := by exact prefixLift 818503
  have htrace : WordTrace (prefixWord ++ tailWord_818503) baseStart_818503 baseEnd_818503 := by
    simpa [prefixWord, tailWord_818503, baseEnd_818503] using wordTrace_append hprefix tailTrace_818503
  have hstable : (prefixWord ++ tailWord_818503).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818503).length < 2 ^ (prefixWord ++ tailWord_818503).sum := by decide
  have hdescent : baseEnd_818503 < baseStart_818503 := by decide
  rcases family_descends (prefixWord ++ tailWord_818503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818551 : List Nat := [1, 1, 3, 1, 1, 2, 4, 5, 2]
def baseStart_818551 : Nat := 118140960795 + 818551 * 2 ^ 59
def prefixEnd_818551 : Nat := 4983230072969 + 3 ^ 40 * 818551 * 2
def baseEnd_818551 : Nat := 373608980638695243687163

theorem tailTrace_818551 : CollatzResearch.WordTrace tailWord_818551 prefixEnd_818551 373608980638695243687163 := by
  unfold tailWord_818551
  simp only [CollatzResearch.WordTrace]
  refine ⟨29855007657536999226071507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19903338438357999484047671 29855007657536999226071507)
  ·
    refine ⟨44782511486305498839107261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29855007657536999226071507 44782511486305498839107261)
    ·
      refine ⟨16793441807364562064665223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44782511486305498839107261 16793441807364562064665223)
      ·
        refine ⟨25190162711046843096997835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16793441807364562064665223 25190162711046843096997835)
        ·
          refine ⟨37785244066570264645496753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25190162711046843096997835 37785244066570264645496753)
          ·
            refine ⟨28338933049927698484122565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37785244066570264645496753 28338933049927698484122565)
            ·
              refine ⟨5313549946861443465772981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28338933049927698484122565 5313549946861443465772981)
              ·
                refine ⟨498145307518260324916217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5313549946861443465772981 498145307518260324916217)
                ·
                  refine ⟨373608980638695243687163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 498145307518260324916217 373608980638695243687163)
                  ·
                    rfl

theorem cell20_818551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 5, 2].length) (baseStart_818551 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_818551 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_818551 prefixEnd_818551 := by exact prefixLift 818551
  have htrace : WordTrace (prefixWord ++ tailWord_818551) baseStart_818551 baseEnd_818551 := by
    simpa [prefixWord, tailWord_818551, baseEnd_818551] using wordTrace_append hprefix tailTrace_818551
  have hstable : (prefixWord ++ tailWord_818551).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818551).length < 2 ^ (prefixWord ++ tailWord_818551).sum := by decide
  have hdescent : baseEnd_818551 < baseStart_818551 := by decide
  rcases family_descends (prefixWord ++ tailWord_818551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818561 : List Nat := [1, 2, 4, 3, 2, 1, 2, 2, 3]
def baseStart_818561 : Nat := 118140960795 + 818561 * 2 ^ 59
def prefixEnd_818561 : Nat := 4983230072969 + 3 ^ 40 * 818561 * 2
def baseEnd_818561 : Nat := 373613544911179653353789

theorem tailTrace_818561 : CollatzResearch.WordTrace tailWord_818561 prefixEnd_818561 373613544911179653353789 := by
  unfold tailWord_818561
  simp only [CollatzResearch.WordTrace]
  refine ⟨29855372387500770933935537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19903581591667180622623691 29855372387500770933935537)
  ·
    refine ⟨22391529290625578200451653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29855372387500770933935537 22391529290625578200451653)
    ·
      refine ⟨4198411741992295912584685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22391529290625578200451653 4198411741992295912584685)
      ·
        refine ⟨1574404403247110967219257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4198411741992295912584685 1574404403247110967219257)
        ·
          refine ⟨1180803302435333225414443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1574404403247110967219257 1180803302435333225414443)
          ·
            refine ⟨1771204953652999838121665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1180803302435333225414443 1771204953652999838121665)
            ·
              refine ⟨1328403715239749878591249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1771204953652999838121665 1328403715239749878591249)
              ·
                refine ⟨996302786429812408943437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1328403715239749878591249 996302786429812408943437)
                ·
                  refine ⟨373613544911179653353789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 996302786429812408943437 373613544911179653353789)
                  ·
                    rfl

theorem cell20_818561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 2, 3].length) (baseStart_818561 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_818561 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_818561 prefixEnd_818561 := by exact prefixLift 818561
  have htrace : WordTrace (prefixWord ++ tailWord_818561) baseStart_818561 baseEnd_818561 := by
    simpa [prefixWord, tailWord_818561, baseEnd_818561] using wordTrace_append hprefix tailTrace_818561
  have hstable : (prefixWord ++ tailWord_818561).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818561).length < 2 ^ (prefixWord ++ tailWord_818561).sum := by decide
  have hdescent : baseEnd_818561 < baseStart_818561 := by decide
  rcases family_descends (prefixWord ++ tailWord_818561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818565 : List Nat := [1, 3, 1, 1, 3, 1, 3, 4, 3]
def baseStart_818565 : Nat := 118140960795 + 818565 * 2 ^ 59
def prefixEnd_818565 : Nat := 4983230072969 + 3 ^ 40 * 818565 * 2
def baseEnd_818565 : Nat := 373615370620173417220439

theorem tailTrace_818565 : CollatzResearch.WordTrace tailWord_818565 prefixEnd_818565 373615370620173417220439 := by
  unfold tailWord_818565
  simp only [CollatzResearch.WordTrace]
  refine ⟨29855518279486279617081149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19903678852990853078054099 29855518279486279617081149)
  ·
    refine ⟨11195819354807354856405431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29855518279486279617081149 11195819354807354856405431)
    ·
      refine ⟨16793729032211032284608147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11195819354807354856405431 16793729032211032284608147)
      ·
        refine ⟨25190593548316548426912221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16793729032211032284608147 25190593548316548426912221)
        ·
          refine ⟨9446472580618705660092083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25190593548316548426912221 9446472580618705660092083)
          ·
            refine ⟨14169708870928058490138125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9446472580618705660092083 14169708870928058490138125)
            ·
              refine ⟨5313640826598021933801797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14169708870928058490138125 5313640826598021933801797)
              ·
                refine ⟨996307654987129112587837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5313640826598021933801797 996307654987129112587837)
                ·
                  refine ⟨373615370620173417220439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 996307654987129112587837 373615370620173417220439)
                  ·
                    rfl

theorem cell20_818565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 4, 3].length) (baseStart_818565 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_818565 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_818565 prefixEnd_818565 := by exact prefixLift 818565
  have htrace : WordTrace (prefixWord ++ tailWord_818565) baseStart_818565 baseEnd_818565 := by
    simpa [prefixWord, tailWord_818565, baseEnd_818565] using wordTrace_append hprefix tailTrace_818565
  have hstable : (prefixWord ++ tailWord_818565).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818565).length < 2 ^ (prefixWord ++ tailWord_818565).sum := by decide
  have hdescent : baseEnd_818565 < baseStart_818565 := by decide
  rcases family_descends (prefixWord ++ tailWord_818565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818568 : List Nat := [2, 1, 3, 3, 1, 3, 1, 4, 2]
def baseStart_818568 : Nat := 118140960795 + 818568 * 2 ^ 59
def prefixEnd_818568 : Nat := 4983230072969 + 3 ^ 40 * 818568 * 2
def baseEnd_818568 : Nat := 373616739901918740120427

theorem tailTrace_818568 : CollatzResearch.WordTrace tailWord_818568 prefixEnd_818568 373616739901918740120427 := by
  unfold tailWord_818568
  simp only [CollatzResearch.WordTrace]
  refine ⟨14927813849237705564720179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19903751798983607419626905 14927813849237705564720179)
  ·
    refine ⟨22391720773856558347080269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14927813849237705564720179 22391720773856558347080269)
    ·
      refine ⟨8396895290196209380155101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22391720773856558347080269 8396895290196209380155101)
      ·
        refine ⟨3148835733823578517558163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8396895290196209380155101 3148835733823578517558163)
        ·
          refine ⟨4723253600735367776337245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3148835733823578517558163 4723253600735367776337245)
          ·
            refine ⟨1771220100275762916126467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4723253600735367776337245 1771220100275762916126467)
            ·
              refine ⟨2656830150413644374189701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1771220100275762916126467 2656830150413644374189701)
              ·
                refine ⟨498155653202558320160569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2656830150413644374189701 498155653202558320160569)
                ·
                  refine ⟨373616739901918740120427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 498155653202558320160569 373616739901918740120427)
                  ·
                    rfl

theorem cell20_818568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 4, 2].length) (baseStart_818568 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_818568 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_818568 prefixEnd_818568 := by exact prefixLift 818568
  have htrace : WordTrace (prefixWord ++ tailWord_818568) baseStart_818568 baseEnd_818568 := by
    simpa [prefixWord, tailWord_818568, baseEnd_818568] using wordTrace_append hprefix tailTrace_818568
  have hstable : (prefixWord ++ tailWord_818568).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818568).length < 2 ^ (prefixWord ++ tailWord_818568).sum := by decide
  have hdescent : baseEnd_818568 < baseStart_818568 := by decide
  rcases family_descends (prefixWord ++ tailWord_818568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818572 : List Nat := [2, 2, 1, 2, 1, 3, 2, 3, 4]
def baseStart_818572 : Nat := 118140960795 + 818572 * 2 ^ 59
def prefixEnd_818572 : Nat := 4983230072969 + 3 ^ 40 * 818572 * 2
def baseEnd_818572 : Nat := 373618565610912503987077

theorem tailTrace_818572 : CollatzResearch.WordTrace tailWord_818572 prefixEnd_818572 373618565610912503987077 := by
  unfold tailWord_818572
  simp only [CollatzResearch.WordTrace]
  refine ⟨14927886795230459906292985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19903849060307279875057313 14927886795230459906292985)
  ·
    refine ⟨11195915096422844929719739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14927886795230459906292985 11195915096422844929719739)
    ·
      refine ⟨16793872644634267394579609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11195915096422844929719739 16793872644634267394579609)
      ·
        refine ⟨12595404483475700545934707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16793872644634267394579609 12595404483475700545934707)
        ·
          refine ⟨18893106725213550818902061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12595404483475700545934707 18893106725213550818902061)
          ·
            refine ⟨7084915021955081557088273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18893106725213550818902061 7084915021955081557088273)
            ·
              refine ⟨5313686266466311167816205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7084915021955081557088273 5313686266466311167816205)
              ·
                refine ⟨1992632349924866687931077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5313686266466311167816205 1992632349924866687931077)
                ·
                  refine ⟨373618565610912503987077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1992632349924866687931077 373618565610912503987077)
                  ·
                    rfl

theorem cell20_818572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 3, 4].length) (baseStart_818572 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_818572 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_818572 prefixEnd_818572 := by exact prefixLift 818572
  have htrace : WordTrace (prefixWord ++ tailWord_818572) baseStart_818572 baseEnd_818572 := by
    simpa [prefixWord, tailWord_818572, baseEnd_818572] using wordTrace_append hprefix tailTrace_818572
  have hstable : (prefixWord ++ tailWord_818572).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818572).length < 2 ^ (prefixWord ++ tailWord_818572).sum := by decide
  have hdescent : baseEnd_818572 < baseStart_818572 := by decide
  rcases family_descends (prefixWord ++ tailWord_818572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818589 : List Nat := [1, 4, 2, 1, 3, 2, 1, 2, 4]
def baseStart_818589 : Nat := 118140960795 + 818589 * 2 ^ 59
def prefixEnd_818589 : Nat := 4983230072969 + 3 ^ 40 * 818589 * 2
def baseEnd_818589 : Nat := 373626324874136000420341

theorem tailTrace_818589 : CollatzResearch.WordTrace tailWord_818589 prefixEnd_818589 373626324874136000420341 := by
  unfold tailWord_818589
  simp only [CollatzResearch.WordTrace]
  refine ⟨29856393631399331715954821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19904262420932887810636547 29856393631399331715954821)
  ·
    refine ⟨5598073805887374696741529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29856393631399331715954821 5598073805887374696741529)
    ·
      refine ⟨4198555354415531022556147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5598073805887374696741529 4198555354415531022556147)
      ·
        refine ⟨6297833031623296533834221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4198555354415531022556147 6297833031623296533834221)
        ·
          refine ⟨2361687386858736200187833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6297833031623296533834221 2361687386858736200187833)
          ·
            refine ⟨1771265540144052150140875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2361687386858736200187833 1771265540144052150140875)
            ·
              refine ⟨2656898310216078225211313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1771265540144052150140875 2656898310216078225211313)
              ·
                refine ⟨1992673732662058668908485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2656898310216078225211313 1992673732662058668908485)
                ·
                  refine ⟨373626324874136000420341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1992673732662058668908485 373626324874136000420341)
                  ·
                    rfl

theorem cell20_818589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_818589 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_818589 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_818589 prefixEnd_818589 := by exact prefixLift 818589
  have htrace : WordTrace (prefixWord ++ tailWord_818589) baseStart_818589 baseEnd_818589 := by
    simpa [prefixWord, tailWord_818589, baseEnd_818589] using wordTrace_append hprefix tailTrace_818589
  have hstable : (prefixWord ++ tailWord_818589).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818589).length < 2 ^ (prefixWord ++ tailWord_818589).sum := by decide
  have hdescent : baseEnd_818589 < baseStart_818589 := by decide
  rcases family_descends (prefixWord ++ tailWord_818589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818620 : List Nat := [2, 2, 2, 4, 2, 1, 1, 1, 5]
def baseStart_818620 : Nat := 118140960795 + 818620 * 2 ^ 59
def prefixEnd_818620 : Nat := 4983230072969 + 3 ^ 40 * 818620 * 2
def baseEnd_818620 : Nat := 373640474118837670386881

theorem tailTrace_818620 : CollatzResearch.WordTrace tailWord_818620 prefixEnd_818620 373640474118837670386881 := by
  unfold tailWord_818620
  simp only [CollatzResearch.WordTrace]
  refine ⟨14928762147143512005166657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19905016196191349340222209 14928762147143512005166657)
  ·
    refine ⟨11196571610357634003874993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14928762147143512005166657 11196571610357634003874993)
    ·
      refine ⟨8397428707768225502906245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11196571610357634003874993 8397428707768225502906245)
      ·
        refine ⟨1574517882706542281794921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8397428707768225502906245 1574517882706542281794921)
        ·
          refine ⟨1180888412029906711346191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1574517882706542281794921 1180888412029906711346191)
          ·
            refine ⟨1771332618044860067019287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1180888412029906711346191 1771332618044860067019287)
            ·
              refine ⟨2656998927067290100528931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1771332618044860067019287 2656998927067290100528931)
              ·
                refine ⟨3985498390600935150793397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2656998927067290100528931 3985498390600935150793397)
                ·
                  refine ⟨373640474118837670386881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3985498390600935150793397 373640474118837670386881)
                  ·
                    rfl

theorem cell20_818620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 5].length) (baseStart_818620 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_818620 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_818620 prefixEnd_818620 := by exact prefixLift 818620
  have htrace : WordTrace (prefixWord ++ tailWord_818620) baseStart_818620 baseEnd_818620 := by
    simpa [prefixWord, tailWord_818620, baseEnd_818620] using wordTrace_append hprefix tailTrace_818620
  have hstable : (prefixWord ++ tailWord_818620).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818620).length < 2 ^ (prefixWord ++ tailWord_818620).sum := by decide
  have hdescent : baseEnd_818620 < baseStart_818620 := by decide
  rcases family_descends (prefixWord ++ tailWord_818620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818627 : List Nat := [1, 1, 1, 3, 1, 1, 6, 4, 2]
def baseStart_818627 : Nat := 118140960795 + 818627 * 2 ^ 59
def prefixEnd_818627 : Nat := 4983230072969 + 3 ^ 40 * 818627 * 2
def baseEnd_818627 : Nat := 373643669109576757153519

theorem tailTrace_818627 : CollatzResearch.WordTrace tailWord_818627 prefixEnd_818627 373643669109576757153519 := by
  unfold tailWord_818627
  simp only [CollatzResearch.WordTrace]
  refine ⟨29857779605261664205838135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19905186403507776137225423 29857779605261664205838135)
  ·
    refine ⟨44786669407892496308757203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29857779605261664205838135 44786669407892496308757203)
    ·
      refine ⟨67180004111838744463135805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44786669407892496308757203 67180004111838744463135805)
      ·
        refine ⟨25192501541939529173675927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67180004111838744463135805 25192501541939529173675927)
        ·
          refine ⟨37788752312909293760513891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25192501541939529173675927 37788752312909293760513891)
          ·
            refine ⟨56683128469363940640770837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37788752312909293760513891 56683128469363940640770837)
            ·
              refine ⟨2657021647001434717536133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 56683128469363940640770837 2657021647001434717536133)
              ·
                refine ⟨498191558812769009538025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2657021647001434717536133 498191558812769009538025)
                ·
                  refine ⟨373643669109576757153519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 498191558812769009538025 373643669109576757153519)
                  ·
                    rfl

theorem cell20_818627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 4, 2].length) (baseStart_818627 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_818627 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_818627 prefixEnd_818627 := by exact prefixLift 818627
  have htrace : WordTrace (prefixWord ++ tailWord_818627) baseStart_818627 baseEnd_818627 := by
    simpa [prefixWord, tailWord_818627, baseEnd_818627] using wordTrace_append hprefix tailTrace_818627
  have hstable : (prefixWord ++ tailWord_818627).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818627).length < 2 ^ (prefixWord ++ tailWord_818627).sum := by decide
  have hdescent : baseEnd_818627 < baseStart_818627 := by decide
  rcases family_descends (prefixWord ++ tailWord_818627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818648 : List Nat := [2, 1, 2, 2, 2, 1, 4, 2, 4]
def baseStart_818648 : Nat := 118140960795 + 818648 * 2 ^ 59
def prefixEnd_818648 : Nat := 4983230072969 + 3 ^ 40 * 818648 * 2
def baseEnd_818648 : Nat := 373653254081794017453433

theorem tailTrace_818648 : CollatzResearch.WordTrace tailWord_818648 prefixEnd_818648 373653254081794017453433 := by
  unfold tailWord_818648
  simp only [CollatzResearch.WordTrace]
  refine ⟨14929272769092792396176299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19905697025457056528235065 14929272769092792396176299)
  ·
    refine ⟨22393909153639188594264449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14929272769092792396176299 22393909153639188594264449)
    ·
      refine ⟨16795431865229391445698337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22393909153639188594264449 16795431865229391445698337)
      ·
        refine ⟨12596573898922043584273753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16795431865229391445698337 12596573898922043584273753)
        ·
          refine ⟨9447430424191532688205315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12596573898922043584273753 9447430424191532688205315)
          ·
            refine ⟨14171145636287299032307973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9447430424191532688205315 14171145636287299032307973)
            ·
              refine ⟨2657089806803868568557745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14171145636287299032307973 2657089806803868568557745)
              ·
                refine ⟨1992817355102901426418309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2657089806803868568557745 1992817355102901426418309)
                ·
                  refine ⟨373653254081794017453433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1992817355102901426418309 373653254081794017453433)
                  ·
                    rfl

theorem cell20_818648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 2, 4].length) (baseStart_818648 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_818648 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_818648 prefixEnd_818648 := by exact prefixLift 818648
  have htrace : WordTrace (prefixWord ++ tailWord_818648) baseStart_818648 baseEnd_818648 := by
    simpa [prefixWord, tailWord_818648, baseEnd_818648] using wordTrace_append hprefix tailTrace_818648
  have hstable : (prefixWord ++ tailWord_818648).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818648).length < 2 ^ (prefixWord ++ tailWord_818648).sum := by decide
  have hdescent : baseEnd_818648 < baseStart_818648 := by decide
  rcases family_descends (prefixWord ++ tailWord_818648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818655 : List Nat := [1, 1, 2, 3, 3, 1, 3, 6]
def baseStart_818655 : Nat := 118140960795 + 818655 * 2 ^ 59
def prefixEnd_818655 : Nat := 4983230072969 + 3 ^ 40 * 818655 * 2
def baseEnd_818655 : Nat := 124552149690844368073357

theorem tailTrace_818655 : CollatzResearch.WordTrace tailWord_818655 prefixEnd_818655 124552149690844368073357 := by
  unfold tailWord_818655
  simp only [CollatzResearch.WordTrace]
  refine ⟨29858800849160224987857419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19905867232773483325238279 29858800849160224987857419)
  ·
    refine ⟨44788201273740337481786129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29858800849160224987857419 44788201273740337481786129)
    ·
      refine ⟨33591150955305253111339597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44788201273740337481786129 33591150955305253111339597)
      ·
        refine ⟨12596681608239469916752349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33591150955305253111339597 12596681608239469916752349)
        ·
          refine ⟨4723755603089801218782131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12596681608239469916752349 4723755603089801218782131)
          ·
            refine ⟨7085633404634701828173197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4723755603089801218782131 7085633404634701828173197)
            ·
              refine ⟨2657112526738013185564949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7085633404634701828173197 2657112526738013185564949)
              ·
                refine ⟨124552149690844368073357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2657112526738013185564949 124552149690844368073357)
                ·
                  rfl

theorem cell20_818655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 6].length) (baseStart_818655 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_818655 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_818655 prefixEnd_818655 := by exact prefixLift 818655
  have htrace : WordTrace (prefixWord ++ tailWord_818655) baseStart_818655 baseEnd_818655 := by
    simpa [prefixWord, tailWord_818655, baseEnd_818655] using wordTrace_append hprefix tailTrace_818655
  have hstable : (prefixWord ++ tailWord_818655).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818655).length < 2 ^ (prefixWord ++ tailWord_818655).sum := by decide
  have hdescent : baseEnd_818655 < baseStart_818655 := by decide
  rcases family_descends (prefixWord ++ tailWord_818655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818661 : List Nat := [1, 3, 1, 5, 1, 3, 1, 3, 2]
def baseStart_818661 : Nat := 118140960795 + 818661 * 2 ^ 59
def prefixEnd_818661 : Nat := 4983230072969 + 3 ^ 40 * 818661 * 2
def baseEnd_818661 : Nat := 373659187636023750020047

theorem tailTrace_818661 : CollatzResearch.WordTrace tailWord_818661 prefixEnd_818661 373659187636023750020047 := by
  unfold tailWord_818661
  simp only [CollatzResearch.WordTrace]
  refine ⟨29859019687138488012575837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19906013124758992008383891 29859019687138488012575837)
  ·
    refine ⟨11197132382676933004715939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29859019687138488012575837 11197132382676933004715939)
    ·
      refine ⟨16795698574015399507073909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11197132382676933004715939 16795698574015399507073909)
      ·
        refine ⟨1574596741313943703788179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16795698574015399507073909 1574596741313943703788179)
        ·
          refine ⟨2361895111970915555682269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1574596741313943703788179 2361895111970915555682269)
          ·
            refine ⟨885710666989093333380851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2361895111970915555682269 885710666989093333380851)
            ·
              refine ⟨1328566000483640000071277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 885710666989093333380851 1328566000483640000071277)
              ·
                refine ⟨498212250181365000026729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1328566000483640000071277 498212250181365000026729)
                ·
                  refine ⟨373659187636023750020047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 498212250181365000026729 373659187636023750020047)
                  ·
                    rfl

theorem cell20_818661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 3, 2].length) (baseStart_818661 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_818661 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_818661 prefixEnd_818661 := by exact prefixLift 818661
  have htrace : WordTrace (prefixWord ++ tailWord_818661) baseStart_818661 baseEnd_818661 := by
    simpa [prefixWord, tailWord_818661, baseEnd_818661] using wordTrace_append hprefix tailTrace_818661
  have hstable : (prefixWord ++ tailWord_818661).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818661).length < 2 ^ (prefixWord ++ tailWord_818661).sum := by decide
  have hdescent : baseEnd_818661 < baseStart_818661 := by decide
  rcases family_descends (prefixWord ++ tailWord_818661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818682 : List Nat := [3, 1, 1, 1, 1, 2, 7, 2, 2]
def baseStart_818682 : Nat := 118140960795 + 818682 * 2 ^ 59
def prefixEnd_818682 : Nat := 4983230072969 + 3 ^ 40 * 818682 * 2
def baseEnd_818682 : Nat := 373668772608241010319961

theorem tailTrace_818682 : CollatzResearch.WordTrace tailWord_818682 prefixEnd_818682 373668772608241010319961 := by
  unfold tailWord_818682
  simp only [CollatzResearch.WordTrace]
  refine ⟨7464946405015602149772575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19906523746708272399393533 7464946405015602149772575)
  ·
    refine ⟨11197419607523403224658863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7464946405015602149772575 11197419607523403224658863)
    ·
      refine ⟨16796129411285104836988295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11197419607523403224658863 16796129411285104836988295)
      ·
        refine ⟨25194194116927657255482443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16796129411285104836988295 25194194116927657255482443)
        ·
          refine ⟨37791291175391485883223665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25194194116927657255482443 37791291175391485883223665)
          ·
            refine ⟨28343468381543614412417749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37791291175391485883223665 28343468381543614412417749)
            ·
              refine ⟨664300040192428462791041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 28343468381543614412417749 664300040192428462791041)
              ·
                refine ⟨498225030144321347093281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 664300040192428462791041 498225030144321347093281)
                ·
                  refine ⟨373668772608241010319961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 498225030144321347093281 373668772608241010319961)
                  ·
                    rfl

theorem cell20_818682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 7, 2, 2].length) (baseStart_818682 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_818682 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_818682 prefixEnd_818682 := by exact prefixLift 818682
  have htrace : WordTrace (prefixWord ++ tailWord_818682) baseStart_818682 baseEnd_818682 := by
    simpa [prefixWord, tailWord_818682, baseEnd_818682] using wordTrace_append hprefix tailTrace_818682
  have hstable : (prefixWord ++ tailWord_818682).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818682).length < 2 ^ (prefixWord ++ tailWord_818682).sum := by decide
  have hdescent : baseEnd_818682 < baseStart_818682 := by decide
  rcases family_descends (prefixWord ++ tailWord_818682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818692 : List Nat := [2, 3, 2, 3, 2, 2, 2, 1, 3]
def baseStart_818692 : Nat := 118140960795 + 818692 * 2 ^ 59
def prefixEnd_818692 : Nat := 4983230072969 + 3 ^ 40 * 818692 * 2
def baseEnd_818692 : Nat := 373673336880725419986587

theorem tailTrace_818692 : CollatzResearch.WordTrace tailWord_818692 prefixEnd_818692 373673336880725419986587 := by
  unfold tailWord_818692
  simp only [CollatzResearch.WordTrace]
  refine ⟨14930075175013090153477165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19906766900017453537969553 14930075175013090153477165)
  ·
    refine ⟨5598778190629908807553937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14930075175013090153477165 5598778190629908807553937)
    ·
      refine ⟨4199083642972431605665453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5598778190629908807553937 4199083642972431605665453)
      ·
        refine ⟨1574656366114661852124545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4199083642972431605665453 1574656366114661852124545)
        ·
          refine ⟨1180992274585996389093409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1574656366114661852124545 1180992274585996389093409)
          ·
            refine ⟨885744205939497291820057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1180992274585996389093409 885744205939497291820057)
            ·
              refine ⟨664308154454622968865043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 885744205939497291820057 664308154454622968865043)
              ·
                refine ⟨996462231681934453297565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 664308154454622968865043 996462231681934453297565)
                ·
                  refine ⟨373673336880725419986587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 996462231681934453297565 373673336880725419986587)
                  ·
                    rfl

theorem cell20_818692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 2, 1, 3].length) (baseStart_818692 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_818692 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_818692 prefixEnd_818692 := by exact prefixLift 818692
  have htrace : WordTrace (prefixWord ++ tailWord_818692) baseStart_818692 baseEnd_818692 := by
    simpa [prefixWord, tailWord_818692, baseEnd_818692] using wordTrace_append hprefix tailTrace_818692
  have hstable : (prefixWord ++ tailWord_818692).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818692).length < 2 ^ (prefixWord ++ tailWord_818692).sum := by decide
  have hdescent : baseEnd_818692 < baseStart_818692 := by decide
  rcases family_descends (prefixWord ++ tailWord_818692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818696 : List Nat := [2, 1, 3, 2, 1, 1, 6, 1, 3]
def baseStart_818696 : Nat := 118140960795 + 818696 * 2 ^ 59
def prefixEnd_818696 : Nat := 4983230072969 + 3 ^ 40 * 818696 * 2
def baseEnd_818696 : Nat := 373675162589719183853237

theorem tailTrace_818696 : CollatzResearch.WordTrace tailWord_818696 prefixEnd_818696 373675162589719183853237 := by
  unfold tailWord_818696
  simp only [CollatzResearch.WordTrace]
  refine ⟨14930148121005844495049971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19906864161341125993399961 14930148121005844495049971)
  ·
    refine ⟨22395222181508766742574957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14930148121005844495049971 22395222181508766742574957)
    ·
      refine ⟨8398208318065787528465609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22395222181508766742574957 8398208318065787528465609)
      ·
        refine ⟨6298656238549340646349207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8398208318065787528465609 6298656238549340646349207)
        ·
          refine ⟨9447984357824010969523811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6298656238549340646349207 9447984357824010969523811)
          ·
            refine ⟨14171976536736016454285717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9447984357824010969523811 14171976536736016454285717)
            ·
              refine ⟨664311400159500771294643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14171976536736016454285717 664311400159500771294643)
              ·
                refine ⟨996467100239251156941965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 664311400159500771294643 996467100239251156941965)
                ·
                  refine ⟨373675162589719183853237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 996467100239251156941965 373675162589719183853237)
                  ·
                    rfl

theorem cell20_818696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 6, 1, 3].length) (baseStart_818696 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_818696 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_818696 prefixEnd_818696 := by exact prefixLift 818696
  have htrace : WordTrace (prefixWord ++ tailWord_818696) baseStart_818696 baseEnd_818696 := by
    simpa [prefixWord, tailWord_818696, baseEnd_818696] using wordTrace_append hprefix tailTrace_818696
  have hstable : (prefixWord ++ tailWord_818696).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818696).length < 2 ^ (prefixWord ++ tailWord_818696).sum := by decide
  have hdescent : baseEnd_818696 < baseStart_818696 := by decide
  rcases family_descends (prefixWord ++ tailWord_818696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818734 : List Nat := [4, 1, 3, 1, 2, 1, 1, 4, 3]
def baseStart_818734 : Nat := 118140960795 + 818734 * 2 ^ 59
def prefixEnd_818734 : Nat := 4983230072969 + 3 ^ 40 * 818734 * 2
def baseEnd_818734 : Nat := 373692506825159940586415

theorem tailTrace_818734 : CollatzResearch.WordTrace tailWord_818734 prefixEnd_818734 373692506825159940586415 := by
  unfold tailWord_818734
  simp only [CollatzResearch.WordTrace]
  refine ⟨3732710276984252684997907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19907788143916014319988837 3732710276984252684997907)
  ·
    refine ⟨5599065415476379027496861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3732710276984252684997907 5599065415476379027496861)
    ·
      refine ⟨2099649530803642135311323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5599065415476379027496861 2099649530803642135311323)
      ·
        refine ⟨3149474296205463202966985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2099649530803642135311323 3149474296205463202966985)
        ·
          refine ⟨2362105722154097402225239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3149474296205463202966985 2362105722154097402225239)
          ·
            refine ⟨3543158583231146103337859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2362105722154097402225239 3543158583231146103337859)
            ·
              refine ⟨5314737874846719155006789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3543158583231146103337859 5314737874846719155006789)
              ·
                refine ⟨996513351533759841563773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5314737874846719155006789 996513351533759841563773)
                ·
                  refine ⟨373692506825159940586415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 996513351533759841563773 373692506825159940586415)
                  ·
                    rfl

theorem cell20_818734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 4, 3].length) (baseStart_818734 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_818734 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_818734 prefixEnd_818734 := by exact prefixLift 818734
  have htrace : WordTrace (prefixWord ++ tailWord_818734) baseStart_818734 baseEnd_818734 := by
    simpa [prefixWord, tailWord_818734, baseEnd_818734] using wordTrace_append hprefix tailTrace_818734
  have hstable : (prefixWord ++ tailWord_818734).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818734).length < 2 ^ (prefixWord ++ tailWord_818734).sum := by decide
  have hdescent : baseEnd_818734 < baseStart_818734 := by decide
  rcases family_descends (prefixWord ++ tailWord_818734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818762 : List Nat := [3, 1, 2, 1, 1, 3, 3, 2, 4]
def baseStart_818762 : Nat := 118140960795 + 818762 * 2 ^ 59
def prefixEnd_818762 : Nat := 4983230072969 + 3 ^ 40 * 818762 * 2
def baseEnd_818762 : Nat := 373705286788116287652967

theorem tailTrace_818762 : CollatzResearch.WordTrace tailWord_818762 prefixEnd_818762 373705286788116287652967 := by
  unfold tailWord_818762
  simp only [CollatzResearch.WordTrace]
  refine ⟨7465675864943145565500635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19908468973181721508001693 7465675864943145565500635)
  ·
    refine ⟨11198513797414718348250953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7465675864943145565500635 11198513797414718348250953)
    ·
      refine ⟨8398885348061038761188215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11198513797414718348250953 8398885348061038761188215)
      ·
        refine ⟨12598328022091558141782323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8398885348061038761188215 12598328022091558141782323)
        ·
          refine ⟨18897492033137337212673485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12598328022091558141782323 18897492033137337212673485)
          ·
            refine ⟨7086559512426501454752557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18897492033137337212673485 7086559512426501454752557)
            ·
              refine ⟨2657459817159938045532209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7086559512426501454752557 2657459817159938045532209)
              ·
                refine ⟨1993094862869953534149157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2657459817159938045532209 1993094862869953534149157)
                ·
                  refine ⟨373705286788116287652967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1993094862869953534149157 373705286788116287652967)
                  ·
                    rfl

theorem cell20_818762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 2, 4].length) (baseStart_818762 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_818762 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_818762 prefixEnd_818762 := by exact prefixLift 818762
  have htrace : WordTrace (prefixWord ++ tailWord_818762) baseStart_818762 baseEnd_818762 := by
    simpa [prefixWord, tailWord_818762, baseEnd_818762] using wordTrace_append hprefix tailTrace_818762
  have hstable : (prefixWord ++ tailWord_818762).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818762).length < 2 ^ (prefixWord ++ tailWord_818762).sum := by decide
  have hdescent : baseEnd_818762 < baseStart_818762 := by decide
  rcases family_descends (prefixWord ++ tailWord_818762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818776 : List Nat := [2, 1, 2, 2, 1, 2, 1, 4, 5]
def baseStart_818776 : Nat := 118140960795 + 818776 * 2 ^ 59
def prefixEnd_818776 : Nat := 4983230072969 + 3 ^ 40 * 818776 * 2
def baseEnd_818776 : Nat := 373711676769594461186243

theorem tailTrace_818776 : CollatzResearch.WordTrace tailWord_818776 prefixEnd_818776 373711676769594461186243 := by
  unfold tailWord_818776
  simp only [CollatzResearch.WordTrace]
  refine ⟨14931607040860931326506091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19908809387814575102008121 14931607040860931326506091)
  ·
    refine ⟨22397410561291396989759137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14931607040860931326506091 22397410561291396989759137)
    ·
      refine ⟨16798057920968547742319353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22397410561291396989759137 16798057920968547742319353)
      ·
        refine ⟨12598543440726410806739515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16798057920968547742319353 12598543440726410806739515)
        ·
          refine ⟨18897815161089616210109273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12598543440726410806739515 18897815161089616210109273)
          ·
            refine ⟨14173361370817212157581955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18897815161089616210109273 14173361370817212157581955)
            ·
              refine ⟨21260042056225818236372933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14173361370817212157581955 21260042056225818236372933)
              ·
                refine ⟨3986257885542340919319925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21260042056225818236372933 3986257885542340919319925)
                ·
                  refine ⟨373711676769594461186243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3986257885542340919319925 373711676769594461186243)
                  ·
                    rfl

theorem cell20_818776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 5].length) (baseStart_818776 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_818776 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_818776 prefixEnd_818776 := by exact prefixLift 818776
  have htrace : WordTrace (prefixWord ++ tailWord_818776) baseStart_818776 baseEnd_818776 := by
    simpa [prefixWord, tailWord_818776, baseEnd_818776] using wordTrace_append hprefix tailTrace_818776
  have hstable : (prefixWord ++ tailWord_818776).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818776).length < 2 ^ (prefixWord ++ tailWord_818776).sum := by decide
  have hdescent : baseEnd_818776 < baseStart_818776 := by decide
  rcases family_descends (prefixWord ++ tailWord_818776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818793 : List Nat := [1, 2, 1, 1, 1, 4, 5, 2, 3]
def baseStart_818793 : Nat := 118140960795 + 818793 * 2 ^ 59
def prefixEnd_818793 : Nat := 4983230072969 + 3 ^ 40 * 818793 * 2
def baseEnd_818793 : Nat := 373719436032817957619507

theorem tailTrace_818793 : CollatzResearch.WordTrace tailWord_818793 prefixEnd_818793 373719436032817957619507 := by
  unfold tailWord_818793
  simp only [CollatzResearch.WordTrace]
  refine ⟨29863834122660274556381033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19909222748440183037587355 29863834122660274556381033)
  ·
    refine ⟨22397875591995205917285775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29863834122660274556381033 22397875591995205917285775)
    ·
      refine ⟨33596813387992808875928663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22397875591995205917285775 33596813387992808875928663)
      ·
        refine ⟨50395220081989213313892995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33596813387992808875928663 50395220081989213313892995)
        ·
          refine ⟨75592830122983819970839493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50395220081989213313892995 75592830122983819970839493)
          ·
            refine ⟨14173655648059466244532405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75592830122983819970839493 14173655648059466244532405)
            ·
              refine ⟨1328780217005574960424913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14173655648059466244532405 1328780217005574960424913)
              ·
                refine ⟨996585162754181220318685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1328780217005574960424913 996585162754181220318685)
                ·
                  refine ⟨373719436032817957619507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 996585162754181220318685 373719436032817957619507)
                  ·
                    rfl

theorem cell20_818793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 2, 3].length) (baseStart_818793 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_818793 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_818793 prefixEnd_818793 := by exact prefixLift 818793
  have htrace : WordTrace (prefixWord ++ tailWord_818793) baseStart_818793 baseEnd_818793 := by
    simpa [prefixWord, tailWord_818793, baseEnd_818793] using wordTrace_append hprefix tailTrace_818793
  have hstable : (prefixWord ++ tailWord_818793).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818793).length < 2 ^ (prefixWord ++ tailWord_818793).sum := by decide
  have hdescent : baseEnd_818793 < baseStart_818793 := by decide
  rcases family_descends (prefixWord ++ tailWord_818793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818800 : List Nat := [2, 1, 1, 1, 6, 1, 1, 3, 4]
def baseStart_818800 : Nat := 118140960795 + 818800 * 2 ^ 59
def prefixEnd_818800 : Nat := 4983230072969 + 3 ^ 40 * 818800 * 2
def baseEnd_818800 : Nat := 373722631023557044386145

theorem tailTrace_818800 : CollatzResearch.WordTrace tailWord_818800 prefixEnd_818800 373722631023557044386145 := by
  unfold tailWord_818800
  simp only [CollatzResearch.WordTrace]
  refine ⟨14932044716817457375942927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19909392955756609834590569 14932044716817457375942927)
  ·
    refine ⟨22398067075226186063914391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14932044716817457375942927 22398067075226186063914391)
    ·
      refine ⟨33597100612839279095871587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22398067075226186063914391 33597100612839279095871587)
      ·
        refine ⟨50395650919258918643807381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33597100612839279095871587 50395650919258918643807381)
        ·
          refine ⟨2362296136840261811428471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 50395650919258918643807381 2362296136840261811428471)
          ·
            refine ⟨3543444205260392717142707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2362296136840261811428471 3543444205260392717142707)
            ·
              refine ⟨5315166307890589075714061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3543444205260392717142707 5315166307890589075714061)
              ·
                refine ⟨1993187365458970903392773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5315166307890589075714061 1993187365458970903392773)
                ·
                  refine ⟨373722631023557044386145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1993187365458970903392773 373722631023557044386145)
                  ·
                    rfl

theorem cell20_818800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 3, 4].length) (baseStart_818800 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_818800 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_818800 prefixEnd_818800 := by exact prefixLift 818800
  have htrace : WordTrace (prefixWord ++ tailWord_818800) baseStart_818800 baseEnd_818800 := by
    simpa [prefixWord, tailWord_818800, baseEnd_818800] using wordTrace_append hprefix tailTrace_818800
  have hstable : (prefixWord ++ tailWord_818800).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818800).length < 2 ^ (prefixWord ++ tailWord_818800).sum := by decide
  have hdescent : baseEnd_818800 < baseStart_818800 := by decide
  rcases family_descends (prefixWord ++ tailWord_818800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818820 : List Nat := [2, 3, 2, 1, 5, 1, 2, 4]
def baseStart_818820 : Nat := 118140960795 + 818820 * 2 ^ 59
def prefixEnd_818820 : Nat := 4983230072969 + 3 ^ 40 * 818820 * 2
def baseEnd_818820 : Nat := 124577253189508621239799

theorem tailTrace_818820 : CollatzResearch.WordTrace tailWord_818820 prefixEnd_818820 124577253189508621239799 := by
  unfold tailWord_818820
  simp only [CollatzResearch.WordTrace]
  refine ⟨14932409446781229083806957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19909879262374972111742609 14932409446781229083806957)
  ·
    refine ⟨5599653542542960906427609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14932409446781229083806957 5599653542542960906427609)
    ·
      refine ⟨4199740156907220679820707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5599653542542960906427609 4199740156907220679820707)
      ·
        refine ⟨6299610235360831019731061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4199740156907220679820707 6299610235360831019731061)
        ·
          refine ⟨590588459565077908099787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6299610235360831019731061 590588459565077908099787)
          ·
            refine ⟨885882689347616862149681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 590588459565077908099787 885882689347616862149681)
            ·
              refine ⟨664412017010712646612261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 885882689347616862149681 664412017010712646612261)
              ·
                refine ⟨124577253189508621239799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 664412017010712646612261 124577253189508621239799)
                ·
                  rfl

theorem cell20_818820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 2, 4].length) (baseStart_818820 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_818820 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_818820 prefixEnd_818820 := by exact prefixLift 818820
  have htrace : WordTrace (prefixWord ++ tailWord_818820) baseStart_818820 baseEnd_818820 := by
    simpa [prefixWord, tailWord_818820, baseEnd_818820] using wordTrace_append hprefix tailTrace_818820
  have hstable : (prefixWord ++ tailWord_818820).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818820).length < 2 ^ (prefixWord ++ tailWord_818820).sum := by decide
  have hdescent : baseEnd_818820 < baseStart_818820 := by decide
  rcases family_descends (prefixWord ++ tailWord_818820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818902 : List Nat := [5, 2, 1, 3, 2, 1, 2, 2, 2]
def baseStart_818902 : Nat := 118140960795 + 818902 * 2 ^ 59
def prefixEnd_818902 : Nat := 4983230072969 + 3 ^ 40 * 818902 * 2
def baseEnd_818902 : Nat := 373769186602898022985729

theorem tailTrace_818902 : CollatzResearch.WordTrace tailWord_818902 prefixEnd_818902 373769186602898022985729 := by
  unfold tailWord_818902
  simp only [CollatzResearch.WordTrace]
  refine ⟨1866738104954086635756185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19911873119510257448065973 1866738104954086635756185)
  ·
    refine ⟨1400053578715564976817139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1866738104954086635756185 1400053578715564976817139)
    ·
      refine ⟨2100080368073347465225709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1400053578715564976817139 2100080368073347465225709)
      ·
        refine ⟨787530138027505299459641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2100080368073347465225709 787530138027505299459641)
        ·
          refine ⟨590647603520628974594731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 787530138027505299459641 590647603520628974594731)
          ·
            refine ⟨885971405280943461892097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 590647603520628974594731 885971405280943461892097)
            ·
              refine ⟨664478553960707596419073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 885971405280943461892097 664478553960707596419073)
              ·
                refine ⟨498358915470530697314305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 664478553960707596419073 498358915470530697314305)
                ·
                  refine ⟨373769186602898022985729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 498358915470530697314305 373769186602898022985729)
                  ·
                    rfl

theorem cell20_818902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_818902 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_818902 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_818902 prefixEnd_818902 := by exact prefixLift 818902
  have htrace : WordTrace (prefixWord ++ tailWord_818902) baseStart_818902 baseEnd_818902 := by
    simpa [prefixWord, tailWord_818902, baseEnd_818902] using wordTrace_append hprefix tailTrace_818902
  have hstable : (prefixWord ++ tailWord_818902).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818902).length < 2 ^ (prefixWord ++ tailWord_818902).sum := by decide
  have hdescent : baseEnd_818902 < baseStart_818902 := by decide
  rcases family_descends (prefixWord ++ tailWord_818902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818935 : List Nat := [1, 1, 3, 1, 1, 1, 5, 1, 6]
def baseStart_818935 : Nat := 118140960795 + 818935 * 2 ^ 59
def prefixEnd_818935 : Nat := 4983230072969 + 3 ^ 40 * 818935 * 2
def baseEnd_818935 : Nat := 373784248702096574885593

theorem tailTrace_818935 : CollatzResearch.WordTrace tailWord_818935 prefixEnd_818935 373784248702096574885593 := by
  unfold tailWord_818935
  simp only [CollatzResearch.WordTrace]
  refine ⟨29869013288145832808050259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19912675525430555205366839 29869013288145832808050259)
  ·
    refine ⟨44803519932218749212075389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29869013288145832808050259 44803519932218749212075389)
    ·
      refine ⟨16801319974582030954528271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44803519932218749212075389 16801319974582030954528271)
      ·
        refine ⟨25201979961873046431792407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16801319974582030954528271 25201979961873046431792407)
        ·
          refine ⟨37802969942809569647688611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25201979961873046431792407 37802969942809569647688611)
          ·
            refine ⟨56704454914214354471532917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37802969942809569647688611 56704454914214354471532917)
            ·
              refine ⟨5316042648207595731706211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56704454914214354471532917 5316042648207595731706211)
              ·
                refine ⟨7974063972311393597559317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5316042648207595731706211 7974063972311393597559317)
                ·
                  refine ⟨373784248702096574885593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7974063972311393597559317 373784248702096574885593)
                  ·
                    rfl

theorem cell20_818935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 6].length) (baseStart_818935 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_818935 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_818935 prefixEnd_818935 := by exact prefixLift 818935
  have htrace : WordTrace (prefixWord ++ tailWord_818935) baseStart_818935 baseEnd_818935 := by
    simpa [prefixWord, tailWord_818935, baseEnd_818935] using wordTrace_append hprefix tailTrace_818935
  have hstable : (prefixWord ++ tailWord_818935).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818935).length < 2 ^ (prefixWord ++ tailWord_818935).sum := by decide
  have hdescent : baseEnd_818935 < baseStart_818935 := by decide
  rcases family_descends (prefixWord ++ tailWord_818935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818948 : List Nat := [2, 3, 2, 2, 1, 3, 2, 3, 2]
def baseStart_818948 : Nat := 118140960795 + 818948 * 2 ^ 59
def prefixEnd_818948 : Nat := 4983230072969 + 3 ^ 40 * 818948 * 2
def baseEnd_818948 : Nat := 373790182256326307452207

theorem tailTrace_818948 : CollatzResearch.WordTrace tailWord_818948 prefixEnd_818948 373790182256326307452207 := by
  unfold tailWord_818948
  simp only [CollatzResearch.WordTrace]
  refine ⟨14934743718549368014136749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19912991624732490685515665 14934743718549368014136749)
  ·
    refine ⟨5600528894456013005301281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14934743718549368014136749 5600528894456013005301281)
    ·
      refine ⟨4200396670842009753975961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5600528894456013005301281 4200396670842009753975961)
      ·
        refine ⟨3150297503131507315481971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4200396670842009753975961 3150297503131507315481971)
        ·
          refine ⟨4725446254697260973222957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3150297503131507315481971 4725446254697260973222957)
          ·
            refine ⟨1772042345511472864958609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4725446254697260973222957 1772042345511472864958609)
            ·
              refine ⟨1329031759133604648718957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1772042345511472864958609 1329031759133604648718957)
              ·
                refine ⟨498386909675101743269609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1329031759133604648718957 498386909675101743269609)
                ·
                  refine ⟨373790182256326307452207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 498386909675101743269609 373790182256326307452207)
                  ·
                    rfl

theorem cell20_818948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 3, 2].length) (baseStart_818948 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_818948 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_818948 prefixEnd_818948 := by exact prefixLift 818948
  have htrace : WordTrace (prefixWord ++ tailWord_818948) baseStart_818948 baseEnd_818948 := by
    simpa [prefixWord, tailWord_818948, baseEnd_818948] using wordTrace_append hprefix tailTrace_818948
  have hstable : (prefixWord ++ tailWord_818948).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818948).length < 2 ^ (prefixWord ++ tailWord_818948).sum := by decide
  have hdescent : baseEnd_818948 < baseStart_818948 := by decide
  rcases family_descends (prefixWord ++ tailWord_818948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_818962 : List Nat := [3, 2, 4, 1, 1, 2, 1, 1, 5]
def baseStart_818962 : Nat := 118140960795 + 818962 * 2 ^ 59
def prefixEnd_818962 : Nat := 4983230072969 + 3 ^ 40 * 818962 * 2
def baseEnd_818962 : Nat := 373796572237804480985483

theorem tailTrace_818962 : CollatzResearch.WordTrace tailWord_818962 prefixEnd_818962 373796572237804480985483 := by
  unfold tailWord_818962
  simp only [CollatzResearch.WordTrace]
  refine ⟨7467499514762004104820785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19913332039365344279522093 7467499514762004104820785)
  ·
    refine ⟨5600624636071503078615589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7467499514762004104820785 5600624636071503078615589)
    ·
      refine ⟨1050117119263406827240423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5600624636071503078615589 1050117119263406827240423)
      ·
        refine ⟨1575175678895110240860635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1050117119263406827240423 1575175678895110240860635)
        ·
          refine ⟨2362763518342665361290953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1575175678895110240860635 2362763518342665361290953)
          ·
            refine ⟨1772072638756999020968215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2362763518342665361290953 1772072638756999020968215)
            ·
              refine ⟨2658108958135498531452323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1772072638756999020968215 2658108958135498531452323)
              ·
                refine ⟨3987163437203247797178485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2658108958135498531452323 3987163437203247797178485)
                ·
                  refine ⟨373796572237804480985483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3987163437203247797178485 373796572237804480985483)
                  ·
                    rfl

theorem cell20_818962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 5].length) (baseStart_818962 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_818962 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_818962 prefixEnd_818962 := by exact prefixLift 818962
  have htrace : WordTrace (prefixWord ++ tailWord_818962) baseStart_818962 baseEnd_818962 := by
    simpa [prefixWord, tailWord_818962, baseEnd_818962] using wordTrace_append hprefix tailTrace_818962
  have hstable : (prefixWord ++ tailWord_818962).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_818962).length < 2 ^ (prefixWord ++ tailWord_818962).sum := by decide
  have hdescent : baseEnd_818962 < baseStart_818962 := by decide
  rcases family_descends (prefixWord ++ tailWord_818962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819004 : List Nat := [2, 2, 2, 2, 1, 1, 3, 2, 5]
def baseStart_819004 : Nat := 118140960795 + 819004 * 2 ^ 59
def prefixEnd_819004 : Nat := 4983230072969 + 3 ^ 40 * 819004 * 2
def baseEnd_819004 : Nat := 373815742182239001585311

theorem tailTrace_819004 : CollatzResearch.WordTrace tailWord_819004 prefixEnd_819004 373815742182239001585311 := by
  unfold tailWord_819004
  simp only [CollatzResearch.WordTrace]
  refine ⟨14935764962447928796156033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19914353283263905061541377 14935764962447928796156033)
  ·
    refine ⟨11201823721835946597117025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14935764962447928796156033 11201823721835946597117025)
    ·
      refine ⟨8401367791376959947837769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11201823721835946597117025 8401367791376959947837769)
      ·
        refine ⟨6301025843532719960878327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8401367791376959947837769 6301025843532719960878327)
        ·
          refine ⟨9451538765299079941317491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6301025843532719960878327 9451538765299079941317491)
          ·
            refine ⟨14177308147948619911976237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9451538765299079941317491 14177308147948619911976237)
            ·
              refine ⟨5316490555480732466991089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14177308147948619911976237 5316490555480732466991089)
              ·
                refine ⟨3987367916610549350243317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5316490555480732466991089 3987367916610549350243317)
                ·
                  refine ⟨373815742182239001585311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3987367916610549350243317 373815742182239001585311)
                  ·
                    rfl

theorem cell20_819004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 5].length) (baseStart_819004 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_819004 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_819004 prefixEnd_819004 := by exact prefixLift 819004
  have htrace : WordTrace (prefixWord ++ tailWord_819004) baseStart_819004 baseEnd_819004 := by
    simpa [prefixWord, tailWord_819004, baseEnd_819004] using wordTrace_append hprefix tailTrace_819004
  have hstable : (prefixWord ++ tailWord_819004).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819004).length < 2 ^ (prefixWord ++ tailWord_819004).sum := by decide
  have hdescent : baseEnd_819004 < baseStart_819004 := by decide
  rcases family_descends (prefixWord ++ tailWord_819004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819049 : List Nat := [1, 2, 1, 1, 1, 3, 1, 6, 4]
def baseStart_819049 : Nat := 118140960795 + 819049 * 2 ^ 59
def prefixEnd_819049 : Nat := 4983230072969 + 3 ^ 40 * 819049 * 2
def baseEnd_819049 : Nat := 373836281408418845085127

theorem tailTrace_819049 : CollatzResearch.WordTrace tailWord_819049 prefixEnd_819049 373836281408418845085127 := by
  unfold tailWord_819049
  simp only [CollatzResearch.WordTrace]
  refine ⟨29873171209732830277700201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19915447473155220185133467 29873171209732830277700201)
  ·
    refine ⟨22404878407299622708275151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29873171209732830277700201 22404878407299622708275151)
    ·
      refine ⟨33607317610949434062412727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22404878407299622708275151 33607317610949434062412727)
      ·
        refine ⟨50410976416424151093619091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33607317610949434062412727 50410976416424151093619091)
        ·
          refine ⟨75616464624636226640428637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50410976416424151093619091 75616464624636226640428637)
          ·
            refine ⟨28356174234238584990160739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75616464624636226640428637 28356174234238584990160739)
            ·
              refine ⟨42534261351357877485241109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28356174234238584990160739 42534261351357877485241109)
              ·
                refine ⟨1993793500844900507120677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 42534261351357877485241109 1993793500844900507120677)
                ·
                  refine ⟨373836281408418845085127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1993793500844900507120677 373836281408418845085127)
                  ·
                    rfl

theorem cell20_819049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 6, 4].length) (baseStart_819049 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_819049 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_819049 prefixEnd_819049 := by exact prefixLift 819049
  have htrace : WordTrace (prefixWord ++ tailWord_819049) baseStart_819049 baseEnd_819049 := by
    simpa [prefixWord, tailWord_819049, baseEnd_819049] using wordTrace_append hprefix tailTrace_819049
  have hstable : (prefixWord ++ tailWord_819049).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819049).length < 2 ^ (prefixWord ++ tailWord_819049).sum := by decide
  have hdescent : baseEnd_819049 < baseStart_819049 := by decide
  rcases family_descends (prefixWord ++ tailWord_819049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819073 : List Nat := [1, 2, 4, 4, 9]
def baseStart_819073 : Nat := 118140960795 + 819073 * 2 ^ 59
def prefixEnd_819073 : Nat := 4983230072969 + 3 ^ 40 * 819073 * 2
def baseEnd_819073 : Nat := 4615397971140511460309

theorem tailTrace_819073 : CollatzResearch.WordTrace tailWord_819073 prefixEnd_819073 4615397971140511460309 := by
  unfold tailWord_819073
  simp only [CollatzResearch.WordTrace]
  refine ⟨29874046561645882376573873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19916031041097254917715915 29874046561645882376573873)
  ·
    refine ⟨22405534921234411782430405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29874046561645882376573873 22405534921234411782430405)
    ·
      refine ⟨4201037797731452209205701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22405534921234411782430405 4201037797731452209205701)
      ·
        refine ⟨787694587074647289226069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4201037797731452209205701 787694587074647289226069)
        ·
          refine ⟨4615397971140511460309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 787694587074647289226069 4615397971140511460309)
          ·
            rfl

theorem cell20_819073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 9].length) (baseStart_819073 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_819073 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_819073 prefixEnd_819073 := by exact prefixLift 819073
  have htrace : WordTrace (prefixWord ++ tailWord_819073) baseStart_819073 baseEnd_819073 := by
    simpa [prefixWord, tailWord_819073, baseEnd_819073] using wordTrace_append hprefix tailTrace_819073
  have hstable : (prefixWord ++ tailWord_819073).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819073).length < 2 ^ (prefixWord ++ tailWord_819073).sum := by decide
  have hdescent : baseEnd_819073 < baseStart_819073 := by decide
  rcases family_descends (prefixWord ++ tailWord_819073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819079 : List Nat := [1, 1, 4, 2, 4, 2, 2, 2, 2]
def baseStart_819079 : Nat := 118140960795 + 819079 * 2 ^ 59
def prefixEnd_819079 : Nat := 4983230072969 + 3 ^ 40 * 819079 * 2
def baseEnd_819079 : Nat := 373849974225872074085005

theorem tailTrace_819079 : CollatzResearch.WordTrace tailWord_819079 prefixEnd_819079 373849974225872074085005 := by
  unfold tailWord_819079
  simp only [CollatzResearch.WordTrace]
  refine ⟨29874265399624145401292291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19916176933082763600861527 29874265399624145401292291)
  ·
    refine ⟨44811398099436218101938437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29874265399624145401292291 44811398099436218101938437)
    ·
      refine ⟨8402137143644290894113457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44811398099436218101938437 8402137143644290894113457)
      ·
        refine ⟨6301602857733218170585093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8402137143644290894113457 6301602857733218170585093)
        ·
          refine ⟨1181550535824978406984705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6301602857733218170585093 1181550535824978406984705)
          ·
            refine ⟨886162901868733805238529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1181550535824978406984705 886162901868733805238529)
            ·
              refine ⟨664622176401550353928897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 886162901868733805238529 664622176401550353928897)
              ·
                refine ⟨498466632301162765446673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 664622176401550353928897 498466632301162765446673)
                ·
                  refine ⟨373849974225872074085005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 498466632301162765446673 373849974225872074085005)
                  ·
                    rfl

theorem cell20_819079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 2, 2, 2].length) (baseStart_819079 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_819079 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_819079 prefixEnd_819079 := by exact prefixLift 819079
  have htrace : WordTrace (prefixWord ++ tailWord_819079) baseStart_819079 baseEnd_819079 := by
    simpa [prefixWord, tailWord_819079, baseEnd_819079] using wordTrace_append hprefix tailTrace_819079
  have hstable : (prefixWord ++ tailWord_819079).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819079).length < 2 ^ (prefixWord ++ tailWord_819079).sum := by decide
  have hdescent : baseEnd_819079 < baseStart_819079 := by decide
  rcases family_descends (prefixWord ++ tailWord_819079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819086 : List Nat := [4, 1, 1, 5, 2, 1, 1, 5]
def baseStart_819086 : Nat := 118140960795 + 819086 * 2 ^ 59
def prefixEnd_819086 : Nat := 4983230072969 + 3 ^ 40 * 819086 * 2
def baseEnd_819086 : Nat := 124617723072203720283881

theorem tailTrace_819086 : CollatzResearch.WordTrace tailWord_819086 prefixEnd_819086 124617723072203720283881 := by
  unfold tailWord_819086
  simp only [CollatzResearch.WordTrace]
  refine ⟨3734315088824848199599639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19916347140399190397864741 3734315088824848199599639)
  ·
    refine ⟨5601472633237272299399459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3734315088824848199599639 5601472633237272299399459)
    ·
      refine ⟨8402208949855908449099189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5601472633237272299399459 8402208949855908449099189)
      ·
        refine ⟨787707089048991417103049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8402208949855908449099189 787707089048991417103049)
        ·
          refine ⟨590780316786743562827287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 787707089048991417103049 590780316786743562827287)
          ·
            refine ⟨886170475180115344240931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 590780316786743562827287 886170475180115344240931)
            ·
              refine ⟨1329255712770173016361397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 886170475180115344240931 1329255712770173016361397)
              ·
                refine ⟨124617723072203720283881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1329255712770173016361397 124617723072203720283881)
                ·
                  rfl

theorem cell20_819086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 5].length) (baseStart_819086 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_819086 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_819086 prefixEnd_819086 := by exact prefixLift 819086
  have htrace : WordTrace (prefixWord ++ tailWord_819086) baseStart_819086 baseEnd_819086 := by
    simpa [prefixWord, tailWord_819086, baseEnd_819086] using wordTrace_append hprefix tailTrace_819086
  have hstable : (prefixWord ++ tailWord_819086).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819086).length < 2 ^ (prefixWord ++ tailWord_819086).sum := by decide
  have hdescent : baseEnd_819086 < baseStart_819086 := by decide
  rcases family_descends (prefixWord ++ tailWord_819086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819090 : List Nat := [3, 2, 3, 2, 1, 1, 3, 5]
def baseStart_819090 : Nat := 118140960795 + 819090 * 2 ^ 59
def prefixEnd_819090 : Nat := 4983230072969 + 3 ^ 40 * 819090 * 2
def baseEnd_819090 : Nat := 124618331641868308239431

theorem tailTrace_819090 : CollatzResearch.WordTrace tailWord_819090 prefixEnd_819090 124618331641868308239431 := by
  unfold tailWord_819090
  simp only [CollatzResearch.WordTrace]
  refine ⟨7468666650646073569985681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19916444401722862853295149 7468666650646073569985681)
  ·
    refine ⟨5601499987984555177489261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7468666650646073569985681 5601499987984555177489261)
    ·
      refine ⟨2100562495494208191558473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5601499987984555177489261 2100562495494208191558473)
      ·
        refine ⟨1575421871620656143668855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2100562495494208191558473 1575421871620656143668855)
        ·
          refine ⟨2363132807430984215503283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1575421871620656143668855 2363132807430984215503283)
          ·
            refine ⟨3544699211146476323254925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2363132807430984215503283 3544699211146476323254925)
            ·
              refine ⟨1329262204179928621220597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3544699211146476323254925 1329262204179928621220597)
              ·
                refine ⟨124618331641868308239431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1329262204179928621220597 124618331641868308239431)
                ·
                  rfl

theorem cell20_819090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 5].length) (baseStart_819090 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_819090 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_819090 prefixEnd_819090 := by exact prefixLift 819090
  have htrace : WordTrace (prefixWord ++ tailWord_819090) baseStart_819090 baseEnd_819090 := by
    simpa [prefixWord, tailWord_819090, baseEnd_819090] using wordTrace_append hprefix tailTrace_819090
  have hstable : (prefixWord ++ tailWord_819090).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819090).length < 2 ^ (prefixWord ++ tailWord_819090).sum := by decide
  have hdescent : baseEnd_819090 < baseStart_819090 := by decide
  rcases family_descends (prefixWord ++ tailWord_819090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819121 : List Nat := [1, 2, 2, 4, 2, 1, 1, 5, 2]
def baseStart_819121 : Nat := 118140960795 + 819121 * 2 ^ 59
def prefixEnd_819121 : Nat := 4983230072969 + 3 ^ 40 * 819121 * 2
def baseEnd_819121 : Nat := 373869144170306594684833

theorem tailTrace_819121 : CollatzResearch.WordTrace tailWord_819121 prefixEnd_819121 373869144170306594684833 := by
  unfold tailWord_819121
  simp only [CollatzResearch.WordTrace]
  refine ⟨29875797265471986574321217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19917198176981324382880811 29875797265471986574321217)
  ·
    refine ⟨22406847949103989930740913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29875797265471986574321217 22406847949103989930740913)
    ·
      refine ⟨16805135961827992448055685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22406847949103989930740913 16805135961827992448055685)
      ·
        refine ⟨3150962992842748584010441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16805135961827992448055685 3150962992842748584010441)
        ·
          refine ⟨2363222244632061438007831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3150962992842748584010441 2363222244632061438007831)
          ·
            refine ⟨3544833366948092157011747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2363222244632061438007831 3544833366948092157011747)
            ·
              refine ⟨5317250050422138235517621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3544833366948092157011747 5317250050422138235517621)
              ·
                refine ⟨498492192227075459579777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5317250050422138235517621 498492192227075459579777)
                ·
                  refine ⟨373869144170306594684833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 498492192227075459579777 373869144170306594684833)
                  ·
                    rfl

theorem cell20_819121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 5, 2].length) (baseStart_819121 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_819121 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_819121 prefixEnd_819121 := by exact prefixLift 819121
  have htrace : WordTrace (prefixWord ++ tailWord_819121) baseStart_819121 baseEnd_819121 := by
    simpa [prefixWord, tailWord_819121, baseEnd_819121] using wordTrace_append hprefix tailTrace_819121
  have hstable : (prefixWord ++ tailWord_819121).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819121).length < 2 ^ (prefixWord ++ tailWord_819121).sum := by decide
  have hdescent : baseEnd_819121 < baseStart_819121 := by decide
  rcases family_descends (prefixWord ++ tailWord_819121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819249 : List Nat := [1, 2, 2, 3, 1, 4, 2, 2, 3]
def baseStart_819249 : Nat := 118140960795 + 819249 * 2 ^ 59
def prefixEnd_819249 : Nat := 4983230072969 + 3 ^ 40 * 819249 * 2
def baseEnd_819249 : Nat := 373927566858107038417643

theorem tailTrace_819249 : CollatzResearch.WordTrace tailWord_819249 prefixEnd_819249 373927566858107038417643 := by
  unfold tailWord_819249
  simp only [CollatzResearch.WordTrace]
  refine ⟨29880465809008264434980801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19920310539338842956653867 29880465809008264434980801)
  ·
    refine ⟨22410349356756198326235601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29880465809008264434980801 22410349356756198326235601)
    ·
      refine ⟨16807762017567148744676701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22410349356756198326235601 16807762017567148744676701)
      ·
        refine ⟨6302910756587680779253763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16807762017567148744676701 6302910756587680779253763)
        ·
          refine ⟨9454366134881521168880645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6302910756587680779253763 9454366134881521168880645)
          ·
            refine ⟨1772693650290285219165121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9454366134881521168880645 1772693650290285219165121)
            ·
              refine ⟨1329520237717713914373841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1772693650290285219165121 1329520237717713914373841)
              ·
                refine ⟨997140178288285435780381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1329520237717713914373841 997140178288285435780381)
                ·
                  refine ⟨373927566858107038417643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 997140178288285435780381 373927566858107038417643)
                  ·
                    rfl

theorem cell20_819249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 2, 3].length) (baseStart_819249 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_819249 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_819249 prefixEnd_819249 := by exact prefixLift 819249
  have htrace : WordTrace (prefixWord ++ tailWord_819249) baseStart_819249 baseEnd_819249 := by
    simpa [prefixWord, tailWord_819249, baseEnd_819249] using wordTrace_append hprefix tailTrace_819249
  have hstable : (prefixWord ++ tailWord_819249).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819249).length < 2 ^ (prefixWord ++ tailWord_819249).sum := by decide
  have hdescent : baseEnd_819249 < baseStart_819249 := by decide
  rcases family_descends (prefixWord ++ tailWord_819249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819308 : List Nat := [2, 2, 1, 1, 3, 4, 1, 1, 5]
def baseStart_819308 : Nat := 118140960795 + 819308 * 2 ^ 59
def prefixEnd_819308 : Nat := 4983230072969 + 3 ^ 40 * 819308 * 2
def baseEnd_819308 : Nat := 373954496065765055450735

theorem tailTrace_819308 : CollatzResearch.WordTrace tailWord_819308 prefixEnd_819308 373954496065765055450735 := by
  unfold tailWord_819308
  simp only [CollatzResearch.WordTrace]
  refine ⟨14941308857897258755689289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19921745143863011674252385 14941308857897258755689289)
  ·
    refine ⟨11205981643422944066766967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14941308857897258755689289 11205981643422944066766967)
    ·
      refine ⟨16808972465134416100150451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11205981643422944066766967 16808972465134416100150451)
      ·
        refine ⟨25213458697701624150225677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16808972465134416100150451 25213458697701624150225677)
        ·
          refine ⟨9455047011638109056334629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25213458697701624150225677 9455047011638109056334629)
          ·
            refine ⟨1772821314682145448062743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9455047011638109056334629 1772821314682145448062743)
            ·
              refine ⟨2659231972023218172094115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1772821314682145448062743 2659231972023218172094115)
              ·
                refine ⟨3988847958034827258141173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2659231972023218172094115 3988847958034827258141173)
                ·
                  refine ⟨373954496065765055450735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3988847958034827258141173 373954496065765055450735)
                  ·
                    rfl

theorem cell20_819308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 5].length) (baseStart_819308 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_819308 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_819308 prefixEnd_819308 := by exact prefixLift 819308
  have htrace : WordTrace (prefixWord ++ tailWord_819308) baseStart_819308 baseEnd_819308 := by
    simpa [prefixWord, tailWord_819308, baseEnd_819308] using wordTrace_append hprefix tailTrace_819308
  have hstable : (prefixWord ++ tailWord_819308).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819308).length < 2 ^ (prefixWord ++ tailWord_819308).sum := by decide
  have hdescent : baseEnd_819308 < baseStart_819308 := by decide
  rcases family_descends (prefixWord ++ tailWord_819308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819346 : List Nat := [3, 2, 3, 1, 1, 1, 1, 1, 7]
def baseStart_819346 : Nat := 118140960795 + 819346 * 2 ^ 59
def prefixEnd_819346 : Nat := 4983230072969 + 3 ^ 40 * 819346 * 2
def baseEnd_819346 : Nat := 373971840301205812183913

theorem tailTrace_819346 : CollatzResearch.WordTrace tailWord_819346 prefixEnd_819346 373971840301205812183913 := by
  unfold tailWord_819346
  simp only [CollatzResearch.WordTrace]
  refine ⟨7471000922414212500315473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19922669126437900000841261 7471000922414212500315473)
  ·
    refine ⟨5603250691810659375236605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7471000922414212500315473 5603250691810659375236605)
    ·
      refine ⟨2101219009428997265713727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5603250691810659375236605 2101219009428997265713727)
      ·
        refine ⟨3151828514143495898570591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2101219009428997265713727 3151828514143495898570591)
        ·
          refine ⟨4727742771215243847855887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3151828514143495898570591 4727742771215243847855887)
          ·
            refine ⟨7091614156822865771783831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4727742771215243847855887 7091614156822865771783831)
            ·
              refine ⟨10637421235234298657675747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7091614156822865771783831 10637421235234298657675747)
              ·
                refine ⟨15956131852851447986513621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10637421235234298657675747 15956131852851447986513621)
                ·
                  refine ⟨373971840301205812183913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15956131852851447986513621 373971840301205812183913)
                  ·
                    rfl

theorem cell20_819346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_819346 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_819346 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_819346 prefixEnd_819346 := by exact prefixLift 819346
  have htrace : WordTrace (prefixWord ++ tailWord_819346) baseStart_819346 baseEnd_819346 := by
    simpa [prefixWord, tailWord_819346, baseEnd_819346] using wordTrace_append hprefix tailTrace_819346
  have hstable : (prefixWord ++ tailWord_819346).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819346).length < 2 ^ (prefixWord ++ tailWord_819346).sum := by decide
  have hdescent : baseEnd_819346 < baseStart_819346 := by decide
  rcases family_descends (prefixWord ++ tailWord_819346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819360 : List Nat := [2, 1, 1, 4, 2, 2, 8]
def baseStart_819360 : Nat := 118140960795 + 819360 * 2 ^ 59
def prefixEnd_819360 : Nat := 4983230072969 + 3 ^ 40 * 819360 * 2
def baseEnd_819360 : Nat := 41553136698075998413021

theorem tailTrace_819360 : CollatzResearch.WordTrace tailWord_819360 prefixEnd_819360 41553136698075998413021 := by
  unfold tailWord_819360
  simp only [CollatzResearch.WordTrace]
  refine ⟨14942257155803065196135767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19923009541070753594847689 14942257155803065196135767)
  ·
    refine ⟨22413385733704597794203651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14942257155803065196135767 22413385733704597794203651)
    ·
      refine ⟨33620078600556896691305477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22413385733704597794203651 33620078600556896691305477)
      ·
        refine ⟨6303764737604418129619777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33620078600556896691305477 6303764737604418129619777)
        ·
          refine ⟨4727823553203313597214833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6303764737604418129619777 4727823553203313597214833)
          ·
            refine ⟨3545867664902485197911125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4727823553203313597214833 3545867664902485197911125)
            ·
              refine ⟨41553136698075998413021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3545867664902485197911125 41553136698075998413021)
              ·
                rfl

theorem cell20_819360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 8].length) (baseStart_819360 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_819360 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_819360 prefixEnd_819360 := by exact prefixLift 819360
  have htrace : WordTrace (prefixWord ++ tailWord_819360) baseStart_819360 baseEnd_819360 := by
    simpa [prefixWord, tailWord_819360, baseEnd_819360] using wordTrace_append hprefix tailTrace_819360
  have hstable : (prefixWord ++ tailWord_819360).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819360).length < 2 ^ (prefixWord ++ tailWord_819360).sum := by decide
  have hdescent : baseEnd_819360 < baseStart_819360 := by decide
  rcases family_descends (prefixWord ++ tailWord_819360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819384 : List Nat := [2, 1, 2, 1, 2, 1, 5, 3, 3]
def baseStart_819384 : Nat := 118140960795 + 819384 * 2 ^ 59
def prefixEnd_819384 : Nat := 4983230072969 + 3 ^ 40 * 819384 * 2
def baseEnd_819384 : Nat := 373989184536646568917091

theorem tailTrace_819384 : CollatzResearch.WordTrace tailWord_819384 prefixEnd_819384 373989184536646568917091 := by
  unfold tailWord_819384
  simp only [CollatzResearch.WordTrace]
  refine ⟨14942694831759591245572603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19923593109012788327430137 14942694831759591245572603)
  ·
    refine ⟨22414042247639386868358905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14942694831759591245572603 22414042247639386868358905)
    ·
      refine ⟨16810531685729540151269179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22414042247639386868358905 16810531685729540151269179)
      ·
        refine ⟨25215797528594310226903769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16810531685729540151269179 25215797528594310226903769)
        ·
          refine ⟨18911848146445732670177827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25215797528594310226903769 18911848146445732670177827)
          ·
            refine ⟨28367772219668599005266741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18911848146445732670177827 28367772219668599005266741)
            ·
              refine ⟨2659478645593931156743757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28367772219668599005266741 2659478645593931156743757)
              ·
                refine ⟨997304492097724183778909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2659478645593931156743757 997304492097724183778909)
                ·
                  refine ⟨373989184536646568917091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 997304492097724183778909 373989184536646568917091)
                  ·
                    rfl

theorem cell20_819384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 3, 3].length) (baseStart_819384 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_819384 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_819384 prefixEnd_819384 := by exact prefixLift 819384
  have htrace : WordTrace (prefixWord ++ tailWord_819384) baseStart_819384 baseEnd_819384 := by
    simpa [prefixWord, tailWord_819384, baseEnd_819384] using wordTrace_append hprefix tailTrace_819384
  have hstable : (prefixWord ++ tailWord_819384).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819384).length < 2 ^ (prefixWord ++ tailWord_819384).sum := by decide
  have hdescent : baseEnd_819384 < baseStart_819384 := by decide
  rcases family_descends (prefixWord ++ tailWord_819384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819421 : List Nat := [1, 4, 3, 2, 1, 3, 2, 2, 2]
def baseStart_819421 : Nat := 118140960795 + 819421 * 2 ^ 59
def prefixEnd_819421 : Nat := 4983230072969 + 3 ^ 40 * 819421 * 2
def baseEnd_819421 : Nat := 374006072344838884683607

theorem tailTrace_819421 : CollatzResearch.WordTrace tailWord_819421 prefixEnd_819421 374006072344838884683607 := by
  unfold tailWord_819421
  simp only [CollatzResearch.WordTrace]
  refine ⟨29886739164385137810242117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19924492776256758540161411 29886739164385137810242117)
  ·
    refine ⟨5603763593322213339420397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29886739164385137810242117 5603763593322213339420397)
    ·
      refine ⟨2101411347495830002282649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5603763593322213339420397 2101411347495830002282649)
      ·
        refine ⟨1576058510621872501711987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2101411347495830002282649 1576058510621872501711987)
        ·
          refine ⟨2364087765932808752567981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1576058510621872501711987 2364087765932808752567981)
          ·
            refine ⟨886532912224803282212993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2364087765932808752567981 886532912224803282212993)
            ·
              refine ⟨664899684168602461659745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 886532912224803282212993 664899684168602461659745)
              ·
                refine ⟨498674763126451846244809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 664899684168602461659745 498674763126451846244809)
                ·
                  refine ⟨374006072344838884683607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 498674763126451846244809 374006072344838884683607)
                  ·
                    rfl

theorem cell20_819421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 2, 2, 2].length) (baseStart_819421 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_819421 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_819421 prefixEnd_819421 := by exact prefixLift 819421
  have htrace : WordTrace (prefixWord ++ tailWord_819421) baseStart_819421 baseEnd_819421 := by
    simpa [prefixWord, tailWord_819421, baseEnd_819421] using wordTrace_append hprefix tailTrace_819421
  have hstable : (prefixWord ++ tailWord_819421).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819421).length < 2 ^ (prefixWord ++ tailWord_819421).sum := by decide
  have hdescent : baseEnd_819421 < baseStart_819421 := by decide
  rcases family_descends (prefixWord ++ tailWord_819421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819508 : List Nat := [2, 5, 1, 1, 1, 2, 4, 4]
def baseStart_819508 : Nat := 118140960795 + 819508 * 2 ^ 59
def prefixEnd_819508 : Nat := 4983230072969 + 3 ^ 40 * 819508 * 2
def baseEnd_819508 : Nat := 124681927171817749594417

theorem tailTrace_819508 : CollatzResearch.WordTrace tailWord_819508 prefixEnd_819508 124681927171817749594417 := by
  unfold tailWord_819508
  simp only [CollatzResearch.WordTrace]
  refine ⟨14944956157534975834329589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19926608210046634445772785 14944956157534975834329589)
  ·
    refine ⟨1401089639768903984468399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14944956157534975834329589 1401089639768903984468399)
    ·
      refine ⟨2101634459653355976702599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1401089639768903984468399 2101634459653355976702599)
      ·
        refine ⟨3152451689480033965053899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2101634459653355976702599 3152451689480033965053899)
        ·
          refine ⟨4728677534220050947580849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3152451689480033965053899 4728677534220050947580849)
          ·
            refine ⟨3546508150665038210685637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4728677534220050947580849 3546508150665038210685637)
            ·
              refine ⟨664970278249694664503557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3546508150665038210685637 664970278249694664503557)
              ·
                refine ⟨124681927171817749594417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 664970278249694664503557 124681927171817749594417)
                ·
                  rfl

theorem cell20_819508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 4, 4].length) (baseStart_819508 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_819508 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_819508 prefixEnd_819508 := by exact prefixLift 819508
  have htrace : WordTrace (prefixWord ++ tailWord_819508) baseStart_819508 baseEnd_819508 := by
    simpa [prefixWord, tailWord_819508, baseEnd_819508] using wordTrace_append hprefix tailTrace_819508
  have hstable : (prefixWord ++ tailWord_819508).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819508).length < 2 ^ (prefixWord ++ tailWord_819508).sum := by decide
  have hdescent : baseEnd_819508 < baseStart_819508 := by decide
  rcases family_descends (prefixWord ++ tailWord_819508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819518 : List Nat := [4, 2, 1, 2, 1, 4, 1, 3, 2]
def baseStart_819518 : Nat := 118140960795 + 819518 * 2 ^ 59
def prefixEnd_819518 : Nat := 4983230072969 + 3 ^ 40 * 819518 * 2
def baseEnd_819518 : Nat := 374050345787937658449877

theorem tailTrace_819518 : CollatzResearch.WordTrace tailWord_819518 prefixEnd_819518 374050345787937658449877 := by
  unfold tailWord_819518
  simp only [CollatzResearch.WordTrace]
  refine ⟨3736284630629215422065401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19926851363355815584348805 3736284630629215422065401)
  ·
    refine ⟨2802213472971911566549051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3736284630629215422065401 2802213472971911566549051)
    ·
      refine ⟨4203320209457867349823577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2802213472971911566549051 4203320209457867349823577)
      ·
        refine ⟨3152490157093400512367683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4203320209457867349823577 3152490157093400512367683)
        ·
          refine ⟨4728735235640100768551525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3152490157093400512367683 4728735235640100768551525)
          ·
            refine ⟨886637856682518894103411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4728735235640100768551525 886637856682518894103411)
            ·
              refine ⟨1329956785023778341155117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 886637856682518894103411 1329956785023778341155117)
              ·
                refine ⟨498733794383916877933169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1329956785023778341155117 498733794383916877933169)
                ·
                  refine ⟨374050345787937658449877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 498733794383916877933169 374050345787937658449877)
                  ·
                    rfl

theorem cell20_819518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 3, 2].length) (baseStart_819518 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_819518 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_819518 prefixEnd_819518 := by exact prefixLift 819518
  have htrace : WordTrace (prefixWord ++ tailWord_819518) baseStart_819518 baseEnd_819518 := by
    simpa [prefixWord, tailWord_819518, baseEnd_819518] using wordTrace_append hprefix tailTrace_819518
  have hstable : (prefixWord ++ tailWord_819518).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819518).length < 2 ^ (prefixWord ++ tailWord_819518).sum := by decide
  have hdescent : baseEnd_819518 < baseStart_819518 := by decide
  rcases family_descends (prefixWord ++ tailWord_819518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819519 : List Nat := [1, 1, 2, 2, 4, 1, 1, 1, 7]
def baseStart_819519 : Nat := 118140960795 + 819519 * 2 ^ 59
def prefixEnd_819519 : Nat := 4983230072969 + 3 ^ 40 * 819519 * 2
def baseEnd_819519 : Nat := 374050802215186099416539

theorem tailTrace_819519 : CollatzResearch.WordTrace tailWord_819519 prefixEnd_819519 374050802215186099416539 := by
  unfold tailWord_819519
  simp only [CollatzResearch.WordTrace]
  refine ⟨29890313518030100547309611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19926875678686733698206407 29890313518030100547309611)
  ·
    refine ⟨44835470277045150820964417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29890313518030100547309611 44835470277045150820964417)
    ·
      refine ⟨33626602707783863115723313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44835470277045150820964417 33626602707783863115723313)
      ·
        refine ⟨25219952030837897336792485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33626602707783863115723313 25219952030837897336792485)
        ·
          refine ⟨4728741005782105750648591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25219952030837897336792485 4728741005782105750648591)
          ·
            refine ⟨7093111508673158625972887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4728741005782105750648591 7093111508673158625972887)
            ·
              refine ⟨10639667263009737938959331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7093111508673158625972887 10639667263009737938959331)
              ·
                refine ⟨15959500894514606908438997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10639667263009737938959331 15959500894514606908438997)
                ·
                  refine ⟨374050802215186099416539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15959500894514606908438997 374050802215186099416539)
                  ·
                    rfl

theorem cell20_819519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 7].length) (baseStart_819519 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_819519 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_819519 prefixEnd_819519 := by exact prefixLift 819519
  have htrace : WordTrace (prefixWord ++ tailWord_819519) baseStart_819519 baseEnd_819519 := by
    simpa [prefixWord, tailWord_819519, baseEnd_819519] using wordTrace_append hprefix tailTrace_819519
  have hstable : (prefixWord ++ tailWord_819519).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819519).length < 2 ^ (prefixWord ++ tailWord_819519).sum := by decide
  have hdescent : baseEnd_819519 < baseStart_819519 := by decide
  rcases family_descends (prefixWord ++ tailWord_819519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819594 : List Nat := [3, 1, 2, 5, 1, 1, 1, 4, 2]
def baseStart_819594 : Nat := 118140960795 + 819594 * 2 ^ 59
def prefixEnd_819594 : Nat := 4983230072969 + 3 ^ 40 * 819594 * 2
def baseEnd_819594 : Nat := 374085034258819171916233

theorem tailTrace_819594 : CollatzResearch.WordTrace tailWord_819594 prefixEnd_819594 374085034258819171916233 := by
  unfold tailWord_819594
  simp only [CollatzResearch.WordTrace]
  refine ⟨7473262248189597089072459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19928699328505592237526557 7473262248189597089072459)
  ·
    refine ⟨11209893372284395633608689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7473262248189597089072459 11209893372284395633608689)
    ·
      refine ⟨8407420029213296725206517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11209893372284395633608689 8407420029213296725206517)
      ·
        refine ⟨788195627738746567988111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8407420029213296725206517 788195627738746567988111)
        ·
          refine ⟨1182293441608119851982167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 788195627738746567988111 1182293441608119851982167)
          ·
            refine ⟨1773440162412179777973251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1182293441608119851982167 1773440162412179777973251)
            ·
              refine ⟨2660160243618269666959877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1773440162412179777973251 2660160243618269666959877)
              ·
                refine ⟨498780045678425562554977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2660160243618269666959877 498780045678425562554977)
                ·
                  refine ⟨374085034258819171916233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 498780045678425562554977 374085034258819171916233)
                  ·
                    rfl

theorem cell20_819594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 4, 2].length) (baseStart_819594 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_819594 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_819594 prefixEnd_819594 := by exact prefixLift 819594
  have htrace : WordTrace (prefixWord ++ tailWord_819594) baseStart_819594 baseEnd_819594 := by
    simpa [prefixWord, tailWord_819594, baseEnd_819594] using wordTrace_append hprefix tailTrace_819594
  have hstable : (prefixWord ++ tailWord_819594).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819594).length < 2 ^ (prefixWord ++ tailWord_819594).sum := by decide
  have hdescent : baseEnd_819594 < baseStart_819594 := by decide
  rcases family_descends (prefixWord ++ tailWord_819594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819619 : List Nat := [1, 1, 1, 4, 1, 5, 1, 2, 4]
def baseStart_819619 : Nat := 118140960795 + 819619 * 2 ^ 59
def prefixEnd_819619 : Nat := 4983230072969 + 3 ^ 40 * 819619 * 2
def baseEnd_819619 : Nat := 374096444940030196082797

theorem tailTrace_819619 : CollatzResearch.WordTrace tailWord_819619 prefixEnd_819619 374096444940030196082797 := by
  unfold tailWord_819619
  simp only [CollatzResearch.WordTrace]
  refine ⟨29893960817667817625949911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19929307211778545083966607 29893960817667817625949911)
  ·
    refine ⟨44840941226501726438924867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29893960817667817625949911 44840941226501726438924867)
    ·
      refine ⟨67261411839752589658387301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44840941226501726438924867 67261411839752589658387301)
      ·
        refine ⟨12611514719953610560947619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67261411839752589658387301 12611514719953610560947619)
        ·
          refine ⟨18917272079930415841421429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12611514719953610560947619 18917272079930415841421429)
          ·
            refine ⟨1773494257493476485133259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18917272079930415841421429 1773494257493476485133259)
            ·
              refine ⟨2660241386240214727699889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1773494257493476485133259 2660241386240214727699889)
              ·
                refine ⟨1995181039680161045774917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2660241386240214727699889 1995181039680161045774917)
                ·
                  refine ⟨374096444940030196082797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1995181039680161045774917 374096444940030196082797)
                  ·
                    rfl

theorem cell20_819619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 2, 4].length) (baseStart_819619 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_819619 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_819619 prefixEnd_819619 := by exact prefixLift 819619
  have htrace : WordTrace (prefixWord ++ tailWord_819619) baseStart_819619 baseEnd_819619 := by
    simpa [prefixWord, tailWord_819619, baseEnd_819619] using wordTrace_append hprefix tailTrace_819619
  have hstable : (prefixWord ++ tailWord_819619).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819619).length < 2 ^ (prefixWord ++ tailWord_819619).sum := by decide
  have hdescent : baseEnd_819619 < baseStart_819619 := by decide
  rcases family_descends (prefixWord ++ tailWord_819619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819640 : List Nat := [2, 1, 2, 1, 2, 2, 1, 1, 8]
def baseStart_819640 : Nat := 118140960795 + 819640 * 2 ^ 59
def prefixEnd_819640 : Nat := 4983230072969 + 3 ^ 40 * 819640 * 2
def baseEnd_819640 : Nat := 374106029912247456382711

theorem tailTrace_819640 : CollatzResearch.WordTrace tailWord_819640 prefixEnd_819640 374106029912247456382711 := by
  unfold tailWord_819640
  simp only [CollatzResearch.WordTrace]
  refine ⟨14947363375295869106232187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19929817833727825474976249 14947363375295869106232187)
  ·
    refine ⟨22421045062943803659348281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14947363375295869106232187 22421045062943803659348281)
    ·
      refine ⟨16815783797207852744511211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22421045062943803659348281 16815783797207852744511211)
      ·
        refine ⟨25223675695811779116766817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16815783797207852744511211 25223675695811779116766817)
        ·
          refine ⟨18917756771858834337575113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25223675695811779116766817 18917756771858834337575113)
          ·
            refine ⟨14188317578894125753181335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18917756771858834337575113 14188317578894125753181335)
            ·
              refine ⟨21282476368341188629772003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14188317578894125753181335 21282476368341188629772003)
              ·
                refine ⟨31923714552511782944658005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21282476368341188629772003 31923714552511782944658005)
                ·
                  refine ⟨374106029912247456382711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31923714552511782944658005 374106029912247456382711)
                  ·
                    rfl

theorem cell20_819640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 8].length) (baseStart_819640 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_819640 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_819640 prefixEnd_819640 := by exact prefixLift 819640
  have htrace : WordTrace (prefixWord ++ tailWord_819640) baseStart_819640 baseEnd_819640 := by
    simpa [prefixWord, tailWord_819640, baseEnd_819640] using wordTrace_append hprefix tailTrace_819640
  have hstable : (prefixWord ++ tailWord_819640).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819640).length < 2 ^ (prefixWord ++ tailWord_819640).sum := by decide
  have hdescent : baseEnd_819640 < baseStart_819640 := by decide
  rcases family_descends (prefixWord ++ tailWord_819640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819698 : List Nat := [3, 2, 1, 4, 3, 1, 6]
def baseStart_819698 : Nat := 118140960795 + 819698 * 2 ^ 59
def prefixEnd_819698 : Nat := 4983230072969 + 3 ^ 40 * 819698 * 2
def baseEnd_819698 : Nat := 41570278076961892494349

theorem tailTrace_819698 : CollatzResearch.WordTrace tailWord_819698 prefixEnd_819698 41570278076961892494349 := by
  unfold tailWord_819698
  simp only [CollatzResearch.WordTrace]
  refine ⟨7474210546095403529518937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19931228122921076078717165 7474210546095403529518937)
  ·
    refine ⟨5605657909571552647139203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7474210546095403529518937 5605657909571552647139203)
    ·
      refine ⟨8408486864357328970708805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5605657909571552647139203 8408486864357328970708805)
      ·
        refine ⟨1576591287066999182007901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8408486864357328970708805 1576591287066999182007901)
        ·
          refine ⟨591221732650124693252963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1576591287066999182007901 591221732650124693252963)
          ·
            refine ⟨886832598975187039879445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 591221732650124693252963 886832598975187039879445)
            ·
              refine ⟨41570278076961892494349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 886832598975187039879445 41570278076961892494349)
              ·
                rfl

theorem cell20_819698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 6].length) (baseStart_819698 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_819698 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_819698 prefixEnd_819698 := by exact prefixLift 819698
  have htrace : WordTrace (prefixWord ++ tailWord_819698) baseStart_819698 baseEnd_819698 := by
    simpa [prefixWord, tailWord_819698, baseEnd_819698] using wordTrace_append hprefix tailTrace_819698
  have hstable : (prefixWord ++ tailWord_819698).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819698).length < 2 ^ (prefixWord ++ tailWord_819698).sum := by decide
  have hdescent : baseEnd_819698 < baseStart_819698 := by decide
  rcases family_descends (prefixWord ++ tailWord_819698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819709 : List Nat := [1, 4, 1, 1, 1, 3, 1, 3, 5]
def baseStart_819709 : Nat := 118140960795 + 819709 * 2 ^ 59
def prefixEnd_819709 : Nat := 4983230072969 + 3 ^ 40 * 819709 * 2
def baseEnd_819709 : Nat := 374137523392389883082429

theorem tailTrace_819709 : CollatzResearch.WordTrace tailWord_819709 prefixEnd_819709 374137523392389883082429 := by
  unfold tailWord_819709
  simp only [CollatzResearch.WordTrace]
  refine ⟨29897243387341762996726181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19931495591561175331150787 29897243387341762996726181)
  ·
    refine ⟨5605733135126580561886159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29897243387341762996726181 5605733135126580561886159)
    ·
      refine ⟨8408599702689870842829239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5605733135126580561886159 8408599702689870842829239)
      ·
        refine ⟨12612899554034806264243859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8408599702689870842829239 12612899554034806264243859)
        ·
          refine ⟨18919349331052209396365789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12612899554034806264243859 18919349331052209396365789)
          ·
            refine ⟨7094755999144578523637171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18919349331052209396365789 7094755999144578523637171)
            ·
              refine ⟨10642133998716867785455757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7094755999144578523637171 10642133998716867785455757)
              ·
                refine ⟨3990800249518825419545909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10642133998716867785455757 3990800249518825419545909)
                ·
                  refine ⟨374137523392389883082429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3990800249518825419545909 374137523392389883082429)
                  ·
                    rfl

theorem cell20_819709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_819709 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_819709 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_819709 prefixEnd_819709 := by exact prefixLift 819709
  have htrace : WordTrace (prefixWord ++ tailWord_819709) baseStart_819709 baseEnd_819709 := by
    simpa [prefixWord, tailWord_819709, baseEnd_819709] using wordTrace_append hprefix tailTrace_819709
  have hstable : (prefixWord ++ tailWord_819709).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819709).length < 2 ^ (prefixWord ++ tailWord_819709).sum := by decide
  have hdescent : baseEnd_819709 < baseStart_819709 := by decide
  rcases family_descends (prefixWord ++ tailWord_819709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819718 : List Nat := [6, 2, 1, 1, 1, 1, 4, 1, 3]
def baseStart_819718 : Nat := 118140960795 + 819718 * 2 ^ 59
def prefixEnd_819718 : Nat := 4983230072969 + 3 ^ 40 * 819718 * 2
def baseEnd_819718 : Nat := 374141631237625851782393

theorem tailTrace_819718 : CollatzResearch.WordTrace tailWord_819718 prefixEnd_819718 374141631237625851782393 := by
  unfold tailWord_819718
  simp only [CollatzResearch.WordTrace]
  refine ⟨934299113884661172931369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 19931714429539438355869205 934299113884661172931369)
  ·
    refine ⟨700724335413495879698527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 934299113884661172931369 700724335413495879698527)
    ·
      refine ⟨1051086503120243819547791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 700724335413495879698527 1051086503120243819547791)
      ·
        refine ⟨1576629754680365729321687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1051086503120243819547791 1576629754680365729321687)
        ·
          refine ⟨2364944632020548593982531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1576629754680365729321687 2364944632020548593982531)
          ·
            refine ⟨3547416948030822890973797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2364944632020548593982531 3547416948030822890973797)
            ·
              refine ⟨665140677755779292057587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3547416948030822890973797 665140677755779292057587)
              ·
                refine ⟨997711016633668938086381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 665140677755779292057587 997711016633668938086381)
                ·
                  refine ⟨374141631237625851782393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 997711016633668938086381 374141631237625851782393)
                  ·
                    rfl

theorem cell20_819718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_819718 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_819718 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_819718 prefixEnd_819718 := by exact prefixLift 819718
  have htrace : WordTrace (prefixWord ++ tailWord_819718) baseStart_819718 baseEnd_819718 := by
    simpa [prefixWord, tailWord_819718, baseEnd_819718] using wordTrace_append hprefix tailTrace_819718
  have hstable : (prefixWord ++ tailWord_819718).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819718).length < 2 ^ (prefixWord ++ tailWord_819718).sum := by decide
  have hdescent : baseEnd_819718 < baseStart_819718 := by decide
  rcases family_descends (prefixWord ++ tailWord_819718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819719 : List Nat := [1, 1, 4, 3, 3, 1, 2, 5]
def baseStart_819719 : Nat := 118140960795 + 819719 * 2 ^ 59
def prefixEnd_819719 : Nat := 4983230072969 + 3 ^ 40 * 819719 * 2
def baseEnd_819719 : Nat := 124714029221624764249685

theorem tailTrace_819719 : CollatzResearch.WordTrace tailWord_819719 prefixEnd_819719 124714029221624764249685 := by
  unfold tailWord_819719
  simp only [CollatzResearch.WordTrace]
  refine ⟨29897608117305534704590211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19931738744870356469726807 29897608117305534704590211)
  ·
    refine ⟨44846412175958302056885317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29897608117305534704590211 44846412175958302056885317)
    ·
      refine ⟨8408702282992181635665997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44846412175958302056885317 8408702282992181635665997)
      ·
        refine ⟨3153263356122068113374749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8408702282992181635665997 3153263356122068113374749)
        ·
          refine ⟨1182473758545775542515531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3153263356122068113374749 1182473758545775542515531)
          ·
            refine ⟨1773710637818663313773297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1182473758545775542515531 1773710637818663313773297)
            ·
              refine ⟨1330282978363997485329973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1773710637818663313773297 1330282978363997485329973)
              ·
                refine ⟨124714029221624764249685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1330282978363997485329973 124714029221624764249685)
                ·
                  rfl

theorem cell20_819719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 5].length) (baseStart_819719 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_819719 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_819719 prefixEnd_819719 := by exact prefixLift 819719
  have htrace : WordTrace (prefixWord ++ tailWord_819719) baseStart_819719 baseEnd_819719 := by
    simpa [prefixWord, tailWord_819719, baseEnd_819719] using wordTrace_append hprefix tailTrace_819719
  have hstable : (prefixWord ++ tailWord_819719).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819719).length < 2 ^ (prefixWord ++ tailWord_819719).sum := by decide
  have hdescent : baseEnd_819719 < baseStart_819719 := by decide
  rcases family_descends (prefixWord ++ tailWord_819719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819740 : List Nat := [2, 2, 3, 1, 2, 2, 2, 6]
def baseStart_819740 : Nat := 118140960795 + 819740 * 2 ^ 59
def prefixEnd_819740 : Nat := 4983230072969 + 3 ^ 40 * 819740 * 2
def baseEnd_819740 : Nat := 124717224212363851016323

theorem tailTrace_819740 : CollatzResearch.WordTrace tailWord_819740 prefixEnd_819740 124717224212363851016323 := by
  unfold tailWord_819740
  simp only [CollatzResearch.WordTrace]
  refine ⟨14949187025114727645552337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19932249366819636860736449 14949187025114727645552337)
  ·
    refine ⟨11211890268836045734164253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14949187025114727645552337 11211890268836045734164253)
    ·
      refine ⟨4204458850813517150311595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11211890268836045734164253 4204458850813517150311595)
      ·
        refine ⟨6306688276220275725467393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4204458850813517150311595 6306688276220275725467393)
        ·
          refine ⟨4730016207165206794100545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6306688276220275725467393 4730016207165206794100545)
          ·
            refine ⟨3547512155373905095575409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4730016207165206794100545 3547512155373905095575409)
            ·
              refine ⟨2660634116530428821681557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3547512155373905095575409 2660634116530428821681557)
              ·
                refine ⟨124717224212363851016323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2660634116530428821681557 124717224212363851016323)
                ·
                  rfl

theorem cell20_819740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 6].length) (baseStart_819740 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_819740 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_819740 prefixEnd_819740 := by exact prefixLift 819740
  have htrace : WordTrace (prefixWord ++ tailWord_819740) baseStart_819740 baseEnd_819740 := by
    simpa [prefixWord, tailWord_819740, baseEnd_819740] using wordTrace_append hprefix tailTrace_819740
  have hstable : (prefixWord ++ tailWord_819740).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819740).length < 2 ^ (prefixWord ++ tailWord_819740).sum := by decide
  have hdescent : baseEnd_819740 < baseStart_819740 := by decide
  rcases family_descends (prefixWord ++ tailWord_819740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819826 : List Nat := [3, 2, 1, 2, 4, 1, 2, 1, 4]
def baseStart_819826 : Nat := 118140960795 + 819826 * 2 ^ 59
def prefixEnd_819826 : Nat := 4983230072969 + 3 ^ 40 * 819826 * 2
def baseEnd_819826 : Nat := 374190925380457476181951

theorem tailTrace_819826 : CollatzResearch.WordTrace tailWord_819826 prefixEnd_819826 374190925380457476181951 := by
  unfold tailWord_819826
  simp only [CollatzResearch.WordTrace]
  refine ⟨7475377681979472994683833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19934340485278594652490221 7475377681979472994683833)
  ·
    refine ⟨5606533261484604746012875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7475377681979472994683833 5606533261484604746012875)
    ·
      refine ⟨8409799892226907119019313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5606533261484604746012875 8409799892226907119019313)
      ·
        refine ⟨6307349919170180339264485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8409799892226907119019313 6307349919170180339264485)
        ·
          refine ⟨1182628109844408813612091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6307349919170180339264485 1182628109844408813612091)
          ·
            refine ⟨1773942164766613220418137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1182628109844408813612091 1773942164766613220418137)
            ·
              refine ⟨1330456623574959915313603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1773942164766613220418137 1330456623574959915313603)
              ·
                refine ⟨1995684935362439872970405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1330456623574959915313603 1995684935362439872970405)
                ·
                  refine ⟨374190925380457476181951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1995684935362439872970405 374190925380457476181951)
                  ·
                    rfl

theorem cell20_819826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 1, 4].length) (baseStart_819826 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_819826 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_819826 prefixEnd_819826 := by exact prefixLift 819826
  have htrace : WordTrace (prefixWord ++ tailWord_819826) baseStart_819826 baseEnd_819826 := by
    simpa [prefixWord, tailWord_819826, baseEnd_819826] using wordTrace_append hprefix tailTrace_819826
  have hstable : (prefixWord ++ tailWord_819826).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819826).length < 2 ^ (prefixWord ++ tailWord_819826).sum := by decide
  have hdescent : baseEnd_819826 < baseStart_819826 := by decide
  rcases family_descends (prefixWord ++ tailWord_819826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819850 : List Nat := [3, 1, 2, 3, 3, 2, 2, 4]
def baseStart_819850 : Nat := 118140960795 + 819850 * 2 ^ 59
def prefixEnd_819850 : Nat := 4983230072969 + 3 ^ 40 * 819850 * 2
def baseEnd_819850 : Nat := 124733959878140019793951

theorem tailTrace_819850 : CollatzResearch.WordTrace tailWord_819850 prefixEnd_819850 124733959878140019793951 := by
  unfold tailWord_819850
  simp only [CollatzResearch.WordTrace]
  refine ⟨7475596519957736019402251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19934924053220629385072669 7475596519957736019402251)
  ·
    refine ⟨11213394779936604029103377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7475596519957736019402251 11213394779936604029103377)
    ·
      refine ⟨8410046084952453021827533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11213394779936604029103377 8410046084952453021827533)
      ·
        refine ⟨3153767281857169883185325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8410046084952453021827533 3153767281857169883185325)
        ·
          refine ⟨1182662730696438706194497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3153767281857169883185325 1182662730696438706194497)
          ·
            refine ⟨886997048022329029645873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1182662730696438706194497 886997048022329029645873)
            ·
              refine ⟨665247786016746772234405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 886997048022329029645873 665247786016746772234405)
              ·
                refine ⟨124733959878140019793951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 665247786016746772234405 124733959878140019793951)
                ·
                  rfl

theorem cell20_819850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 2, 4].length) (baseStart_819850 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_819850 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_819850 prefixEnd_819850 := by exact prefixLift 819850
  have htrace : WordTrace (prefixWord ++ tailWord_819850) baseStart_819850 baseEnd_819850 := by
    simpa [prefixWord, tailWord_819850, baseEnd_819850] using wordTrace_append hprefix tailTrace_819850
  have hstable : (prefixWord ++ tailWord_819850).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819850).length < 2 ^ (prefixWord ++ tailWord_819850).sum := by decide
  have hdescent : baseEnd_819850 < baseStart_819850 := by decide
  rcases family_descends (prefixWord ++ tailWord_819850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819854 : List Nat := [4, 1, 1, 3, 1, 1, 3, 6]
def baseStart_819854 : Nat := 118140960795 + 819854 * 2 ^ 59
def prefixEnd_819854 : Nat := 4983230072969 + 3 ^ 40 * 819854 * 2
def baseEnd_819854 : Nat := 124734568447804607749501

theorem tailTrace_819854 : CollatzResearch.WordTrace tailWord_819854 prefixEnd_819854 124734568447804607749501 := by
  unfold tailWord_819854
  simp only [CollatzResearch.WordTrace]
  refine ⟨3737816496477056595094327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19935021314544301840503077 3737816496477056595094327)
  ·
    refine ⟨5606724744715584892641491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3737816496477056595094327 5606724744715584892641491)
    ·
      refine ⟨8410087117073377338962237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5606724744715584892641491 8410087117073377338962237)
      ·
        refine ⟨3153782668902516502110839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8410087117073377338962237 3153782668902516502110839)
        ·
          refine ⟨4730674003353774753166259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3153782668902516502110839 4730674003353774753166259)
          ·
            refine ⟨7096011005030662129749389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4730674003353774753166259 7096011005030662129749389)
            ·
              refine ⟨2661004126886498298656021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7096011005030662129749389 2661004126886498298656021)
              ·
                refine ⟨124734568447804607749501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2661004126886498298656021 124734568447804607749501)
                ·
                  rfl

theorem cell20_819854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_819854 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_819854 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_819854 prefixEnd_819854 := by exact prefixLift 819854
  have htrace : WordTrace (prefixWord ++ tailWord_819854) baseStart_819854 baseEnd_819854 := by
    simpa [prefixWord, tailWord_819854, baseEnd_819854] using wordTrace_append hprefix tailTrace_819854
  have hstable : (prefixWord ++ tailWord_819854).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819854).length < 2 ^ (prefixWord ++ tailWord_819854).sum := by decide
  have hdescent : baseEnd_819854 < baseStart_819854 := by decide
  rcases family_descends (prefixWord ++ tailWord_819854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819860 : List Nat := [2, 4, 2, 2, 1, 3, 1, 3, 2]
def baseStart_819860 : Nat := 118140960795 + 819860 * 2 ^ 59
def prefixEnd_819860 : Nat := 4983230072969 + 3 ^ 40 * 819860 * 2
def baseEnd_819860 : Nat := 374206443906904469048479

theorem tailTrace_819860 : CollatzResearch.WordTrace tailWord_819860 prefixEnd_819860 374206443906904469048479 := by
  unfold tailWord_819860
  simp only [CollatzResearch.WordTrace]
  refine ⟨14951375404897357892736517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19935167206529810523648689 14951375404897357892736517)
  ·
    refine ⟨2803382888418254604888097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14951375404897357892736517 2803382888418254604888097)
    ·
      refine ⟨2102537166313690953666073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2803382888418254604888097 2102537166313690953666073)
      ·
        refine ⟨1576902874735268215249555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2102537166313690953666073 1576902874735268215249555)
        ·
          refine ⟨2365354312102902322874333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1576902874735268215249555 2365354312102902322874333)
          ·
            refine ⟨887007867038588371077875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2365354312102902322874333 887007867038588371077875)
            ·
              refine ⟨1330511800557882556616813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 887007867038588371077875 1330511800557882556616813)
              ·
                refine ⟨498941925209205958731305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1330511800557882556616813 498941925209205958731305)
                ·
                  refine ⟨374206443906904469048479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 498941925209205958731305 374206443906904469048479)
                  ·
                    rfl

theorem cell20_819860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 3, 2].length) (baseStart_819860 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_819860 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_819860 prefixEnd_819860 := by exact prefixLift 819860
  have htrace : WordTrace (prefixWord ++ tailWord_819860) baseStart_819860 baseEnd_819860 := by
    simpa [prefixWord, tailWord_819860, baseEnd_819860] using wordTrace_append hprefix tailTrace_819860
  have hstable : (prefixWord ++ tailWord_819860).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819860).length < 2 ^ (prefixWord ++ tailWord_819860).sum := by decide
  have hdescent : baseEnd_819860 < baseStart_819860 := by decide
  rcases family_descends (prefixWord ++ tailWord_819860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819940 : List Nat := [2, 3, 1, 1, 1, 5, 1, 4, 2]
def baseStart_819940 : Nat := 118140960795 + 819940 * 2 ^ 59
def prefixEnd_819940 : Nat := 4983230072969 + 3 ^ 40 * 819940 * 2
def baseEnd_819940 : Nat := 374242958086779746381485

theorem tailTrace_819940 : CollatzResearch.WordTrace tailWord_819940 prefixEnd_819940 374242958086779746381485 := by
  unfold tailWord_819940
  simp only [CollatzResearch.WordTrace]
  refine ⟨14952834324752444724192637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19937112433003259632256849 14952834324752444724192637)
  ·
    refine ⟨5607312871782166771572239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14952834324752444724192637 5607312871782166771572239)
    ·
      refine ⟨8410969307673250157358359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5607312871782166771572239 8410969307673250157358359)
      ·
        refine ⟨12616453961509875236037539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8410969307673250157358359 12616453961509875236037539)
        ·
          refine ⟨18924680942264812854056309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12616453961509875236037539 18924680942264812854056309)
          ·
            refine ⟨1774188838337326205067779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18924680942264812854056309 1774188838337326205067779)
            ·
              refine ⟨2661283257505989307601669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1774188838337326205067779 2661283257505989307601669)
              ·
                refine ⟨498990610782372995175313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2661283257505989307601669 498990610782372995175313)
                ·
                  refine ⟨374242958086779746381485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 498990610782372995175313 374242958086779746381485)
                  ·
                    rfl

theorem cell20_819940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 4, 2].length) (baseStart_819940 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_819940 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_819940 prefixEnd_819940 := by exact prefixLift 819940
  have htrace : WordTrace (prefixWord ++ tailWord_819940) baseStart_819940 baseEnd_819940 := by
    simpa [prefixWord, tailWord_819940, baseEnd_819940] using wordTrace_append hprefix tailTrace_819940
  have hstable : (prefixWord ++ tailWord_819940).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819940).length < 2 ^ (prefixWord ++ tailWord_819940).sum := by decide
  have hdescent : baseEnd_819940 < baseStart_819940 := by decide
  rcases family_descends (prefixWord ++ tailWord_819940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819954 : List Nat := [3, 2, 1, 3, 1, 2, 2, 3, 3]
def baseStart_819954 : Nat := 118140960795 + 819954 * 2 ^ 59
def prefixEnd_819954 : Nat := 4983230072969 + 3 ^ 40 * 819954 * 2
def baseEnd_819954 : Nat := 374249348068257919914761

theorem tailTrace_819954 : CollatzResearch.WordTrace tailWord_819954 prefixEnd_819954 374249348068257919914761 := by
  unfold tailWord_819954
  simp only [CollatzResearch.WordTrace]
  refine ⟨7476544817863542459848729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19937452847636113226263277 7476544817863542459848729)
  ·
    refine ⟨5607408613397656844886547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7476544817863542459848729 5607408613397656844886547)
    ·
      refine ⟨8411112920096485267329821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5607408613397656844886547 8411112920096485267329821)
      ·
        refine ⟨3154167345036181975248683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8411112920096485267329821 3154167345036181975248683)
        ·
          refine ⟨4731251017554272962873025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3154167345036181975248683 4731251017554272962873025)
          ·
            refine ⟨3548438263165704722154769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4731251017554272962873025 3548438263165704722154769)
            ·
              refine ⟨2661328697374278541616077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3548438263165704722154769 2661328697374278541616077)
              ·
                refine ⟨997998261515354453106029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2661328697374278541616077 997998261515354453106029)
                ·
                  refine ⟨374249348068257919914761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 997998261515354453106029 374249348068257919914761)
                  ·
                    rfl

theorem cell20_819954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 3, 3].length) (baseStart_819954 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_819954 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_819954 prefixEnd_819954 := by exact prefixLift 819954
  have htrace : WordTrace (prefixWord ++ tailWord_819954) baseStart_819954 baseEnd_819954 := by
    simpa [prefixWord, tailWord_819954, baseEnd_819954] using wordTrace_append hprefix tailTrace_819954
  have hstable : (prefixWord ++ tailWord_819954).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819954).length < 2 ^ (prefixWord ++ tailWord_819954).sum := by decide
  have hdescent : baseEnd_819954 < baseStart_819954 := by decide
  rcases family_descends (prefixWord ++ tailWord_819954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819978 : List Nat := [3, 1, 2, 2, 1, 2, 4, 3, 2]
def baseStart_819978 : Nat := 118140960795 + 819978 * 2 ^ 59
def prefixEnd_819978 : Nat := 4983230072969 + 3 ^ 40 * 819978 * 2
def baseEnd_819978 : Nat := 374260302322220503114663

theorem tailTrace_819978 : CollatzResearch.WordTrace tailWord_819978 prefixEnd_819978 374260302322220503114663 := by
  unfold tailWord_819978
  simp only [CollatzResearch.WordTrace]
  refine ⟨7476763655841805484567147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19938036415578147958845725 7476763655841805484567147)
  ·
    refine ⟨11215145483762708226850721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7476763655841805484567147 11215145483762708226850721)
    ·
      refine ⟨8411359112822031170138041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11215145483762708226850721 8411359112822031170138041)
      ·
        refine ⟨6308519334616523377603531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8411359112822031170138041 6308519334616523377603531)
        ·
          refine ⟨9462779001924785066405297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6308519334616523377603531 9462779001924785066405297)
          ·
            refine ⟨7097084251443588799803973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9462779001924785066405297 7097084251443588799803973)
            ·
              refine ⟨1330703297145672899963245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7097084251443588799803973 1330703297145672899963245)
              ·
                refine ⟨499013736429627337486217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1330703297145672899963245 499013736429627337486217)
                ·
                  refine ⟨374260302322220503114663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 499013736429627337486217 374260302322220503114663)
                  ·
                    rfl

theorem cell20_819978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 3, 2].length) (baseStart_819978 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_819978 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_819978 prefixEnd_819978 := by exact prefixLift 819978
  have htrace : WordTrace (prefixWord ++ tailWord_819978) baseStart_819978 baseEnd_819978 := by
    simpa [prefixWord, tailWord_819978, baseEnd_819978] using wordTrace_append hprefix tailTrace_819978
  have hstable : (prefixWord ++ tailWord_819978).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819978).length < 2 ^ (prefixWord ++ tailWord_819978).sum := by decide
  have hdescent : baseEnd_819978 < baseStart_819978 := by decide
  rcases family_descends (prefixWord ++ tailWord_819978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819982 : List Nat := [4, 1, 1, 2, 1, 1, 1, 1, 8]
def baseStart_819982 : Nat := 118140960795 + 819982 * 2 ^ 59
def prefixEnd_819982 : Nat := 4983230072969 + 3 ^ 40 * 819982 * 2
def baseEnd_819982 : Nat := 374262128031214266981313

theorem tailTrace_819982 : CollatzResearch.WordTrace tailWord_819982 prefixEnd_819982 374262128031214266981313 := by
  unfold tailWord_819982
  simp only [CollatzResearch.WordTrace]
  refine ⟨3738400064419091327676775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19938133676901820414276133 3738400064419091327676775)
  ·
    refine ⟨5607600096628636991515163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3738400064419091327676775 5607600096628636991515163)
    ·
      refine ⟨8411400144942955487272745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5607600096628636991515163 8411400144942955487272745)
      ·
        refine ⟨6308550108707216615454559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8411400144942955487272745 6308550108707216615454559)
        ·
          refine ⟨9462825163060824923181839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6308550108707216615454559 9462825163060824923181839)
          ·
            refine ⟨14194237744591237384772759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9462825163060824923181839 14194237744591237384772759)
            ·
              refine ⟨21291356616886856077159139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14194237744591237384772759 21291356616886856077159139)
              ·
                refine ⟨31937034925330284115738709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21291356616886856077159139 31937034925330284115738709)
                ·
                  refine ⟨374262128031214266981313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31937034925330284115738709 374262128031214266981313)
                  ·
                    rfl

theorem cell20_819982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_819982 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_819982 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_819982 prefixEnd_819982 := by exact prefixLift 819982
  have htrace : WordTrace (prefixWord ++ tailWord_819982) baseStart_819982 baseEnd_819982 := by
    simpa [prefixWord, tailWord_819982, baseEnd_819982] using wordTrace_append hprefix tailTrace_819982
  have hstable : (prefixWord ++ tailWord_819982).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819982).length < 2 ^ (prefixWord ++ tailWord_819982).sum := by decide
  have hdescent : baseEnd_819982 < baseStart_819982 := by decide
  rcases family_descends (prefixWord ++ tailWord_819982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819989 : List Nat := [1, 3, 2, 1, 2, 2, 9]
def baseStart_819989 : Nat := 118140960795 + 819989 * 2 ^ 59
def prefixEnd_819989 : Nat := 4983230072969 + 3 ^ 40 * 819989 * 2
def baseEnd_819989 : Nat := 41585035891328150416439

theorem tailTrace_819989 : CollatzResearch.WordTrace tailWord_819989 prefixEnd_819989 41585035891328150416439 := by
  unfold tailWord_819989
  simp only [CollatzResearch.WordTrace]
  refine ⟨29907455826327370816919021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19938303884218247211279347 29907455826327370816919021)
  ·
    refine ⟨11215295934872764056344633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29907455826327370816919021 11215295934872764056344633)
    ·
      refine ⟨8411471951154573042258475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11215295934872764056344633 8411471951154573042258475)
      ·
        refine ⟨12617207926731859563387713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8411471951154573042258475 12617207926731859563387713)
        ·
          refine ⟨9462905945048894672540785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12617207926731859563387713 9462905945048894672540785)
          ·
            refine ⟨7097179458786671004405589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9462905945048894672540785 7097179458786671004405589)
            ·
              refine ⟨41585035891328150416439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7097179458786671004405589 41585035891328150416439)
              ·
                rfl

theorem cell20_819989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 9].length) (baseStart_819989 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_819989 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_819989 prefixEnd_819989 := by exact prefixLift 819989
  have htrace : WordTrace (prefixWord ++ tailWord_819989) baseStart_819989 baseEnd_819989 := by
    simpa [prefixWord, tailWord_819989, baseEnd_819989] using wordTrace_append hprefix tailTrace_819989
  have hstable : (prefixWord ++ tailWord_819989).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819989).length < 2 ^ (prefixWord ++ tailWord_819989).sum := by decide
  have hdescent : baseEnd_819989 < baseStart_819989 := by decide
  rcases family_descends (prefixWord ++ tailWord_819989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_819999 : List Nat := [1, 1, 2, 4, 2, 3, 2, 1, 4]
def baseStart_819999 : Nat := 118140960795 + 819999 * 2 ^ 59
def prefixEnd_819999 : Nat := 4983230072969 + 3 ^ 40 * 819999 * 2
def baseEnd_819999 : Nat := 374269887294437763414577

theorem tailTrace_819999 : CollatzResearch.WordTrace tailWord_819999 prefixEnd_819999 374269887294437763414577 := by
  unfold tailWord_819999
  simp only [CollatzResearch.WordTrace]
  refine ⟨29907820556291142524783051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19938547037527428349855367 29907820556291142524783051)
  ·
    refine ⟨44861730834436713787174577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29907820556291142524783051 44861730834436713787174577)
    ·
      refine ⟨33646298125827535340380933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44861730834436713787174577 33646298125827535340380933)
      ·
        refine ⟨6308680898592662876321425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33646298125827535340380933 6308680898592662876321425)
        ·
          refine ⟨4731510673944497157241069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6308680898592662876321425 4731510673944497157241069)
          ·
            refine ⟨1774316502729186433965401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4731510673944497157241069 1774316502729186433965401)
            ·
              refine ⟨1330737377046889825474051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1774316502729186433965401 1330737377046889825474051)
              ·
                refine ⟨1996106065570334738211077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1330737377046889825474051 1996106065570334738211077)
                ·
                  refine ⟨374269887294437763414577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1996106065570334738211077 374269887294437763414577)
                  ·
                    rfl

theorem cell20_819999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 1, 4].length) (baseStart_819999 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_819999 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_819999 prefixEnd_819999 := by exact prefixLift 819999
  have htrace : WordTrace (prefixWord ++ tailWord_819999) baseStart_819999 baseEnd_819999 := by
    simpa [prefixWord, tailWord_819999, baseEnd_819999] using wordTrace_append hprefix tailTrace_819999
  have hstable : (prefixWord ++ tailWord_819999).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_819999).length < 2 ^ (prefixWord ++ tailWord_819999).sum := by decide
  have hdescent : baseEnd_819999 < baseStart_819999 := by decide
  rcases family_descends (prefixWord ++ tailWord_819999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
