import V185TrunkScan20Chunk119

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_729786 : List Nat := [3, 1, 1, 1, 2, 3, 5, 4]
def baseStart_729786 : Nat := 118140960795 + 729786 * 2 ^ 59
def prefixEnd_729786 : Nat := 4983230072969 + 3 ^ 40 * 729786 * 2
def baseEnd_729786 : Nat := 111031405310277612627787

theorem tailTrace_729786 : CollatzResearch.WordTrace tailWord_729786 prefixEnd_729786 111031405310277612627787 := by
  unfold tailWord_729786
  simp only [CollatzResearch.WordTrace]
  refine ⟨6654370533529358592752303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17744988089411622914006141 6654370533529358592752303)
  ·
    refine ⟨9981555800294037889128455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6654370533529358592752303 9981555800294037889128455)
    ·
      refine ⟨14972333700441056833692683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9981555800294037889128455 14972333700441056833692683)
      ·
        refine ⟨22458500550661585250539025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14972333700441056833692683 22458500550661585250539025)
        ·
          refine ⟨16843875412996188937904269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22458500550661585250539025 16843875412996188937904269)
          ·
            refine ⟨6316453279873570851714101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16843875412996188937904269 6316453279873570851714101)
            ·
              refine ⟨592167494988147267348197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6316453279873570851714101 592167494988147267348197)
              ·
                refine ⟨111031405310277612627787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 592167494988147267348197 111031405310277612627787)
                ·
                  rfl

theorem cell20_729786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 5, 4].length) (baseStart_729786 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_729786 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_729786 prefixEnd_729786 := by exact prefixLift 729786
  have htrace : WordTrace (prefixWord ++ tailWord_729786) baseStart_729786 baseEnd_729786 := by
    simpa [prefixWord, tailWord_729786, baseEnd_729786] using wordTrace_append hprefix tailTrace_729786
  have hstable : (prefixWord ++ tailWord_729786).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729786).length < 2 ^ (prefixWord ++ tailWord_729786).sum := by decide
  have hdescent : baseEnd_729786 < baseStart_729786 := by decide
  rcases family_descends (prefixWord ++ tailWord_729786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729796 : List Nat := [2, 3, 3, 1, 1, 2, 1, 5, 2]
def baseStart_729796 : Nat := 118140960795 + 729796 * 2 ^ 59
def prefixEnd_729796 : Nat := 4983230072969 + 3 ^ 40 * 729796 * 2
def baseEnd_729796 : Nat := 333098780203317247549987

theorem tailTrace_729796 : CollatzResearch.WordTrace tailWord_729796 prefixEnd_729796 333098780203317247549987 := by
  unfold tailWord_729796
  simp only [CollatzResearch.WordTrace]
  refine ⟨13308923432040603039436621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17745231242720804052582161 13308923432040603039436621)
  ·
    refine ⟨4990846287015226139788733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13308923432040603039436621 4990846287015226139788733)
    ·
      refine ⟨1871567357630709802420775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4990846287015226139788733 1871567357630709802420775)
      ·
        refine ⟨2807351036446064703631163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1871567357630709802420775 2807351036446064703631163)
        ·
          refine ⟨4211026554669097055446745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2807351036446064703631163 4211026554669097055446745)
          ·
            refine ⟨3158269916001822791585059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4211026554669097055446745 3158269916001822791585059)
            ·
              refine ⟨4737404874002734187377589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3158269916001822791585059 4737404874002734187377589)
              ·
                refine ⟨444131706937756330066649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4737404874002734187377589 444131706937756330066649)
                ·
                  refine ⟨333098780203317247549987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 444131706937756330066649 333098780203317247549987)
                  ·
                    rfl

theorem cell20_729796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 5, 2].length) (baseStart_729796 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_729796 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_729796 prefixEnd_729796 := by exact prefixLift 729796
  have htrace : WordTrace (prefixWord ++ tailWord_729796) baseStart_729796 baseEnd_729796 := by
    simpa [prefixWord, tailWord_729796, baseEnd_729796] using wordTrace_append hprefix tailTrace_729796
  have hstable : (prefixWord ++ tailWord_729796).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729796).length < 2 ^ (prefixWord ++ tailWord_729796).sum := by decide
  have hdescent : baseEnd_729796 < baseStart_729796 := by decide
  rcases family_descends (prefixWord ++ tailWord_729796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729810 : List Nat := [3, 2, 2, 2, 3, 1, 1, 1, 5]
def baseStart_729810 : Nat := 118140960795 + 729810 * 2 ^ 59
def prefixEnd_729810 : Nat := 4983230072969 + 3 ^ 40 * 729810 * 2
def baseEnd_729810 : Nat := 333105170184795421083263

theorem tailTrace_729810 : CollatzResearch.WordTrace tailWord_729810 prefixEnd_729810 333105170184795421083263 := by
  unfold tailWord_729810
  simp only [CollatzResearch.WordTrace]
  refine ⟨6654589371507621617470721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17745571657353657646588589 6654589371507621617470721)
  ·
    refine ⟨4990942028630716213103041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6654589371507621617470721 4990942028630716213103041)
    ·
      refine ⟨3743206521473037159827281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4990942028630716213103041 3743206521473037159827281)
      ·
        refine ⟨2807404891104777869870461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3743206521473037159827281 2807404891104777869870461)
        ·
          refine ⟨1052776834164291701201423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2807404891104777869870461 1052776834164291701201423)
          ·
            refine ⟨1579165251246437551802135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1052776834164291701201423 1579165251246437551802135)
            ·
              refine ⟨2368747876869656327703203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1579165251246437551802135 2368747876869656327703203)
              ·
                refine ⟨3553121815304484491554805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2368747876869656327703203 3553121815304484491554805)
                ·
                  refine ⟨333105170184795421083263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3553121815304484491554805 333105170184795421083263)
                  ·
                    rfl

theorem cell20_729810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 5].length) (baseStart_729810 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_729810 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_729810 prefixEnd_729810 := by exact prefixLift 729810
  have htrace : WordTrace (prefixWord ++ tailWord_729810) baseStart_729810 baseEnd_729810 := by
    simpa [prefixWord, tailWord_729810, baseEnd_729810] using wordTrace_append hprefix tailTrace_729810
  have hstable : (prefixWord ++ tailWord_729810).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729810).length < 2 ^ (prefixWord ++ tailWord_729810).sum := by decide
  have hdescent : baseEnd_729810 < baseStart_729810 := by decide
  rcases family_descends (prefixWord ++ tailWord_729810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729817 : List Nat := [1, 2, 1, 2, 3, 2, 1, 6, 2]
def baseStart_729817 : Nat := 118140960795 + 729817 * 2 ^ 59
def prefixEnd_729817 : Nat := 4983230072969 + 3 ^ 40 * 729817 * 2
def baseEnd_729817 : Nat := 333108365175534507849901

theorem tailTrace_729817 : CollatzResearch.WordTrace tailWord_729817 prefixEnd_729817 333108365175534507849901 := by
  unfold tailWord_729817
  simp only [CollatzResearch.WordTrace]
  refine ⟨26618612797005126665387705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17745741864670084443591803 26618612797005126665387705)
  ·
    refine ⟨19963959597753844999040779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26618612797005126665387705 19963959597753844999040779)
    ·
      refine ⟨29945939396630767498561169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19963959597753844999040779 29945939396630767498561169)
      ·
        refine ⟨22459454547473075623920877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29945939396630767498561169 22459454547473075623920877)
        ·
          refine ⟨8422295455302403358970329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22459454547473075623920877 8422295455302403358970329)
          ·
            refine ⟨6316721591476802519227747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8422295455302403358970329 6316721591476802519227747)
            ·
              refine ⟨9475082387215203778841621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6316721591476802519227747 9475082387215203778841621)
              ·
                refine ⟨444144486900712677133201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9475082387215203778841621 444144486900712677133201)
                ·
                  refine ⟨333108365175534507849901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 444144486900712677133201 333108365175534507849901)
                  ·
                    rfl

theorem cell20_729817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 6, 2].length) (baseStart_729817 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_729817 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_729817 prefixEnd_729817 := by exact prefixLift 729817
  have htrace : WordTrace (prefixWord ++ tailWord_729817) baseStart_729817 baseEnd_729817 := by
    simpa [prefixWord, tailWord_729817, baseEnd_729817] using wordTrace_append hprefix tailTrace_729817
  have hstable : (prefixWord ++ tailWord_729817).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729817).length < 2 ^ (prefixWord ++ tailWord_729817).sum := by decide
  have hdescent : baseEnd_729817 < baseStart_729817 := by decide
  rcases family_descends (prefixWord ++ tailWord_729817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729827 : List Nat := [1, 1, 1, 7, 1, 2, 3, 1, 3]
def baseStart_729827 : Nat := 118140960795 + 729827 * 2 ^ 59
def prefixEnd_729827 : Nat := 4983230072969 + 3 ^ 40 * 729827 * 2
def baseEnd_729827 : Nat := 333112929448018917516527

theorem tailTrace_729827 : CollatzResearch.WordTrace tailWord_729827 prefixEnd_729827 333112929448018917516527 := by
  unfold tailWord_729827
  simp only [CollatzResearch.WordTrace]
  refine ⟨26618977526968898373251735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17745985017979265582167823 26618977526968898373251735)
  ·
    refine ⟨39928466290453347559877603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26618977526968898373251735 39928466290453347559877603)
    ·
      refine ⟨59892699435680021339816405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39928466290453347559877603 59892699435680021339816405)
      ·
        refine ⟨1403735143023750500151947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 59892699435680021339816405 1403735143023750500151947)
        ·
          refine ⟨2105602714535625750227921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1403735143023750500151947 2105602714535625750227921)
          ·
            refine ⟨1579202035901719312670941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2105602714535625750227921 1579202035901719312670941)
            ·
              refine ⟨592200763463144742251603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1579202035901719312670941 592200763463144742251603)
              ·
                refine ⟨888301145194717113377405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 592200763463144742251603 888301145194717113377405)
                ·
                  refine ⟨333112929448018917516527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 888301145194717113377405 333112929448018917516527)
                  ·
                    rfl

theorem cell20_729827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 3, 1, 3].length) (baseStart_729827 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_729827 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_729827 prefixEnd_729827 := by exact prefixLift 729827
  have htrace : WordTrace (prefixWord ++ tailWord_729827) baseStart_729827 baseEnd_729827 := by
    simpa [prefixWord, tailWord_729827, baseEnd_729827] using wordTrace_append hprefix tailTrace_729827
  have hstable : (prefixWord ++ tailWord_729827).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729827).length < 2 ^ (prefixWord ++ tailWord_729827).sum := by decide
  have hdescent : baseEnd_729827 < baseStart_729827 := by decide
  rcases family_descends (prefixWord ++ tailWord_729827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729935 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 10]
def baseStart_729935 : Nat := 118140960795 + 729935 * 2 ^ 59
def prefixEnd_729935 : Nat := 4983230072969 + 3 ^ 40 * 729935 * 2
def baseEnd_729935 : Nat := 333162223590850541916085

theorem tailTrace_729935 : CollatzResearch.WordTrace tailWord_729935 prefixEnd_729935 333162223590850541916085 := by
  unfold tailWord_729935
  simp only [CollatzResearch.WordTrace]
  refine ⟨26622916610577632818183259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17748611073718421878788839 26622916610577632818183259)
  ·
    refine ⟨39934374915866449227274889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26622916610577632818183259 39934374915866449227274889)
    ·
      refine ⟨29950781186899836920456167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39934374915866449227274889 29950781186899836920456167)
      ·
        refine ⟨44926171780349755380684251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29950781186899836920456167 44926171780349755380684251)
        ·
          refine ⟨67389257670524633071026377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44926171780349755380684251 67389257670524633071026377)
          ·
            refine ⟨50541943252893474803269783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67389257670524633071026377 50541943252893474803269783)
            ·
              refine ⟨75812914879340212204904675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50541943252893474803269783 75812914879340212204904675)
              ·
                refine ⟨113719372319010318307357013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75812914879340212204904675 113719372319010318307357013)
                ·
                  refine ⟨333162223590850541916085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 113719372319010318307357013 333162223590850541916085)
                  ·
                    rfl

theorem cell20_729935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 10].length) (baseStart_729935 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_729935 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_729935 prefixEnd_729935 := by exact prefixLift 729935
  have htrace : WordTrace (prefixWord ++ tailWord_729935) baseStart_729935 baseEnd_729935 := by
    simpa [prefixWord, tailWord_729935, baseEnd_729935] using wordTrace_append hprefix tailTrace_729935
  have hstable : (prefixWord ++ tailWord_729935).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729935).length < 2 ^ (prefixWord ++ tailWord_729935).sum := by decide
  have hdescent : baseEnd_729935 < baseStart_729935 := by decide
  rcases family_descends (prefixWord ++ tailWord_729935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729945 : List Nat := [1, 2, 1, 2, 2, 4, 2, 3, 3]
def baseStart_729945 : Nat := 118140960795 + 729945 * 2 ^ 59
def prefixEnd_729945 : Nat := 4983230072969 + 3 ^ 40 * 729945 * 2
def baseEnd_729945 : Nat := 333166787863334951582711

theorem tailTrace_729945 : CollatzResearch.WordTrace tailWord_729945 prefixEnd_729945 333166787863334951582711 := by
  unfold tailWord_729945
  simp only [CollatzResearch.WordTrace]
  refine ⟨26623281340541404526047289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17748854227027603017364859 26623281340541404526047289)
  ·
    refine ⟨19967461005406053394535467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26623281340541404526047289 19967461005406053394535467)
    ·
      refine ⟨29951191508109080091803201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19967461005406053394535467 29951191508109080091803201)
      ·
        refine ⟨22463393631081810068852401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29951191508109080091803201 22463393631081810068852401)
        ·
          refine ⟨16847545223311357551639301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22463393631081810068852401 16847545223311357551639301)
          ·
            refine ⟨3158914729370879540932369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16847545223311357551639301 3158914729370879540932369)
            ·
              refine ⟨2369186047028159655699277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3158914729370879540932369 2369186047028159655699277)
              ·
                refine ⟨888444767635559870887229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2369186047028159655699277 888444767635559870887229)
                ·
                  refine ⟨333166787863334951582711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 888444767635559870887229 333166787863334951582711)
                  ·
                    rfl

theorem cell20_729945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 3, 3].length) (baseStart_729945 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_729945 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_729945 prefixEnd_729945 := by exact prefixLift 729945
  have htrace : WordTrace (prefixWord ++ tailWord_729945) baseStart_729945 baseEnd_729945 := by
    simpa [prefixWord, tailWord_729945, baseEnd_729945] using wordTrace_append hprefix tailTrace_729945
  have hstable : (prefixWord ++ tailWord_729945).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729945).length < 2 ^ (prefixWord ++ tailWord_729945).sum := by decide
  have hdescent : baseEnd_729945 < baseStart_729945 := by decide
  rcases family_descends (prefixWord ++ tailWord_729945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729952 : List Nat := [2, 1, 1, 3, 3, 1, 3, 2, 4]
def baseStart_729952 : Nat := 118140960795 + 729952 * 2 ^ 59
def prefixEnd_729952 : Nat := 4983230072969 + 3 ^ 40 * 729952 * 2
def baseEnd_729952 : Nat := 333169982854074038349349

theorem tailTrace_729952 : CollatzResearch.WordTrace tailWord_729952 prefixEnd_729952 333169982854074038349349 := by
  unfold tailWord_729952
  simp only [CollatzResearch.WordTrace]
  refine ⟨13311768325758022360776055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17749024434344029814368073 13311768325758022360776055)
  ·
    refine ⟨19967652488637033541164083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13311768325758022360776055 19967652488637033541164083)
    ·
      refine ⟨29951478732955550311746125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19967652488637033541164083 29951478732955550311746125)
      ·
        refine ⟨11231804524858331366904797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29951478732955550311746125 11231804524858331366904797)
        ·
          refine ⟨4211926696821874262589299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11231804524858331366904797 4211926696821874262589299)
          ·
            refine ⟨6317890045232811393883949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4211926696821874262589299 6317890045232811393883949)
            ·
              refine ⟨2369208766962304272706481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6317890045232811393883949 2369208766962304272706481)
              ·
                refine ⟨1776906575221728204529861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2369208766962304272706481 1776906575221728204529861)
                ·
                  refine ⟨333169982854074038349349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1776906575221728204529861 333169982854074038349349)
                  ·
                    rfl

theorem cell20_729952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 2, 4].length) (baseStart_729952 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_729952 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_729952 prefixEnd_729952 := by exact prefixLift 729952
  have htrace : WordTrace (prefixWord ++ tailWord_729952) baseStart_729952 baseEnd_729952 := by
    simpa [prefixWord, tailWord_729952, baseEnd_729952] using wordTrace_append hprefix tailTrace_729952
  have hstable : (prefixWord ++ tailWord_729952).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729952).length < 2 ^ (prefixWord ++ tailWord_729952).sum := by decide
  have hdescent : baseEnd_729952 < baseStart_729952 := by decide
  rcases family_descends (prefixWord ++ tailWord_729952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729969 : List Nat := [1, 2, 2, 2, 1, 4, 1, 5, 2]
def baseStart_729969 : Nat := 118140960795 + 729969 * 2 ^ 59
def prefixEnd_729969 : Nat := 4983230072969 + 3 ^ 40 * 729969 * 2
def baseEnd_729969 : Nat := 333177742117297534782613

theorem tailTrace_729969 : CollatzResearch.WordTrace tailWord_729969 prefixEnd_729969 333177742117297534782613 := by
  unfold tailWord_729969
  simp only [CollatzResearch.WordTrace]
  refine ⟨26624156692454456624920961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17749437794969637749947307 26624156692454456624920961)
  ·
    refine ⟨19968117519340842468690721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26624156692454456624920961 19968117519340842468690721)
    ·
      refine ⟨14976088139505631851518041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19968117519340842468690721 14976088139505631851518041)
      ·
        refine ⟨11232066104629223888638531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14976088139505631851518041 11232066104629223888638531)
        ·
          refine ⟨16848099156943835832957797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11232066104629223888638531 16848099156943835832957797)
          ·
            refine ⟨3159018591926969218679587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16848099156943835832957797 3159018591926969218679587)
            ·
              refine ⟨4738527887890453828019381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3159018591926969218679587 4738527887890453828019381)
              ·
                refine ⟨444236989489730046376817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4738527887890453828019381 444236989489730046376817)
                ·
                  refine ⟨333177742117297534782613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 444236989489730046376817 333177742117297534782613)
                  ·
                    rfl

theorem cell20_729969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 5, 2].length) (baseStart_729969 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_729969 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_729969 prefixEnd_729969 := by exact prefixLift 729969
  have htrace : WordTrace (prefixWord ++ tailWord_729969) baseStart_729969 baseEnd_729969 := by
    simpa [prefixWord, tailWord_729969, baseEnd_729969] using wordTrace_append hprefix tailTrace_729969
  have hstable : (prefixWord ++ tailWord_729969).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729969).length < 2 ^ (prefixWord ++ tailWord_729969).sum := by decide
  have hdescent : baseEnd_729969 < baseStart_729969 := by decide
  rcases family_descends (prefixWord ++ tailWord_729969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729983 : List Nat := [1, 1, 2, 2, 1, 1, 7, 2, 3]
def baseStart_729983 : Nat := 118140960795 + 729983 * 2 ^ 59
def prefixEnd_729983 : Nat := 4983230072969 + 3 ^ 40 * 729983 * 2
def baseEnd_729983 : Nat := 333184132098775708315889

theorem tailTrace_729983 : CollatzResearch.WordTrace tailWord_729983 prefixEnd_729983 333184132098775708315889 := by
  unfold tailWord_729983
  simp only [CollatzResearch.WordTrace]
  refine ⟨26624667314403737015930603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17749778209602491343953735 26624667314403737015930603)
  ·
    refine ⟨39937000971605605523895905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26624667314403737015930603 39937000971605605523895905)
    ·
      refine ⟨29952750728704204142921929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39937000971605605523895905 29952750728704204142921929)
      ·
        refine ⟨22464563046528153107191447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29952750728704204142921929 22464563046528153107191447)
        ·
          refine ⟨33696844569792229660787171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22464563046528153107191447 33696844569792229660787171)
          ·
            refine ⟨50545266854688344491180757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33696844569792229660787171 50545266854688344491180757)
            ·
              refine ⟨1184654691906758074012049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 50545266854688344491180757 1184654691906758074012049)
              ·
                refine ⟨888491018930068555509037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1184654691906758074012049 888491018930068555509037)
                ·
                  refine ⟨333184132098775708315889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 888491018930068555509037 333184132098775708315889)
                  ·
                    rfl

theorem cell20_729983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 2, 3].length) (baseStart_729983 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_729983 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_729983 prefixEnd_729983 := by exact prefixLift 729983
  have htrace : WordTrace (prefixWord ++ tailWord_729983) baseStart_729983 baseEnd_729983 := by
    simpa [prefixWord, tailWord_729983, baseEnd_729983] using wordTrace_append hprefix tailTrace_729983
  have hstable : (prefixWord ++ tailWord_729983).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729983).length < 2 ^ (prefixWord ++ tailWord_729983).sum := by decide
  have hdescent : baseEnd_729983 < baseStart_729983 := by decide
  rcases family_descends (prefixWord ++ tailWord_729983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730010 : List Nat := [3, 1, 1, 4, 4, 1, 2, 4]
def baseStart_730010 : Nat := 118140960795 + 730010 * 2 ^ 59
def prefixEnd_730010 : Nat := 4983230072969 + 3 ^ 40 * 730010 * 2
def baseEnd_730010 : Nat := 111065485211494538138593

theorem tailTrace_730010 : CollatzResearch.WordTrace tailWord_730010 prefixEnd_730010 111065485211494538138593 := by
  unfold tailWord_730010
  simp only [CollatzResearch.WordTrace]
  refine ⟨6656413021326480156790871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17750434723537280418108989 6656413021326480156790871)
  ·
    refine ⟨9984619531989720235186307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6656413021326480156790871 9984619531989720235186307)
    ·
      refine ⟨14976929297984580352779461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9984619531989720235186307 14976929297984580352779461)
      ·
        refine ⟨2808174243372108816146149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14976929297984580352779461 2808174243372108816146149)
        ·
          refine ⟨526532670632270403027403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2808174243372108816146149 526532670632270403027403)
          ·
            refine ⟨789799005948405604541105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 526532670632270403027403 789799005948405604541105)
            ·
              refine ⟨592349254461304203405829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 789799005948405604541105 592349254461304203405829)
              ·
                refine ⟨111065485211494538138593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 592349254461304203405829 111065485211494538138593)
                ·
                  rfl

theorem cell20_730010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 2, 4].length) (baseStart_730010 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_730010 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_730010 prefixEnd_730010 := by exact prefixLift 730010
  have htrace : WordTrace (prefixWord ++ tailWord_730010) baseStart_730010 baseEnd_730010 := by
    simpa [prefixWord, tailWord_730010, baseEnd_730010] using wordTrace_append hprefix tailTrace_730010
  have hstable : (prefixWord ++ tailWord_730010).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730010).length < 2 ^ (prefixWord ++ tailWord_730010).sum := by decide
  have hdescent : baseEnd_730010 < baseStart_730010 := by decide
  rcases family_descends (prefixWord ++ tailWord_730010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730042 : List Nat := [3, 1, 1, 1, 2, 1, 3, 3, 5]
def baseStart_730042 : Nat := 118140960795 + 730042 * 2 ^ 59
def prefixEnd_730042 : Nat := 4983230072969 + 3 ^ 40 * 730042 * 2
def baseEnd_730042 : Nat := 333211061306433725348981

theorem tailTrace_730042 : CollatzResearch.WordTrace tailWord_730042 prefixEnd_730042 333211061306433725348981 := by
  unfold tailWord_730042
  simp only [CollatzResearch.WordTrace]
  refine ⟨6656704805297497523082095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17751212814126660061552253 6656704805297497523082095)
  ·
    refine ⟨9985057207946246284623143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6656704805297497523082095 9985057207946246284623143)
    ·
      refine ⟨14977585811919369426934715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9985057207946246284623143 14977585811919369426934715)
      ·
        refine ⟨22466378717879054140402073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14977585811919369426934715 22466378717879054140402073)
        ·
          refine ⟨16849784038409290605301555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22466378717879054140402073 16849784038409290605301555)
          ·
            refine ⟨25274676057613935907952333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16849784038409290605301555 25274676057613935907952333)
            ·
              refine ⟨9478003521605225965482125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25274676057613935907952333 9478003521605225965482125)
              ·
                refine ⟨3554251320601959737055797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9478003521605225965482125 3554251320601959737055797)
                ·
                  refine ⟨333211061306433725348981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3554251320601959737055797 333211061306433725348981)
                  ·
                    rfl

theorem cell20_730042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 5].length) (baseStart_730042 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_730042 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_730042 prefixEnd_730042 := by exact prefixLift 730042
  have htrace : WordTrace (prefixWord ++ tailWord_730042) baseStart_730042 baseEnd_730042 := by
    simpa [prefixWord, tailWord_730042, baseEnd_730042] using wordTrace_append hprefix tailTrace_730042
  have hstable : (prefixWord ++ tailWord_730042).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730042).length < 2 ^ (prefixWord ++ tailWord_730042).sum := by decide
  have hdescent : baseEnd_730042 < baseStart_730042 := by decide
  rcases family_descends (prefixWord ++ tailWord_730042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730059 : List Nat := [1, 1, 1, 1, 3, 6, 1, 3, 3]
def baseStart_730059 : Nat := 118140960795 + 730059 * 2 ^ 59
def prefixEnd_730059 : Nat := 4983230072969 + 3 ^ 40 * 730059 * 2
def baseEnd_730059 : Nat := 333218820569657221782245

theorem tailTrace_730059 : CollatzResearch.WordTrace tailWord_730059 prefixEnd_730059 333218820569657221782245 := by
  unfold tailWord_730059
  simp only [CollatzResearch.WordTrace]
  refine ⟨26627439262128401995697231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17751626174752267997131487 26627439262128401995697231)
  ·
    refine ⟨39941158893192602993545847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26627439262128401995697231 39941158893192602993545847)
    ·
      refine ⟨59911738339788904490318771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39941158893192602993545847 59911738339788904490318771)
      ·
        refine ⟨89867607509683356735478157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59911738339788904490318771 89867607509683356735478157)
        ·
          refine ⟨33700352816131258775804309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89867607509683356735478157 33700352816131258775804309)
          ·
            refine ⟨1579704038256152755115827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 33700352816131258775804309 1579704038256152755115827)
            ·
              refine ⟨2369556057384229132673741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1579704038256152755115827 2369556057384229132673741)
              ·
                refine ⟨888583521519085924752653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2369556057384229132673741 888583521519085924752653)
                ·
                  refine ⟨333218820569657221782245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 888583521519085924752653 333218820569657221782245)
                  ·
                    rfl

theorem cell20_730059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 3, 3].length) (baseStart_730059 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_730059 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_730059 prefixEnd_730059 := by exact prefixLift 730059
  have htrace : WordTrace (prefixWord ++ tailWord_730059) baseStart_730059 baseEnd_730059 := by
    simpa [prefixWord, tailWord_730059, baseEnd_730059] using wordTrace_append hprefix tailTrace_730059
  have hstable : (prefixWord ++ tailWord_730059).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730059).length < 2 ^ (prefixWord ++ tailWord_730059).sum := by decide
  have hdescent : baseEnd_730059 < baseStart_730059 := by decide
  rcases family_descends (prefixWord ++ tailWord_730059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730073 : List Nat := [1, 2, 1, 2, 5, 1, 2, 6]
def baseStart_730073 : Nat := 118140960795 + 730073 * 2 ^ 59
def prefixEnd_730073 : Nat := 4983230072969 + 3 ^ 40 * 730073 * 2
def baseEnd_730073 : Nat := 111075070183711798438507

theorem tailTrace_730073 : CollatzResearch.WordTrace tailWord_730073 prefixEnd_730073 111075070183711798438507 := by
  unfold tailWord_730073
  simp only [CollatzResearch.WordTrace]
  refine ⟨26627949884077682386706873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17751966589385121591137915 26627949884077682386706873)
  ·
    refine ⟨19970962413058261790030155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26627949884077682386706873 19970962413058261790030155)
    ·
      refine ⟨29956443619587392685045233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19970962413058261790030155 29956443619587392685045233)
      ·
        refine ⟨22467332714690544513783925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29956443619587392685045233 22467332714690544513783925)
        ·
          refine ⟨2106312442002238548167243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22467332714690544513783925 2106312442002238548167243)
          ·
            refine ⟨3159468663003357822250865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2106312442002238548167243 3159468663003357822250865)
            ·
              refine ⟨2369601497252518366688149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3159468663003357822250865 2369601497252518366688149)
              ·
                refine ⟨111075070183711798438507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2369601497252518366688149 111075070183711798438507)
                ·
                  rfl

theorem cell20_730073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 6].length) (baseStart_730073 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_730073 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_730073 prefixEnd_730073 := by exact prefixLift 730073
  have htrace : WordTrace (prefixWord ++ tailWord_730073) baseStart_730073 baseEnd_730073 := by
    simpa [prefixWord, tailWord_730073, baseEnd_730073] using wordTrace_append hprefix tailTrace_730073
  have hstable : (prefixWord ++ tailWord_730073).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730073).length < 2 ^ (prefixWord ++ tailWord_730073).sum := by decide
  have hdescent : baseEnd_730073 < baseStart_730073 := by decide
  rcases family_descends (prefixWord ++ tailWord_730073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730083 : List Nat := [1, 1, 1, 6, 1, 1, 2, 5, 2]
def baseStart_730083 : Nat := 118140960795 + 730083 * 2 ^ 59
def prefixEnd_730083 : Nat := 4983230072969 + 3 ^ 40 * 730083 * 2
def baseEnd_730083 : Nat := 333229774823619804982147

theorem tailTrace_730083 : CollatzResearch.WordTrace tailWord_730083 prefixEnd_730083 333229774823619804982147 := by
  unfold tailWord_730083
  simp only [CollatzResearch.WordTrace]
  refine ⟨26628314614041454094570903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17752209742694302729713935 26628314614041454094570903)
  ·
    refine ⟨39942471921062181141856355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26628314614041454094570903 39942471921062181141856355)
    ·
      refine ⟨59913707881593271712784533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39942471921062181141856355 59913707881593271712784533)
      ·
        refine ⟨2808455056949684611536775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 59913707881593271712784533 2808455056949684611536775)
        ·
          refine ⟨4212682585424526917305163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2808455056949684611536775 4212682585424526917305163)
          ·
            refine ⟨6319023878136790375957745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4212682585424526917305163 6319023878136790375957745)
            ·
              refine ⟨4739267908602592781968309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6319023878136790375957745 4739267908602592781968309)
              ·
                refine ⟨444306366431493073309529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4739267908602592781968309 444306366431493073309529)
                ·
                  refine ⟨333229774823619804982147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 444306366431493073309529 333229774823619804982147)
                  ·
                    rfl

theorem cell20_730083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 5, 2].length) (baseStart_730083 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_730083 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_730083 prefixEnd_730083 := by exact prefixLift 730083
  have htrace : WordTrace (prefixWord ++ tailWord_730083) baseStart_730083 baseEnd_730083 := by
    simpa [prefixWord, tailWord_730083, baseEnd_730083] using wordTrace_append hprefix tailTrace_730083
  have hstable : (prefixWord ++ tailWord_730083).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730083).length < 2 ^ (prefixWord ++ tailWord_730083).sum := by decide
  have hdescent : baseEnd_730083 < baseStart_730083 := by decide
  rcases family_descends (prefixWord ++ tailWord_730083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730097 : List Nat := [1, 2, 2, 2, 4, 1, 1, 4, 3]
def baseStart_730097 : Nat := 118140960795 + 730097 * 2 ^ 59
def prefixEnd_730097 : Nat := 4983230072969 + 3 ^ 40 * 730097 * 2
def baseEnd_730097 : Nat := 333236164805097978515423

theorem tailTrace_730097 : CollatzResearch.WordTrace tailWord_730097 prefixEnd_730097 333236164805097978515423 := by
  unfold tailWord_730097
  simp only [CollatzResearch.WordTrace]
  refine ⟨26628825235990734485580545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17752550157327156323720363 26628825235990734485580545)
  ·
    refine ⟨19971618926993050864185409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26628825235990734485580545 19971618926993050864185409)
    ·
      refine ⟨14978714195244788148139057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19971618926993050864185409 14978714195244788148139057)
      ·
        refine ⟨11234035646433591111104293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14978714195244788148139057 11234035646433591111104293)
        ·
          refine ⟨2106381683706298333332055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11234035646433591111104293 2106381683706298333332055)
          ·
            refine ⟨3159572525559447499998083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2106381683706298333332055 3159572525559447499998083)
            ·
              refine ⟨4739358788339171249997125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3159572525559447499998083 4739358788339171249997125)
              ·
                refine ⟨888629772813594609374461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4739358788339171249997125 888629772813594609374461)
                ·
                  refine ⟨333236164805097978515423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 888629772813594609374461 333236164805097978515423)
                  ·
                    rfl

theorem cell20_730097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 4, 3].length) (baseStart_730097 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_730097 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_730097 prefixEnd_730097 := by exact prefixLift 730097
  have htrace : WordTrace (prefixWord ++ tailWord_730097) baseStart_730097 baseEnd_730097 := by
    simpa [prefixWord, tailWord_730097, baseEnd_730097] using wordTrace_append hprefix tailTrace_730097
  have hstable : (prefixWord ++ tailWord_730097).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730097).length < 2 ^ (prefixWord ++ tailWord_730097).sum := by decide
  have hdescent : baseEnd_730097 < baseStart_730097 := by decide
  rcases family_descends (prefixWord ++ tailWord_730097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730156 : List Nat := [2, 2, 1, 1, 1, 2, 5, 1, 5]
def baseStart_730156 : Nat := 118140960795 + 730156 * 2 ^ 59
def prefixEnd_730156 : Nat := 4983230072969 + 3 ^ 40 * 730156 * 2
def baseEnd_730156 : Nat := 333263094012755995548515

theorem tailTrace_730156 : CollatzResearch.WordTrace tailWord_730156 prefixEnd_730156 333263094012755995548515 := by
  unfold tailWord_730156
  simp only [CollatzResearch.WordTrace]
  refine ⟨13315488571388493780989161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17753984761851325041318881 13315488571388493780989161)
  ·
    refine ⟨9986616428541370335741871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13315488571388493780989161 9986616428541370335741871)
    ·
      refine ⟨14979924642812055503612807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9986616428541370335741871 14979924642812055503612807)
      ·
        refine ⟨22469886964218083255419211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14979924642812055503612807 22469886964218083255419211)
        ·
          refine ⟨33704830446327124883128817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22469886964218083255419211 33704830446327124883128817)
          ·
            refine ⟨25278622834745343662346613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33704830446327124883128817 25278622834745343662346613)
            ·
              refine ⟨2369870890757375968344995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25278622834745343662346613 2369870890757375968344995)
              ·
                refine ⟨3554806336136063952517493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2369870890757375968344995 3554806336136063952517493)
                ·
                  refine ⟨333263094012755995548515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3554806336136063952517493 333263094012755995548515)
                  ·
                    rfl

theorem cell20_730156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 5].length) (baseStart_730156 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_730156 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_730156 prefixEnd_730156 := by exact prefixLift 730156
  have htrace : WordTrace (prefixWord ++ tailWord_730156) baseStart_730156 baseEnd_730156 := by
    simpa [prefixWord, tailWord_730156, baseEnd_730156] using wordTrace_append hprefix tailTrace_730156
  have hstable : (prefixWord ++ tailWord_730156).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730156).length < 2 ^ (prefixWord ++ tailWord_730156).sum := by decide
  have hdescent : baseEnd_730156 < baseStart_730156 := by decide
  rcases family_descends (prefixWord ++ tailWord_730156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730266 : List Nat := [3, 1, 1, 5, 1, 2, 2, 2, 3]
def baseStart_730266 : Nat := 118140960795 + 730266 * 2 ^ 59
def prefixEnd_730266 : Nat := 4983230072969 + 3 ^ 40 * 730266 * 2
def baseEnd_730266 : Nat := 333313301010084501881399

theorem tailTrace_730266 : CollatzResearch.WordTrace tailWord_730266 prefixEnd_730266 333313301010084501881399 := by
  unfold tailWord_730266
  simp only [CollatzResearch.WordTrace]
  refine ⟨6658747293094619087120663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17756659448252317565655101 6658747293094619087120663)
  ·
    refine ⟨9988120939641928630680995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6658747293094619087120663 9988120939641928630680995)
    ·
      refine ⟨14982181409462892946021493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9988120939641928630680995 14982181409462892946021493)
      ·
        refine ⟨1404579507137146213689515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14982181409462892946021493 1404579507137146213689515)
        ·
          refine ⟨2106869260705719320534273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1404579507137146213689515 2106869260705719320534273)
          ·
            refine ⟨1580151945529289490400705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2106869260705719320534273 1580151945529289490400705)
            ·
              refine ⟨1185113959146967117800529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1580151945529289490400705 1185113959146967117800529)
              ·
                refine ⟨888835469360225338350397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1185113959146967117800529 888835469360225338350397)
                ·
                  refine ⟨333313301010084501881399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 888835469360225338350397 333313301010084501881399)
                  ·
                    rfl

theorem cell20_730266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 2, 3].length) (baseStart_730266 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_730266 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_730266 prefixEnd_730266 := by exact prefixLift 730266
  have htrace : WordTrace (prefixWord ++ tailWord_730266) baseStart_730266 baseEnd_730266 := by
    simpa [prefixWord, tailWord_730266, baseEnd_730266] using wordTrace_append hprefix tailTrace_730266
  have hstable : (prefixWord ++ tailWord_730266).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730266).length < 2 ^ (prefixWord ++ tailWord_730266).sum := by decide
  have hdescent : baseEnd_730266 < baseStart_730266 := by decide
  rcases family_descends (prefixWord ++ tailWord_730266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730273 : List Nat := [1, 2, 3, 3, 1, 1, 3, 4, 2]
def baseStart_730273 : Nat := 118140960795 + 730273 * 2 ^ 59
def prefixEnd_730273 : Nat := 4983230072969 + 3 ^ 40 * 730273 * 2
def baseEnd_730273 : Nat := 333316496000823588648037

theorem tailTrace_730273 : CollatzResearch.WordTrace tailWord_730273 prefixEnd_730273 333316496000823588648037 := by
  unfold tailWord_730273
  simp only [CollatzResearch.WordTrace]
  refine ⟨26635244483353116543987473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17756829655568744362658315 26635244483353116543987473)
  ·
    refine ⟨19976433362514837407990605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26635244483353116543987473 19976433362514837407990605)
    ·
      refine ⟨7491162510943064027996477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19976433362514837407990605 7491162510943064027996477)
      ·
        refine ⟨2809185941603649010498679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7491162510943064027996477 2809185941603649010498679)
        ·
          refine ⟨4213778912405473515748019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2809185941603649010498679 4213778912405473515748019)
          ·
            refine ⟨6320668368608210273622029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4213778912405473515748019 6320668368608210273622029)
            ·
              refine ⟨2370250638228078852608261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6320668368608210273622029 2370250638228078852608261)
              ·
                refine ⟨444421994667764784864049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2370250638228078852608261 444421994667764784864049)
                ·
                  refine ⟨333316496000823588648037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 444421994667764784864049 333316496000823588648037)
                  ·
                    rfl

theorem cell20_730273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 4, 2].length) (baseStart_730273 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_730273 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_730273 prefixEnd_730273 := by exact prefixLift 730273
  have htrace : WordTrace (prefixWord ++ tailWord_730273) baseStart_730273 baseEnd_730273 := by
    simpa [prefixWord, tailWord_730273, baseEnd_730273] using wordTrace_append hprefix tailTrace_730273
  have hstable : (prefixWord ++ tailWord_730273).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730273).length < 2 ^ (prefixWord ++ tailWord_730273).sum := by decide
  have hdescent : baseEnd_730273 < baseStart_730273 := by decide
  rcases family_descends (prefixWord ++ tailWord_730273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730284 : List Nat := [2, 2, 1, 1, 1, 1, 1, 11]
def baseStart_730284 : Nat := 118140960795 + 730284 * 2 ^ 59
def prefixEnd_730284 : Nat := 4983230072969 + 3 ^ 40 * 730284 * 2
def baseEnd_730284 : Nat := 111107172233518813093775

theorem tailTrace_730284 : CollatzResearch.WordTrace tailWord_730284 prefixEnd_730284 111107172233518813093775 := by
  unfold tailWord_730284
  simp only [CollatzResearch.WordTrace]
  refine ⟨13317822843156632711318953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17757097124208843615091937 13317822843156632711318953)
  ·
    refine ⟨9988367132367474533489215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13317822843156632711318953 9988367132367474533489215)
    ·
      refine ⟨14982550698551211800233823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9988367132367474533489215 14982550698551211800233823)
      ·
        refine ⟨22473826047826817700350735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14982550698551211800233823 22473826047826817700350735)
        ·
          refine ⟨33710739071740226550526103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22473826047826817700350735 33710739071740226550526103)
          ·
            refine ⟨50566108607610339825789155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33710739071740226550526103 50566108607610339825789155)
            ·
              refine ⟨75849162911415509738683733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50566108607610339825789155 75849162911415509738683733)
              ·
                refine ⟨111107172233518813093775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 75849162911415509738683733 111107172233518813093775)
                ·
                  rfl

theorem cell20_730284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 11].length) (baseStart_730284 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_730284 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_730284 prefixEnd_730284 := by exact prefixLift 730284
  have htrace : WordTrace (prefixWord ++ tailWord_730284) baseStart_730284 baseEnd_730284 := by
    simpa [prefixWord, tailWord_730284, baseEnd_730284] using wordTrace_append hprefix tailTrace_730284
  have hstable : (prefixWord ++ tailWord_730284).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730284).length < 2 ^ (prefixWord ++ tailWord_730284).sum := by decide
  have hdescent : baseEnd_730284 < baseStart_730284 := by decide
  rcases family_descends (prefixWord ++ tailWord_730284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730317 : List Nat := [1, 6, 2, 2, 2, 1, 1, 2, 3]
def baseStart_730317 : Nat := 118140960795 + 730317 * 2 ^ 59
def prefixEnd_730317 : Nat := 4983230072969 + 3 ^ 40 * 730317 * 2
def baseEnd_730317 : Nat := 333336578799754991181191

theorem tailTrace_730317 : CollatzResearch.WordTrace tailWord_730317 prefixEnd_730317 333336578799754991181191 := by
  unfold tailWord_730317
  simp only [CollatzResearch.WordTrace]
  refine ⟨26636849295193712058589205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17757899530129141372392803 26636849295193712058589205)
  ·
    refine ⟨1248602310712205252746369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 26636849295193712058589205 1248602310712205252746369)
    ·
      refine ⟨936451733034153939559777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1248602310712205252746369 936451733034153939559777)
      ·
        refine ⟨702338799775615454669833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 936451733034153939559777 702338799775615454669833)
        ·
          refine ⟨526754099831711591002375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 702338799775615454669833 526754099831711591002375)
          ·
            refine ⟨790131149747567386503563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 526754099831711591002375 790131149747567386503563)
            ·
              refine ⟨1185196724621351079755345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 790131149747567386503563 1185196724621351079755345)
              ·
                refine ⟨888897543466013309816509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1185196724621351079755345 888897543466013309816509)
                ·
                  refine ⟨333336578799754991181191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 888897543466013309816509 333336578799754991181191)
                  ·
                    rfl

theorem cell20_730317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_730317 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_730317 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_730317 prefixEnd_730317 := by exact prefixLift 730317
  have htrace : WordTrace (prefixWord ++ tailWord_730317) baseStart_730317 baseEnd_730317 := by
    simpa [prefixWord, tailWord_730317, baseEnd_730317] using wordTrace_append hprefix tailTrace_730317
  have hstable : (prefixWord ++ tailWord_730317).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730317).length < 2 ^ (prefixWord ++ tailWord_730317).sum := by decide
  have hdescent : baseEnd_730317 < baseStart_730317 := by decide
  rcases family_descends (prefixWord ++ tailWord_730317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730325 : List Nat := [1, 3, 2, 4, 1, 2, 1, 1, 5]
def baseStart_730325 : Nat := 118140960795 + 730325 * 2 ^ 59
def prefixEnd_730325 : Nat := 4983230072969 + 3 ^ 40 * 730325 * 2
def baseEnd_730325 : Nat := 333340230217742518914491

theorem tailTrace_730325 : CollatzResearch.WordTrace tailWord_730325 prefixEnd_730325 333340230217742518914491 := by
  unfold tailWord_730325
  simp only [CollatzResearch.WordTrace]
  refine ⟨26637141079164729424880429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17758094052776486283253619 26637141079164729424880429)
  ·
    refine ⟨9988927904686773534330161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26637141079164729424880429 9988927904686773534330161)
    ·
      refine ⟨7491695928515080150747621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9988927904686773534330161 7491695928515080150747621)
      ·
        refine ⟨1404692986596577528265179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7491695928515080150747621 1404692986596577528265179)
        ·
          refine ⟨2107039479894866292397769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1404692986596577528265179 2107039479894866292397769)
          ·
            refine ⟨1580279609921149719298327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2107039479894866292397769 1580279609921149719298327)
            ·
              refine ⟨2370419414881724578947491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1580279609921149719298327 2370419414881724578947491)
              ·
                refine ⟨3555629122322586868421237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2370419414881724578947491 3555629122322586868421237)
                ·
                  refine ⟨333340230217742518914491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3555629122322586868421237 333340230217742518914491)
                  ·
                    rfl

theorem cell20_730325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 5].length) (baseStart_730325 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_730325 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_730325 prefixEnd_730325 := by exact prefixLift 730325
  have htrace : WordTrace (prefixWord ++ tailWord_730325) baseStart_730325 baseEnd_730325 := by
    simpa [prefixWord, tailWord_730325, baseEnd_730325] using wordTrace_append hprefix tailTrace_730325
  have hstable : (prefixWord ++ tailWord_730325).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730325).length < 2 ^ (prefixWord ++ tailWord_730325).sum := by decide
  have hdescent : baseEnd_730325 < baseStart_730325 := by decide
  rcases family_descends (prefixWord ++ tailWord_730325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730366 : List Nat := [4, 2, 2, 1, 1, 2, 3, 3, 2]
def baseStart_730366 : Nat := 118140960795 + 730366 * 2 ^ 59
def prefixEnd_730366 : Nat := 4983230072969 + 3 ^ 40 * 730366 * 2
def baseEnd_730366 : Nat := 333358943734928598547657

theorem tailTrace_730366 : CollatzResearch.WordTrace tailWord_730366 prefixEnd_730366 333358943734928598547657 := by
  unfold tailWord_730366
  simp only [CollatzResearch.WordTrace]
  refine ⟨3329829559002024178390369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17759090981344128951415301 3329829559002024178390369)
  ·
    refine ⟨2497372169251518133792777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3329829559002024178390369 2497372169251518133792777)
    ·
      refine ⟨1873029126938638600344583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2497372169251518133792777 1873029126938638600344583)
      ·
        refine ⟨2809543690407957900516875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1873029126938638600344583 2809543690407957900516875)
        ·
          refine ⟨4214315535611936850775313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2809543690407957900516875 4214315535611936850775313)
          ·
            refine ⟨3160736651708952638081485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4214315535611936850775313 3160736651708952638081485)
            ·
              refine ⟨1185276244390857239280557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3160736651708952638081485 1185276244390857239280557)
              ·
                refine ⟨444478591646571464730209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1185276244390857239280557 444478591646571464730209)
                ·
                  refine ⟨333358943734928598547657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 444478591646571464730209 333358943734928598547657)
                  ·
                    rfl

theorem cell20_730366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 3, 2].length) (baseStart_730366 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_730366 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_730366 prefixEnd_730366 := by exact prefixLift 730366
  have htrace : WordTrace (prefixWord ++ tailWord_730366) baseStart_730366 baseEnd_730366 := by
    simpa [prefixWord, tailWord_730366, baseEnd_730366] using wordTrace_append hprefix tailTrace_730366
  have hstable : (prefixWord ++ tailWord_730366).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730366).length < 2 ^ (prefixWord ++ tailWord_730366).sum := by decide
  have hdescent : baseEnd_730366 < baseStart_730366 := by decide
  rcases family_descends (prefixWord ++ tailWord_730366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730397 : List Nat := [1, 4, 2, 3, 1, 3, 2, 1, 3]
def baseStart_730397 : Nat := 118140960795 + 730397 * 2 ^ 59
def prefixEnd_730397 : Nat := 4983230072969 + 3 ^ 40 * 730397 * 2
def baseEnd_730397 : Nat := 333373092979630268514197

theorem tailTrace_730397 : CollatzResearch.WordTrace tailWord_730397 prefixEnd_730397 333373092979630268514197 := by
  unfold tailWord_730397
  simp only [CollatzResearch.WordTrace]
  refine ⟨26639767134903885721501445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17759844756602590481000963 26639767134903885721501445)
  ·
    refine ⟨4994956337794478572781521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26639767134903885721501445 4994956337794478572781521)
    ·
      refine ⟨3746217253345858929586141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4994956337794478572781521 3746217253345858929586141)
      ·
        refine ⟨1404831470004697098594803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3746217253345858929586141 1404831470004697098594803)
        ·
          refine ⟨2107247205007045647892205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1404831470004697098594803 2107247205007045647892205)
          ·
            refine ⟨790217701877642117959577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2107247205007045647892205 790217701877642117959577)
            ·
              refine ⟨592663276408231588469683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 790217701877642117959577 592663276408231588469683)
              ·
                refine ⟨888994914612347382704525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 592663276408231588469683 888994914612347382704525)
                ·
                  refine ⟨333373092979630268514197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 888994914612347382704525 333373092979630268514197)
                  ·
                    rfl

theorem cell20_730397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 2, 1, 3].length) (baseStart_730397 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_730397 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_730397 prefixEnd_730397 := by exact prefixLift 730397
  have htrace : WordTrace (prefixWord ++ tailWord_730397) baseStart_730397 baseEnd_730397 := by
    simpa [prefixWord, tailWord_730397, baseEnd_730397] using wordTrace_append hprefix tailTrace_730397
  have hstable : (prefixWord ++ tailWord_730397).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730397).length < 2 ^ (prefixWord ++ tailWord_730397).sum := by decide
  have hdescent : baseEnd_730397 < baseStart_730397 := by decide
  rcases family_descends (prefixWord ++ tailWord_730397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730438 : List Nat := [6, 1, 1, 3, 1, 1, 1, 4, 2]
def baseStart_730438 : Nat := 118140960795 + 730438 * 2 ^ 59
def prefixEnd_730438 : Nat := 4983230072969 + 3 ^ 40 * 730438 * 2
def baseEnd_730438 : Nat := 333391806496816348147363

theorem tailTrace_730438 : CollatzResearch.WordTrace tailWord_730438 prefixEnd_730438 333391806496816348147363 := by
  unfold tailWord_730438
  simp only [CollatzResearch.WordTrace]
  refine ⟨832539453992354678866999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 17760841685170233149162645 832539453992354678866999)
  ·
    refine ⟨1248809180988532018300499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 832539453992354678866999 1248809180988532018300499)
    ·
      refine ⟨1873213771482798027450749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1248809180988532018300499 1873213771482798027450749)
      ·
        refine ⟨702455164306049260294031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1873213771482798027450749 702455164306049260294031)
        ·
          refine ⟨1053682746459073890441047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 702455164306049260294031 1053682746459073890441047)
          ·
            refine ⟨1580524119688610835661571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1053682746459073890441047 1580524119688610835661571)
            ·
              refine ⟨2370786179532916253492357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1580524119688610835661571 2370786179532916253492357)
              ·
                refine ⟨444522408662421797529817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2370786179532916253492357 444522408662421797529817)
                ·
                  refine ⟨333391806496816348147363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 444522408662421797529817 333391806496816348147363)
                  ·
                    rfl

theorem cell20_730438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_730438 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_730438 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_730438 prefixEnd_730438 := by exact prefixLift 730438
  have htrace : WordTrace (prefixWord ++ tailWord_730438) baseStart_730438 baseEnd_730438 := by
    simpa [prefixWord, tailWord_730438, baseEnd_730438] using wordTrace_append hprefix tailTrace_730438
  have hstable : (prefixWord ++ tailWord_730438).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730438).length < 2 ^ (prefixWord ++ tailWord_730438).sum := by decide
  have hdescent : baseEnd_730438 < baseStart_730438 := by decide
  rcases family_descends (prefixWord ++ tailWord_730438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730439 : List Nat := [1, 1, 4, 1, 2, 4, 2, 2, 3]
def baseStart_730439 : Nat := 118140960795 + 730439 * 2 ^ 59
def prefixEnd_730439 : Nat := 4983230072969 + 3 ^ 40 * 730439 * 2
def baseEnd_730439 : Nat := 333392262924064789114025

theorem tailTrace_730439 : CollatzResearch.WordTrace tailWord_730439 prefixEnd_730439 333392262924064789114025 := by
  unfold tailWord_730439
  simp only [CollatzResearch.WordTrace]
  refine ⟨26641299000751726894530371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17760866000501151263020247 26641299000751726894530371)
  ·
    refine ⟨39961948501127590341795557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26641299000751726894530371 39961948501127590341795557)
    ·
      refine ⟨7492865343961423189086667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39961948501127590341795557 7492865343961423189086667)
      ·
        refine ⟨11239298015942134783630001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7492865343961423189086667 11239298015942134783630001)
        ·
          refine ⟨8429473511956601087722501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11239298015942134783630001 8429473511956601087722501)
          ·
            refine ⟨1580526283491862703947969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8429473511956601087722501 1580526283491862703947969)
            ·
              refine ⟨1185394712618897027960977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1580526283491862703947969 1185394712618897027960977)
              ·
                refine ⟨889046034464172770970733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1185394712618897027960977 889046034464172770970733)
                ·
                  refine ⟨333392262924064789114025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 889046034464172770970733 333392262924064789114025)
                  ·
                    rfl

theorem cell20_730439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 2, 3].length) (baseStart_730439 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_730439 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_730439 prefixEnd_730439 := by exact prefixLift 730439
  have htrace : WordTrace (prefixWord ++ tailWord_730439) baseStart_730439 baseEnd_730439 := by
    simpa [prefixWord, tailWord_730439, baseEnd_730439] using wordTrace_append hprefix tailTrace_730439
  have hstable : (prefixWord ++ tailWord_730439).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730439).length < 2 ^ (prefixWord ++ tailWord_730439).sum := by decide
  have hdescent : baseEnd_730439 < baseStart_730439 := by decide
  rcases family_descends (prefixWord ++ tailWord_730439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730443 : List Nat := [1, 1, 1, 1, 3, 1, 1, 2, 9]
def baseStart_730443 : Nat := 118140960795 + 730443 * 2 ^ 59
def prefixEnd_730443 : Nat := 4983230072969 + 3 ^ 40 * 730443 * 2
def baseEnd_730443 : Nat := 333394088633058552980675

theorem tailTrace_730443 : CollatzResearch.WordTrace tailWord_730443 prefixEnd_730443 333394088633058552980675 := by
  unfold tailWord_730443
  simp only [CollatzResearch.WordTrace]
  refine ⟨26641444892737235577675983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17760963261824823718450655 26641444892737235577675983)
  ·
    refine ⟨39962167339105853366513975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26641444892737235577675983 39962167339105853366513975)
    ·
      refine ⟨59943251008658780049770963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39962167339105853366513975 59943251008658780049770963)
      ·
        refine ⟨89914876512988170074656445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59943251008658780049770963 89914876512988170074656445)
        ·
          refine ⟨33718078692370563777996167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89914876512988170074656445 33718078692370563777996167)
          ·
            refine ⟨50577118038555845666994251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33718078692370563777996167 50577118038555845666994251)
            ·
              refine ⟨75865677057833768500491377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50577118038555845666994251 75865677057833768500491377)
              ·
                refine ⟨56899257793375326375368533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75865677057833768500491377 56899257793375326375368533)
                ·
                  refine ⟨333394088633058552980675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 56899257793375326375368533 333394088633058552980675)
                  ·
                    rfl

theorem cell20_730443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 9].length) (baseStart_730443 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_730443 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_730443 prefixEnd_730443 := by exact prefixLift 730443
  have htrace : WordTrace (prefixWord ++ tailWord_730443) baseStart_730443 baseEnd_730443 := by
    simpa [prefixWord, tailWord_730443, baseEnd_730443] using wordTrace_append hprefix tailTrace_730443
  have hstable : (prefixWord ++ tailWord_730443).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730443).length < 2 ^ (prefixWord ++ tailWord_730443).sum := by decide
  have hdescent : baseEnd_730443 < baseStart_730443 := by decide
  rcases family_descends (prefixWord ++ tailWord_730443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730453 : List Nat := [1, 3, 2, 2, 3, 1, 3, 5]
def baseStart_730453 : Nat := 118140960795 + 730453 * 2 ^ 59
def prefixEnd_730453 : Nat := 4983230072969 + 3 ^ 40 * 730453 * 2
def baseEnd_730453 : Nat := 111132884301847654215767

theorem tailTrace_730453 : CollatzResearch.WordTrace tailWord_730453 prefixEnd_730453 111132884301847654215767 := by
  unfold tailWord_730453
  simp only [CollatzResearch.WordTrace]
  refine ⟨26641809622701007285540013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17761206415134004857026675 26641809622701007285540013)
  ·
    refine ⟨9990678608512877732077505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26641809622701007285540013 9990678608512877732077505)
    ·
      refine ⟨7493008956384658299058129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9990678608512877732077505 7493008956384658299058129)
      ·
        refine ⟨5619756717288493724293597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7493008956384658299058129 5619756717288493724293597)
        ·
          refine ⟨2107408768983185146610099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5619756717288493724293597 2107408768983185146610099)
          ·
            refine ⟨3161113153474777719915149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2107408768983185146610099 3161113153474777719915149)
            ·
              refine ⟨1185417432553041644968181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3161113153474777719915149 1185417432553041644968181)
              ·
                refine ⟨111132884301847654215767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1185417432553041644968181 111132884301847654215767)
                ·
                  rfl

theorem cell20_730453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 5].length) (baseStart_730453 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_730453 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_730453 prefixEnd_730453 := by exact prefixLift 730453
  have htrace : WordTrace (prefixWord ++ tailWord_730453) baseStart_730453 baseEnd_730453 := by
    simpa [prefixWord, tailWord_730453, baseEnd_730453] using wordTrace_append hprefix tailTrace_730453
  have hstable : (prefixWord ++ tailWord_730453).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730453).length < 2 ^ (prefixWord ++ tailWord_730453).sum := by decide
  have hdescent : baseEnd_730453 < baseStart_730453 := by decide
  rcases family_descends (prefixWord ++ tailWord_730453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730467 : List Nat := [1, 1, 1, 5, 2, 2, 1, 1, 6]
def baseStart_730467 : Nat := 118140960795 + 730467 * 2 ^ 59
def prefixEnd_730467 : Nat := 4983230072969 + 3 ^ 40 * 730467 * 2
def baseEnd_730467 : Nat := 333405042887021136180577

theorem tailTrace_730467 : CollatzResearch.WordTrace tailWord_730467 prefixEnd_730467 333405042887021136180577 := by
  unfold tailWord_730467
  simp only [CollatzResearch.WordTrace]
  refine ⟨26642320244650287676549655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17761546829766858451033103 26642320244650287676549655)
  ·
    refine ⟨39963480366975431514824483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26642320244650287676549655 39963480366975431514824483)
    ·
      refine ⟨59945220550463147272236725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39963480366975431514824483 59945220550463147272236725)
      ·
        refine ⟨5619864426605920056772193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59945220550463147272236725 5619864426605920056772193)
        ·
          refine ⟨4214898319954440042579145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5619864426605920056772193 4214898319954440042579145)
          ·
            refine ⟨3161173739965830031934359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4214898319954440042579145 3161173739965830031934359)
            ·
              refine ⟨4741760609948745047901539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3161173739965830031934359 4741760609948745047901539)
              ·
                refine ⟨7112640914923117571852309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4741760609948745047901539 7112640914923117571852309)
                ·
                  refine ⟨333405042887021136180577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7112640914923117571852309 333405042887021136180577)
                  ·
                    rfl

theorem cell20_730467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 6].length) (baseStart_730467 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_730467 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_730467 prefixEnd_730467 := by exact prefixLift 730467
  have htrace : WordTrace (prefixWord ++ tailWord_730467) baseStart_730467 baseEnd_730467 := by
    simpa [prefixWord, tailWord_730467, baseEnd_730467] using wordTrace_append hprefix tailTrace_730467
  have hstable : (prefixWord ++ tailWord_730467).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730467).length < 2 ^ (prefixWord ++ tailWord_730467).sum := by decide
  have hdescent : baseEnd_730467 < baseStart_730467 := by decide
  rcases family_descends (prefixWord ++ tailWord_730467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730556 : List Nat := [2, 2, 2, 4, 3, 1, 1, 1, 4]
def baseStart_730556 : Nat := 118140960795 + 730556 * 2 ^ 59
def prefixEnd_730556 : Nat := 4983230072969 + 3 ^ 40 * 730556 * 2
def baseEnd_730556 : Nat := 333445664912132382213547

theorem tailTrace_730556 : CollatzResearch.WordTrace tailWord_730556 prefixEnd_730556 333445664912132382213547 := by
  unfold tailWord_730556
  simp only [CollatzResearch.WordTrace]
  refine ⟨13322783170663927938269761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17763710894218570584359681 13322783170663927938269761)
  ·
    refine ⟨9992087377997945953702321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13322783170663927938269761 9992087377997945953702321)
    ·
      refine ⟨7494065533498459465276741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9992087377997945953702321 7494065533498459465276741)
      ·
        refine ⟨1405137287530961149739389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7494065533498459465276741 1405137287530961149739389)
        ·
          refine ⟨526926482824110431152271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1405137287530961149739389 526926482824110431152271)
          ·
            refine ⟨790389724236165646728407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 526926482824110431152271 790389724236165646728407)
            ·
              refine ⟨1185584586354248470092611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 790389724236165646728407 1185584586354248470092611)
              ·
                refine ⟨1778376879531372705138917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1185584586354248470092611 1778376879531372705138917)
                ·
                  refine ⟨333445664912132382213547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1778376879531372705138917 333445664912132382213547)
                  ·
                    rfl

theorem cell20_730556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 1, 4].length) (baseStart_730556 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_730556 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_730556 prefixEnd_730556 := by exact prefixLift 730556
  have htrace : WordTrace (prefixWord ++ tailWord_730556) baseStart_730556 baseEnd_730556 := by
    simpa [prefixWord, tailWord_730556, baseEnd_730556] using wordTrace_append hprefix tailTrace_730556
  have hstable : (prefixWord ++ tailWord_730556).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730556).length < 2 ^ (prefixWord ++ tailWord_730556).sum := by decide
  have hdescent : baseEnd_730556 < baseStart_730556 := by decide
  rcases family_descends (prefixWord ++ tailWord_730556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730560 : List Nat := [2, 1, 1, 2, 3, 1, 2, 6, 2]
def baseStart_730560 : Nat := 118140960795 + 730560 * 2 ^ 59
def prefixEnd_730560 : Nat := 4983230072969 + 3 ^ 40 * 730560 * 2
def baseEnd_730560 : Nat := 333447490621126146080197

theorem tailTrace_730560 : CollatzResearch.WordTrace tailWord_730560 prefixEnd_730560 333447490621126146080197 := by
  unfold tailWord_730560
  simp only [CollatzResearch.WordTrace]
  refine ⟨13322856116656682279842567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17763808155542243039790089 13322856116656682279842567)
  ·
    refine ⟨19984284174985023419763851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13322856116656682279842567 19984284174985023419763851)
    ·
      refine ⟨29976426262477535129645777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19984284174985023419763851 29976426262477535129645777)
      ·
        refine ⟨22482319696858151347234333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29976426262477535129645777 22482319696858151347234333)
        ·
          refine ⟨8430869886321806755212875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22482319696858151347234333 8430869886321806755212875)
          ·
            refine ⟨12646304829482710132819313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8430869886321806755212875 12646304829482710132819313)
            ·
              refine ⟨9484728622112032599614485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12646304829482710132819313 9484728622112032599614485)
              ·
                refine ⟨444596654161501528106929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9484728622112032599614485 444596654161501528106929)
                ·
                  refine ⟨333447490621126146080197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 444596654161501528106929 333447490621126146080197)
                  ·
                    rfl

theorem cell20_730560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 6, 2].length) (baseStart_730560 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_730560 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_730560 prefixEnd_730560 := by exact prefixLift 730560
  have htrace : WordTrace (prefixWord ++ tailWord_730560) baseStart_730560 baseEnd_730560 := by
    simpa [prefixWord, tailWord_730560, baseEnd_730560] using wordTrace_append hprefix tailTrace_730560
  have hstable : (prefixWord ++ tailWord_730560).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730560).length < 2 ^ (prefixWord ++ tailWord_730560).sum := by decide
  have hdescent : baseEnd_730560 < baseStart_730560 := by decide
  rcases family_descends (prefixWord ++ tailWord_730560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730562 : List Nat := [3, 5, 2, 1, 1, 2, 2, 1, 3]
def baseStart_730562 : Nat := 118140960795 + 730562 * 2 ^ 59
def prefixEnd_730562 : Nat := 4983230072969 + 3 ^ 40 * 730562 * 2
def baseEnd_730562 : Nat := 333448403475623028013523

theorem tailTrace_730562 : CollatzResearch.WordTrace tailWord_730562 prefixEnd_730562 333448403475623028013523 := by
  unfold tailWord_730562
  simp only [CollatzResearch.WordTrace]
  refine ⟨6661446294826529725314485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17763856786204079267505293 6661446294826529725314485)
  ·
    refine ⟨624510590139987161748233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6661446294826529725314485 624510590139987161748233)
    ·
      refine ⟨468382942604990371311175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 624510590139987161748233 468382942604990371311175)
      ·
        refine ⟨702574413907485556966763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 468382942604990371311175 702574413907485556966763)
        ·
          refine ⟨1053861620861228335450145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 702574413907485556966763 1053861620861228335450145)
          ·
            refine ⟨790396215645921251587609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1053861620861228335450145 790396215645921251587609)
            ·
              refine ⟨592797161734440938690707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 790396215645921251587609 592797161734440938690707)
              ·
                refine ⟨889195742601661408036061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 592797161734440938690707 889195742601661408036061)
                ·
                  refine ⟨333448403475623028013523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 889195742601661408036061 333448403475623028013523)
                  ·
                    rfl

theorem cell20_730562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_730562 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_730562 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_730562 prefixEnd_730562 := by exact prefixLift 730562
  have htrace : WordTrace (prefixWord ++ tailWord_730562) baseStart_730562 baseEnd_730562 := by
    simpa [prefixWord, tailWord_730562, baseEnd_730562] using wordTrace_append hprefix tailTrace_730562
  have hstable : (prefixWord ++ tailWord_730562).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730562).length < 2 ^ (prefixWord ++ tailWord_730562).sum := by decide
  have hdescent : baseEnd_730562 < baseStart_730562 := by decide
  rcases family_descends (prefixWord ++ tailWord_730562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730570 : List Nat := [3, 1, 2, 1, 2, 5, 2, 1, 3]
def baseStart_730570 : Nat := 118140960795 + 730570 * 2 ^ 59
def prefixEnd_730570 : Nat := 4983230072969 + 3 ^ 40 * 730570 * 2
def baseEnd_730570 : Nat := 333452054893610555746823

theorem tailTrace_730570 : CollatzResearch.WordTrace tailWord_730570 prefixEnd_730570 333452054893610555746823 := by
  unfold tailWord_730570
  simp only [CollatzResearch.WordTrace]
  refine ⟨6661519240819284066887291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17764051308851424178366109 6661519240819284066887291)
  ·
    refine ⟨9992278861228926100330937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6661519240819284066887291 9992278861228926100330937)
    ·
      refine ⟨7494209145921694575248203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9992278861228926100330937 7494209145921694575248203)
      ·
        refine ⟨11241313718882541862872305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7494209145921694575248203 11241313718882541862872305)
        ·
          refine ⟨8430985289161906397154229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11241313718882541862872305 8430985289161906397154229)
          ·
            refine ⟨790404870858928724733209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8430985289161906397154229 790404870858928724733209)
            ·
              refine ⟨592803653144196543549907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 790404870858928724733209 592803653144196543549907)
              ·
                refine ⟨889205479716294815324861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 592803653144196543549907 889205479716294815324861)
                ·
                  refine ⟨333452054893610555746823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 889205479716294815324861 333452054893610555746823)
                  ·
                    rfl

theorem cell20_730570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 2, 1, 3].length) (baseStart_730570 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_730570 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_730570 prefixEnd_730570 := by exact prefixLift 730570
  have htrace : WordTrace (prefixWord ++ tailWord_730570) baseStart_730570 baseEnd_730570 := by
    simpa [prefixWord, tailWord_730570, baseEnd_730570] using wordTrace_append hprefix tailTrace_730570
  have hstable : (prefixWord ++ tailWord_730570).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730570).length < 2 ^ (prefixWord ++ tailWord_730570).sum := by decide
  have hdescent : baseEnd_730570 < baseStart_730570 := by decide
  rcases family_descends (prefixWord ++ tailWord_730570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730581 : List Nat := [1, 3, 2, 3, 1, 1, 2, 1, 6]
def baseStart_730581 : Nat := 118140960795 + 730581 * 2 ^ 59
def prefixEnd_730581 : Nat := 4983230072969 + 3 ^ 40 * 730581 * 2
def baseEnd_730581 : Nat := 333457075593343406380111

theorem tailTrace_730581 : CollatzResearch.WordTrace tailWord_730581 prefixEnd_730581 333457075593343406380111 := by
  unfold tailWord_730581
  simp only [CollatzResearch.WordTrace]
  refine ⟨26646478166237285146199597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17764318777491523430799731 26646478166237285146199597)
  ·
    refine ⟨9992429312338981929824849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26646478166237285146199597 9992429312338981929824849)
    ·
      refine ⟨7494321984254236447368637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9992429312338981929824849 7494321984254236447368637)
      ·
        refine ⟨2810370744095338667763239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7494321984254236447368637 2810370744095338667763239)
        ·
          refine ⟨4215556116143008001644859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2810370744095338667763239 4215556116143008001644859)
          ·
            refine ⟨6323334174214512002467289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4215556116143008001644859 6323334174214512002467289)
            ·
              refine ⟨4742500630660884001850467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6323334174214512002467289 4742500630660884001850467)
              ·
                refine ⟨7113750945991326002775701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4742500630660884001850467 7113750945991326002775701)
                ·
                  refine ⟨333457075593343406380111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7113750945991326002775701 333457075593343406380111)
                  ·
                    rfl

theorem cell20_730581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 6].length) (baseStart_730581 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_730581 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_730581 prefixEnd_730581 := by exact prefixLift 730581
  have htrace : WordTrace (prefixWord ++ tailWord_730581) baseStart_730581 baseEnd_730581 := by
    simpa [prefixWord, tailWord_730581, baseEnd_730581] using wordTrace_append hprefix tailTrace_730581
  have hstable : (prefixWord ++ tailWord_730581).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730581).length < 2 ^ (prefixWord ++ tailWord_730581).sum := by decide
  have hdescent : baseEnd_730581 < baseStart_730581 := by decide
  rcases family_descends (prefixWord ++ tailWord_730581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730605 : List Nat := [1, 5, 1, 3, 2, 8]
def baseStart_730605 : Nat := 118140960795 + 730605 * 2 ^ 59
def prefixEnd_730605 : Nat := 4983230072969 + 3 ^ 40 * 730605 * 2
def baseEnd_730605 : Nat := 12350667772122444058519

theorem tailTrace_730605 : CollatzResearch.WordTrace tailWord_730605 prefixEnd_730605 12350667772122444058519 := by
  unfold tailWord_730605
  simp only [CollatzResearch.WordTrace]
  refine ⟨26647353518150337245073269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17764902345433558163382179 26647353518150337245073269)
  ·
    refine ⟨2498189392326594116725619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26647353518150337245073269 2498189392326594116725619)
    ·
      refine ⟨3747284088489891175088429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2498189392326594116725619 3747284088489891175088429)
      ·
        refine ⟨1405231533183709190658161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3747284088489891175088429 1405231533183709190658161)
        ·
          refine ⟨1053923649887781892993621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1405231533183709190658161 1053923649887781892993621)
          ·
            refine ⟨12350667772122444058519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1053923649887781892993621 12350667772122444058519)
            ·
              rfl

theorem cell20_730605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 8].length) (baseStart_730605 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_730605 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_730605 prefixEnd_730605 := by exact prefixLift 730605
  have htrace : WordTrace (prefixWord ++ tailWord_730605) baseStart_730605 baseEnd_730605 := by
    simpa [prefixWord, tailWord_730605, baseEnd_730605] using wordTrace_append hprefix tailTrace_730605
  have hstable : (prefixWord ++ tailWord_730605).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730605).length < 2 ^ (prefixWord ++ tailWord_730605).sum := by decide
  have hdescent : baseEnd_730605 < baseStart_730605 := by decide
  rcases family_descends (prefixWord ++ tailWord_730605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730636 : List Nat := [2, 2, 1, 2, 5, 1, 1, 2, 4]
def baseStart_730636 : Nat := 118140960795 + 730636 * 2 ^ 59
def prefixEnd_730636 : Nat := 4983230072969 + 3 ^ 40 * 730636 * 2
def baseEnd_730636 : Nat := 333482179092007659546553

theorem tailTrace_730636 : CollatzResearch.WordTrace tailWord_730636 prefixEnd_730636 333482179092007659546553 := by
  unfold tailWord_730636
  simp only [CollatzResearch.WordTrace]
  refine ⟨13324242090519014769725881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17765656120692019692967841 13324242090519014769725881)
  ·
    refine ⟨9993181567889261077294411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13324242090519014769725881 9993181567889261077294411)
    ·
      refine ⟨14989772351833891615941617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9993181567889261077294411 14989772351833891615941617)
      ·
        refine ⟨11242329263875418711956213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14989772351833891615941617 11242329263875418711956213)
        ·
          refine ⟨1053968368488320504245895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11242329263875418711956213 1053968368488320504245895)
          ·
            refine ⟨1580952552732480756368843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1053968368488320504245895 1580952552732480756368843)
            ·
              refine ⟨2371428829098721134553265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1580952552732480756368843 2371428829098721134553265)
              ·
                refine ⟨1778571621824040850914949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2371428829098721134553265 1778571621824040850914949)
                ·
                  refine ⟨333482179092007659546553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1778571621824040850914949 333482179092007659546553)
                  ·
                    rfl

theorem cell20_730636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 2, 4].length) (baseStart_730636 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_730636 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_730636 prefixEnd_730636 := by exact prefixLift 730636
  have htrace : WordTrace (prefixWord ++ tailWord_730636) baseStart_730636 baseEnd_730636 := by
    simpa [prefixWord, tailWord_730636, baseEnd_730636] using wordTrace_append hprefix tailTrace_730636
  have hstable : (prefixWord ++ tailWord_730636).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730636).length < 2 ^ (prefixWord ++ tailWord_730636).sum := by decide
  have hdescent : baseEnd_730636 < baseStart_730636 := by decide
  rcases family_descends (prefixWord ++ tailWord_730636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730643 : List Nat := [1, 1, 1, 2, 1, 7, 3, 4]
def baseStart_730643 : Nat := 118140960795 + 730643 * 2 ^ 59
def prefixEnd_730643 : Nat := 4983230072969 + 3 ^ 40 * 730643 * 2
def baseEnd_730643 : Nat := 111161791360915582104397

theorem tailTrace_730643 : CollatzResearch.WordTrace tailWord_730643 prefixEnd_730643 111161791360915582104397 := by
  unfold tailWord_730643
  simp only [CollatzResearch.WordTrace]
  refine ⟨26648739492012669734956583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17765826328008446489971055 26648739492012669734956583)
  ·
    refine ⟨39973109238019004602434875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26648739492012669734956583 39973109238019004602434875)
    ·
      refine ⟨59959663857028506903652313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39973109238019004602434875 59959663857028506903652313)
      ·
        refine ⟨44969747892771380177739235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59959663857028506903652313 44969747892771380177739235)
        ·
          refine ⟨67454621839157070266608853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44969747892771380177739235 67454621839157070266608853)
          ·
            refine ⟨1580967699355243834373645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 67454621839157070266608853 1580967699355243834373645)
            ·
              refine ⟨592862887258216437890117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1580967699355243834373645 592862887258216437890117)
              ·
                refine ⟨111161791360915582104397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 592862887258216437890117 111161791360915582104397)
                ·
                  rfl

theorem cell20_730643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 3, 4].length) (baseStart_730643 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_730643 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_730643 prefixEnd_730643 := by exact prefixLift 730643
  have htrace : WordTrace (prefixWord ++ tailWord_730643) baseStart_730643 baseEnd_730643 := by
    simpa [prefixWord, tailWord_730643, baseEnd_730643] using wordTrace_append hprefix tailTrace_730643
  have hstable : (prefixWord ++ tailWord_730643).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730643).length < 2 ^ (prefixWord ++ tailWord_730643).sum := by decide
  have hdescent : baseEnd_730643 < baseStart_730643 := by decide
  rcases family_descends (prefixWord ++ tailWord_730643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730653 : List Nat := [1, 4, 2, 2, 1, 1, 4, 3, 2]
def baseStart_730653 : Nat := 118140960795 + 730653 * 2 ^ 59
def prefixEnd_730653 : Nat := 4983230072969 + 3 ^ 40 * 730653 * 2
def baseEnd_730653 : Nat := 333489938355231155979817

theorem tailTrace_730653 : CollatzResearch.WordTrace tailWord_730653 prefixEnd_730653 333489938355231155979817 := by
  unfold tailWord_730653
  simp only [CollatzResearch.WordTrace]
  refine ⟨26649104221976441442820613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17766069481317627628547075 26649104221976441442820613)
  ·
    refine ⟨4996707041620582770528865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26649104221976441442820613 4996707041620582770528865)
    ·
      refine ⟨3747530281215437077896649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4996707041620582770528865 3747530281215437077896649)
      ·
        refine ⟨2810647710911577808422487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3747530281215437077896649 2810647710911577808422487)
        ·
          refine ⟨4215971566367366712633731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2810647710911577808422487 4215971566367366712633731)
          ·
            refine ⟨6323957349551050068950597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4215971566367366712633731 6323957349551050068950597)
            ·
              refine ⟨1185742003040821887928237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6323957349551050068950597 1185742003040821887928237)
              ·
                refine ⟨444653251140308207973089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1185742003040821887928237 444653251140308207973089)
                ·
                  refine ⟨333489938355231155979817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 444653251140308207973089 333489938355231155979817)
                  ·
                    rfl

theorem cell20_730653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 3, 2].length) (baseStart_730653 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_730653 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_730653 prefixEnd_730653 := by exact prefixLift 730653
  have htrace : WordTrace (prefixWord ++ tailWord_730653) baseStart_730653 baseEnd_730653 := by
    simpa [prefixWord, tailWord_730653, baseEnd_730653] using wordTrace_append hprefix tailTrace_730653
  have hstable : (prefixWord ++ tailWord_730653).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730653).length < 2 ^ (prefixWord ++ tailWord_730653).sum := by decide
  have hdescent : baseEnd_730653 < baseStart_730653 := by decide
  rcases family_descends (prefixWord ++ tailWord_730653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730684 : List Nat := [2, 2, 2, 2, 4, 1, 3, 1, 3]
def baseStart_730684 : Nat := 118140960795 + 730684 * 2 ^ 59
def prefixEnd_730684 : Nat := 4983230072969 + 3 ^ 40 * 730684 * 2
def baseEnd_730684 : Nat := 333504087599932825946357

theorem tailTrace_730684 : CollatzResearch.WordTrace tailWord_730684 prefixEnd_730684 333504087599932825946357 := by
  unfold tailWord_730684
  simp only [CollatzResearch.WordTrace]
  refine ⟨13325117442432066868599553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17766823256576089158132737 13325117442432066868599553)
  ·
    refine ⟨9993838081824050151449665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13325117442432066868599553 9993838081824050151449665)
    ·
      refine ⟨7495378561368037613587249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9993838081824050151449665 7495378561368037613587249)
      ·
        refine ⟨5621533921026028210190437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7495378561368037613587249 5621533921026028210190437)
        ·
          refine ⟨1054037610192380289410707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5621533921026028210190437 1054037610192380289410707)
          ·
            refine ⟨1581056415288570434116061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1054037610192380289410707 1581056415288570434116061)
            ·
              refine ⟨592896155733213912793523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1581056415288570434116061 592896155733213912793523)
              ·
                refine ⟨889344233599820869190285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 592896155733213912793523 889344233599820869190285)
                ·
                  refine ⟨333504087599932825946357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 889344233599820869190285 333504087599932825946357)
                  ·
                    rfl

theorem cell20_730684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 3, 1, 3].length) (baseStart_730684 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_730684 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_730684 prefixEnd_730684 := by exact prefixLift 730684
  have htrace : WordTrace (prefixWord ++ tailWord_730684) baseStart_730684 baseEnd_730684 := by
    simpa [prefixWord, tailWord_730684, baseEnd_730684] using wordTrace_append hprefix tailTrace_730684
  have hstable : (prefixWord ++ tailWord_730684).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730684).length < 2 ^ (prefixWord ++ tailWord_730684).sum := by decide
  have hdescent : baseEnd_730684 < baseStart_730684 := by decide
  rcases family_descends (prefixWord ++ tailWord_730684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730694 : List Nat := [6, 1, 1, 1, 3, 2, 2, 4]
def baseStart_730694 : Nat := 118140960795 + 730694 * 2 ^ 59
def prefixEnd_730694 : Nat := 4983230072969 + 3 ^ 40 * 730694 * 2
def baseEnd_730694 : Nat := 111169550624139078537661

theorem tailTrace_730694 : CollatzResearch.WordTrace tailWord_730694 prefixEnd_730694 111169550624139078537661 := by
  unfold tailWord_730694
  simp only [CollatzResearch.WordTrace]
  refine ⟨832831237963372045158223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 17767066409885270296708757 832831237963372045158223)
  ·
    refine ⟨1249246856945058067737335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 832831237963372045158223 1249246856945058067737335)
    ·
      refine ⟨1873870285417587101606003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1249246856945058067737335 1873870285417587101606003)
      ·
        refine ⟨2810805428126380652409005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1873870285417587101606003 2810805428126380652409005)
        ·
          refine ⟨1054052035547392744653377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2810805428126380652409005 1054052035547392744653377)
          ·
            refine ⟨790539026660544558490033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1054052035547392744653377 790539026660544558490033)
            ·
              refine ⟨592904269995408418867525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 790539026660544558490033 592904269995408418867525)
              ·
                refine ⟨111169550624139078537661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 592904269995408418867525 111169550624139078537661)
                ·
                  rfl

theorem cell20_730694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_730694 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_730694 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_730694 prefixEnd_730694 := by exact prefixLift 730694
  have htrace : WordTrace (prefixWord ++ tailWord_730694) baseStart_730694 baseEnd_730694 := by
    simpa [prefixWord, tailWord_730694, baseEnd_730694] using wordTrace_append hprefix tailTrace_730694
  have hstable : (prefixWord ++ tailWord_730694).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730694).length < 2 ^ (prefixWord ++ tailWord_730694).sum := by decide
  have hdescent : baseEnd_730694 < baseStart_730694 := by decide
  rcases family_descends (prefixWord ++ tailWord_730694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730784 : List Nat := [2, 1, 1, 4, 3, 3, 2, 2, 2]
def baseStart_730784 : Nat := 118140960795 + 730784 * 2 ^ 59
def prefixEnd_730784 : Nat := 4983230072969 + 3 ^ 40 * 730784 * 2
def baseEnd_730784 : Nat := 333549730324776922612615

theorem tailTrace_730784 : CollatzResearch.WordTrace tailWord_730784 prefixEnd_730784 333549730324776922612615 := by
  unfold tailWord_730784
  simp only [CollatzResearch.WordTrace]
  refine ⟨13326941092250925407919703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17769254789667900543892937 13326941092250925407919703)
  ·
    refine ⟨19990411638376388111879555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13326941092250925407919703 19990411638376388111879555)
    ·
      refine ⟨29985617457564582167819333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19990411638376388111879555 29985617457564582167819333)
      ·
        refine ⟨5622303273293359156466125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29985617457564582167819333 5622303273293359156466125)
        ·
          refine ⟨2108363727485009683674797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5622303273293359156466125 2108363727485009683674797)
          ·
            refine ⟨790636397806878631378049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2108363727485009683674797 790636397806878631378049)
            ·
              refine ⟨592977298355158973533537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 790636397806878631378049 592977298355158973533537)
              ·
                refine ⟨444732973766369230150153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 592977298355158973533537 444732973766369230150153)
                ·
                  refine ⟨333549730324776922612615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 444732973766369230150153 333549730324776922612615)
                  ·
                    rfl

theorem cell20_730784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 2, 2, 2].length) (baseStart_730784 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_730784 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_730784 prefixEnd_730784 := by exact prefixLift 730784
  have htrace : WordTrace (prefixWord ++ tailWord_730784) baseStart_730784 baseEnd_730784 := by
    simpa [prefixWord, tailWord_730784, baseEnd_730784] using wordTrace_append hprefix tailTrace_730784
  have hstable : (prefixWord ++ tailWord_730784).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730784).length < 2 ^ (prefixWord ++ tailWord_730784).sum := by decide
  have hdescent : baseEnd_730784 < baseStart_730784 := by decide
  rcases family_descends (prefixWord ++ tailWord_730784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730802 : List Nat := [3, 2, 1, 1, 1, 2, 4, 3, 3]
def baseStart_730802 : Nat := 118140960795 + 730802 * 2 ^ 59
def prefixEnd_730802 : Nat := 4983230072969 + 3 ^ 40 * 730802 * 2
def baseEnd_730802 : Nat := 333557946015248860012541

theorem tailTrace_730802 : CollatzResearch.WordTrace tailWord_730802 prefixEnd_730802 333557946015248860012541 := by
  unfold tailWord_730802
  simp only [CollatzResearch.WordTrace]
  refine ⟨6663634674609159972498665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17769692465624426593329773 6663634674609159972498665)
  ·
    refine ⟨4997726005956869979373999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6663634674609159972498665 4997726005956869979373999)
    ·
      refine ⟨7496589008935304969060999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4997726005956869979373999 7496589008935304969060999)
      ·
        refine ⟨11244883513402957453591499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7496589008935304969060999 11244883513402957453591499)
        ·
          refine ⟨16867325270104436180387249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11244883513402957453591499 16867325270104436180387249)
          ·
            refine ⟨12650493952578327135290437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16867325270104436180387249 12650493952578327135290437)
            ·
              refine ⟨2371967616108436337866957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12650493952578327135290437 2371967616108436337866957)
              ·
                refine ⟨889487856040663626700109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2371967616108436337866957 889487856040663626700109)
                ·
                  refine ⟨333557946015248860012541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 889487856040663626700109 333557946015248860012541)
                  ·
                    rfl

theorem cell20_730802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 3, 3].length) (baseStart_730802 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_730802 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_730802 prefixEnd_730802 := by exact prefixLift 730802
  have htrace : WordTrace (prefixWord ++ tailWord_730802) baseStart_730802 baseEnd_730802 := by
    simpa [prefixWord, tailWord_730802, baseEnd_730802] using wordTrace_append hprefix tailTrace_730802
  have hstable : (prefixWord ++ tailWord_730802).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730802).length < 2 ^ (prefixWord ++ tailWord_730802).sum := by decide
  have hdescent : baseEnd_730802 < baseStart_730802 := by decide
  rcases family_descends (prefixWord ++ tailWord_730802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730818 : List Nat := [3, 5, 1, 2, 1, 1, 2, 3, 2]
def baseStart_730818 : Nat := 118140960795 + 730818 * 2 ^ 59
def prefixEnd_730818 : Nat := 4983230072969 + 3 ^ 40 * 730818 * 2
def baseEnd_730818 : Nat := 333565248851223915479143

theorem tailTrace_730818 : CollatzResearch.WordTrace tailWord_730818 prefixEnd_730818 333565248851223915479143 := by
  unfold tailWord_730818
  simp only [CollatzResearch.WordTrace]
  refine ⟨6663780566594668655644277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17770081510919116415051405 6663780566594668655644277)
  ·
    refine ⟨624729428118250186466651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6663780566594668655644277 624729428118250186466651)
    ·
      refine ⟨937094142177375279699977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 624729428118250186466651 937094142177375279699977)
      ·
        refine ⟨702820606633031459774983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 937094142177375279699977 702820606633031459774983)
        ·
          refine ⟨1054230909949547189662475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 702820606633031459774983 1054230909949547189662475)
          ·
            refine ⟨1581346364924320784493713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1054230909949547189662475 1581346364924320784493713)
            ·
              refine ⟨1186009773693240588370285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1581346364924320784493713 1186009773693240588370285)
              ·
                refine ⟨444753665134965220638857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1186009773693240588370285 444753665134965220638857)
                ·
                  refine ⟨333565248851223915479143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 444753665134965220638857 333565248851223915479143)
                  ·
                    rfl

theorem cell20_730818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_730818 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_730818 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_730818 prefixEnd_730818 := by exact prefixLift 730818
  have htrace : WordTrace (prefixWord ++ tailWord_730818) baseStart_730818 baseEnd_730818 := by
    simpa [prefixWord, tailWord_730818, baseEnd_730818] using wordTrace_append hprefix tailTrace_730818
  have hstable : (prefixWord ++ tailWord_730818).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730818).length < 2 ^ (prefixWord ++ tailWord_730818).sum := by decide
  have hdescent : baseEnd_730818 < baseStart_730818 := by decide
  rcases family_descends (prefixWord ++ tailWord_730818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730823 : List Nat := [1, 1, 4, 1, 1, 1, 4, 2, 5]
def baseStart_730823 : Nat := 118140960795 + 730823 * 2 ^ 59
def prefixEnd_730823 : Nat := 4983230072969 + 3 ^ 40 * 730823 * 2
def baseEnd_730823 : Nat := 333567530987466120312455

theorem tailTrace_730823 : CollatzResearch.WordTrace tailWord_730823 prefixEnd_730823 333567530987466120312455 := by
  unfold tailWord_730823
  simp only [CollatzResearch.WordTrace]
  refine ⟨26655304631360560476509123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17770203087573706984339415 26655304631360560476509123)
  ·
    refine ⟨39982956947040840714763685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26655304631360560476509123 39982956947040840714763685)
    ·
      refine ⟨7496804427570157634018191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39982956947040840714763685 7496804427570157634018191)
      ·
        refine ⟨11245206641355236451027287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7496804427570157634018191 11245206641355236451027287)
        ·
          refine ⟨16867809962032854676540931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11245206641355236451027287 16867809962032854676540931)
          ·
            refine ⟨25301714943049282014811397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16867809962032854676540931 25301714943049282014811397)
            ·
              refine ⟨4744071551821740377777137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25301714943049282014811397 4744071551821740377777137)
              ·
                refine ⟨3558053663866305283332853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4744071551821740377777137 3558053663866305283332853)
                ·
                  refine ⟨333567530987466120312455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3558053663866305283332853 333567530987466120312455)
                  ·
                    rfl

theorem cell20_730823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 5].length) (baseStart_730823 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_730823 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_730823 prefixEnd_730823 := by exact prefixLift 730823
  have htrace : WordTrace (prefixWord ++ tailWord_730823) baseStart_730823 baseEnd_730823 := by
    simpa [prefixWord, tailWord_730823, baseEnd_730823] using wordTrace_append hprefix tailTrace_730823
  have hstable : (prefixWord ++ tailWord_730823).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730823).length < 2 ^ (prefixWord ++ tailWord_730823).sum := by decide
  have hdescent : baseEnd_730823 < baseStart_730823 := by decide
  rcases family_descends (prefixWord ++ tailWord_730823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730836 : List Nat := [2, 4, 1, 3, 1, 3, 1, 2, 3]
def baseStart_730836 : Nat := 118140960795 + 730836 * 2 ^ 59
def prefixEnd_730836 : Nat := 4983230072969 + 3 ^ 40 * 730836 * 2
def baseEnd_730836 : Nat := 333573464541695852879069

theorem tailTrace_730836 : CollatzResearch.WordTrace tailWord_730836 prefixEnd_730836 333573464541695852879069 := by
  unfold tailWord_730836
  simp only [CollatzResearch.WordTrace]
  refine ⟨13327889390156731848366181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17770519186875642464488241 13327889390156731848366181)
  ·
    refine ⟨2498979260654387221568659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13327889390156731848366181 2498979260654387221568659)
    ·
      refine ⟨3748468890981580832352989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2498979260654387221568659 3748468890981580832352989)
      ·
        refine ⟨1405675834118092812132371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3748468890981580832352989 1405675834118092812132371)
        ·
          refine ⟨2108513751177139218198557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1405675834118092812132371 2108513751177139218198557)
          ·
            refine ⟨790692656691427206824459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2108513751177139218198557 790692656691427206824459)
            ·
              refine ⟨1186038985037140810236689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 790692656691427206824459 1186038985037140810236689)
              ·
                refine ⟨889529238777855607677517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1186038985037140810236689 889529238777855607677517)
                ·
                  refine ⟨333573464541695852879069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 889529238777855607677517 333573464541695852879069)
                  ·
                    rfl

theorem cell20_730836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_730836 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_730836 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_730836 prefixEnd_730836 := by exact prefixLift 730836
  have htrace : WordTrace (prefixWord ++ tailWord_730836) baseStart_730836 baseEnd_730836 := by
    simpa [prefixWord, tailWord_730836, baseEnd_730836] using wordTrace_append hprefix tailTrace_730836
  have hstable : (prefixWord ++ tailWord_730836).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730836).length < 2 ^ (prefixWord ++ tailWord_730836).sum := by decide
  have hdescent : baseEnd_730836 < baseStart_730836 := by decide
  rcases family_descends (prefixWord ++ tailWord_730836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730847 : List Nat := [1, 1, 2, 3, 2, 2, 4, 1, 4]
def baseStart_730847 : Nat := 118140960795 + 730847 * 2 ^ 59
def prefixEnd_730847 : Nat := 4983230072969 + 3 ^ 40 * 730847 * 2
def baseEnd_730847 : Nat := 333578485241428703512357

theorem tailTrace_730847 : CollatzResearch.WordTrace tailWord_730847 prefixEnd_730847 333578485241428703512357 := by
  unfold tailWord_730847
  simp only [CollatzResearch.WordTrace]
  refine ⟨26656179983273612575382795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17770786655515741716921863 26656179983273612575382795)
  ·
    refine ⟨39984269974910418863074193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26656179983273612575382795 39984269974910418863074193)
    ·
      refine ⟨29988202481182814147305645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39984269974910418863074193 29988202481182814147305645)
      ·
        refine ⟨11245575930443555305239617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29988202481182814147305645 11245575930443555305239617)
        ·
          refine ⟨8434181947832666478929713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11245575930443555305239617 8434181947832666478929713)
          ·
            refine ⟨6325636460874499859197285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8434181947832666478929713 6325636460874499859197285)
            ·
              refine ⟨1186056836413968723599491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6325636460874499859197285 1186056836413968723599491)
              ·
                refine ⟨1779085254620953085399237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1186056836413968723599491 1779085254620953085399237)
                ·
                  refine ⟨333578485241428703512357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1779085254620953085399237 333578485241428703512357)
                  ·
                    rfl

theorem cell20_730847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 1, 4].length) (baseStart_730847 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_730847 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_730847 prefixEnd_730847 := by exact prefixLift 730847
  have htrace : WordTrace (prefixWord ++ tailWord_730847) baseStart_730847 baseEnd_730847 := by
    simpa [prefixWord, tailWord_730847, baseEnd_730847] using wordTrace_append hprefix tailTrace_730847
  have hstable : (prefixWord ++ tailWord_730847).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730847).length < 2 ^ (prefixWord ++ tailWord_730847).sum := by decide
  have hdescent : baseEnd_730847 < baseStart_730847 := by decide
  rcases family_descends (prefixWord ++ tailWord_730847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730930 : List Nat := [3, 2, 1, 1, 3, 2, 2, 6]
def baseStart_730930 : Nat := 118140960795 + 730930 * 2 ^ 59
def prefixEnd_730930 : Nat := 4983230072969 + 3 ^ 40 * 730930 * 2
def baseEnd_730930 : Nat := 111205456234349767915117

theorem tailTrace_730930 : CollatzResearch.WordTrace tailWord_730930 prefixEnd_730930 111205456234349767915117 := by
  unfold tailWord_730930
  simp only [CollatzResearch.WordTrace]
  refine ⟨6664801810493229437663561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17772804827981945167102829 6664801810493229437663561)
  ·
    refine ⟨4998601357869922078247671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6664801810493229437663561 4998601357869922078247671)
    ·
      refine ⟨7497902036804883117371507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4998601357869922078247671 7497902036804883117371507)
      ·
        refine ⟨11246853055207324676057261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7497902036804883117371507 11246853055207324676057261)
        ·
          refine ⟨4217569895702746753521473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11246853055207324676057261 4217569895702746753521473)
          ·
            refine ⟨3163177421777060065141105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4217569895702746753521473 3163177421777060065141105)
            ·
              refine ⟨2372383066332795048855829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3163177421777060065141105 2372383066332795048855829)
              ·
                refine ⟨111205456234349767915117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2372383066332795048855829 111205456234349767915117)
                ·
                  rfl

theorem cell20_730930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 6].length) (baseStart_730930 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_730930 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_730930 prefixEnd_730930 := by exact prefixLift 730930
  have htrace : WordTrace (prefixWord ++ tailWord_730930) baseStart_730930 baseEnd_730930 := by
    simpa [prefixWord, tailWord_730930, baseEnd_730930] using wordTrace_append hprefix tailTrace_730930
  have hstable : (prefixWord ++ tailWord_730930).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730930).length < 2 ^ (prefixWord ++ tailWord_730930).sum := by decide
  have hdescent : baseEnd_730930 < baseStart_730930 := by decide
  rcases family_descends (prefixWord ++ tailWord_730930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730950 : List Nat := [6, 1, 1, 2, 1, 1, 1, 4, 3]
def baseStart_730950 : Nat := 118140960795 + 730950 * 2 ^ 59
def prefixEnd_730950 : Nat := 4983230072969 + 3 ^ 40 * 730950 * 2
def baseEnd_730950 : Nat := 333625497248018123078603

theorem tailTrace_730950 : CollatzResearch.WordTrace tailWord_730950 prefixEnd_730950 333625497248018123078603 := by
  unfold tailWord_730950
  simp only [CollatzResearch.WordTrace]
  refine ⟨833123021934389411449447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 17773291134600307444254869 833123021934389411449447)
  ·
    refine ⟨1249684532901584117174171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 833123021934389411449447 1249684532901584117174171)
    ·
      refine ⟨1874526799352376175761257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1249684532901584117174171 1874526799352376175761257)
      ·
        refine ⟨1405895099514282131820943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1874526799352376175761257 1405895099514282131820943)
        ·
          refine ⟨2108842649271423197731415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1405895099514282131820943 2108842649271423197731415)
          ·
            refine ⟨3163263973907134796597123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2108842649271423197731415 3163263973907134796597123)
            ·
              refine ⟨4744895960860702194895685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3163263973907134796597123 4744895960860702194895685)
              ·
                refine ⟨889667992661381661542941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4744895960860702194895685 889667992661381661542941)
                ·
                  refine ⟨333625497248018123078603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 889667992661381661542941 333625497248018123078603)
                  ·
                    rfl

theorem cell20_730950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_730950 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_730950 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_730950 prefixEnd_730950 := by exact prefixLift 730950
  have htrace : WordTrace (prefixWord ++ tailWord_730950) baseStart_730950 baseEnd_730950 := by
    simpa [prefixWord, tailWord_730950, baseEnd_730950] using wordTrace_append hprefix tailTrace_730950
  have hstable : (prefixWord ++ tailWord_730950).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730950).length < 2 ^ (prefixWord ++ tailWord_730950).sum := by decide
  have hdescent : baseEnd_730950 < baseStart_730950 := by decide
  rcases family_descends (prefixWord ++ tailWord_730950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730954 : List Nat := [3, 1, 2, 1, 1, 1, 6, 2, 3]
def baseStart_730954 : Nat := 118140960795 + 730954 * 2 ^ 59
def prefixEnd_730954 : Nat := 4983230072969 + 3 ^ 40 * 730954 * 2
def baseEnd_730954 : Nat := 333627322957011886945253

theorem tailTrace_730954 : CollatzResearch.WordTrace tailWord_730954 prefixEnd_730954 333627322957011886945253 := by
  unfold tailWord_730954
  simp only [CollatzResearch.WordTrace]
  refine ⟨6665020648471492462381979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17773388395923979899685277 6665020648471492462381979)
  ·
    refine ⟨9997530972707238693572969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6665020648471492462381979 9997530972707238693572969)
    ·
      refine ⟨7498148229530429020179727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9997530972707238693572969 7498148229530429020179727)
      ·
        refine ⟨11247222344295643530269591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7498148229530429020179727 11247222344295643530269591)
        ·
          refine ⟨16870833516443465295404387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11247222344295643530269591 16870833516443465295404387)
          ·
            refine ⟨25306250274665197943106581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16870833516443465295404387 25306250274665197943106581)
            ·
              refine ⟨1186230481624931153583121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 25306250274665197943106581 1186230481624931153583121)
              ·
                refine ⟨889672861218698365187341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1186230481624931153583121 889672861218698365187341)
                ·
                  refine ⟨333627322957011886945253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 889672861218698365187341 333627322957011886945253)
                  ·
                    rfl

theorem cell20_730954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 2, 3].length) (baseStart_730954 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_730954 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_730954 prefixEnd_730954 := by exact prefixLift 730954
  have htrace : WordTrace (prefixWord ++ tailWord_730954) baseStart_730954 baseEnd_730954 := by
    simpa [prefixWord, tailWord_730954, baseEnd_730954] using wordTrace_append hprefix tailTrace_730954
  have hstable : (prefixWord ++ tailWord_730954).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730954).length < 2 ^ (prefixWord ++ tailWord_730954).sum := by decide
  have hdescent : baseEnd_730954 < baseStart_730954 := by decide
  rcases family_descends (prefixWord ++ tailWord_730954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_730978 : List Nat := [3, 3, 2, 1, 2, 2, 1, 2, 4]
def baseStart_730978 : Nat := 118140960795 + 730978 * 2 ^ 59
def prefixEnd_730978 : Nat := 4983230072969 + 3 ^ 40 * 730978 * 2
def baseEnd_730978 : Nat := 333638277210974470145155

theorem tailTrace_730978 : CollatzResearch.WordTrace tailWord_730978 prefixEnd_730978 333638277210974470145155 := by
  unfold tailWord_730978
  simp only [CollatzResearch.WordTrace]
  refine ⟨6665239486449755487100397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17773971963866014632267725 6665239486449755487100397)
  ·
    refine ⟨2499464807418658307662649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6665239486449755487100397 2499464807418658307662649)
    ·
      refine ⟨1874598605563993730746987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2499464807418658307662649 1874598605563993730746987)
      ·
        refine ⟨2811897908345990596120481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1874598605563993730746987 2811897908345990596120481)
        ·
          refine ⟨2108923431259492947090361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2811897908345990596120481 2108923431259492947090361)
          ·
            refine ⟨1581692573444619710317771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2108923431259492947090361 1581692573444619710317771)
            ·
              refine ⟨2372538860166929565476657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1581692573444619710317771 2372538860166929565476657)
              ·
                refine ⟨1779404145125197174107493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2372538860166929565476657 1779404145125197174107493)
                ·
                  refine ⟨333638277210974470145155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1779404145125197174107493 333638277210974470145155)
                  ·
                    rfl

theorem cell20_730978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_730978 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_730978 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_730978 prefixEnd_730978 := by exact prefixLift 730978
  have htrace : WordTrace (prefixWord ++ tailWord_730978) baseStart_730978 baseEnd_730978 := by
    simpa [prefixWord, tailWord_730978, baseEnd_730978] using wordTrace_append hprefix tailTrace_730978
  have hstable : (prefixWord ++ tailWord_730978).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_730978).length < 2 ^ (prefixWord ++ tailWord_730978).sum := by decide
  have hdescent : baseEnd_730978 < baseStart_730978 := by decide
  rcases family_descends (prefixWord ++ tailWord_730978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731009 : List Nat := [1, 2, 4, 4, 1, 1, 1, 1, 5]
def baseStart_731009 : Nat := 118140960795 + 731009 * 2 ^ 59
def prefixEnd_731009 : Nat := 4983230072969 + 3 ^ 40 * 731009 * 2
def baseEnd_731009 : Nat := 333652426455676140111695

theorem tailTrace_731009 : CollatzResearch.WordTrace tailWord_731009 prefixEnd_731009 333652426455676140111695 := by
  unfold tailWord_731009
  simp only [CollatzResearch.WordTrace]
  refine ⟨26662088608686714242780081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17774725739124476161853387 26662088608686714242780081)
  ·
    refine ⟨19996566456515035682085061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26662088608686714242780081 19996566456515035682085061)
    ·
      refine ⟨3749356210596569190390949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19996566456515035682085061 3749356210596569190390949)
      ·
        refine ⟨703004289486856723198303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3749356210596569190390949 703004289486856723198303)
        ·
          refine ⟨1054506434230285084797455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 703004289486856723198303 1054506434230285084797455)
          ·
            refine ⟨1581759651345427627196183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1054506434230285084797455 1581759651345427627196183)
            ·
              refine ⟨2372639477018141440794275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1581759651345427627196183 2372639477018141440794275)
              ·
                refine ⟨3558959215527212161191413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2372639477018141440794275 3558959215527212161191413)
                ·
                  refine ⟨333652426455676140111695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3558959215527212161191413 333652426455676140111695)
                  ·
                    rfl

theorem cell20_731009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 5].length) (baseStart_731009 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_731009 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_731009 prefixEnd_731009 := by exact prefixLift 731009
  have htrace : WordTrace (prefixWord ++ tailWord_731009) baseStart_731009 baseEnd_731009 := by
    simpa [prefixWord, tailWord_731009, baseEnd_731009] using wordTrace_append hprefix tailTrace_731009
  have hstable : (prefixWord ++ tailWord_731009).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731009).length < 2 ^ (prefixWord ++ tailWord_731009).sum := by decide
  have hdescent : baseEnd_731009 < baseStart_731009 := by decide
  rcases family_descends (prefixWord ++ tailWord_731009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731013 : List Nat := [1, 3, 1, 1, 3, 2, 3, 1, 5]
def baseStart_731013 : Nat := 118140960795 + 731013 * 2 ^ 59
def prefixEnd_731013 : Nat := 4983230072969 + 3 ^ 40 * 731013 * 2
def baseEnd_731013 : Nat := 333654252164669903978345

theorem tailTrace_731013 : CollatzResearch.WordTrace tailWord_731013 prefixEnd_731013 333654252164669903978345 := by
  unfold tailWord_731013
  simp only [CollatzResearch.WordTrace]
  refine ⟨26662234500672222925925693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17774823000448148617283795 26662234500672222925925693)
  ·
    refine ⟨9998337937752083597222135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26662234500672222925925693 9998337937752083597222135)
    ·
      refine ⟨14997506906628125395833203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9998337937752083597222135 14997506906628125395833203)
      ·
        refine ⟨22496260359942188093749805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14997506906628125395833203 22496260359942188093749805)
        ·
          refine ⟨8436097634978320535156177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22496260359942188093749805 8436097634978320535156177)
          ·
            refine ⟨6327073226233740401367133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8436097634978320535156177 6327073226233740401367133)
            ·
              refine ⟨2372652459837652650512675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6327073226233740401367133 2372652459837652650512675)
              ·
                refine ⟨3558978689756478975769013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2372652459837652650512675 3558978689756478975769013)
                ·
                  refine ⟨333654252164669903978345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3558978689756478975769013 333654252164669903978345)
                  ·
                    rfl

theorem cell20_731013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 5].length) (baseStart_731013 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_731013 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_731013 prefixEnd_731013 := by exact prefixLift 731013
  have htrace : WordTrace (prefixWord ++ tailWord_731013) baseStart_731013 baseEnd_731013 := by
    simpa [prefixWord, tailWord_731013, baseEnd_731013] using wordTrace_append hprefix tailTrace_731013
  have hstable : (prefixWord ++ tailWord_731013).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731013).length < 2 ^ (prefixWord ++ tailWord_731013).sum := by decide
  have hdescent : baseEnd_731013 < baseStart_731013 := by decide
  rcases family_descends (prefixWord ++ tailWord_731013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731016 : List Nat := [2, 1, 3, 3, 3, 1, 2, 1, 4]
def baseStart_731016 : Nat := 118140960795 + 731016 * 2 ^ 59
def prefixEnd_731016 : Nat := 4983230072969 + 3 ^ 40 * 731016 * 2
def baseEnd_731016 : Nat := 333655621446415226878333

theorem tailTrace_731016 : CollatzResearch.WordTrace tailWord_731016 prefixEnd_731016 333655621446415226878333 := by
  unfold tailWord_731016
  simp only [CollatzResearch.WordTrace]
  refine ⟨13331171959830677219142451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17774895946440902958856601 13331171959830677219142451)
  ·
    refine ⟨19996757939746015828713677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13331171959830677219142451 19996757939746015828713677)
    ·
      refine ⟨7498784227404755935767629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19996757939746015828713677 7498784227404755935767629)
      ·
        refine ⟨2812044085276783475912861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7498784227404755935767629 2812044085276783475912861)
        ·
          refine ⟨1054516531978793803467323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2812044085276783475912861 1054516531978793803467323)
          ·
            refine ⟨1581774797968190705200985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1054516531978793803467323 1581774797968190705200985)
            ·
              refine ⟨1186331098476143028900739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1581774797968190705200985 1186331098476143028900739)
              ·
                refine ⟨1779496647714214543351109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1186331098476143028900739 1779496647714214543351109)
                ·
                  refine ⟨333655621446415226878333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1779496647714214543351109 333655621446415226878333)
                  ·
                    rfl

theorem cell20_731016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 1, 4].length) (baseStart_731016 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_731016 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_731016 prefixEnd_731016 := by exact prefixLift 731016
  have htrace : WordTrace (prefixWord ++ tailWord_731016) baseStart_731016 baseEnd_731016 := by
    simpa [prefixWord, tailWord_731016, baseEnd_731016] using wordTrace_append hprefix tailTrace_731016
  have hstable : (prefixWord ++ tailWord_731016).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731016).length < 2 ^ (prefixWord ++ tailWord_731016).sum := by decide
  have hdescent : baseEnd_731016 < baseStart_731016 := by decide
  rcases family_descends (prefixWord ++ tailWord_731016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731026 : List Nat := [3, 2, 3, 2, 1, 2, 3, 1, 3]
def baseStart_731026 : Nat := 118140960795 + 731026 * 2 ^ 59
def prefixEnd_731026 : Nat := 4983230072969 + 3 ^ 40 * 731026 * 2
def baseEnd_731026 : Nat := 333660185718899636544959

theorem tailTrace_731026 : CollatzResearch.WordTrace tailWord_731026 prefixEnd_731026 333660185718899636544959 := by
  unfold tailWord_731026
  simp only [CollatzResearch.WordTrace]
  refine ⟨6665677162406281536537233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17775139099750084097432621 6665677162406281536537233)
  ·
    refine ⟨4999257871804711152402925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6665677162406281536537233 4999257871804711152402925)
    ·
      refine ⟨1874721701926766682151097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4999257871804711152402925 1874721701926766682151097)
      ·
        refine ⟨1406041276445075011613323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1874721701926766682151097 1406041276445075011613323)
        ·
          refine ⟨2109061914667612517419985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1406041276445075011613323 2109061914667612517419985)
          ·
            refine ⟨1581796436000709388064989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2109061914667612517419985 1581796436000709388064989)
            ·
              refine ⟨593173663500266020524371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1581796436000709388064989 593173663500266020524371)
              ·
                refine ⟨889760495250399030786557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 593173663500266020524371 889760495250399030786557)
                ·
                  refine ⟨333660185718899636544959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 889760495250399030786557 333660185718899636544959)
                  ·
                    rfl

theorem cell20_731026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 3, 1, 3].length) (baseStart_731026 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_731026 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_731026 prefixEnd_731026 := by exact prefixLift 731026
  have htrace : WordTrace (prefixWord ++ tailWord_731026) baseStart_731026 baseEnd_731026 := by
    simpa [prefixWord, tailWord_731026, baseEnd_731026] using wordTrace_append hprefix tailTrace_731026
  have hstable : (prefixWord ++ tailWord_731026).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731026).length < 2 ^ (prefixWord ++ tailWord_731026).sum := by decide
  have hdescent : baseEnd_731026 < baseStart_731026 := by decide
  rcases family_descends (prefixWord ++ tailWord_731026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731037 : List Nat := [1, 4, 2, 1, 2, 2, 2, 2, 4]
def baseStart_731037 : Nat := 118140960795 + 731037 * 2 ^ 59
def prefixEnd_731037 : Nat := 4983230072969 + 3 ^ 40 * 731037 * 2
def baseEnd_731037 : Nat := 333665206418632487178247

theorem tailTrace_731037 : CollatzResearch.WordTrace tailWord_731037 prefixEnd_731037 333665206418632487178247 := by
  unfold tailWord_731037
  simp only [CollatzResearch.WordTrace]
  refine ⟨26663109852585275024799365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17775406568390183349866243 26663109852585275024799365)
  ·
    refine ⟨4999333097359739067149881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26663109852585275024799365 4999333097359739067149881)
    ·
      refine ⟨3749499823019804300362411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4999333097359739067149881 3749499823019804300362411)
      ·
        refine ⟨5624249734529706450543617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3749499823019804300362411 5624249734529706450543617)
        ·
          refine ⟨4218187300897279837907713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5624249734529706450543617 4218187300897279837907713)
          ·
            refine ⟨3163640475672959878430785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4218187300897279837907713 3163640475672959878430785)
            ·
              refine ⟨2372730356754719908823089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3163640475672959878430785 2372730356754719908823089)
              ·
                refine ⟨1779547767566039931617317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2372730356754719908823089 1779547767566039931617317)
                ·
                  refine ⟨333665206418632487178247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1779547767566039931617317 333665206418632487178247)
                  ·
                    rfl

theorem cell20_731037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_731037 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_731037 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_731037 prefixEnd_731037 := by exact prefixLift 731037
  have htrace : WordTrace (prefixWord ++ tailWord_731037) baseStart_731037 baseEnd_731037 := by
    simpa [prefixWord, tailWord_731037, baseEnd_731037] using wordTrace_append hprefix tailTrace_731037
  have hstable : (prefixWord ++ tailWord_731037).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731037).length < 2 ^ (prefixWord ++ tailWord_731037).sum := by decide
  have hdescent : baseEnd_731037 < baseStart_731037 := by decide
  rcases family_descends (prefixWord ++ tailWord_731037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731044 : List Nat := [2, 3, 1, 2, 1, 4, 1, 6]
def baseStart_731044 : Nat := 118140960795 + 731044 * 2 ^ 59
def prefixEnd_731044 : Nat := 4983230072969 + 3 ^ 40 * 731044 * 2
def baseEnd_731044 : Nat := 111222800469790524648295

theorem tailTrace_731044 : CollatzResearch.WordTrace tailWord_731044 prefixEnd_731044 111222800469790524648295 := by
  unfold tailWord_731044
  simp only [CollatzResearch.WordTrace]
  refine ⟨13331682581779957610152093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17775576775706610146869457 13331682581779957610152093)
  ·
    refine ⟨4999380968167484103807035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13331682581779957610152093 4999380968167484103807035)
    ·
      refine ⟨7499071452251226155710553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4999380968167484103807035 7499071452251226155710553)
      ·
        refine ⟨5624303589188419616782915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7499071452251226155710553 5624303589188419616782915)
        ·
          refine ⟨8436455383782629425174373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5624303589188419616782915 8436455383782629425174373)
          ·
            refine ⟨1581835384459243017220195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8436455383782629425174373 1581835384459243017220195)
            ·
              refine ⟨2372753076688864525830293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1581835384459243017220195 2372753076688864525830293)
              ·
                refine ⟨111222800469790524648295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2372753076688864525830293 111222800469790524648295)
                ·
                  rfl

theorem cell20_731044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 6].length) (baseStart_731044 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_731044 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_731044 prefixEnd_731044 := by exact prefixLift 731044
  have htrace : WordTrace (prefixWord ++ tailWord_731044) baseStart_731044 baseEnd_731044 := by
    simpa [prefixWord, tailWord_731044, baseEnd_731044] using wordTrace_append hprefix tailTrace_731044
  have hstable : (prefixWord ++ tailWord_731044).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731044).length < 2 ^ (prefixWord ++ tailWord_731044).sum := by decide
  have hdescent : baseEnd_731044 < baseStart_731044 := by decide
  rcases family_descends (prefixWord ++ tailWord_731044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731058 : List Nat := [3, 2, 1, 1, 1, 1, 1, 4, 6]
def baseStart_731058 : Nat := 118140960795 + 731058 * 2 ^ 59
def prefixEnd_731058 : Nat := 4983230072969 + 3 ^ 40 * 731058 * 2
def baseEnd_731058 : Nat := 333674791390849747478161

theorem tailTrace_731058 : CollatzResearch.WordTrace tailWord_731058 prefixEnd_731058 333674791390849747478161 := by
  unfold tailWord_731058
  simp only [CollatzResearch.WordTrace]
  refine ⟨6665968946377298902828457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17775917190339463740875885 6665968946377298902828457)
  ·
    refine ⟨4999476709782974177121343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6665968946377298902828457 4999476709782974177121343)
    ·
      refine ⟨7499215064674461265682015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4999476709782974177121343 7499215064674461265682015)
      ·
        refine ⟨11248822597011691898523023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7499215064674461265682015 11248822597011691898523023)
        ·
          refine ⟨16873233895517537847784535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11248822597011691898523023 16873233895517537847784535)
          ·
            refine ⟨25309850843276306771676803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16873233895517537847784535 25309850843276306771676803)
            ·
              refine ⟨37964776264914460157515205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25309850843276306771676803 37964776264914460157515205)
              ·
                refine ⟨7118395549671461279534101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37964776264914460157515205 7118395549671461279534101)
                ·
                  refine ⟨333674791390849747478161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7118395549671461279534101 333674791390849747478161)
                  ·
                    rfl

theorem cell20_731058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_731058 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_731058 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_731058 prefixEnd_731058 := by exact prefixLift 731058
  have htrace : WordTrace (prefixWord ++ tailWord_731058) baseStart_731058 baseEnd_731058 := by
    simpa [prefixWord, tailWord_731058, baseEnd_731058] using wordTrace_append hprefix tailTrace_731058
  have hstable : (prefixWord ++ tailWord_731058).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731058).length < 2 ^ (prefixWord ++ tailWord_731058).sum := by decide
  have hdescent : baseEnd_731058 < baseStart_731058 := by decide
  rcases family_descends (prefixWord ++ tailWord_731058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731096 : List Nat := [2, 1, 2, 2, 2, 2, 2, 1, 6]
def baseStart_731096 : Nat := 118140960795 + 731096 * 2 ^ 59
def prefixEnd_731096 : Nat := 4983230072969 + 3 ^ 40 * 731096 * 2
def baseEnd_731096 : Nat := 333692135626290504211339

theorem tailTrace_731096 : CollatzResearch.WordTrace tailWord_731096 prefixEnd_731096 333692135626290504211339 := by
  unfold tailWord_731096
  simp only [CollatzResearch.WordTrace]
  refine ⟨13332630879685764050598571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17776841172914352067464761 13332630879685764050598571)
  ·
    refine ⟨19998946319528646075897857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13332630879685764050598571 19998946319528646075897857)
    ·
      refine ⟨14999209739646484556923393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19998946319528646075897857 14999209739646484556923393)
      ·
        refine ⟨11249407304734863417692545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14999209739646484556923393 11249407304734863417692545)
        ·
          refine ⟨8437055478551147563269409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11249407304734863417692545 8437055478551147563269409)
          ·
            refine ⟨6327791608913360672452057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8437055478551147563269409 6327791608913360672452057)
            ·
              refine ⟨4745843706685020504339043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6327791608913360672452057 4745843706685020504339043)
              ·
                refine ⟨7118765560027530756508565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4745843706685020504339043 7118765560027530756508565)
                ·
                  refine ⟨333692135626290504211339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7118765560027530756508565 333692135626290504211339)
                  ·
                    rfl

theorem cell20_731096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 6].length) (baseStart_731096 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_731096 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_731096 prefixEnd_731096 := by exact prefixLift 731096
  have htrace : WordTrace (prefixWord ++ tailWord_731096) baseStart_731096 baseEnd_731096 := by
    simpa [prefixWord, tailWord_731096, baseEnd_731096] using wordTrace_append hprefix tailTrace_731096
  have hstable : (prefixWord ++ tailWord_731096).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731096).length < 2 ^ (prefixWord ++ tailWord_731096).sum := by decide
  have hdescent : baseEnd_731096 < baseStart_731096 := by decide
  rcases family_descends (prefixWord ++ tailWord_731096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731175 : List Nat := [1, 1, 7, 1, 2, 1, 7]
def baseStart_731175 : Nat := 118140960795 + 731175 * 2 ^ 59
def prefixEnd_731175 : Nat := 4983230072969 + 3 ^ 40 * 731175 * 2
def baseEnd_731175 : Nat := 37080910375435260064187

theorem tailTrace_731175 : CollatzResearch.WordTrace tailWord_731175 prefixEnd_731175 37080910375435260064187 := by
  unfold tailWord_731175
  simp only [CollatzResearch.WordTrace]
  refine ⟨26668143126085324593322979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17778762084056883062215319 26668143126085324593322979)
  ·
    refine ⟨40002214689127986889984469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26668143126085324593322979 40002214689127986889984469)
    ·
      refine ⟨937551906776437192734011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 40002214689127986889984469 937551906776437192734011)
      ·
        refine ⟨1406327860164655789101017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 937551906776437192734011 1406327860164655789101017)
        ·
          refine ⟨1054745895123491841825763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1406327860164655789101017 1054745895123491841825763)
          ·
            refine ⟨1582118842685237762738645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1054745895123491841825763 1582118842685237762738645)
            ·
              refine ⟨37080910375435260064187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1582118842685237762738645 37080910375435260064187)
              ·
                rfl

theorem cell20_731175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 7].length) (baseStart_731175 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_731175 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_731175 prefixEnd_731175 := by exact prefixLift 731175
  have htrace : WordTrace (prefixWord ++ tailWord_731175) baseStart_731175 baseEnd_731175 := by
    simpa [prefixWord, tailWord_731175, baseEnd_731175] using wordTrace_append hprefix tailTrace_731175
  have hstable : (prefixWord ++ tailWord_731175).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731175).length < 2 ^ (prefixWord ++ tailWord_731175).sum := by decide
  have hdescent : baseEnd_731175 < baseStart_731175 := by decide
  rcases family_descends (prefixWord ++ tailWord_731175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731182 : List Nat := [4, 1, 3, 1, 1, 3, 1, 1, 5]
def baseStart_731182 : Nat := 118140960795 + 731182 * 2 ^ 59
def prefixEnd_731182 : Nat := 4983230072969 + 3 ^ 40 * 731182 * 2
def baseEnd_731182 : Nat := 333731388369656427344321

theorem tailTrace_731182 : CollatzResearch.WordTrace tailWord_731182 prefixEnd_731182 333731388369656427344321 := by
  unfold tailWord_731182
  simp only [CollatzResearch.WordTrace]
  refine ⟨3333549804632495598603475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17778932291373309859218533 3333549804632495598603475)
  ·
    refine ⟨5000324706948743397905213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3333549804632495598603475 5000324706948743397905213)
    ·
      refine ⟨1875121765105778774214455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5000324706948743397905213 1875121765105778774214455)
      ·
        refine ⟨2812682647658668161321683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1875121765105778774214455 2812682647658668161321683)
        ·
          refine ⟨4219023971488002241982525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2812682647658668161321683 4219023971488002241982525)
          ·
            refine ⟨1582133989308000840743447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4219023971488002241982525 1582133989308000840743447)
            ·
              refine ⟨2373200983962001261115171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1582133989308000840743447 2373200983962001261115171)
              ·
                refine ⟨3559801475943001891672757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2373200983962001261115171 3559801475943001891672757)
                ·
                  refine ⟨333731388369656427344321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3559801475943001891672757 333731388369656427344321)
                  ·
                    rfl

theorem cell20_731182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_731182 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_731182 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_731182 prefixEnd_731182 := by exact prefixLift 731182
  have htrace : WordTrace (prefixWord ++ tailWord_731182) baseStart_731182 baseEnd_731182 := by
    simpa [prefixWord, tailWord_731182, baseEnd_731182] using wordTrace_append hprefix tailTrace_731182
  have hstable : (prefixWord ++ tailWord_731182).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731182).length < 2 ^ (prefixWord ++ tailWord_731182).sum := by decide
  have hdescent : baseEnd_731182 < baseStart_731182 := by decide
  rcases family_descends (prefixWord ++ tailWord_731182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731206 : List Nat := [6, 1, 1, 1, 1, 1, 1, 4, 4]
def baseStart_731206 : Nat := 118140960795 + 731206 * 2 ^ 59
def prefixEnd_731206 : Nat := 4983230072969 + 3 ^ 40 * 731206 * 2
def baseEnd_731206 : Nat := 333742342623619010544223

theorem tailTrace_731206 : CollatzResearch.WordTrace tailWord_731206 prefixEnd_731206 333742342623619010544223 := by
  unfold tailWord_731206
  simp only [CollatzResearch.WordTrace]
  refine ⟨833414805905406777740671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 17779515859315344591800981 833414805905406777740671)
  ·
    refine ⟨1250122208858110166611007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 833414805905406777740671 1250122208858110166611007)
    ·
      refine ⟨1875183313287165249916511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1250122208858110166611007 1875183313287165249916511)
      ·
        refine ⟨2812774969930747874874767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1875183313287165249916511 2812774969930747874874767)
        ·
          refine ⟨4219162454896121812312151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2812774969930747874874767 4219162454896121812312151)
          ·
            refine ⟨6328743682344182718468227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4219162454896121812312151 6328743682344182718468227)
            ·
              refine ⟨9493115523516274077702341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6328743682344182718468227 9493115523516274077702341)
              ·
                refine ⟨1779959160659301389569189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9493115523516274077702341 1779959160659301389569189)
                ·
                  refine ⟨333742342623619010544223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1779959160659301389569189 333742342623619010544223)
                  ·
                    rfl

theorem cell20_731206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_731206 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_731206 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_731206 prefixEnd_731206 := by exact prefixLift 731206
  have htrace : WordTrace (prefixWord ++ tailWord_731206) baseStart_731206 baseEnd_731206 := by
    simpa [prefixWord, tailWord_731206, baseEnd_731206] using wordTrace_append hprefix tailTrace_731206
  have hstable : (prefixWord ++ tailWord_731206).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731206).length < 2 ^ (prefixWord ++ tailWord_731206).sum := by decide
  have hdescent : baseEnd_731206 < baseStart_731206 := by decide
  rcases family_descends (prefixWord ++ tailWord_731206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731241 : List Nat := [1, 2, 1, 1, 1, 5, 2, 4, 3]
def baseStart_731241 : Nat := 118140960795 + 731241 * 2 ^ 59
def prefixEnd_731241 : Nat := 4983230072969 + 3 ^ 40 * 731241 * 2
def baseEnd_731241 : Nat := 333758317577314444377413

theorem tailTrace_731241 : CollatzResearch.WordTrace tailWord_731241 prefixEnd_731241 333758317577314444377413 := by
  unfold tailWord_731241
  simp only [CollatzResearch.WordTrace]
  refine ⟨26670550343846217865225577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17780366895897478576817051 26670550343846217865225577)
  ·
    refine ⟨20002912757884663398919183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26670550343846217865225577 20002912757884663398919183)
    ·
      refine ⟨30004369136826995098378775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20002912757884663398919183 30004369136826995098378775)
      ·
        refine ⟨45006553705240492647568163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30004369136826995098378775 45006553705240492647568163)
        ·
          refine ⟨67509830557860738971352245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45006553705240492647568163 67509830557860738971352245)
          ·
            refine ⟨6329046614799444278564273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67509830557860738971352245 6329046614799444278564273)
            ·
              refine ⟨4746784961099583208923205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6329046614799444278564273 4746784961099583208923205)
              ·
                refine ⟨890022180206171851673101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4746784961099583208923205 890022180206171851673101)
                ·
                  refine ⟨333758317577314444377413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 890022180206171851673101 333758317577314444377413)
                  ·
                    rfl

theorem cell20_731241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 4, 3].length) (baseStart_731241 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_731241 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_731241 prefixEnd_731241 := by exact prefixLift 731241
  have htrace : WordTrace (prefixWord ++ tailWord_731241) baseStart_731241 baseEnd_731241 := by
    simpa [prefixWord, tailWord_731241, baseEnd_731241] using wordTrace_append hprefix tailTrace_731241
  have hstable : (prefixWord ++ tailWord_731241).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731241).length < 2 ^ (prefixWord ++ tailWord_731241).sum := by decide
  have hdescent : baseEnd_731241 < baseStart_731241 := by decide
  rcases family_descends (prefixWord ++ tailWord_731241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731254 : List Nat := [5, 1, 1, 2, 1, 4, 2, 1, 3]
def baseStart_731254 : Nat := 118140960795 + 731254 * 2 ^ 59
def prefixEnd_731254 : Nat := 4983230072969 + 3 ^ 40 * 731254 * 2
def baseEnd_731254 : Nat := 333764251131544176944027

theorem tailTrace_731254 : CollatzResearch.WordTrace tailWord_731254 prefixEnd_731254 333764251131544176944027 := by
  unfold tailWord_731254
  simp only [CollatzResearch.WordTrace]
  refine ⟨1666939030799945067840551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17780682995199414056965877 1666939030799945067840551)
  ·
    refine ⟨2500408546199917601760827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1666939030799945067840551 2500408546199917601760827)
    ·
      refine ⟨3750612819299876402641241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2500408546199917601760827 3750612819299876402641241)
      ·
        refine ⟨2812959614474907301980931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3750612819299876402641241 2812959614474907301980931)
        ·
          refine ⟨4219439421712360952971397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2812959614474907301980931 4219439421712360952971397)
          ·
            refine ⟨791144891571067678682137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4219439421712360952971397 791144891571067678682137)
            ·
              refine ⟨593358668678300759011603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 791144891571067678682137 593358668678300759011603)
              ·
                refine ⟨890038003017451138517405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 593358668678300759011603 890038003017451138517405)
                ·
                  refine ⟨333764251131544176944027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 890038003017451138517405 333764251131544176944027)
                  ·
                    rfl

theorem cell20_731254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_731254 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_731254 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_731254 prefixEnd_731254 := by exact prefixLift 731254
  have htrace : WordTrace (prefixWord ++ tailWord_731254) baseStart_731254 baseEnd_731254 := by
    simpa [prefixWord, tailWord_731254, baseEnd_731254] using wordTrace_append hprefix tailTrace_731254
  have hstable : (prefixWord ++ tailWord_731254).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731254).length < 2 ^ (prefixWord ++ tailWord_731254).sum := by decide
  have hdescent : baseEnd_731254 < baseStart_731254 := by decide
  rcases family_descends (prefixWord ++ tailWord_731254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731255 : List Nat := [1, 1, 3, 1, 1, 5, 1, 7]
def baseStart_731255 : Nat := 118140960795 + 731255 * 2 ^ 59
def prefixEnd_731255 : Nat := 4983230072969 + 3 ^ 40 * 731255 * 2
def baseEnd_731255 : Nat := 111254902519597539303563

theorem tailTrace_731255 : CollatzResearch.WordTrace tailWord_731255 prefixEnd_731255 111254902519597539303563 := by
  unfold tailWord_731255
  simp only [CollatzResearch.WordTrace]
  refine ⟨26671060965795498256235219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17780707310530332170823479 26671060965795498256235219)
  ·
    refine ⟨40006591448693247384352829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26671060965795498256235219 40006591448693247384352829)
    ·
      refine ⟨15002471793259967769132311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40006591448693247384352829 15002471793259967769132311)
      ·
        refine ⟨22503707689889951653698467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15002471793259967769132311 22503707689889951653698467)
        ·
          refine ⟨33755561534834927480547701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22503707689889951653698467 33755561534834927480547701)
          ·
            refine ⟨3164583893890774451301347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33755561534834927480547701 3164583893890774451301347)
            ·
              refine ⟨4746875840836161676952021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3164583893890774451301347 4746875840836161676952021)
              ·
                refine ⟨111254902519597539303563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4746875840836161676952021 111254902519597539303563)
                ·
                  rfl

theorem cell20_731255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 7].length) (baseStart_731255 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_731255 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_731255 prefixEnd_731255 := by exact prefixLift 731255
  have htrace : WordTrace (prefixWord ++ tailWord_731255) baseStart_731255 baseEnd_731255 := by
    simpa [prefixWord, tailWord_731255, baseEnd_731255] using wordTrace_append hprefix tailTrace_731255
  have hstable : (prefixWord ++ tailWord_731255).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731255).length < 2 ^ (prefixWord ++ tailWord_731255).sum := by decide
  have hdescent : baseEnd_731255 < baseStart_731255 := by decide
  rcases family_descends (prefixWord ++ tailWord_731255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731272 : List Nat := [2, 1, 3, 4, 1, 1, 2, 6]
def baseStart_731272 : Nat := 118140960795 + 731272 * 2 ^ 59
def prefixEnd_731272 : Nat := 4983230072969 + 3 ^ 40 * 731272 * 2
def baseEnd_731272 : Nat := 111257488940672038114651

theorem tailTrace_731272 : CollatzResearch.WordTrace tailWord_731272 prefixEnd_731272 111257488940672038114651 := by
  unfold tailWord_731272
  simp only [CollatzResearch.WordTrace]
  refine ⟨13335840503366955079802035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17781120671155940106402713 13335840503366955079802035)
  ·
    refine ⟨20003760755050432619703053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13335840503366955079802035 20003760755050432619703053)
    ·
      refine ⟨7501410283143912232388645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20003760755050432619703053 7501410283143912232388645)
      ·
        refine ⟨1406514428089483543572871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7501410283143912232388645 1406514428089483543572871)
        ·
          refine ⟨2109771642134225315359307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1406514428089483543572871 2109771642134225315359307)
          ·
            refine ⟨3164657463201337973038961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2109771642134225315359307 3164657463201337973038961)
            ·
              refine ⟨2373493097401003479779221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3164657463201337973038961 2373493097401003479779221)
              ·
                refine ⟨111257488940672038114651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2373493097401003479779221 111257488940672038114651)
                ·
                  rfl

theorem cell20_731272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 6].length) (baseStart_731272 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_731272 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_731272 prefixEnd_731272 := by exact prefixLift 731272
  have htrace : WordTrace (prefixWord ++ tailWord_731272) baseStart_731272 baseEnd_731272 := by
    simpa [prefixWord, tailWord_731272, baseEnd_731272] using wordTrace_append hprefix tailTrace_731272
  have hstable : (prefixWord ++ tailWord_731272).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731272).length < 2 ^ (prefixWord ++ tailWord_731272).sum := by decide
  have hdescent : baseEnd_731272 < baseStart_731272 := by decide
  rcases family_descends (prefixWord ++ tailWord_731272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731282 : List Nat := [3, 2, 3, 1, 1, 1, 2, 5, 2]
def baseStart_731282 : Nat := 118140960795 + 731282 * 2 ^ 59
def prefixEnd_731282 : Nat := 4983230072969 + 3 ^ 40 * 731282 * 2
def baseEnd_731282 : Nat := 333777031094500524010579

theorem tailTrace_731282 : CollatzResearch.WordTrace tailWord_731282 prefixEnd_731282 333777031094500524010579 := by
  unfold tailWord_731282
  simp only [CollatzResearch.WordTrace]
  refine ⟨6668011434174420466867025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17781363824465121244978733 6668011434174420466867025)
  ·
    refine ⟨5001008575630815350150269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6668011434174420466867025 5001008575630815350150269)
    ·
      refine ⟨1875378215861555756306351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5001008575630815350150269 1875378215861555756306351)
      ·
        refine ⟨2813067323792333634459527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1875378215861555756306351 2813067323792333634459527)
        ·
          refine ⟨4219600985688500451689291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2813067323792333634459527 4219600985688500451689291)
          ·
            refine ⟨6329401478532750677533937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4219600985688500451689291 6329401478532750677533937)
            ·
              refine ⟨4747051108899563008150453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6329401478532750677533937 4747051108899563008150453)
              ·
                refine ⟨445036041459334032014105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4747051108899563008150453 445036041459334032014105)
                ·
                  refine ⟨333777031094500524010579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 445036041459334032014105 333777031094500524010579)
                  ·
                    rfl

theorem cell20_731282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 5, 2].length) (baseStart_731282 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_731282 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_731282 prefixEnd_731282 := by exact prefixLift 731282
  have htrace : WordTrace (prefixWord ++ tailWord_731282) baseStart_731282 baseEnd_731282 := by
    simpa [prefixWord, tailWord_731282, baseEnd_731282] using wordTrace_append hprefix tailTrace_731282
  have hstable : (prefixWord ++ tailWord_731282).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731282).length < 2 ^ (prefixWord ++ tailWord_731282).sum := by decide
  have hdescent : baseEnd_731282 < baseStart_731282 := by decide
  rcases family_descends (prefixWord ++ tailWord_731282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731293 : List Nat := [1, 4, 2, 1, 1, 11]
def baseStart_731293 : Nat := 118140960795 + 731293 * 2 ^ 59
def prefixEnd_731293 : Nat := 4983230072969 + 3 ^ 40 * 731293 * 2
def baseEnd_731293 : Nat := 12362298214601236097921

theorem tailTrace_731293 : CollatzResearch.WordTrace tailWord_731293 prefixEnd_731293 12362298214601236097921 := by
  unfold tailWord_731293
  simp only [CollatzResearch.WordTrace]
  refine ⟨26672446939657830746118533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17781631293105220497412355 26672446939657830746118533)
  ·
    refine ⟨5001083801185843264897225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26672446939657830746118533 5001083801185843264897225)
    ·
      refine ⟨3750812850889382448672919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5001083801185843264897225 3750812850889382448672919)
      ·
        refine ⟨5626219276334073673009379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3750812850889382448672919 5626219276334073673009379)
        ·
          refine ⟨8439328914501110509514069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5626219276334073673009379 8439328914501110509514069)
          ·
            refine ⟨12362298214601236097921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8439328914501110509514069 12362298214601236097921)
            ·
              rfl

theorem cell20_731293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 11].length) (baseStart_731293 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_731293 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_731293 prefixEnd_731293 := by exact prefixLift 731293
  have htrace : WordTrace (prefixWord ++ tailWord_731293) baseStart_731293 baseEnd_731293 := by
    simpa [prefixWord, tailWord_731293, baseEnd_731293] using wordTrace_append hprefix tailTrace_731293
  have hstable : (prefixWord ++ tailWord_731293).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731293).length < 2 ^ (prefixWord ++ tailWord_731293).sum := by decide
  have hdescent : baseEnd_731293 < baseStart_731293 := by decide
  rcases family_descends (prefixWord ++ tailWord_731293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731296 : List Nat := [2, 1, 1, 4, 2, 3, 2, 2, 3]
def baseStart_731296 : Nat := 118140960795 + 731296 * 2 ^ 59
def prefixEnd_731296 : Nat := 4983230072969 + 3 ^ 40 * 731296 * 2
def baseEnd_731296 : Nat := 333783421075978697543855

theorem tailTrace_731296 : CollatzResearch.WordTrace tailWord_731296 prefixEnd_731296 333783421075978697543855 := by
  unfold tailWord_731296
  simp only [CollatzResearch.WordTrace]
  refine ⟨13336278179323481129238871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17781704239097974838985161 13336278179323481129238871)
  ·
    refine ⟨20004417268985221693858307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13336278179323481129238871 20004417268985221693858307)
    ·
      refine ⟨30006625903477832540787461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20004417268985221693858307 30006625903477832540787461)
      ·
        refine ⟨5626242356902093601397649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30006625903477832540787461 5626242356902093601397649)
        ·
          refine ⟨4219681767676570201048237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5626242356902093601397649 4219681767676570201048237)
          ·
            refine ⟨1582380662878713825393089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4219681767676570201048237 1582380662878713825393089)
            ·
              refine ⟨1186785497159035369044817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1582380662878713825393089 1186785497159035369044817)
              ·
                refine ⟨890089122869276526783613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1186785497159035369044817 890089122869276526783613)
                ·
                  refine ⟨333783421075978697543855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 890089122869276526783613 333783421075978697543855)
                  ·
                    rfl

theorem cell20_731296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 2, 3].length) (baseStart_731296 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_731296 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_731296 prefixEnd_731296 := by exact prefixLift 731296
  have htrace : WordTrace (prefixWord ++ tailWord_731296) baseStart_731296 baseEnd_731296 := by
    simpa [prefixWord, tailWord_731296, baseEnd_731296] using wordTrace_append hprefix tailTrace_731296
  have hstable : (prefixWord ++ tailWord_731296).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731296).length < 2 ^ (prefixWord ++ tailWord_731296).sum := by decide
  have hdescent : baseEnd_731296 < baseStart_731296 := by decide
  rcases family_descends (prefixWord ++ tailWord_731296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731306 : List Nat := [3, 1, 5, 1, 2, 2, 1, 5]
def baseStart_731306 : Nat := 118140960795 + 731306 * 2 ^ 59
def prefixEnd_731306 : Nat := 4983230072969 + 3 ^ 40 * 731306 * 2
def baseEnd_731306 : Nat := 111262661782821035736827

theorem tailTrace_731306 : CollatzResearch.WordTrace tailWord_731306 prefixEnd_731306 111262661782821035736827 := by
  unfold tailWord_731306
  simp only [CollatzResearch.WordTrace]
  refine ⟨6668230272152683491585443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17781947392407155977561181 6668230272152683491585443)
  ·
    refine ⟨10002345408229025237378165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6668230272152683491585443 10002345408229025237378165)
    ·
      refine ⟨937719882021471116004203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10002345408229025237378165 937719882021471116004203)
      ·
        refine ⟨1406579823032206674006305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 937719882021471116004203 1406579823032206674006305)
        ·
          refine ⟨1054934867274155005504729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1406579823032206674006305 1054934867274155005504729)
          ·
            refine ⟨791201150455616254128547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1054934867274155005504729 791201150455616254128547)
            ·
              refine ⟨1186801725683424381192821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 791201150455616254128547 1186801725683424381192821)
              ·
                refine ⟨111262661782821035736827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1186801725683424381192821 111262661782821035736827)
                ·
                  rfl

theorem cell20_731306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 5].length) (baseStart_731306 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_731306 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_731306 prefixEnd_731306 := by exact prefixLift 731306
  have htrace : WordTrace (prefixWord ++ tailWord_731306) baseStart_731306 baseEnd_731306 := by
    simpa [prefixWord, tailWord_731306, baseEnd_731306] using wordTrace_append hprefix tailTrace_731306
  have hstable : (prefixWord ++ tailWord_731306).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731306).length < 2 ^ (prefixWord ++ tailWord_731306).sum := by decide
  have hdescent : baseEnd_731306 < baseStart_731306 := by decide
  rcases family_descends (prefixWord ++ tailWord_731306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731316 : List Nat := [2, 5, 3, 1, 1, 1, 1, 2, 4]
def baseStart_731316 : Nat := 118140960795 + 731316 * 2 ^ 59
def prefixEnd_731316 : Nat := 4983230072969 + 3 ^ 40 * 731316 * 2
def baseEnd_731316 : Nat := 333792549620947516877107

theorem tailTrace_731316 : CollatzResearch.WordTrace tailWord_731316 prefixEnd_731316 333792549620947516877107 := by
  unfold tailWord_731316
  simp only [CollatzResearch.WordTrace]
  refine ⟨13336642909287252837102901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17782190545716337116137201 13336642909287252837102901)
  ·
    refine ⟨1250310272745679953478397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13336642909287252837102901 1250310272745679953478397)
    ·
      refine ⟨468866352279629982554399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1250310272745679953478397 468866352279629982554399)
      ·
        refine ⟨703299528419444973831599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 468866352279629982554399 703299528419444973831599)
        ·
          refine ⟨1054949292629167460747399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 703299528419444973831599 1054949292629167460747399)
          ·
            refine ⟨1582423938943751191121099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1054949292629167460747399 1582423938943751191121099)
            ·
              refine ⟨2373635908415626786681649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1582423938943751191121099 2373635908415626786681649)
              ·
                refine ⟨1780226931311720090011237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2373635908415626786681649 1780226931311720090011237)
                ·
                  refine ⟨333792549620947516877107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1780226931311720090011237 333792549620947516877107)
                  ·
                    rfl

theorem cell20_731316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_731316 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_731316 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_731316 prefixEnd_731316 := by exact prefixLift 731316
  have htrace : WordTrace (prefixWord ++ tailWord_731316) baseStart_731316 baseEnd_731316 := by
    simpa [prefixWord, tailWord_731316, baseEnd_731316] using wordTrace_append hprefix tailTrace_731316
  have hstable : (prefixWord ++ tailWord_731316).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731316).length < 2 ^ (prefixWord ++ tailWord_731316).sum := by decide
  have hdescent : baseEnd_731316 < baseStart_731316 := by decide
  rcases family_descends (prefixWord ++ tailWord_731316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731372 : List Nat := [2, 2, 1, 1, 2, 3, 5, 1, 3]
def baseStart_731372 : Nat := 118140960795 + 731372 * 2 ^ 59
def prefixEnd_731372 : Nat := 4983230072969 + 3 ^ 40 * 731372 * 2
def baseEnd_731372 : Nat := 333818109546860211010211

theorem tailTrace_731372 : CollatzResearch.WordTrace tailWord_731372 prefixEnd_731372 333818109546860211010211 := by
  unfold tailWord_731372
  simp only [CollatzResearch.WordTrace]
  refine ⟨13337664153185813619122185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17783552204247751492162913 13337664153185813619122185)
  ·
    refine ⟨10003248114889360214341639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13337664153185813619122185 10003248114889360214341639)
    ·
      refine ⟨15004872172334040321512459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10003248114889360214341639 15004872172334040321512459)
      ·
        refine ⟨22507308258501060482268689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15004872172334040321512459 22507308258501060482268689)
        ·
          refine ⟨16880481193875795361701517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22507308258501060482268689 16880481193875795361701517)
          ·
            refine ⟨6330180447703423260638069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16880481193875795361701517 6330180447703423260638069)
            ·
              refine ⟨593454416972195930684819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6330180447703423260638069 593454416972195930684819)
              ·
                refine ⟨890181625458293896027229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 593454416972195930684819 890181625458293896027229)
                ·
                  refine ⟨333818109546860211010211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 890181625458293896027229 333818109546860211010211)
                  ·
                    rfl

theorem cell20_731372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 3].length) (baseStart_731372 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_731372 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_731372 prefixEnd_731372 := by exact prefixLift 731372
  have htrace : WordTrace (prefixWord ++ tailWord_731372) baseStart_731372 baseEnd_731372 := by
    simpa [prefixWord, tailWord_731372, baseEnd_731372] using wordTrace_append hprefix tailTrace_731372
  have hstable : (prefixWord ++ tailWord_731372).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731372).length < 2 ^ (prefixWord ++ tailWord_731372).sum := by decide
  have hdescent : baseEnd_731372 < baseStart_731372 := by decide
  rcases family_descends (prefixWord ++ tailWord_731372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731386 : List Nat := [3, 1, 1, 1, 1, 5, 4, 4]
def baseStart_731386 : Nat := 118140960795 + 731386 * 2 ^ 59
def prefixEnd_731386 : Nat := 4983230072969 + 3 ^ 40 * 731386 * 2
def baseEnd_731386 : Nat := 111274833176112794847829

theorem tailTrace_731386 : CollatzResearch.WordTrace tailWord_731386 prefixEnd_731386 111274833176112794847829 := by
  unfold tailWord_731386
  simp only [CollatzResearch.WordTrace]
  refine ⟨6668959732080226907313503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17783892618880605086169341 6668959732080226907313503)
  ·
    refine ⟨10003439598120340360970255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6668959732080226907313503 10003439598120340360970255)
    ·
      refine ⟨15005159397180510541455383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10003439598120340360970255 15005159397180510541455383)
      ·
        refine ⟨22507739095770765812183075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15005159397180510541455383 22507739095770765812183075)
        ·
          refine ⟨33761608643656148718274613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22507739095770765812183075 33761608643656148718274613)
          ·
            refine ⟨3165150810342763942338245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33761608643656148718274613 3165150810342763942338245)
            ·
              refine ⟨593465776939268239188421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3165150810342763942338245 593465776939268239188421)
              ·
                refine ⟨111274833176112794847829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 593465776939268239188421 111274833176112794847829)
                ·
                  rfl

theorem cell20_731386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 4, 4].length) (baseStart_731386 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_731386 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_731386 prefixEnd_731386 := by exact prefixLift 731386
  have htrace : WordTrace (prefixWord ++ tailWord_731386) baseStart_731386 baseEnd_731386 := by
    simpa [prefixWord, tailWord_731386, baseEnd_731386] using wordTrace_append hprefix tailTrace_731386
  have hstable : (prefixWord ++ tailWord_731386).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731386).length < 2 ^ (prefixWord ++ tailWord_731386).sum := by decide
  have hdescent : baseEnd_731386 < baseStart_731386 := by decide
  rcases family_descends (prefixWord ++ tailWord_731386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731424 : List Nat := [2, 1, 1, 5, 2, 2, 2, 5]
def baseStart_731424 : Nat := 118140960795 + 731424 * 2 ^ 59
def prefixEnd_731424 : Nat := 4983230072969 + 3 ^ 40 * 731424 * 2
def baseEnd_731424 : Nat := 111280614587926380425555

theorem tailTrace_731424 : CollatzResearch.WordTrace tailWord_731424 prefixEnd_731424 111280614587926380425555 := by
  unfold tailWord_731424
  simp only [CollatzResearch.WordTrace]
  refine ⟨13338612451091620059568663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17784816601455493412758217 13338612451091620059568663)
  ·
    refine ⟨20007918676637430089352995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13338612451091620059568663 20007918676637430089352995)
    ·
      refine ⟨30011878014956145134029493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20007918676637430089352995 30011878014956145134029493)
      ·
        refine ⟨2813613563902138606315265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30011878014956145134029493 2813613563902138606315265)
        ·
          refine ⟨2110210172926603954736449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2813613563902138606315265 2110210172926603954736449)
          ·
            refine ⟨1582657629694952966052337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2110210172926603954736449 1582657629694952966052337)
            ·
              refine ⟨1186993222271214724539253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1582657629694952966052337 1186993222271214724539253)
              ·
                refine ⟨111280614587926380425555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1186993222271214724539253 111280614587926380425555)
                ·
                  rfl

theorem cell20_731424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 5].length) (baseStart_731424 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_731424 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_731424 prefixEnd_731424 := by exact prefixLift 731424
  have htrace : WordTrace (prefixWord ++ tailWord_731424) baseStart_731424 baseEnd_731424 := by
    simpa [prefixWord, tailWord_731424, baseEnd_731424] using wordTrace_append hprefix tailTrace_731424
  have hstable : (prefixWord ++ tailWord_731424).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731424).length < 2 ^ (prefixWord ++ tailWord_731424).sum := by decide
  have hdescent : baseEnd_731424 < baseStart_731424 := by decide
  rcases family_descends (prefixWord ++ tailWord_731424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731445 : List Nat := [1, 3, 3, 1, 2, 1, 1, 8]
def baseStart_731445 : Nat := 118140960795 + 731445 * 2 ^ 59
def prefixEnd_731445 : Nat := 4983230072969 + 3 ^ 40 * 731445 * 2
def baseEnd_731445 : Nat := 111283809578665467192193

theorem tailTrace_731445 : CollatzResearch.WordTrace tailWord_731445 prefixEnd_731445 111283809578665467192193 := by
  unfold tailWord_731445
  simp only [CollatzResearch.WordTrace]
  refine ⟨26677990835107160705651789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17785327223404773803767859 26677990835107160705651789)
  ·
    refine ⟨10004246563165185264619421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26677990835107160705651789 10004246563165185264619421)
    ·
      refine ⟨3751592461186944474232283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10004246563165185264619421 3751592461186944474232283)
      ·
        refine ⟨5627388691780416711348425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3751592461186944474232283 5627388691780416711348425)
        ·
          refine ⟨4220541518835312533511319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5627388691780416711348425 4220541518835312533511319)
          ·
            refine ⟨6330812278252968800266979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4220541518835312533511319 6330812278252968800266979)
            ·
              refine ⟨9496218417379453200400469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6330812278252968800266979 9496218417379453200400469)
              ·
                refine ⟨111283809578665467192193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9496218417379453200400469 111283809578665467192193)
                ·
                  rfl

theorem cell20_731445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 8].length) (baseStart_731445 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_731445 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_731445 prefixEnd_731445 := by exact prefixLift 731445
  have htrace : WordTrace (prefixWord ++ tailWord_731445) baseStart_731445 baseEnd_731445 := by
    simpa [prefixWord, tailWord_731445, baseEnd_731445] using wordTrace_append hprefix tailTrace_731445
  have hstable : (prefixWord ++ tailWord_731445).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731445).length < 2 ^ (prefixWord ++ tailWord_731445).sum := by decide
  have hdescent : baseEnd_731445 < baseStart_731445 := by decide
  rcases family_descends (prefixWord ++ tailWord_731445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731455 : List Nat := [1, 1, 2, 2, 4, 1, 2, 5, 2]
def baseStart_731455 : Nat := 118140960795 + 731455 * 2 ^ 59
def prefixEnd_731455 : Nat := 4983230072969 + 3 ^ 40 * 731455 * 2
def baseEnd_731455 : Nat := 333855993008480811243205

theorem tailTrace_731455 : CollatzResearch.WordTrace tailWord_731455 prefixEnd_731455 333855993008480811243205 := by
  unfold tailWord_731455
  simp only [CollatzResearch.WordTrace]
  refine ⟨26678355565070932413515819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17785570376713954942343879 26678355565070932413515819)
  ·
    refine ⟨40017533347606398620273729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26678355565070932413515819 40017533347606398620273729)
    ·
      refine ⟨30013150010704798965205297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40017533347606398620273729 30013150010704798965205297)
      ·
        refine ⟨22509862508028599223903973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30013150010704798965205297 22509862508028599223903973)
        ·
          refine ⟨4220599220255362354481995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22509862508028599223903973 4220599220255362354481995)
          ·
            refine ⟨6330898830383043531722993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4220599220255362354481995 6330898830383043531722993)
            ·
              refine ⟨4748174122787282648792245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6330898830383043531722993 4748174122787282648792245)
              ·
                refine ⟨445141324011307748324273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4748174122787282648792245 445141324011307748324273)
                ·
                  refine ⟨333855993008480811243205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 445141324011307748324273 333855993008480811243205)
                  ·
                    rfl

theorem cell20_731455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 5, 2].length) (baseStart_731455 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_731455 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_731455 prefixEnd_731455 := by exact prefixLift 731455
  have htrace : WordTrace (prefixWord ++ tailWord_731455) baseStart_731455 baseEnd_731455 := by
    simpa [prefixWord, tailWord_731455, baseEnd_731455] using wordTrace_append hprefix tailTrace_731455
  have hstable : (prefixWord ++ tailWord_731455).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731455).length < 2 ^ (prefixWord ++ tailWord_731455).sum := by decide
  have hdescent : baseEnd_731455 < baseStart_731455 := by decide
  rcases family_descends (prefixWord ++ tailWord_731455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731462 : List Nat := [6, 1, 1, 12]
def baseStart_731462 : Nat := 118140960795 + 731462 * 2 ^ 59
def prefixEnd_731462 : Nat := 4983230072969 + 3 ^ 40 * 731462 * 2
def baseEnd_731462 : Nat := 1373906123453579827201

theorem tailTrace_731462 : CollatzResearch.WordTrace tailWord_731462 prefixEnd_731462 1373906123453579827201 := by
  unfold tailWord_731462
  simp only [CollatzResearch.WordTrace]
  refine ⟨833706589876424144031895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 17785740584030381739347093 833706589876424144031895)
  ·
    refine ⟨1250559884814636216047843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 833706589876424144031895 1250559884814636216047843)
    ·
      refine ⟨1875839827221954324071765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1250559884814636216047843 1875839827221954324071765)
      ·
        refine ⟨1373906123453579827201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 1875839827221954324071765 1373906123453579827201)
        ·
          rfl

theorem cell20_731462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 12].length) (baseStart_731462 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_731462 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_731462 prefixEnd_731462 := by exact prefixLift 731462
  have htrace : WordTrace (prefixWord ++ tailWord_731462) baseStart_731462 baseEnd_731462 := by
    simpa [prefixWord, tailWord_731462, baseEnd_731462] using wordTrace_append hprefix tailTrace_731462
  have hstable : (prefixWord ++ tailWord_731462).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731462).length < 2 ^ (prefixWord ++ tailWord_731462).sum := by decide
  have hdescent : baseEnd_731462 < baseStart_731462 := by decide
  rcases family_descends (prefixWord ++ tailWord_731462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731472 : List Nat := [2, 1, 1, 1, 1, 6, 4, 2, 2]
def baseStart_731472 : Nat := 118140960795 + 731472 * 2 ^ 59
def prefixEnd_731472 : Nat := 4983230072969 + 3 ^ 40 * 731472 * 2
def baseEnd_731472 : Nat := 333863752271704307676469

theorem tailTrace_731472 : CollatzResearch.WordTrace tailWord_731472 prefixEnd_731472 333863752271704307676469 := by
  unfold tailWord_731472
  simp only [CollatzResearch.WordTrace]
  refine ⟨13339487803004672158442335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17785983737339562877923113 13339487803004672158442335)
  ·
    refine ⟨20009231704507008237663503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13339487803004672158442335 20009231704507008237663503)
    ·
      refine ⟨30013847556760512356495255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20009231704507008237663503 30013847556760512356495255)
      ·
        refine ⟨45020771335140768534742883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30013847556760512356495255 45020771335140768534742883)
        ·
          refine ⟨67531157002711152802114325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45020771335140768534742883 67531157002711152802114325)
          ·
            refine ⟨3165522984502085287599109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 67531157002711152802114325 3165522984502085287599109)
            ·
              refine ⟨593535559594140991424833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3165522984502085287599109 593535559594140991424833)
              ·
                refine ⟨445151669695605743568625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 593535559594140991424833 445151669695605743568625)
                ·
                  refine ⟨333863752271704307676469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 445151669695605743568625 333863752271704307676469)
                  ·
                    rfl

theorem cell20_731472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 4, 2, 2].length) (baseStart_731472 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_731472 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_731472 prefixEnd_731472 := by exact prefixLift 731472
  have htrace : WordTrace (prefixWord ++ tailWord_731472) baseStart_731472 baseEnd_731472 := by
    simpa [prefixWord, tailWord_731472, baseEnd_731472] using wordTrace_append hprefix tailTrace_731472
  have hstable : (prefixWord ++ tailWord_731472).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731472).length < 2 ^ (prefixWord ++ tailWord_731472).sum := by decide
  have hdescent : baseEnd_731472 < baseStart_731472 := by decide
  rcases family_descends (prefixWord ++ tailWord_731472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731531 : List Nat := [1, 1, 1, 1, 4, 4, 2, 4, 2]
def baseStart_731531 : Nat := 118140960795 + 731531 * 2 ^ 59
def prefixEnd_731531 : Nat := 4983230072969 + 3 ^ 40 * 731531 * 2
def baseEnd_731531 : Nat := 333890681479362324709561

theorem tailTrace_731531 : CollatzResearch.WordTrace tailWord_731531 prefixEnd_731531 333890681479362324709561 := by
  unfold tailWord_731531
  simp only [CollatzResearch.WordTrace]
  refine ⟨26681127512795597393282447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17787418341863731595521631 26681127512795597393282447)
  ·
    refine ⟨40021691269193396089923671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26681127512795597393282447 40021691269193396089923671)
    ·
      refine ⟨60032536903790094134885507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40021691269193396089923671 60032536903790094134885507)
      ·
        refine ⟨90048805355685141202328261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60032536903790094134885507 90048805355685141202328261)
        ·
          refine ⟨16884151004190963975436549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90048805355685141202328261 16884151004190963975436549)
          ·
            refine ⟨3165778313285805745394353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16884151004190963975436549 3165778313285805745394353)
            ·
              refine ⟨2374333734964354309045765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3165778313285805745394353 2374333734964354309045765)
              ·
                refine ⟨445187575305816432946081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2374333734964354309045765 445187575305816432946081)
                ·
                  refine ⟨333890681479362324709561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 445187575305816432946081 333890681479362324709561)
                  ·
                    rfl

theorem cell20_731531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 4, 2].length) (baseStart_731531 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_731531 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_731531 prefixEnd_731531 := by exact prefixLift 731531
  have htrace : WordTrace (prefixWord ++ tailWord_731531) baseStart_731531 baseEnd_731531 := by
    simpa [prefixWord, tailWord_731531, baseEnd_731531] using wordTrace_append hprefix tailTrace_731531
  have hstable : (prefixWord ++ tailWord_731531).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731531).length < 2 ^ (prefixWord ++ tailWord_731531).sum := by decide
  have hdescent : baseEnd_731531 < baseStart_731531 := by decide
  rcases family_descends (prefixWord ++ tailWord_731531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731552 : List Nat := [2, 1, 1, 4, 1, 3, 2, 2, 4]
def baseStart_731552 : Nat := 118140960795 + 731552 * 2 ^ 59
def prefixEnd_731552 : Nat := 4983230072969 + 3 ^ 40 * 731552 * 2
def baseEnd_731552 : Nat := 333900266451579585009475

theorem tailTrace_731552 : CollatzResearch.WordTrace tailWord_731552 prefixEnd_731552 333900266451579585009475 := by
  unfold tailWord_731552
  simp only [CollatzResearch.WordTrace]
  refine ⟨13340946722859758989898455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17787928963813011986531273 13340946722859758989898455)
  ·
    refine ⟨20011420084289638484847683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13340946722859758989898455 20011420084289638484847683)
    ·
      refine ⟨30017130126434457727271525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20011420084289638484847683 30017130126434457727271525)
      ·
        refine ⟨5628211898706460823863411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30017130126434457727271525 5628211898706460823863411)
        ·
          refine ⟨8442317848059691235795117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5628211898706460823863411 8442317848059691235795117)
          ·
            refine ⟨3165869193022384213423169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8442317848059691235795117 3165869193022384213423169)
            ·
              refine ⟨2374401894766788160067377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3165869193022384213423169 2374401894766788160067377)
              ·
                refine ⟨1780801421075091120050533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2374401894766788160067377 1780801421075091120050533)
                ·
                  refine ⟨333900266451579585009475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1780801421075091120050533 333900266451579585009475)
                  ·
                    rfl

theorem cell20_731552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 2, 4].length) (baseStart_731552 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_731552 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_731552 prefixEnd_731552 := by exact prefixLift 731552
  have htrace : WordTrace (prefixWord ++ tailWord_731552) baseStart_731552 baseEnd_731552 := by
    simpa [prefixWord, tailWord_731552, baseEnd_731552] using wordTrace_append hprefix tailTrace_731552
  have hstable : (prefixWord ++ tailWord_731552).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731552).length < 2 ^ (prefixWord ++ tailWord_731552).sum := by decide
  have hdescent : baseEnd_731552 < baseStart_731552 := by decide
  rcases family_descends (prefixWord ++ tailWord_731552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731572 : List Nat := [2, 5, 2, 2, 1, 2, 6]
def baseStart_731572 : Nat := 118140960795 + 731572 * 2 ^ 59
def prefixEnd_731572 : Nat := 4983230072969 + 3 ^ 40 * 731572 * 2
def baseEnd_731572 : Nat := 37101043888505378260303

theorem tailTrace_731572 : CollatzResearch.WordTrace tailWord_731572 prefixEnd_731572 37101043888505378260303 := by
  unfold tailWord_731572
  simp only [CollatzResearch.WordTrace]
  refine ⟨13341311452823530697762485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17788415270431374263683313 13341311452823530697762485)
  ·
    refine ⟨1250747948702206002915233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13341311452823530697762485 1250747948702206002915233)
    ·
      refine ⟨938060961526654502186425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1250747948702206002915233 938060961526654502186425)
      ·
        refine ⟨703545721144990876639819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 938060961526654502186425 703545721144990876639819)
        ·
          refine ⟨1055318581717486314959729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 703545721144990876639819 1055318581717486314959729)
          ·
            refine ⟨791488936288114736219797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1055318581717486314959729 791488936288114736219797)
            ·
              refine ⟨37101043888505378260303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 791488936288114736219797 37101043888505378260303)
              ·
                rfl

theorem cell20_731572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 6].length) (baseStart_731572 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_731572 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_731572 prefixEnd_731572 := by exact prefixLift 731572
  have htrace : WordTrace (prefixWord ++ tailWord_731572) baseStart_731572 baseEnd_731572 := by
    simpa [prefixWord, tailWord_731572, baseEnd_731572] using wordTrace_append hprefix tailTrace_731572
  have hstable : (prefixWord ++ tailWord_731572).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731572).length < 2 ^ (prefixWord ++ tailWord_731572).sum := by decide
  have hdescent : baseEnd_731572 < baseStart_731572 := by decide
  rcases family_descends (prefixWord ++ tailWord_731572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731596 : List Nat := [2, 2, 1, 4, 4, 1, 2, 1, 3]
def baseStart_731596 : Nat := 118140960795 + 731596 * 2 ^ 59
def prefixEnd_731596 : Nat := 4983230072969 + 3 ^ 40 * 731596 * 2
def baseEnd_731596 : Nat := 333920349250510987542629

theorem tailTrace_731596 : CollatzResearch.WordTrace tailWord_731596 prefixEnd_731596 333920349250510987542629 := by
  unfold tailWord_731596
  simp only [CollatzResearch.WordTrace]
  refine ⟨13341749128780056747199321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17788998838373408996265761 13341749128780056747199321)
  ·
    refine ⟨10006311846585042560399491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13341749128780056747199321 10006311846585042560399491)
    ·
      refine ⟨15009467769877563840599237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10006311846585042560399491 15009467769877563840599237)
      ·
        refine ⟨2814275206852043220112357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15009467769877563840599237 2814275206852043220112357)
        ·
          refine ⟨527676601284758103771067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2814275206852043220112357 527676601284758103771067)
          ·
            refine ⟨791514901927137155656601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 527676601284758103771067 791514901927137155656601)
            ·
              refine ⟨593636176445352866742451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 791514901927137155656601 593636176445352866742451)
              ·
                refine ⟨890454264668029300113677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 593636176445352866742451 890454264668029300113677)
                ·
                  refine ⟨333920349250510987542629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 890454264668029300113677 333920349250510987542629)
                  ·
                    rfl

theorem cell20_731596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 2, 1, 3].length) (baseStart_731596 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_731596 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_731596 prefixEnd_731596 := by exact prefixLift 731596
  have htrace : WordTrace (prefixWord ++ tailWord_731596) baseStart_731596 baseEnd_731596 := by
    simpa [prefixWord, tailWord_731596, baseEnd_731596] using wordTrace_append hprefix tailTrace_731596
  have hstable : (prefixWord ++ tailWord_731596).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731596).length < 2 ^ (prefixWord ++ tailWord_731596).sum := by decide
  have hdescent : baseEnd_731596 < baseStart_731596 := by decide
  rcases family_descends (prefixWord ++ tailWord_731596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731637 : List Nat := [1, 3, 5, 1, 3, 1, 2, 2, 2]
def baseStart_731637 : Nat := 118140960795 + 731637 * 2 ^ 59
def prefixEnd_731637 : Nat := 4983230072969 + 3 ^ 40 * 731637 * 2
def baseEnd_731637 : Nat := 333939062767697067175795

theorem tailTrace_731637 : CollatzResearch.WordTrace tailWord_731637 prefixEnd_731637 333939062767697067175795 := by
  unfold tailWord_731637
  simp only [CollatzResearch.WordTrace]
  refine ⟨26684993650411577496641165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17789995766941051664427443 26684993650411577496641165)
  ·
    refine ⟨10006872618904341561240437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26684993650411577496641165 10006872618904341561240437)
    ·
      refine ⟨938144308022282021366291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10006872618904341561240437 938144308022282021366291)
      ·
        refine ⟨1407216462033423032049437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 938144308022282021366291 1407216462033423032049437)
        ·
          refine ⟨527706173262533637018539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1407216462033423032049437 527706173262533637018539)
          ·
            refine ⟨791559259893800455527809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 527706173262533637018539 791559259893800455527809)
            ·
              refine ⟨593669444920350341645857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 791559259893800455527809 593669444920350341645857)
              ·
                refine ⟨445252083690262756234393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 593669444920350341645857 445252083690262756234393)
                ·
                  refine ⟨333939062767697067175795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 445252083690262756234393 333939062767697067175795)
                  ·
                    rfl

theorem cell20_731637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 2, 2, 2].length) (baseStart_731637 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_731637 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_731637 prefixEnd_731637 := by exact prefixLift 731637
  have htrace : WordTrace (prefixWord ++ tailWord_731637) baseStart_731637 baseEnd_731637 := by
    simpa [prefixWord, tailWord_731637, baseEnd_731637] using wordTrace_append hprefix tailTrace_731637
  have hstable : (prefixWord ++ tailWord_731637).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731637).length < 2 ^ (prefixWord ++ tailWord_731637).sum := by decide
  have hdescent : baseEnd_731637 < baseStart_731637 := by decide
  rcases family_descends (prefixWord ++ tailWord_731637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731638 : List Nat := [5, 1, 1, 1, 2, 1, 4, 2, 3]
def baseStart_731638 : Nat := 118140960795 + 731638 * 2 ^ 59
def prefixEnd_731638 : Nat := 4983230072969 + 3 ^ 40 * 731638 * 2
def baseEnd_731638 : Nat := 333939519194945508142457

theorem tailTrace_731638 : CollatzResearch.WordTrace tailWord_731638 prefixEnd_731638 333939519194945508142457 := by
  unfold tailWord_731638
  simp only [CollatzResearch.WordTrace]
  refine ⟨1667814382712997166714223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17790020082271969778285045 1667814382712997166714223)
  ·
    refine ⟨2501721574069495750071335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1667814382712997166714223 2501721574069495750071335)
    ·
      refine ⟨3752582361104243625107003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2501721574069495750071335 3752582361104243625107003)
      ·
        refine ⟨5628873541656365437660505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3752582361104243625107003 5628873541656365437660505)
        ·
          refine ⟨4221655156242274078245379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5628873541656365437660505 4221655156242274078245379)
          ·
            refine ⟨6332482734363411117368069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4221655156242274078245379 6332482734363411117368069)
            ·
              refine ⟨1187340512693139584506513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6332482734363411117368069 1187340512693139584506513)
              ·
                refine ⟨890505384519854688379885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1187340512693139584506513 890505384519854688379885)
                ·
                  refine ⟨333939519194945508142457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 890505384519854688379885 333939519194945508142457)
                  ·
                    rfl

theorem cell20_731638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_731638 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_731638 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_731638 prefixEnd_731638 := by exact prefixLift 731638
  have htrace : WordTrace (prefixWord ++ tailWord_731638) baseStart_731638 baseEnd_731638 := by
    simpa [prefixWord, tailWord_731638, baseEnd_731638] using wordTrace_append hprefix tailTrace_731638
  have hstable : (prefixWord ++ tailWord_731638).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731638).length < 2 ^ (prefixWord ++ tailWord_731638).sum := by decide
  have hdescent : baseEnd_731638 < baseStart_731638 := by decide
  rcases family_descends (prefixWord ++ tailWord_731638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731645 : List Nat := [1, 4, 1, 1, 1, 3, 3, 4, 2]
def baseStart_731645 : Nat := 118140960795 + 731645 * 2 ^ 59
def prefixEnd_731645 : Nat := 4983230072969 + 3 ^ 40 * 731645 * 2
def baseEnd_731645 : Nat := 333942714185684594909095

theorem tailTrace_731645 : CollatzResearch.WordTrace tailWord_731645 prefixEnd_731645 333942714185684594909095 := by
  unfold tailWord_731645
  simp only [CollatzResearch.WordTrace]
  refine ⟨26685285434382594862932389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17790190289588396575288259 26685285434382594862932389)
  ·
    refine ⟨5003491018946736536799823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26685285434382594862932389 5003491018946736536799823)
    ·
      refine ⟨7505236528420104805199735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5003491018946736536799823 7505236528420104805199735)
      ·
        refine ⟨11257854792630157207799603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7505236528420104805199735 11257854792630157207799603)
        ·
          refine ⟨16886782188945235811699405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11257854792630157207799603 16886782188945235811699405)
          ·
            refine ⟨6332543320854463429387277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16886782188945235811699405 6332543320854463429387277)
            ·
              refine ⟨2374703745320423786020229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6332543320854463429387277 2374703745320423786020229)
              ·
                refine ⟨445256952247579459878793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2374703745320423786020229 445256952247579459878793)
                ·
                  refine ⟨333942714185684594909095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 445256952247579459878793 333942714185684594909095)
                  ·
                    rfl

theorem cell20_731645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 4, 2].length) (baseStart_731645 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_731645 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_731645 prefixEnd_731645 := by exact prefixLift 731645
  have htrace : WordTrace (prefixWord ++ tailWord_731645) baseStart_731645 baseEnd_731645 := by
    simpa [prefixWord, tailWord_731645, baseEnd_731645] using wordTrace_append hprefix tailTrace_731645
  have hstable : (prefixWord ++ tailWord_731645).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731645).length < 2 ^ (prefixWord ++ tailWord_731645).sum := by decide
  have hdescent : baseEnd_731645 < baseStart_731645 := by decide
  rcases family_descends (prefixWord ++ tailWord_731645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731652 : List Nat := [2, 3, 2, 3, 1, 1, 3, 5]
def baseStart_731652 : Nat := 118140960795 + 731652 * 2 ^ 59
def prefixEnd_731652 : Nat := 4983230072969 + 3 ^ 40 * 731652 * 2
def baseEnd_731652 : Nat := 111315303058807893891911

theorem tailTrace_731652 : CollatzResearch.WordTrace tailWord_731652 prefixEnd_731652 111315303058807893891911 := by
  unfold tailWord_731652
  simp only [CollatzResearch.WordTrace]
  refine ⟨13342770372678617529218605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17790360496904823372291473 13342770372678617529218605)
  ·
    refine ⟨5003538889754481573456977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13342770372678617529218605 5003538889754481573456977)
    ·
      refine ⟨3752654167315861180092733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5003538889754481573456977 3752654167315861180092733)
      ·
        refine ⟨1407245312743447942534775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3752654167315861180092733 1407245312743447942534775)
        ·
          refine ⟨2110867969115171913802163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1407245312743447942534775 2110867969115171913802163)
          ·
            refine ⟨3166301953672757870703245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2110867969115171913802163 3166301953672757870703245)
            ·
              refine ⟨1187363232627284201513717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3166301953672757870703245 1187363232627284201513717)
              ·
                refine ⟨111315303058807893891911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1187363232627284201513717 111315303058807893891911)
                ·
                  rfl

theorem cell20_731652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 5].length) (baseStart_731652 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_731652 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_731652 prefixEnd_731652 := by exact prefixLift 731652
  have htrace : WordTrace (prefixWord ++ tailWord_731652) baseStart_731652 baseEnd_731652 := by
    simpa [prefixWord, tailWord_731652, baseEnd_731652] using wordTrace_append hprefix tailTrace_731652
  have hstable : (prefixWord ++ tailWord_731652).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731652).length < 2 ^ (prefixWord ++ tailWord_731652).sum := by decide
  have hdescent : baseEnd_731652 < baseStart_731652 := by decide
  rcases family_descends (prefixWord ++ tailWord_731652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731659 : List Nat := [1, 1, 1, 1, 7, 1, 2, 3, 3]
def baseStart_731659 : Nat := 118140960795 + 731659 * 2 ^ 59
def prefixEnd_731659 : Nat := 4983230072969 + 3 ^ 40 * 731659 * 2
def baseEnd_731659 : Nat := 333949104167162768442371

theorem tailTrace_731659 : CollatzResearch.WordTrace tailWord_731659 prefixEnd_731659 333949104167162768442371 := by
  unfold tailWord_731659
  simp only [CollatzResearch.WordTrace]
  refine ⟨26685796056331875253942031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17790530704221250169294687 26685796056331875253942031)
  ·
    refine ⟨40028694084497812880913047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26685796056331875253942031 40028694084497812880913047)
    ·
      refine ⟨60043041126746719321369571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40028694084497812880913047 60043041126746719321369571)
      ·
        refine ⟨90064561690120078982054357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60043041126746719321369571 90064561690120078982054357)
        ·
          refine ⟨2110888164612189351141899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 90064561690120078982054357 2110888164612189351141899)
          ·
            refine ⟨3166332246918284026712849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2110888164612189351141899 3166332246918284026712849)
            ·
              refine ⟨2374749185188713020034637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3166332246918284026712849 2374749185188713020034637)
              ·
                refine ⟨890530944445767382512989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2374749185188713020034637 890530944445767382512989)
                ·
                  refine ⟨333949104167162768442371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 890530944445767382512989 333949104167162768442371)
                  ·
                    rfl

theorem cell20_731659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 3, 3].length) (baseStart_731659 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_731659 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_731659 prefixEnd_731659 := by exact prefixLift 731659
  have htrace : WordTrace (prefixWord ++ tailWord_731659) baseStart_731659 baseEnd_731659 := by
    simpa [prefixWord, tailWord_731659, baseEnd_731659] using wordTrace_append hprefix tailTrace_731659
  have hstable : (prefixWord ++ tailWord_731659).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731659).length < 2 ^ (prefixWord ++ tailWord_731659).sum := by decide
  have hdescent : baseEnd_731659 < baseStart_731659 := by decide
  rcases family_descends (prefixWord ++ tailWord_731659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731683 : List Nat := [1, 1, 1, 4, 4, 1, 1, 5, 2]
def baseStart_731683 : Nat := 118140960795 + 731683 * 2 ^ 59
def prefixEnd_731683 : Nat := 4983230072969 + 3 ^ 40 * 731683 * 2
def baseEnd_731683 : Nat := 333960058421125351642273

theorem tailTrace_731683 : CollatzResearch.WordTrace tailWord_731683 prefixEnd_731683 333960058421125351642273 := by
  unfold tailWord_731683
  simp only [CollatzResearch.WordTrace]
  refine ⟨26686671408244927352815703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17791114272163284901877135 26686671408244927352815703)
  ·
    refine ⟨40030007112367391029223555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26686671408244927352815703 40030007112367391029223555)
    ·
      refine ⟨60045010668551086543835333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40030007112367391029223555 60045010668551086543835333)
      ·
        refine ⟨11258439500353328726969125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60045010668551086543835333 11258439500353328726969125)
        ·
          refine ⟨2110957406316249136306711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11258439500353328726969125 2110957406316249136306711)
          ·
            refine ⟨3166436109474373704460067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2110957406316249136306711 3166436109474373704460067)
            ·
              refine ⟨4749654164211560556690101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3166436109474373704460067 4749654164211560556690101)
              ·
                refine ⟨445280077894833802189697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4749654164211560556690101 445280077894833802189697)
                ·
                  refine ⟨333960058421125351642273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 445280077894833802189697 333960058421125351642273)
                  ·
                    rfl

theorem cell20_731683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 5, 2].length) (baseStart_731683 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_731683 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_731683 prefixEnd_731683 := by exact prefixLift 731683
  have htrace : WordTrace (prefixWord ++ tailWord_731683) baseStart_731683 baseEnd_731683 := by
    simpa [prefixWord, tailWord_731683, baseEnd_731683] using wordTrace_append hprefix tailTrace_731683
  have hstable : (prefixWord ++ tailWord_731683).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731683).length < 2 ^ (prefixWord ++ tailWord_731683).sum := by decide
  have hdescent : baseEnd_731683 < baseStart_731683 := by decide
  rcases family_descends (prefixWord ++ tailWord_731683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731697 : List Nat := [1, 2, 2, 3, 1, 1, 5, 2, 3]
def baseStart_731697 : Nat := 118140960795 + 731697 * 2 ^ 59
def prefixEnd_731697 : Nat := 4983230072969 + 3 ^ 40 * 731697 * 2
def baseEnd_731697 : Nat := 333966448402603525175549

theorem tailTrace_731697 : CollatzResearch.WordTrace tailWord_731697 prefixEnd_731697 333966448402603525175549 := by
  unfold tailWord_731697
  simp only [CollatzResearch.WordTrace]
  refine ⟨26687182030194207743825345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17791454686796138495883563 26687182030194207743825345)
  ·
    refine ⟨20015386522645655807869009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26687182030194207743825345 20015386522645655807869009)
    ·
      refine ⟨15011539891984241855901757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20015386522645655807869009 15011539891984241855901757)
      ·
        refine ⟨5629327459494090695963159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15011539891984241855901757 5629327459494090695963159)
        ·
          refine ⟨8443991189241136043944739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5629327459494090695963159 8443991189241136043944739)
          ·
            refine ⟨12665986783861704065917109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8443991189241136043944739 12665986783861704065917109)
            ·
              refine ⟨1187436260987034756179729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12665986783861704065917109 1187436260987034756179729)
              ·
                refine ⟨890577195740276067134797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1187436260987034756179729 890577195740276067134797)
                ·
                  refine ⟨333966448402603525175549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 890577195740276067134797 333966448402603525175549)
                  ·
                    rfl

theorem cell20_731697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 2, 3].length) (baseStart_731697 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_731697 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_731697 prefixEnd_731697 := by exact prefixLift 731697
  have htrace : WordTrace (prefixWord ++ tailWord_731697) baseStart_731697 baseEnd_731697 := by
    simpa [prefixWord, tailWord_731697, baseEnd_731697] using wordTrace_append hprefix tailTrace_731697
  have hstable : (prefixWord ++ tailWord_731697).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731697).length < 2 ^ (prefixWord ++ tailWord_731697).sum := by decide
  have hdescent : baseEnd_731697 < baseStart_731697 := by decide
  rcases family_descends (prefixWord ++ tailWord_731697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731704 : List Nat := [2, 1, 2, 1, 4, 1, 4, 1, 4]
def baseStart_731704 : Nat := 118140960795 + 731704 * 2 ^ 59
def prefixEnd_731704 : Nat := 4983230072969 + 3 ^ 40 * 731704 * 2
def baseEnd_731704 : Nat := 333969643393342611942187

theorem tailTrace_731704 : CollatzResearch.WordTrace tailWord_731704 prefixEnd_731704 333969643393342611942187 := by
  unfold tailWord_731704
  simp only [CollatzResearch.WordTrace]
  refine ⟨13343718670584423969665083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17791624894112565292886777 13343718670584423969665083)
  ·
    refine ⟨20015578005876635954497625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13343718670584423969665083 20015578005876635954497625)
    ·
      refine ⟨15011683504407476965873219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20015578005876635954497625 15011683504407476965873219)
      ·
        refine ⟨22517525256611215448809829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15011683504407476965873219 22517525256611215448809829)
        ·
          refine ⟨4222035985614602896651843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22517525256611215448809829 4222035985614602896651843)
          ·
            refine ⟨6333053978421904344977765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4222035985614602896651843 6333053978421904344977765)
            ·
              refine ⟨1187447620954107064683331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6333053978421904344977765 1187447620954107064683331)
              ·
                refine ⟨1781171431431160597024997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1187447620954107064683331 1781171431431160597024997)
                ·
                  refine ⟨333969643393342611942187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1781171431431160597024997 333969643393342611942187)
                  ·
                    rfl

theorem cell20_731704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 1, 4].length) (baseStart_731704 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_731704 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_731704 prefixEnd_731704 := by exact prefixLift 731704
  have htrace : WordTrace (prefixWord ++ tailWord_731704) baseStart_731704 baseEnd_731704 := by
    simpa [prefixWord, tailWord_731704, baseEnd_731704] using wordTrace_append hprefix tailTrace_731704
  have hstable : (prefixWord ++ tailWord_731704).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731704).length < 2 ^ (prefixWord ++ tailWord_731704).sum := by decide
  have hdescent : baseEnd_731704 < baseStart_731704 := by decide
  rcases family_descends (prefixWord ++ tailWord_731704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731710 : List Nat := [4, 2, 1, 4, 1, 1, 3, 1, 3]
def baseStart_731710 : Nat := 118140960795 + 731710 * 2 ^ 59
def prefixEnd_731710 : Nat := 4983230072969 + 3 ^ 40 * 731710 * 2
def baseEnd_731710 : Nat := 333972381956833257742163

theorem tailTrace_731710 : CollatzResearch.WordTrace tailWord_731710 prefixEnd_731710 333972381956833257742163 := by
  unfold tailWord_731710
  simp only [CollatzResearch.WordTrace]
  refine ⟨3335957022393388870506073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17791770786098073976032389 3335957022393388870506073)
  ·
    refine ⟨2501967766795041652879555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3335957022393388870506073 2501967766795041652879555)
    ·
      refine ⟨3752951650192562479319333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2501967766795041652879555 3752951650192562479319333)
      ·
        refine ⟨703678434411105464872375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3752951650192562479319333 703678434411105464872375)
        ·
          refine ⟨1055517651616658197308563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 703678434411105464872375 1055517651616658197308563)
          ·
            refine ⟨1583276477424987295962845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1055517651616658197308563 1583276477424987295962845)
            ·
              refine ⟨593728679034370235986067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1583276477424987295962845 593728679034370235986067)
              ·
                refine ⟨890593018551555353979101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 593728679034370235986067 890593018551555353979101)
                ·
                  refine ⟨333972381956833257742163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 890593018551555353979101 333972381956833257742163)
                  ·
                    rfl

theorem cell20_731710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_731710 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_731710 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_731710 prefixEnd_731710 := by exact prefixLift 731710
  have htrace : WordTrace (prefixWord ++ tailWord_731710) baseStart_731710 baseEnd_731710 := by
    simpa [prefixWord, tailWord_731710, baseEnd_731710] using wordTrace_append hprefix tailTrace_731710
  have hstable : (prefixWord ++ tailWord_731710).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731710).length < 2 ^ (prefixWord ++ tailWord_731710).sum := by decide
  have hdescent : baseEnd_731710 < baseStart_731710 := by decide
  rcases family_descends (prefixWord ++ tailWord_731710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731756 : List Nat := [2, 2, 1, 1, 3, 1, 4, 1, 5]
def baseStart_731756 : Nat := 118140960795 + 731756 * 2 ^ 59
def prefixEnd_731756 : Nat := 4983230072969 + 3 ^ 40 * 731756 * 2
def baseEnd_731756 : Nat := 333993377610261542208641

theorem tailTrace_731756 : CollatzResearch.WordTrace tailWord_731756 prefixEnd_731756 333993377610261542208641 := by
  unfold tailWord_731756
  simp only [CollatzResearch.WordTrace]
  refine ⟨13344666968490230410111561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17792889291320307213482081 13344666968490230410111561)
  ·
    refine ⟨10008500226367672807583671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13344666968490230410111561 10008500226367672807583671)
    ·
      refine ⟨15012750339551509211375507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10008500226367672807583671 15012750339551509211375507)
      ·
        refine ⟨22519125509327263817063261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15012750339551509211375507 22519125509327263817063261)
        ·
          refine ⟨8444672065997723931398723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22519125509327263817063261 8444672065997723931398723)
          ·
            refine ⟨12667008098996585897098085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8444672065997723931398723 12667008098996585897098085)
            ·
              refine ⟨2375064018561859855705891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12667008098996585897098085 2375064018561859855705891)
              ·
                refine ⟨3562596027842789783558837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2375064018561859855705891 3562596027842789783558837)
                ·
                  refine ⟨333993377610261542208641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3562596027842789783558837 333993377610261542208641)
                  ·
                    rfl

theorem cell20_731756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 5].length) (baseStart_731756 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_731756 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_731756 prefixEnd_731756 := by exact prefixLift 731756
  have htrace : WordTrace (prefixWord ++ tailWord_731756) baseStart_731756 baseEnd_731756 := by
    simpa [prefixWord, tailWord_731756, baseEnd_731756] using wordTrace_append hprefix tailTrace_731756
  have hstable : (prefixWord ++ tailWord_731756).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731756).length < 2 ^ (prefixWord ++ tailWord_731756).sum := by decide
  have hdescent : baseEnd_731756 < baseStart_731756 := by decide
  rcases family_descends (prefixWord ++ tailWord_731756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731763 : List Nat := [1, 1, 1, 2, 2, 1, 1, 7, 4]
def baseStart_731763 : Nat := 118140960795 + 731763 * 2 ^ 59
def prefixEnd_731763 : Nat := 4983230072969 + 3 ^ 40 * 731763 * 2
def baseEnd_731763 : Nat := 333996572601000628975279

theorem tailTrace_731763 : CollatzResearch.WordTrace tailWord_731763 prefixEnd_731763 333996572601000628975279 := by
  unfold tailWord_731763
  simp only [CollatzResearch.WordTrace]
  refine ⟨26689589247955101015727943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17793059498636734010485295 26689589247955101015727943)
  ·
    refine ⟨40034383871932651523591915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26689589247955101015727943 40034383871932651523591915)
    ·
      refine ⟨60051575807898977285387873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40034383871932651523591915 60051575807898977285387873)
      ·
        refine ⟨45038681855924232964040905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60051575807898977285387873 45038681855924232964040905)
        ·
          refine ⟨33779011391943174723030679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45038681855924232964040905 33779011391943174723030679)
          ·
            refine ⟨50668517087914762084546019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33779011391943174723030679 50668517087914762084546019)
            ·
              refine ⟨76002775631872143126819029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50668517087914762084546019 76002775631872143126819029)
              ·
                refine ⟨1781315053872003354534821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 76002775631872143126819029 1781315053872003354534821)
                ·
                  refine ⟨333996572601000628975279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1781315053872003354534821 333996572601000628975279)
                  ·
                    rfl

theorem cell20_731763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 7, 4].length) (baseStart_731763 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_731763 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_731763 prefixEnd_731763 := by exact prefixLift 731763
  have htrace : WordTrace (prefixWord ++ tailWord_731763) baseStart_731763 baseEnd_731763 := by
    simpa [prefixWord, tailWord_731763, baseEnd_731763] using wordTrace_append hprefix tailTrace_731763
  have hstable : (prefixWord ++ tailWord_731763).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731763).length < 2 ^ (prefixWord ++ tailWord_731763).sum := by decide
  have hdescent : baseEnd_731763 < baseStart_731763 := by decide
  rcases family_descends (prefixWord ++ tailWord_731763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731808 : List Nat := [2, 1, 1, 4, 12]
def baseStart_731808 : Nat := 118140960795 + 731808 * 2 ^ 59
def prefixEnd_731808 : Nat := 4983230072969 + 3 ^ 40 * 731808 * 2
def baseEnd_731808 : Nat := 4123668047249141635495

theorem tailTrace_731808 : CollatzResearch.WordTrace tailWord_731808 prefixEnd_731808 4123668047249141635495 := by
  unfold tailWord_731808
  simp only [CollatzResearch.WordTrace]
  refine ⟨13345615266396036850558039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17794153688528049134077385 13345615266396036850558039)
  ·
    refine ⟨20018422899594055275837059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13345615266396036850558039 20018422899594055275837059)
    ·
      refine ⟨30027634349391082913755589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20018422899594055275837059 30027634349391082913755589)
      ·
        refine ⟨5630181440510828046329173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30027634349391082913755589 5630181440510828046329173)
        ·
          refine ⟨4123668047249141635495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 5630181440510828046329173 4123668047249141635495)
          ·
            rfl

theorem cell20_731808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 12].length) (baseStart_731808 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_731808 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_731808 prefixEnd_731808 := by exact prefixLift 731808
  have htrace : WordTrace (prefixWord ++ tailWord_731808) baseStart_731808 baseEnd_731808 := by
    simpa [prefixWord, tailWord_731808, baseEnd_731808] using wordTrace_append hprefix tailTrace_731808
  have hstable : (prefixWord ++ tailWord_731808).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731808).length < 2 ^ (prefixWord ++ tailWord_731808).sum := by decide
  have hdescent : baseEnd_731808 < baseStart_731808 := by decide
  rcases family_descends (prefixWord ++ tailWord_731808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731839 : List Nat := [1, 1, 2, 2, 2, 4, 1, 1, 6]
def baseStart_731839 : Nat := 118140960795 + 731839 * 2 ^ 59
def prefixEnd_731839 : Nat := 4983230072969 + 3 ^ 40 * 731839 * 2
def baseEnd_731839 : Nat := 334031261071882142441635

theorem tailTrace_731839 : CollatzResearch.WordTrace tailWord_731839 prefixEnd_731839 334031261071882142441635 := by
  unfold tailWord_731839
  simp only [CollatzResearch.WordTrace]
  refine ⟨26692361195679765995494571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17794907463786510663663047 26692361195679765995494571)
  ·
    refine ⟨40038541793519648993241857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26692361195679765995494571 40038541793519648993241857)
    ·
      refine ⟨30028906345139736744931393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40038541793519648993241857 30028906345139736744931393)
      ·
        refine ⟨22521679758854802558698545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30028906345139736744931393 22521679758854802558698545)
        ·
          refine ⟨16891259819141101919023909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22521679758854802558698545 16891259819141101919023909)
          ·
            refine ⟨3167111216088956609816983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16891259819141101919023909 3167111216088956609816983)
            ·
              refine ⟨4750666824133434914725475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3167111216088956609816983 4750666824133434914725475)
              ·
                refine ⟨7126000236200152372088213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4750666824133434914725475 7126000236200152372088213)
                ·
                  refine ⟨334031261071882142441635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7126000236200152372088213 334031261071882142441635)
                  ·
                    rfl

theorem cell20_731839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 6].length) (baseStart_731839 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_731839 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_731839 prefixEnd_731839 := by exact prefixLift 731839
  have htrace : WordTrace (prefixWord ++ tailWord_731839) baseStart_731839 baseEnd_731839 := by
    simpa [prefixWord, tailWord_731839, baseEnd_731839] using wordTrace_append hprefix tailTrace_731839
  have hstable : (prefixWord ++ tailWord_731839).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731839).length < 2 ^ (prefixWord ++ tailWord_731839).sum := by decide
  have hdescent : baseEnd_731839 < baseStart_731839 := by decide
  rcases family_descends (prefixWord ++ tailWord_731839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731852 : List Nat := [2, 2, 1, 5, 1, 2, 2, 3, 2]
def baseStart_731852 : Nat := 118140960795 + 731852 * 2 ^ 59
def prefixEnd_731852 : Nat := 4983230072969 + 3 ^ 40 * 731852 * 2
def baseEnd_731852 : Nat := 334037194626111875008249

theorem tailTrace_731852 : CollatzResearch.WordTrace tailWord_731852 prefixEnd_731852 334037194626111875008249 := by
  unfold tailWord_731852
  simp only [CollatzResearch.WordTrace]
  refine ⟨13346417672316334607858905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17795223563088446143811873 13346417672316334607858905)
  ·
    refine ⟨10009813254237250955894179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13346417672316334607858905 10009813254237250955894179)
    ·
      refine ⟨15014719881355876433841269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10009813254237250955894179 15014719881355876433841269)
      ·
        refine ⟨1407629988877113415672619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15014719881355876433841269 1407629988877113415672619)
        ·
          refine ⟨2111444983315670123508929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1407629988877113415672619 2111444983315670123508929)
          ·
            refine ⟨1583583737486752592631697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2111444983315670123508929 1583583737486752592631697)
            ·
              refine ⟨1187687803115064444473773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1583583737486752592631697 1187687803115064444473773)
              ·
                refine ⟨445382926168149166677665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1187687803115064444473773 445382926168149166677665)
                ·
                  refine ⟨334037194626111875008249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 445382926168149166677665 334037194626111875008249)
                  ·
                    rfl

theorem cell20_731852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 3, 2].length) (baseStart_731852 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_731852 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_731852 prefixEnd_731852 := by exact prefixLift 731852
  have htrace : WordTrace (prefixWord ++ tailWord_731852) baseStart_731852 baseEnd_731852 := by
    simpa [prefixWord, tailWord_731852, baseEnd_731852] using wordTrace_append hprefix tailTrace_731852
  have hstable : (prefixWord ++ tailWord_731852).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731852).length < 2 ^ (prefixWord ++ tailWord_731852).sum := by decide
  have hdescent : baseEnd_731852 < baseStart_731852 := by decide
  rcases family_descends (prefixWord ++ tailWord_731852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731873 : List Nat := [1, 2, 3, 1, 4, 1, 2, 4, 2]
def baseStart_731873 : Nat := 118140960795 + 731873 * 2 ^ 59
def prefixEnd_731873 : Nat := 4983230072969 + 3 ^ 40 * 731873 * 2
def baseEnd_731873 : Nat := 334046779598329135308163

theorem tailTrace_731873 : CollatzResearch.WordTrace tailWord_731873 prefixEnd_731873 334046779598329135308163 := by
  unfold tailWord_731873
  simp only [CollatzResearch.WordTrace]
  refine ⟨26693601277556589802232273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17795734185037726534821515 26693601277556589802232273)
  ·
    refine ⟨20020200958167442351674205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26693601277556589802232273 20020200958167442351674205)
    ·
      refine ⟨7507575359312790881877827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20020200958167442351674205 7507575359312790881877827)
      ·
        refine ⟨11261363038969186322816741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7507575359312790881877827 11261363038969186322816741)
        ·
          refine ⟨2111505569806722435528139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11261363038969186322816741 2111505569806722435528139)
          ·
            refine ⟨3167258354710083653292209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2111505569806722435528139 3167258354710083653292209)
            ·
              refine ⟨2375443766032562739969157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3167258354710083653292209 2375443766032562739969157)
              ·
                refine ⟨445395706131105513744217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2375443766032562739969157 445395706131105513744217)
                ·
                  refine ⟨334046779598329135308163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 445395706131105513744217 334046779598329135308163)
                  ·
                    rfl

theorem cell20_731873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 4, 2].length) (baseStart_731873 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_731873 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_731873 prefixEnd_731873 := by exact prefixLift 731873
  have htrace : WordTrace (prefixWord ++ tailWord_731873) baseStart_731873 baseEnd_731873 := by
    simpa [prefixWord, tailWord_731873, baseEnd_731873] using wordTrace_append hprefix tailTrace_731873
  have hstable : (prefixWord ++ tailWord_731873).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731873).length < 2 ^ (prefixWord ++ tailWord_731873).sum := by decide
  have hdescent : baseEnd_731873 < baseStart_731873 := by decide
  rcases family_descends (prefixWord ++ tailWord_731873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731884 : List Nat := [2, 2, 1, 1, 2, 2, 1, 9]
def baseStart_731884 : Nat := 118140960795 + 731884 * 2 ^ 59
def prefixEnd_731884 : Nat := 4983230072969 + 3 ^ 40 * 731884 * 2
def baseEnd_731884 : Nat := 111350600099353995313817

theorem tailTrace_731884 : CollatzResearch.WordTrace tailWord_731884 prefixEnd_731884 111350600099353995313817 := by
  unfold tailWord_731884
  simp only [CollatzResearch.WordTrace]
  refine ⟨13347001240258369340441353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17796001653677825787255137 13347001240258369340441353)
  ·
    refine ⟨10010250930193777005331015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13347001240258369340441353 10010250930193777005331015)
    ·
      refine ⟨15015376395290665507996523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10010250930193777005331015 15015376395290665507996523)
      ·
        refine ⟨22523064592935998261994785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15015376395290665507996523 22523064592935998261994785)
        ·
          refine ⟨16892298444701998696496089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22523064592935998261994785 16892298444701998696496089)
          ·
            refine ⟨12669223833526499022372067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16892298444701998696496089 12669223833526499022372067)
            ·
              refine ⟨19003835750289748533558101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12669223833526499022372067 19003835750289748533558101)
              ·
                refine ⟨111350600099353995313817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19003835750289748533558101 111350600099353995313817)
                ·
                  rfl

theorem cell20_731884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 9].length) (baseStart_731884 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_731884 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_731884 prefixEnd_731884 := by exact prefixLift 731884
  have htrace : WordTrace (prefixWord ++ tailWord_731884) baseStart_731884 baseEnd_731884 := by
    simpa [prefixWord, tailWord_731884, baseEnd_731884] using wordTrace_append hprefix tailTrace_731884
  have hstable : (prefixWord ++ tailWord_731884).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731884).length < 2 ^ (prefixWord ++ tailWord_731884).sum := by decide
  have hdescent : baseEnd_731884 < baseStart_731884 := by decide
  rcases family_descends (prefixWord ++ tailWord_731884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731893 : List Nat := [1, 3, 6, 1, 1, 2, 2, 4]
def baseStart_731893 : Nat := 118140960795 + 731893 * 2 ^ 59
def prefixEnd_731893 : Nat := 4983230072969 + 3 ^ 40 * 731893 * 2
def baseEnd_731893 : Nat := 111351969381099318213805

theorem tailTrace_731893 : CollatzResearch.WordTrace tailWord_731893 prefixEnd_731893 111351969381099318213805 := by
  unfold tailWord_731893
  simp only [CollatzResearch.WordTrace]
  refine ⟨26694330737484133217960333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17796220491656088811973555 26694330737484133217960333)
  ·
    refine ⟨10010374026556549956735125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26694330737484133217960333 10010374026556549956735125)
    ·
      refine ⟨469236282494838279221959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 10010374026556549956735125 469236282494838279221959)
      ·
        refine ⟨703854423742257418832939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 469236282494838279221959 703854423742257418832939)
        ·
          refine ⟨1055781635613386128249409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 703854423742257418832939 1055781635613386128249409)
          ·
            refine ⟨791836226710039596187057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1055781635613386128249409 791836226710039596187057)
            ·
              refine ⟨593877170032529697140293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 791836226710039596187057 593877170032529697140293)
              ·
                refine ⟨111351969381099318213805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 593877170032529697140293 111351969381099318213805)
                ·
                  rfl

theorem cell20_731893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 2, 4].length) (baseStart_731893 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_731893 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_731893 prefixEnd_731893 := by exact prefixLift 731893
  have htrace : WordTrace (prefixWord ++ tailWord_731893) baseStart_731893 baseEnd_731893 := by
    simpa [prefixWord, tailWord_731893, baseEnd_731893] using wordTrace_append hprefix tailTrace_731893
  have hstable : (prefixWord ++ tailWord_731893).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731893).length < 2 ^ (prefixWord ++ tailWord_731893).sum := by decide
  have hdescent : baseEnd_731893 < baseStart_731893 := by decide
  rcases family_descends (prefixWord ++ tailWord_731893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731894 : List Nat := [5, 1, 1, 1, 1, 2, 1, 4, 4]
def baseStart_731894 : Nat := 118140960795 + 731894 * 2 ^ 59
def prefixEnd_731894 : Nat := 4983230072969 + 3 ^ 40 * 731894 * 2
def baseEnd_731894 : Nat := 334056364570546395608077

theorem tailTrace_731894 : CollatzResearch.WordTrace tailWord_731894 prefixEnd_731894 334056364570546395608077 := by
  unfold tailWord_731894
  simp only [CollatzResearch.WordTrace]
  refine ⟨1668397950655031899296671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17796244806987006925831157 1668397950655031899296671)
  ·
    refine ⟨2502596925982547848945007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1668397950655031899296671 2502596925982547848945007)
    ·
      refine ⟨3753895388973821773417511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2502596925982547848945007 3753895388973821773417511)
      ·
        refine ⟨5630843083460732660126267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3753895388973821773417511 5630843083460732660126267)
        ·
          refine ⟨8446264625191098990189401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5630843083460732660126267 8446264625191098990189401)
          ·
            refine ⟨6334698468893324242642051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8446264625191098990189401 6334698468893324242642051)
            ·
              refine ⟨9502047703339986363963077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6334698468893324242642051 9502047703339986363963077)
              ·
                refine ⟨1781633944376247443243077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9502047703339986363963077 1781633944376247443243077)
                ·
                  refine ⟨334056364570546395608077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1781633944376247443243077 334056364570546395608077)
                  ·
                    rfl

theorem cell20_731894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_731894 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_731894 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_731894 prefixEnd_731894 := by exact prefixLift 731894
  have htrace : WordTrace (prefixWord ++ tailWord_731894) baseStart_731894 baseEnd_731894 := by
    simpa [prefixWord, tailWord_731894, baseEnd_731894] using wordTrace_append hprefix tailTrace_731894
  have hstable : (prefixWord ++ tailWord_731894).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731894).length < 2 ^ (prefixWord ++ tailWord_731894).sum := by decide
  have hdescent : baseEnd_731894 < baseStart_731894 := by decide
  rcases family_descends (prefixWord ++ tailWord_731894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731908 : List Nat := [2, 3, 2, 2, 1, 1, 1, 1, 7]
def baseStart_731908 : Nat := 118140960795 + 731908 * 2 ^ 59
def prefixEnd_731908 : Nat := 4983230072969 + 3 ^ 40 * 731908 * 2
def baseEnd_731908 : Nat := 334062754552024569141353

theorem tailTrace_731908 : CollatzResearch.WordTrace tailWord_731908 prefixEnd_731908 334062754552024569141353 := by
  unfold tailWord_731908
  simp only [CollatzResearch.WordTrace]
  refine ⟨13347438916214895389878189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17796585221619860519837585 13347438916214895389878189)
  ·
    refine ⟨5005289593580585771204321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13347438916214895389878189 5005289593580585771204321)
    ·
      refine ⟨3753967195185439328403241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5005289593580585771204321 3753967195185439328403241)
      ·
        refine ⟨2815475396389079496302431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3753967195185439328403241 2815475396389079496302431)
        ·
          refine ⟨4223213094583619244453647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2815475396389079496302431 4223213094583619244453647)
          ·
            refine ⟨6334819641875428866680471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4223213094583619244453647 6334819641875428866680471)
            ·
              refine ⟨9502229462813143300020707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6334819641875428866680471 9502229462813143300020707)
              ·
                refine ⟨14253344194219714950031061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9502229462813143300020707 14253344194219714950031061)
                ·
                  refine ⟨334062754552024569141353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14253344194219714950031061 334062754552024569141353)
                  ·
                    rfl

theorem cell20_731908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_731908 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_731908 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_731908 prefixEnd_731908 := by exact prefixLift 731908
  have htrace : WordTrace (prefixWord ++ tailWord_731908) baseStart_731908 baseEnd_731908 := by
    simpa [prefixWord, tailWord_731908, baseEnd_731908] using wordTrace_append hprefix tailTrace_731908
  have hstable : (prefixWord ++ tailWord_731908).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731908).length < 2 ^ (prefixWord ++ tailWord_731908).sum := by decide
  have hdescent : baseEnd_731908 < baseStart_731908 := by decide
  rcases family_descends (prefixWord ++ tailWord_731908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731932 : List Nat := [2, 2, 3, 1, 1, 3, 3, 1, 4]
def baseStart_731932 : Nat := 118140960795 + 731932 * 2 ^ 59
def prefixEnd_731932 : Nat := 4983230072969 + 3 ^ 40 * 731932 * 2
def baseEnd_731932 : Nat := 334073708805987152341255

theorem tailTrace_731932 : CollatzResearch.WordTrace tailWord_731932 prefixEnd_731932 334073708805987152341255 := by
  unfold tailWord_731932
  simp only [CollatzResearch.WordTrace]
  refine ⟨13347876592171421439315025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17797168789561895252420033 13347876592171421439315025)
  ·
    refine ⟨10010907444128566079486269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13347876592171421439315025 10010907444128566079486269)
    ·
      refine ⟨3754090291548212279807351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10010907444128566079486269 3754090291548212279807351)
      ·
        refine ⟨5631135437322318419711027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3754090291548212279807351 5631135437322318419711027)
        ·
          refine ⟨8446703155983477629566541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5631135437322318419711027 8446703155983477629566541)
          ·
            refine ⟨3167513683493804111087453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8446703155983477629566541 3167513683493804111087453)
            ·
              refine ⟨1187817631310176541657795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3167513683493804111087453 1187817631310176541657795)
              ·
                refine ⟨1781726446965264812486693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1187817631310176541657795 1781726446965264812486693)
                ·
                  refine ⟨334073708805987152341255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1781726446965264812486693 334073708805987152341255)
                  ·
                    rfl

theorem cell20_731932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 1, 4].length) (baseStart_731932 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_731932 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_731932 prefixEnd_731932 := by exact prefixLift 731932
  have htrace : WordTrace (prefixWord ++ tailWord_731932) baseStart_731932 baseEnd_731932 := by
    simpa [prefixWord, tailWord_731932, baseEnd_731932] using wordTrace_append hprefix tailTrace_731932
  have hstable : (prefixWord ++ tailWord_731932).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731932).length < 2 ^ (prefixWord ++ tailWord_731932).sum := by decide
  have hdescent : baseEnd_731932 < baseStart_731932 := by decide
  rcases family_descends (prefixWord ++ tailWord_731932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731953 : List Nat := [1, 2, 2, 3, 2, 1, 2, 1, 6]
def baseStart_731953 : Nat := 118140960795 + 731953 * 2 ^ 59
def prefixEnd_731953 : Nat := 4983230072969 + 3 ^ 40 * 731953 * 2
def baseEnd_731953 : Nat := 334083293778204412641169

theorem tailTrace_731953 : CollatzResearch.WordTrace tailWord_731953 prefixEnd_731953 334083293778204412641169 := by
  unfold tailWord_731953
  simp only [CollatzResearch.WordTrace]
  refine ⟨26696519117266763465144513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17797679411511175643429675 26696519117266763465144513)
  ·
    refine ⟨20022389337950072598858385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26696519117266763465144513 20022389337950072598858385)
    ·
      refine ⟨15016792003462554449143789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20022389337950072598858385 15016792003462554449143789)
      ·
        refine ⟨5631297001298457918428921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15016792003462554449143789 5631297001298457918428921)
        ·
          refine ⟨4223472750973843438821691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5631297001298457918428921 4223472750973843438821691)
          ·
            refine ⟨6335209126460765158232537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4223472750973843438821691 6335209126460765158232537)
            ·
              refine ⟨4751406844845573868674403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6335209126460765158232537 4751406844845573868674403)
              ·
                refine ⟨7127110267268360803011605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4751406844845573868674403 7127110267268360803011605)
                ·
                  refine ⟨334083293778204412641169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7127110267268360803011605 334083293778204412641169)
                  ·
                    rfl

theorem cell20_731953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 6].length) (baseStart_731953 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_731953 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_731953 prefixEnd_731953 := by exact prefixLift 731953
  have htrace : WordTrace (prefixWord ++ tailWord_731953) baseStart_731953 baseEnd_731953 := by
    simpa [prefixWord, tailWord_731953, baseEnd_731953] using wordTrace_append hprefix tailTrace_731953
  have hstable : (prefixWord ++ tailWord_731953).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731953).length < 2 ^ (prefixWord ++ tailWord_731953).sum := by decide
  have hdescent : baseEnd_731953 < baseStart_731953 := by decide
  rcases family_descends (prefixWord ++ tailWord_731953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731960 : List Nat := [2, 1, 2, 1, 3, 2, 1, 8]
def baseStart_731960 : Nat := 118140960795 + 731960 * 2 ^ 59
def prefixEnd_731960 : Nat := 4983230072969 + 3 ^ 40 * 731960 * 2
def baseEnd_731960 : Nat := 111362162922981166469269

theorem tailTrace_731960 : CollatzResearch.WordTrace tailWord_731960 prefixEnd_731960 111362162922981166469269 := by
  unfold tailWord_731960
  simp only [CollatzResearch.WordTrace]
  refine ⟨13348387214120701830324667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17797849618827602440432889 13348387214120701830324667)
  ·
    refine ⟨20022580821181052745487001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13348387214120701830324667 20022580821181052745487001)
    ·
      refine ⟨15016935615885789559115251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20022580821181052745487001 15016935615885789559115251)
      ·
        refine ⟨22525403423828684338672877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15016935615885789559115251 22525403423828684338672877)
        ·
          refine ⟨8447026283935756627002329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22525403423828684338672877 8447026283935756627002329)
          ·
            refine ⟨6335269712951817470251747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8447026283935756627002329 6335269712951817470251747)
            ·
              refine ⟨9502904569427726205377621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6335269712951817470251747 9502904569427726205377621)
              ·
                refine ⟨111362162922981166469269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9502904569427726205377621 111362162922981166469269)
                ·
                  rfl

theorem cell20_731960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 8].length) (baseStart_731960 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_731960 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_731960 prefixEnd_731960 := by exact prefixLift 731960
  have htrace : WordTrace (prefixWord ++ tailWord_731960) baseStart_731960 baseEnd_731960 := by
    simpa [prefixWord, tailWord_731960, baseEnd_731960] using wordTrace_append hprefix tailTrace_731960
  have hstable : (prefixWord ++ tailWord_731960).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731960).length < 2 ^ (prefixWord ++ tailWord_731960).sum := by decide
  have hdescent : baseEnd_731960 < baseStart_731960 := by decide
  rcases family_descends (prefixWord ++ tailWord_731960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_731984 : List Nat := [2, 1, 1, 1, 1, 4, 3, 4, 3]
def baseStart_731984 : Nat := 118140960795 + 731984 * 2 ^ 59
def prefixEnd_731984 : Nat := 4983230072969 + 3 ^ 40 * 731984 * 2
def baseEnd_731984 : Nat := 334097443022906082607709

theorem tailTrace_731984 : CollatzResearch.WordTrace tailWord_731984 prefixEnd_731984 334097443022906082607709 := by
  unfold tailWord_731984
  simp only [CollatzResearch.WordTrace]
  refine ⟨13348824890077227879761503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17798433186769637173015337 13348824890077227879761503)
  ·
    refine ⟨20023237335115841819642255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13348824890077227879761503 20023237335115841819642255)
    ·
      refine ⟨30034856002673762729463383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20023237335115841819642255 30034856002673762729463383)
      ·
        refine ⟨45052284004010644094195075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30034856002673762729463383 45052284004010644094195075)
        ·
          refine ⟨67578426006015966141292613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45052284004010644094195075 67578426006015966141292613)
          ·
            refine ⟨12670954876127993651492365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67578426006015966141292613 12670954876127993651492365)
            ·
              refine ⟨4751608078547997619309637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12670954876127993651492365 4751608078547997619309637)
              ·
                refine ⟨890926514727749553620557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4751608078547997619309637 890926514727749553620557)
                ·
                  refine ⟨334097443022906082607709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 890926514727749553620557 334097443022906082607709)
                  ·
                    rfl

theorem cell20_731984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 4, 3].length) (baseStart_731984 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_731984 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_731984 prefixEnd_731984 := by exact prefixLift 731984
  have htrace : WordTrace (prefixWord ++ tailWord_731984) baseStart_731984 baseEnd_731984 := by
    simpa [prefixWord, tailWord_731984, baseEnd_731984] using wordTrace_append hprefix tailTrace_731984
  have hstable : (prefixWord ++ tailWord_731984).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_731984).length < 2 ^ (prefixWord ++ tailWord_731984).sum := by decide
  have hdescent : baseEnd_731984 < baseStart_731984 := by decide
  rcases family_descends (prefixWord ++ tailWord_731984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732008 : List Nat := [2, 1, 4, 2, 1, 3, 1, 2, 4]
def baseStart_732008 : Nat := 118140960795 + 732008 * 2 ^ 59
def prefixEnd_732008 : Nat := 4983230072969 + 3 ^ 40 * 732008 * 2
def baseEnd_732008 : Nat := 334108397276868665807611

theorem tailTrace_732008 : CollatzResearch.WordTrace tailWord_732008 prefixEnd_732008 334108397276868665807611 := by
  unfold tailWord_732008
  simp only [CollatzResearch.WordTrace]
  refine ⟨13349262566033753929198339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17799016754711671905597785 13349262566033753929198339)
  ·
    refine ⟨20023893849050630893797509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13349262566033753929198339 20023893849050630893797509)
    ·
      refine ⟨3754480096696993292587033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20023893849050630893797509 3754480096696993292587033)
      ·
        refine ⟨2815860072522744969440275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3754480096696993292587033 2815860072522744969440275)
        ·
          refine ⟨4223790108784117454160413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2815860072522744969440275 4223790108784117454160413)
          ·
            refine ⟨1583921290794044045310155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4223790108784117454160413 1583921290794044045310155)
            ·
              refine ⟨2375881936191066067965233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1583921290794044045310155 2375881936191066067965233)
              ·
                refine ⟨1781911452143299550973925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2375881936191066067965233 1781911452143299550973925)
                ·
                  refine ⟨334108397276868665807611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1781911452143299550973925 334108397276868665807611)
                  ·
                    rfl

theorem cell20_732008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 2, 4].length) (baseStart_732008 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_732008 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_732008 prefixEnd_732008 := by exact prefixLift 732008
  have htrace : WordTrace (prefixWord ++ tailWord_732008) baseStart_732008 baseEnd_732008 := by
    simpa [prefixWord, tailWord_732008, baseEnd_732008] using wordTrace_append hprefix tailTrace_732008
  have hstable : (prefixWord ++ tailWord_732008).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732008).length < 2 ^ (prefixWord ++ tailWord_732008).sum := by decide
  have hdescent : baseEnd_732008 < baseStart_732008 := by decide
  rcases family_descends (prefixWord ++ tailWord_732008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732025 : List Nat := [1, 2, 1, 3, 2, 4, 2, 3, 2]
def baseStart_732025 : Nat := 118140960795 + 732025 * 2 ^ 59
def prefixEnd_732025 : Nat := 4983230072969 + 3 ^ 40 * 732025 * 2
def baseEnd_732025 : Nat := 334116156540092162240875

theorem tailTrace_732025 : CollatzResearch.WordTrace tailWord_732025 prefixEnd_732025 334116156540092162240875 := by
  unfold tailWord_732025
  simp only [CollatzResearch.WordTrace]
  refine ⟨26699145173005919761765529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17799430115337279841177019 26699145173005919761765529)
  ·
    refine ⟨20024358879754439821324147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26699145173005919761765529 20024358879754439821324147)
    ·
      refine ⟨30036538319631659731986221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20024358879754439821324147 30036538319631659731986221)
      ·
        refine ⟨11263701869861872399494833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30036538319631659731986221 11263701869861872399494833)
        ·
          refine ⟨8447776402396404299621125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11263701869861872399494833 8447776402396404299621125)
          ·
            refine ⟨1583958075449325806178961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8447776402396404299621125 1583958075449325806178961)
            ·
              refine ⟨1187968556586994354634221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1583958075449325806178961 1187968556586994354634221)
              ·
                refine ⟨445488208720122882987833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1187968556586994354634221 445488208720122882987833)
                ·
                  refine ⟨334116156540092162240875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 445488208720122882987833 334116156540092162240875)
                  ·
                    rfl

theorem cell20_732025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 3, 2].length) (baseStart_732025 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_732025 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_732025 prefixEnd_732025 := by exact prefixLift 732025
  have htrace : WordTrace (prefixWord ++ tailWord_732025) baseStart_732025 baseEnd_732025 := by
    simpa [prefixWord, tailWord_732025, baseEnd_732025] using wordTrace_append hprefix tailTrace_732025
  have hstable : (prefixWord ++ tailWord_732025).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732025).length < 2 ^ (prefixWord ++ tailWord_732025).sum := by decide
  have hdescent : baseEnd_732025 < baseStart_732025 := by decide
  rcases family_descends (prefixWord ++ tailWord_732025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732039 : List Nat := [1, 1, 4, 2, 3, 1, 3, 2, 3]
def baseStart_732039 : Nat := 118140960795 + 732039 * 2 ^ 59
def prefixEnd_732039 : Nat := 4983230072969 + 3 ^ 40 * 732039 * 2
def baseEnd_732039 : Nat := 334122546521570335774151

theorem tailTrace_732039 : CollatzResearch.WordTrace tailWord_732039 prefixEnd_732039 334122546521570335774151 := by
  unfold tailWord_732039
  simp only [CollatzResearch.WordTrace]
  refine ⟨26699655794955200152775171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17799770529970133435183447 26699655794955200152775171)
  ·
    refine ⟨40049483692432800229162757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26699655794955200152775171 40049483692432800229162757)
    ·
      refine ⟨7509278192331150042968017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40049483692432800229162757 7509278192331150042968017)
      ·
        refine ⟨5631958644248362532226013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7509278192331150042968017 5631958644248362532226013)
        ·
          refine ⟨2111984491593135949584755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5631958644248362532226013 2111984491593135949584755)
          ·
            refine ⟨3167976737389703924377133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2111984491593135949584755 3167976737389703924377133)
            ·
              refine ⟨1187991276521138971641425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3167976737389703924377133 1187991276521138971641425)
              ·
                refine ⟨890993457390854228731069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1187991276521138971641425 890993457390854228731069)
                ·
                  refine ⟨334122546521570335774151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 890993457390854228731069 334122546521570335774151)
                  ·
                    rfl

theorem cell20_732039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 2, 3].length) (baseStart_732039 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_732039 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_732039 prefixEnd_732039 := by exact prefixLift 732039
  have htrace : WordTrace (prefixWord ++ tailWord_732039) baseStart_732039 baseEnd_732039 := by
    simpa [prefixWord, tailWord_732039, baseEnd_732039] using wordTrace_append hprefix tailTrace_732039
  have hstable : (prefixWord ++ tailWord_732039).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732039).length < 2 ^ (prefixWord ++ tailWord_732039).sum := by decide
  have hdescent : baseEnd_732039 < baseStart_732039 := by decide
  rcases family_descends (prefixWord ++ tailWord_732039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732067 : List Nat := [1, 1, 1, 4, 1, 2, 4, 2, 4]
def baseStart_732067 : Nat := 118140960795 + 732067 * 2 ^ 59
def prefixEnd_732067 : Nat := 4983230072969 + 3 ^ 40 * 732067 * 2
def baseEnd_732067 : Nat := 334135326484526682840703

theorem tailTrace_732067 : CollatzResearch.WordTrace tailWord_732067 prefixEnd_732067 334135326484526682840703 := by
  unfold tailWord_732067
  simp only [CollatzResearch.WordTrace]
  refine ⟨26700677038853760934794455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17800451359235840623196303 26700677038853760934794455)
  ·
    refine ⟨40051015558280641402191683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26700677038853760934794455 40051015558280641402191683)
    ·
      refine ⟨60076523337420962103287525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40051015558280641402191683 60076523337420962103287525)
      ·
        refine ⟨11264348125766430394366411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60076523337420962103287525 11264348125766430394366411)
        ·
          refine ⟨16896522188649645591549617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11264348125766430394366411 16896522188649645591549617)
          ·
            refine ⟨12672391641487234193662213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16896522188649645591549617 12672391641487234193662213)
            ·
              refine ⟨2376073432778856411311665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12672391641487234193662213 2376073432778856411311665)
              ·
                refine ⟨1782055074584142308483749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2376073432778856411311665 1782055074584142308483749)
                ·
                  refine ⟨334135326484526682840703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1782055074584142308483749 334135326484526682840703)
                  ·
                    rfl

theorem cell20_732067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 2, 4].length) (baseStart_732067 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_732067 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_732067 prefixEnd_732067 := by exact prefixLift 732067
  have htrace : WordTrace (prefixWord ++ tailWord_732067) baseStart_732067 baseEnd_732067 := by
    simpa [prefixWord, tailWord_732067, baseEnd_732067] using wordTrace_append hprefix tailTrace_732067
  have hstable : (prefixWord ++ tailWord_732067).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732067).length < 2 ^ (prefixWord ++ tailWord_732067).sum := by decide
  have hdescent : baseEnd_732067 < baseStart_732067 := by decide
  rcases family_descends (prefixWord ++ tailWord_732067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732119 : List Nat := [1, 1, 3, 2, 1, 1, 2, 2, 7]
def baseStart_732119 : Nat := 118140960795 + 732119 * 2 ^ 59
def prefixEnd_732119 : Nat := 4983230072969 + 3 ^ 40 * 732119 * 2
def baseEnd_732119 : Nat := 334159060701445613107157

theorem tailTrace_732119 : CollatzResearch.WordTrace tailWord_732119 prefixEnd_732119 334159060701445613107157 := by
  unfold tailWord_732119
  simp only [CollatzResearch.WordTrace]
  refine ⟨26702573634665373815687411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17801715756443582543791607 26702573634665373815687411)
  ·
    refine ⟨40053860451998060723531117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26702573634665373815687411 40053860451998060723531117)
    ·
      refine ⟨15020197669499272771324169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40053860451998060723531117 15020197669499272771324169)
      ·
        refine ⟨11265148252124454578493127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15020197669499272771324169 11265148252124454578493127)
        ·
          refine ⟨16897722378186681867739691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11265148252124454578493127 16897722378186681867739691)
          ·
            refine ⟨25346583567280022801609537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16897722378186681867739691 25346583567280022801609537)
            ·
              refine ⟨19009937675460017101207153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25346583567280022801609537 19009937675460017101207153)
              ·
                refine ⟨14257453256595012825905365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19009937675460017101207153 14257453256595012825905365)
                ·
                  refine ⟨334159060701445613107157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14257453256595012825905365 334159060701445613107157)
                  ·
                    rfl

theorem cell20_732119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 7].length) (baseStart_732119 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_732119 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_732119 prefixEnd_732119 := by exact prefixLift 732119
  have htrace : WordTrace (prefixWord ++ tailWord_732119) baseStart_732119 baseEnd_732119 := by
    simpa [prefixWord, tailWord_732119, baseEnd_732119] using wordTrace_append hprefix tailTrace_732119
  have hstable : (prefixWord ++ tailWord_732119).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732119).length < 2 ^ (prefixWord ++ tailWord_732119).sum := by decide
  have hdescent : baseEnd_732119 < baseStart_732119 := by decide
  rcases family_descends (prefixWord ++ tailWord_732119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732146 : List Nat := [3, 2, 1, 5, 2, 7]
def baseStart_732146 : Nat := 118140960795 + 732146 * 2 ^ 59
def prefixEnd_732146 : Nat := 4983230072969 + 3 ^ 40 * 732146 * 2
def baseEnd_732146 : Nat := 12376717934709389600261

theorem tailTrace_732146 : CollatzResearch.WordTrace tailWord_732146 prefixEnd_732146 12376717934709389600261 := by
  unfold tailWord_732146
  simp only [CollatzResearch.WordTrace]
  refine ⟨6675889601391889356730073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17802372270378371617946861 6675889601391889356730073)
  ·
    refine ⟨5006917201043917017547555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6675889601391889356730073 5006917201043917017547555)
    ·
      refine ⟨7510375801565875526321333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5006917201043917017547555 7510375801565875526321333)
      ·
        refine ⟨704097731396800830592625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7510375801565875526321333 704097731396800830592625)
        ·
          refine ⟨528073298547600622944469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 704097731396800830592625 528073298547600622944469)
          ·
            refine ⟨12376717934709389600261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 528073298547600622944469 12376717934709389600261)
            ·
              rfl

theorem cell20_732146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 7].length) (baseStart_732146 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_732146 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_732146 prefixEnd_732146 := by exact prefixLift 732146
  have htrace : WordTrace (prefixWord ++ tailWord_732146) baseStart_732146 baseEnd_732146 := by
    simpa [prefixWord, tailWord_732146, baseEnd_732146] using wordTrace_append hprefix tailTrace_732146
  have hstable : (prefixWord ++ tailWord_732146).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732146).length < 2 ^ (prefixWord ++ tailWord_732146).sum := by decide
  have hdescent : baseEnd_732146 < baseStart_732146 := by decide
  rcases family_descends (prefixWord ++ tailWord_732146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732148 : List Nat := [2, 6, 2, 1, 1, 2, 2, 2, 2]
def baseStart_732148 : Nat := 118140960795 + 732148 * 2 ^ 59
def prefixEnd_732148 : Nat := 4983230072969 + 3 ^ 40 * 732148 * 2
def baseEnd_732148 : Nat := 334172297091650401140373

theorem tailTrace_732148 : CollatzResearch.WordTrace tailWord_732148 prefixEnd_732148 334172297091650401140373 := by
  unfold tailWord_732148
  simp only [CollatzResearch.WordTrace]
  refine ⟨13351815675780155884246549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17802420901040207845662065 13351815675780155884246549)
  ·
    refine ⟨625866359802194807074057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 13351815675780155884246549 625866359802194807074057)
    ·
      refine ⟨469399769851646105305543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 625866359802194807074057 469399769851646105305543)
      ·
        refine ⟨704099654777469157958315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 469399769851646105305543 704099654777469157958315)
        ·
          refine ⟨1056149482166203736937473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 704099654777469157958315 1056149482166203736937473)
          ·
            refine ⟨792112111624652802703105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1056149482166203736937473 792112111624652802703105)
            ·
              refine ⟨594084083718489602027329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 792112111624652802703105 594084083718489602027329)
              ·
                refine ⟨445563062788867201520497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 594084083718489602027329 445563062788867201520497)
                ·
                  refine ⟨334172297091650401140373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 445563062788867201520497 334172297091650401140373)
                  ·
                    rfl

theorem cell20_732148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_732148 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_732148 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_732148 prefixEnd_732148 := by exact prefixLift 732148
  have htrace : WordTrace (prefixWord ++ tailWord_732148) baseStart_732148 baseEnd_732148 := by
    simpa [prefixWord, tailWord_732148, baseEnd_732148] using wordTrace_append hprefix tailTrace_732148
  have hstable : (prefixWord ++ tailWord_732148).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732148).length < 2 ^ (prefixWord ++ tailWord_732148).sum := by decide
  have hdescent : baseEnd_732148 < baseStart_732148 := by decide
  rcases family_descends (prefixWord ++ tailWord_732148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732149 : List Nat := [1, 3, 5, 2, 1, 1, 2, 2, 3]
def baseStart_732149 : Nat := 118140960795 + 732149 * 2 ^ 59
def prefixEnd_732149 : Nat := 4983230072969 + 3 ^ 40 * 732149 * 2
def baseEnd_732149 : Nat := 334172753518898842107035

theorem tailTrace_732149 : CollatzResearch.WordTrace tailWord_732149 prefixEnd_732149 334172753518898842107035 := by
  unfold tailWord_732149
  simp only [CollatzResearch.WordTrace]
  refine ⟨26703667824556688939279501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17802445216371125959519667 26703667824556688939279501)
  ·
    refine ⟨10013875434208758352229813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26703667824556688939279501 10013875434208758352229813)
    ·
      refine ⟨938800821957071095521545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10013875434208758352229813 938800821957071095521545)
      ·
        refine ⟨704100616467803321641159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 938800821957071095521545 704100616467803321641159)
        ·
          refine ⟨1056150924701704982461739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 704100616467803321641159 1056150924701704982461739)
          ·
            refine ⟨1584226387052557473692609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1056150924701704982461739 1584226387052557473692609)
            ·
              refine ⟨1188169790289418105269457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1584226387052557473692609 1188169790289418105269457)
              ·
                refine ⟨891127342717063578952093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1188169790289418105269457 891127342717063578952093)
                ·
                  refine ⟨334172753518898842107035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 891127342717063578952093 334172753518898842107035)
                  ·
                    rfl

theorem cell20_732149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 2, 3].length) (baseStart_732149 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_732149 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_732149 prefixEnd_732149 := by exact prefixLift 732149
  have htrace : WordTrace (prefixWord ++ tailWord_732149) baseStart_732149 baseEnd_732149 := by
    simpa [prefixWord, tailWord_732149, baseEnd_732149] using wordTrace_append hprefix tailTrace_732149
  have hstable : (prefixWord ++ tailWord_732149).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732149).length < 2 ^ (prefixWord ++ tailWord_732149).sum := by decide
  have hdescent : baseEnd_732149 < baseStart_732149 := by decide
  rcases family_descends (prefixWord ++ tailWord_732149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732156 : List Nat := [2, 2, 2, 1, 2, 5, 2, 2, 2]
def baseStart_732156 : Nat := 118140960795 + 732156 * 2 ^ 59
def prefixEnd_732156 : Nat := 4983230072969 + 3 ^ 40 * 732156 * 2
def baseEnd_732156 : Nat := 334175948509637928873673

theorem tailTrace_732156 : CollatzResearch.WordTrace tailWord_732156 prefixEnd_732156 334175948509637928873673 := by
  unfold tailWord_732156
  simp only [CollatzResearch.WordTrace]
  refine ⟨13351961567765664567392161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17802615423687552756522881 13351961567765664567392161)
  ·
    refine ⟨10013971175824248425544121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13351961567765664567392161 10013971175824248425544121)
    ·
      refine ⟨7510478381868186319158091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10013971175824248425544121 7510478381868186319158091)
      ·
        refine ⟨11265717572802279478737137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7510478381868186319158091 11265717572802279478737137)
        ·
          refine ⟨8449288179601709609052853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11265717572802279478737137 8449288179601709609052853)
          ·
            refine ⟨792120766837660275848705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8449288179601709609052853 792120766837660275848705)
            ·
              refine ⟨594090575128245206886529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 792120766837660275848705 594090575128245206886529)
              ·
                refine ⟨445567931346183905164897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 594090575128245206886529 445567931346183905164897)
                ·
                  refine ⟨334175948509637928873673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 445567931346183905164897 334175948509637928873673)
                  ·
                    rfl

theorem cell20_732156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 2, 2, 2].length) (baseStart_732156 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_732156 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_732156 prefixEnd_732156 := by exact prefixLift 732156
  have htrace : WordTrace (prefixWord ++ tailWord_732156) baseStart_732156 baseEnd_732156 := by
    simpa [prefixWord, tailWord_732156, baseEnd_732156] using wordTrace_append hprefix tailTrace_732156
  have hstable : (prefixWord ++ tailWord_732156).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732156).length < 2 ^ (prefixWord ++ tailWord_732156).sum := by decide
  have hdescent : baseEnd_732156 < baseStart_732156 := by decide
  rcases family_descends (prefixWord ++ tailWord_732156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732181 : List Nat := [1, 3, 2, 1, 4, 1, 1, 1, 6]
def baseStart_732181 : Nat := 118140960795 + 732181 * 2 ^ 59
def prefixEnd_732181 : Nat := 4983230072969 + 3 ^ 40 * 732181 * 2
def baseEnd_732181 : Nat := 334187359190848953040237

theorem tailTrace_732181 : CollatzResearch.WordTrace tailWord_732181 prefixEnd_732181 334187359190848953040237 := by
  unfold tailWord_732181
  simp only [CollatzResearch.WordTrace]
  refine ⟨26704834960440758404444397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17803223306960505602962931 26704834960440758404444397)
  ·
    refine ⟨10014313110165284401666649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26704834960440758404444397 10014313110165284401666649)
    ·
      refine ⟨7510734832623963301249987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10014313110165284401666649 7510734832623963301249987)
      ·
        refine ⟨11266102248935944951874981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7510734832623963301249987 11266102248935944951874981)
        ·
          refine ⟨2112394171675489678476559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11266102248935944951874981 2112394171675489678476559)
          ·
            refine ⟨3168591257513234517714839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2112394171675489678476559 3168591257513234517714839)
            ·
              refine ⟨4752886886269851776572259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3168591257513234517714839 4752886886269851776572259)
              ·
                refine ⟨7129330329404777664858389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4752886886269851776572259 7129330329404777664858389)
                ·
                  refine ⟨334187359190848953040237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7129330329404777664858389 334187359190848953040237)
                  ·
                    rfl

theorem cell20_732181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 6].length) (baseStart_732181 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_732181 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_732181 prefixEnd_732181 := by exact prefixLift 732181
  have htrace : WordTrace (prefixWord ++ tailWord_732181) baseStart_732181 baseEnd_732181 := by
    simpa [prefixWord, tailWord_732181, baseEnd_732181] using wordTrace_append hprefix tailTrace_732181
  have hstable : (prefixWord ++ tailWord_732181).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732181).length < 2 ^ (prefixWord ++ tailWord_732181).sum := by decide
  have hdescent : baseEnd_732181 < baseStart_732181 := by decide
  rcases family_descends (prefixWord ++ tailWord_732181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732270 : List Nat := [4, 1, 2, 2, 1, 3, 3, 2, 2]
def baseStart_732270 : Nat := 118140960795 + 732270 * 2 ^ 59
def prefixEnd_732270 : Nat := 4983230072969 + 3 ^ 40 * 732270 * 2
def baseEnd_732270 : Nat := 334227981215960199073207

theorem tailTrace_732270 : CollatzResearch.WordTrace tailWord_732270 prefixEnd_732270 334227981215960199073207 := by
  unfold tailWord_732270
  simp only [CollatzResearch.WordTrace]
  refine ⟨3338510132139790825554283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17805387371412217736289509 3338510132139790825554283)
  ·
    refine ⟨5007765198209686238331425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3338510132139790825554283 5007765198209686238331425)
    ·
      refine ⟨3755823898657264678748569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5007765198209686238331425 3755823898657264678748569)
      ·
        refine ⟨2816867923992948509061427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3755823898657264678748569 2816867923992948509061427)
        ·
          refine ⟨4225301885989422763592141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2816867923992948509061427 4225301885989422763592141)
          ·
            refine ⟨1584488207246033536347053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4225301885989422763592141 1584488207246033536347053)
            ·
              refine ⟨594183077717262576130145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1584488207246033536347053 594183077717262576130145)
              ·
                refine ⟨445637308287946932097609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 594183077717262576130145 445637308287946932097609)
                ·
                  refine ⟨334227981215960199073207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 445637308287946932097609 334227981215960199073207)
                  ·
                    rfl

theorem cell20_732270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 3, 2, 2].length) (baseStart_732270 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_732270 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_732270 prefixEnd_732270 := by exact prefixLift 732270
  have htrace : WordTrace (prefixWord ++ tailWord_732270) baseStart_732270 baseEnd_732270 := by
    simpa [prefixWord, tailWord_732270, baseEnd_732270] using wordTrace_append hprefix tailTrace_732270
  have hstable : (prefixWord ++ tailWord_732270).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732270).length < 2 ^ (prefixWord ++ tailWord_732270).sum := by decide
  have hdescent : baseEnd_732270 < baseStart_732270 := by decide
  rcases family_descends (prefixWord ++ tailWord_732270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732271 : List Nat := [1, 1, 2, 1, 3, 3, 1, 3, 5]
def baseStart_732271 : Nat := 118140960795 + 732271 * 2 ^ 59
def prefixEnd_732271 : Nat := 4983230072969 + 3 ^ 40 * 732271 * 2
def baseEnd_732271 : Nat := 334228437643208640039869

theorem tailTrace_732271 : CollatzResearch.WordTrace tailWord_732271 prefixEnd_732271 334228437643208640039869 := by
  unfold tailWord_732271
  simp only [CollatzResearch.WordTrace]
  refine ⟨26708117530114703775220667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17805411686743135850147111 26708117530114703775220667)
  ·
    refine ⟨40062176295172055662831001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26708117530114703775220667 40062176295172055662831001)
    ·
      refine ⟨30046632221379041747123251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40062176295172055662831001 30046632221379041747123251)
      ·
        refine ⟨45069948332068562620684877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30046632221379041747123251 45069948332068562620684877)
        ·
          refine ⟨16901230624525710982756829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45069948332068562620684877 16901230624525710982756829)
          ·
            refine ⟨6337961484197141618533811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16901230624525710982756829 6337961484197141618533811)
            ·
              refine ⟨9506942226295712427800717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6337961484197141618533811 9506942226295712427800717)
              ·
                refine ⟨3565103334860892160425269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9506942226295712427800717 3565103334860892160425269)
                ·
                  refine ⟨334228437643208640039869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3565103334860892160425269 334228437643208640039869)
                  ·
                    rfl

theorem cell20_732271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 5].length) (baseStart_732271 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_732271 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_732271 prefixEnd_732271 := by exact prefixLift 732271
  have htrace : WordTrace (prefixWord ++ tailWord_732271) baseStart_732271 baseEnd_732271 := by
    simpa [prefixWord, tailWord_732271, baseEnd_732271] using wordTrace_append hprefix tailTrace_732271
  have hstable : (prefixWord ++ tailWord_732271).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732271).length < 2 ^ (prefixWord ++ tailWord_732271).sum := by decide
  have hdescent : baseEnd_732271 < baseStart_732271 := by decide
  rcases family_descends (prefixWord ++ tailWord_732271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732281 : List Nat := [1, 2, 1, 3, 5, 1, 2, 5]
def baseStart_732281 : Nat := 118140960795 + 732281 * 2 ^ 59
def prefixEnd_732281 : Nat := 4983230072969 + 3 ^ 40 * 732281 * 2
def baseEnd_732281 : Nat := 111411000638564349902165

theorem tailTrace_732281 : CollatzResearch.WordTrace tailWord_732281 prefixEnd_732281 111411000638564349902165 := by
  unfold tailWord_732281
  simp only [CollatzResearch.WordTrace]
  refine ⟨26708482260078475483084697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17805654840052316988723131 26708482260078475483084697)
  ·
    refine ⟨20031361695058856612313523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26708482260078475483084697 20031361695058856612313523)
    ·
      refine ⟨30047042542588284918470285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20031361695058856612313523 30047042542588284918470285)
      ·
        refine ⟨11267640953470606844426357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30047042542588284918470285 11267640953470606844426357)
        ·
          refine ⟨1056341339387869391664971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11267640953470606844426357 1056341339387869391664971)
          ·
            refine ⟨1584512009081804087497457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1056341339387869391664971 1584512009081804087497457)
            ·
              refine ⟨1188384006811353065623093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1584512009081804087497457 1188384006811353065623093)
              ·
                refine ⟨111411000638564349902165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1188384006811353065623093 111411000638564349902165)
                ·
                  rfl

theorem cell20_732281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 5].length) (baseStart_732281 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_732281 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_732281 prefixEnd_732281 := by exact prefixLift 732281
  have htrace : WordTrace (prefixWord ++ tailWord_732281) baseStart_732281 baseEnd_732281 := by
    simpa [prefixWord, tailWord_732281, baseEnd_732281] using wordTrace_append hprefix tailTrace_732281
  have hstable : (prefixWord ++ tailWord_732281).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732281).length < 2 ^ (prefixWord ++ tailWord_732281).sum := by decide
  have hdescent : baseEnd_732281 < baseStart_732281 := by decide
  rcases family_descends (prefixWord ++ tailWord_732281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732309 : List Nat := [1, 3, 2, 1, 1, 1, 2, 4, 5]
def baseStart_732309 : Nat := 118140960795 + 732309 * 2 ^ 59
def prefixEnd_732309 : Nat := 4983230072969 + 3 ^ 40 * 732309 * 2
def baseEnd_732309 : Nat := 334245781878649396773047

theorem tailTrace_732309 : CollatzResearch.WordTrace tailWord_732309 prefixEnd_732309 334245781878649396773047 := by
  unfold tailWord_732309
  simp only [CollatzResearch.WordTrace]
  refine ⟨26709503503977036265103981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17806335669318024176735987 26709503503977036265103981)
  ·
    refine ⟨10016063813991388599413993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26709503503977036265103981 10016063813991388599413993)
    ·
      refine ⟨7512047860493541449560495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10016063813991388599413993 7512047860493541449560495)
      ·
        refine ⟨11268071790740312174340743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7512047860493541449560495 11268071790740312174340743)
        ·
          refine ⟨16902107686110468261511115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11268071790740312174340743 16902107686110468261511115)
          ·
            refine ⟨25353161529165702392266673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16902107686110468261511115 25353161529165702392266673)
            ·
              refine ⟨19014871146874276794200005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25353161529165702392266673 19014871146874276794200005)
              ·
                refine ⟨3565288340038926898912501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19014871146874276794200005 3565288340038926898912501)
                ·
                  refine ⟨334245781878649396773047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3565288340038926898912501 334245781878649396773047)
                  ·
                    rfl

theorem cell20_732309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_732309 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_732309 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_732309 prefixEnd_732309 := by exact prefixLift 732309
  have htrace : WordTrace (prefixWord ++ tailWord_732309) baseStart_732309 baseEnd_732309 := by
    simpa [prefixWord, tailWord_732309, baseEnd_732309] using wordTrace_append hprefix tailTrace_732309
  have hstable : (prefixWord ++ tailWord_732309).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732309).length < 2 ^ (prefixWord ++ tailWord_732309).sum := by decide
  have hdescent : baseEnd_732309 < baseStart_732309 := by decide
  rcases family_descends (prefixWord ++ tailWord_732309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732319 : List Nat := [1, 1, 2, 6, 3, 7]
def baseStart_732319 : Nat := 118140960795 + 732319 * 2 ^ 59
def prefixEnd_732319 : Nat := 4983230072969 + 3 ^ 40 * 732319 * 2
def baseEnd_732319 : Nat := 12379642450041992831099

theorem tailTrace_732319 : CollatzResearch.WordTrace tailWord_732319 prefixEnd_732319 12379642450041992831099 := by
  unfold tailWord_732319
  simp only [CollatzResearch.WordTrace]
  refine ⟨26709868233940807972968011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17806578822627205315312007 26709868233940807972968011)
  ·
    refine ⟨40064802350911211959452017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26709868233940807972968011 40064802350911211959452017)
    ·
      refine ⟨30048601763183408969589013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40064802350911211959452017 30048601763183408969589013)
      ·
        refine ⟨1408528207649222295449485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 30048601763183408969589013 1408528207649222295449485)
        ·
          refine ⟨528198077868458360793557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1408528207649222295449485 528198077868458360793557)
          ·
            refine ⟨12379642450041992831099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 528198077868458360793557 12379642450041992831099)
            ·
              rfl

theorem cell20_732319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 7].length) (baseStart_732319 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_732319 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_732319 prefixEnd_732319 := by exact prefixLift 732319
  have htrace : WordTrace (prefixWord ++ tailWord_732319) baseStart_732319 baseEnd_732319 := by
    simpa [prefixWord, tailWord_732319, baseEnd_732319] using wordTrace_append hprefix tailTrace_732319
  have hstable : (prefixWord ++ tailWord_732319).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732319).length < 2 ^ (prefixWord ++ tailWord_732319).sum := by decide
  have hdescent : baseEnd_732319 < baseStart_732319 := by decide
  rcases family_descends (prefixWord ++ tailWord_732319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732322 : List Nat := [3, 3, 1, 3, 2, 1, 2, 2, 3]
def baseStart_732322 : Nat := 118140960795 + 732322 * 2 ^ 59
def prefixEnd_732322 : Nat := 4983230072969 + 3 ^ 40 * 732322 * 2
def baseEnd_732322 : Nat := 334251715432879129339661

theorem tailTrace_732322 : CollatzResearch.WordTrace tailWord_732322 prefixEnd_732322 334251715432879129339661 := by
  unfold tailWord_732322
  simp only [CollatzResearch.WordTrace]
  refine ⟨6677494413232484871331805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17806651768619959656884813 6677494413232484871331805)
  ·
    refine ⟨2504060404962181826749427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6677494413232484871331805 2504060404962181826749427)
    ·
      refine ⟨3756090607443272740124141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2504060404962181826749427 3756090607443272740124141)
      ·
        refine ⟨1408533977791227277546553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3756090607443272740124141 1408533977791227277546553)
        ·
          refine ⟨1056400483343420458159915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1408533977791227277546553 1056400483343420458159915)
          ·
            refine ⟨1584600725015130687239873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1056400483343420458159915 1584600725015130687239873)
            ·
              refine ⟨1188450543761348015429905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1584600725015130687239873 1188450543761348015429905)
              ·
                refine ⟨891337907821011011572429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1188450543761348015429905 891337907821011011572429)
                ·
                  refine ⟨334251715432879129339661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 891337907821011011572429 334251715432879129339661)
                  ·
                    rfl

theorem cell20_732322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_732322 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_732322 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_732322 prefixEnd_732322 := by exact prefixLift 732322
  have htrace : WordTrace (prefixWord ++ tailWord_732322) baseStart_732322 baseEnd_732322 := by
    simpa [prefixWord, tailWord_732322, baseEnd_732322] using wordTrace_append hprefix tailTrace_732322
  have hstable : (prefixWord ++ tailWord_732322).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732322).length < 2 ^ (prefixWord ++ tailWord_732322).sum := by decide
  have hdescent : baseEnd_732322 < baseStart_732322 := by decide
  rcases family_descends (prefixWord ++ tailWord_732322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732350 : List Nat := [4, 2, 1, 1, 3, 2, 1, 2, 4]
def baseStart_732350 : Nat := 118140960795 + 732350 * 2 ^ 59
def prefixEnd_732350 : Nat := 4983230072969 + 3 ^ 40 * 732350 * 2
def baseEnd_732350 : Nat := 334264495395835476406213

theorem tailTrace_732350 : CollatzResearch.WordTrace tailWord_732350 prefixEnd_732350 334264495395835476406213 := by
  unfold tailWord_732350
  simp only [CollatzResearch.WordTrace]
  refine ⟨3338874862103562533418313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17807332597885666844897669 3338874862103562533418313)
  ·
    refine ⟨2504156146577671900063735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3338874862103562533418313 2504156146577671900063735)
    ·
      refine ⟨3756234219866507850095603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2504156146577671900063735 3756234219866507850095603)
      ·
        refine ⟨5634351329799761775143405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3756234219866507850095603 5634351329799761775143405)
        ·
          refine ⟨2112881748674910665678777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5634351329799761775143405 2112881748674910665678777)
          ·
            refine ⟨1584661311506182999259083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2112881748674910665678777 1584661311506182999259083)
            ·
              refine ⟨2376991967259274498888625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1584661311506182999259083 2376991967259274498888625)
              ·
                refine ⟨1782743975444455874166469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2376991967259274498888625 1782743975444455874166469)
                ·
                  refine ⟨334264495395835476406213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1782743975444455874166469 334264495395835476406213)
                  ·
                    rfl

theorem cell20_732350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_732350 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_732350 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_732350 prefixEnd_732350 := by exact prefixLift 732350
  have htrace : WordTrace (prefixWord ++ tailWord_732350) baseStart_732350 baseEnd_732350 := by
    simpa [prefixWord, tailWord_732350, baseEnd_732350] using wordTrace_append hprefix tailTrace_732350
  have hstable : (prefixWord ++ tailWord_732350).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732350).length < 2 ^ (prefixWord ++ tailWord_732350).sum := by decide
  have hdescent : baseEnd_732350 < baseStart_732350 := by decide
  rcases family_descends (prefixWord ++ tailWord_732350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732374 : List Nat := [5, 2, 1, 2, 2, 1, 7]
def baseStart_732374 : Nat := 118140960795 + 732374 * 2 ^ 59
def prefixEnd_732374 : Nat := 4983230072969 + 3 ^ 40 * 732374 * 2
def baseEnd_732374 : Nat := 37141716627755339956235

theorem tailTrace_732374 : CollatzResearch.WordTrace tailWord_732374 prefixEnd_732374 37141716627755339956235 := by
  unfold tailWord_732374
  simp only [CollatzResearch.WordTrace]
  refine ⟨1669492140546347022888761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17807916165827701577480117 1669492140546347022888761)
  ·
    refine ⟨1252119105409760267166571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1669492140546347022888761 1252119105409760267166571)
    ·
      refine ⟨1878178658114640400749857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1252119105409760267166571 1878178658114640400749857)
      ·
        refine ⟨1408633993585980300562393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1878178658114640400749857 1408633993585980300562393)
        ·
          refine ⟨1056475495189485225421795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1408633993585980300562393 1056475495189485225421795)
          ·
            refine ⟨1584713242784227838132693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1056475495189485225421795 1584713242784227838132693)
            ·
              refine ⟨37141716627755339956235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1584713242784227838132693 37141716627755339956235)
              ·
                rfl

theorem cell20_732374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 7].length) (baseStart_732374 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_732374 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_732374 prefixEnd_732374 := by exact prefixLift 732374
  have htrace : WordTrace (prefixWord ++ tailWord_732374) baseStart_732374 baseEnd_732374 := by
    simpa [prefixWord, tailWord_732374, baseEnd_732374] using wordTrace_append hprefix tailTrace_732374
  have hstable : (prefixWord ++ tailWord_732374).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732374).length < 2 ^ (prefixWord ++ tailWord_732374).sum := by decide
  have hdescent : baseEnd_732374 < baseStart_732374 := by decide
  rcases family_descends (prefixWord ++ tailWord_732374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732381 : List Nat := [1, 4, 3, 2, 2, 1, 1, 1, 5]
def baseStart_732381 : Nat := 118140960795 + 732381 * 2 ^ 59
def prefixEnd_732381 : Nat := 4983230072969 + 3 ^ 40 * 732381 * 2
def baseEnd_732381 : Nat := 334278644640537146372753

theorem tailTrace_732381 : CollatzResearch.WordTrace tailWord_732381 prefixEnd_732381 334278644640537146372753 := by
  unfold tailWord_732381
  simp only [CollatzResearch.WordTrace]
  refine ⟨26712129559716192561724997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17808086373144128374483331 26712129559716192561724997)
  ·
    refine ⟨5008524292446786105323437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26712129559716192561724997 5008524292446786105323437)
    ·
      refine ⟨1878196609667544789496289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5008524292446786105323437 1878196609667544789496289)
      ·
        refine ⟨1408647457250658592122217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1878196609667544789496289 1408647457250658592122217)
        ·
          refine ⟨1056485592937993944091663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1408647457250658592122217 1056485592937993944091663)
          ·
            refine ⟨1584728389406990916137495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1056485592937993944091663 1584728389406990916137495)
            ·
              refine ⟨2377092584110486374206243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1584728389406990916137495 2377092584110486374206243)
              ·
                refine ⟨3565638876165729561309365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2377092584110486374206243 3565638876165729561309365)
                ·
                  refine ⟨334278644640537146372753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3565638876165729561309365 334278644640537146372753)
                  ·
                    rfl

theorem cell20_732381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 5].length) (baseStart_732381 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_732381 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_732381 prefixEnd_732381 := by exact prefixLift 732381
  have htrace : WordTrace (prefixWord ++ tailWord_732381) baseStart_732381 baseEnd_732381 := by
    simpa [prefixWord, tailWord_732381, baseEnd_732381] using wordTrace_append hprefix tailTrace_732381
  have hstable : (prefixWord ++ tailWord_732381).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732381).length < 2 ^ (prefixWord ++ tailWord_732381).sum := by decide
  have hdescent : baseEnd_732381 < baseStart_732381 := by decide
  rcases family_descends (prefixWord ++ tailWord_732381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732388 : List Nat := [2, 3, 1, 1, 1, 2, 4, 4, 2]
def baseStart_732388 : Nat := 118140960795 + 732388 * 2 ^ 59
def prefixEnd_732388 : Nat := 4983230072969 + 3 ^ 40 * 732388 * 2
def baseEnd_732388 : Nat := 334281839631276233139391

theorem tailTrace_732388 : CollatzResearch.WordTrace tailWord_732388 prefixEnd_732388 334281839631276233139391 := by
  unfold tailWord_732388
  simp only [CollatzResearch.WordTrace]
  refine ⟨13356192435345416378614909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17808256580460555171486545 13356192435345416378614909)
  ·
    refine ⟨5008572163254531141980591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13356192435345416378614909 5008572163254531141980591)
    ·
      refine ⟨7512858244881796712970887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5008572163254531141980591 7512858244881796712970887)
      ·
        refine ⟨11269287367322695069456331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7512858244881796712970887 11269287367322695069456331)
        ·
          refine ⟨16903931050984042604184497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11269287367322695069456331 16903931050984042604184497)
          ·
            refine ⟨12677948288238031953138373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16903931050984042604184497 12677948288238031953138373)
            ·
              refine ⟨2377115304044630991213445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12677948288238031953138373 2377115304044630991213445)
              ·
                refine ⟨445709119508368310852521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2377115304044630991213445 445709119508368310852521)
                ·
                  refine ⟨334281839631276233139391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 445709119508368310852521 334281839631276233139391)
                  ·
                    rfl

theorem cell20_732388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 4, 2].length) (baseStart_732388 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_732388 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_732388 prefixEnd_732388 := by exact prefixLift 732388
  have htrace : WordTrace (prefixWord ++ tailWord_732388) baseStart_732388 baseEnd_732388 := by
    simpa [prefixWord, tailWord_732388, baseEnd_732388] using wordTrace_append hprefix tailTrace_732388
  have hstable : (prefixWord ++ tailWord_732388).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732388).length < 2 ^ (prefixWord ++ tailWord_732388).sum := by decide
  have hdescent : baseEnd_732388 < baseStart_732388 := by decide
  rcases family_descends (prefixWord ++ tailWord_732388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732412 : List Nat := [2, 2, 2, 1, 5, 2, 2, 4]
def baseStart_732412 : Nat := 118140960795 + 732412 * 2 ^ 59
def prefixEnd_732412 : Nat := 4983230072969 + 3 ^ 40 * 732412 * 2
def baseEnd_732412 : Nat := 111430931295079605446431

theorem tailTrace_732412 : CollatzResearch.WordTrace tailWord_732412 prefixEnd_732412 111430931295079605446431 := by
  unfold tailWord_732412
  simp only [CollatzResearch.WordTrace]
  refine ⟨13356630111301942428051745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17808840148402589904068993 13356630111301942428051745)
  ·
    refine ⟨10017472583476456821038809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13356630111301942428051745 10017472583476456821038809)
    ·
      refine ⟨7513104437607342615779107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10017472583476456821038809 7513104437607342615779107)
      ·
        refine ⟨11269656656411013923668661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7513104437607342615779107 11269656656411013923668661)
        ·
          refine ⟨1056530311538532555343937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11269656656411013923668661 1056530311538532555343937)
          ·
            refine ⟨792397733653899416507953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1056530311538532555343937 792397733653899416507953)
            ·
              refine ⟨594298300240424562380965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 792397733653899416507953 594298300240424562380965)
              ·
                refine ⟨111430931295079605446431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 594298300240424562380965 111430931295079605446431)
                ·
                  rfl

theorem cell20_732412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 2, 4].length) (baseStart_732412 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_732412 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_732412 prefixEnd_732412 := by exact prefixLift 732412
  have htrace : WordTrace (prefixWord ++ tailWord_732412) baseStart_732412 baseEnd_732412 := by
    simpa [prefixWord, tailWord_732412, baseEnd_732412] using wordTrace_append hprefix tailTrace_732412
  have hstable : (prefixWord ++ tailWord_732412).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732412).length < 2 ^ (prefixWord ++ tailWord_732412).sum := by decide
  have hdescent : baseEnd_732412 < baseStart_732412 := by decide
  rcases family_descends (prefixWord ++ tailWord_732412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732516 : List Nat := [2, 3, 1, 1, 3, 2, 2, 3, 3]
def baseStart_732516 : Nat := 118140960795 + 732516 * 2 ^ 59
def prefixEnd_732516 : Nat := 4983230072969 + 3 ^ 40 * 732516 * 2
def baseEnd_732516 : Nat := 334340262319076676872201

theorem tailTrace_732516 : CollatzResearch.WordTrace tailWord_732516 prefixEnd_732516 334340262319076676872201 := by
  unfold tailWord_732516
  simp only [CollatzResearch.WordTrace]
  refine ⟨13358526707113555308944701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17811368942818073745259601 13358526707113555308944701)
  ·
    refine ⟨5009447515167583240854263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13358526707113555308944701 5009447515167583240854263)
    ·
      refine ⟨7514171272751374861281395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5009447515167583240854263 7514171272751374861281395)
      ·
        refine ⟨11271256909127062291922093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7514171272751374861281395 11271256909127062291922093)
        ·
          refine ⟨4226721340922648359470785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11271256909127062291922093 4226721340922648359470785)
          ·
            refine ⟨3170041005691986269603089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4226721340922648359470785 3170041005691986269603089)
            ·
              refine ⟨2377530754268989702202317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3170041005691986269603089 2377530754268989702202317)
              ·
                refine ⟨891574032850871138325869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2377530754268989702202317 891574032850871138325869)
                ·
                  refine ⟨334340262319076676872201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 891574032850871138325869 334340262319076676872201)
                  ·
                    rfl

theorem cell20_732516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 3, 3].length) (baseStart_732516 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_732516 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_732516 prefixEnd_732516 := by exact prefixLift 732516
  have htrace : WordTrace (prefixWord ++ tailWord_732516) baseStart_732516 baseEnd_732516 := by
    simpa [prefixWord, tailWord_732516, baseEnd_732516] using wordTrace_append hprefix tailTrace_732516
  have hstable : (prefixWord ++ tailWord_732516).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732516).length < 2 ^ (prefixWord ++ tailWord_732516).sum := by decide
  have hdescent : baseEnd_732516 < baseStart_732516 := by decide
  rcases family_descends (prefixWord ++ tailWord_732516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732540 : List Nat := [2, 2, 2, 1, 1, 1, 6, 3, 2]
def baseStart_732540 : Nat := 118140960795 + 732540 * 2 ^ 59
def prefixEnd_732540 : Nat := 4983230072969 + 3 ^ 40 * 732540 * 2
def baseEnd_732540 : Nat := 334351216573039260072103

theorem tailTrace_732540 : CollatzResearch.WordTrace tailWord_732540 prefixEnd_732540 334351216573039260072103 := by
  unfold tailWord_732540
  simp only [CollatzResearch.WordTrace]
  refine ⟨13358964383070081358381537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17811952510760108477842049 13358964383070081358381537)
  ·
    refine ⟨10019223287302561018786153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13358964383070081358381537 10019223287302561018786153)
    ·
      refine ⟨7514417465476920764089615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10019223287302561018786153 7514417465476920764089615)
      ·
        refine ⟨11271626198215381146134423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7514417465476920764089615 11271626198215381146134423)
        ·
          refine ⟨16907439297323071719201635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11271626198215381146134423 16907439297323071719201635)
          ·
            refine ⟨25361158945984607578802453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16907439297323071719201635 25361158945984607578802453)
            ·
              refine ⟨1188804325593028480256365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 25361158945984607578802453 1188804325593028480256365)
              ·
                refine ⟨445801622097385680096137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1188804325593028480256365 445801622097385680096137)
                ·
                  refine ⟨334351216573039260072103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 445801622097385680096137 334351216573039260072103)
                  ·
                    rfl

theorem cell20_732540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 3, 2].length) (baseStart_732540 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_732540 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_732540 prefixEnd_732540 := by exact prefixLift 732540
  have htrace : WordTrace (prefixWord ++ tailWord_732540) baseStart_732540 baseEnd_732540 := by
    simpa [prefixWord, tailWord_732540, baseEnd_732540] using wordTrace_append hprefix tailTrace_732540
  have hstable : (prefixWord ++ tailWord_732540).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732540).length < 2 ^ (prefixWord ++ tailWord_732540).sum := by decide
  have hdescent : baseEnd_732540 < baseStart_732540 := by decide
  rcases family_descends (prefixWord ++ tailWord_732540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732612 : List Nat := [2, 3, 3, 2, 1, 2, 3, 2, 2]
def baseStart_732612 : Nat := 118140960795 + 732612 * 2 ^ 59
def prefixEnd_732612 : Nat := 4983230072969 + 3 ^ 40 * 732612 * 2
def baseEnd_732612 : Nat := 334384079334927009671809

theorem tailTrace_732612 : CollatzResearch.WordTrace tailWord_732612 prefixEnd_732612 334384079334927009671809 := by
  unfold tailWord_732612
  simp only [CollatzResearch.WordTrace]
  refine ⟨13360277410939659506692045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17813703214586212675589393 13360277410939659506692045)
  ·
    refine ⟨5010104029102372315009517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13360277410939659506692045 5010104029102372315009517)
    ·
      refine ⟨1878789010913389618128569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5010104029102372315009517 1878789010913389618128569)
      ·
        refine ⟨1409091758185042213596427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1878789010913389618128569 1409091758185042213596427)
        ·
          refine ⟨2113637637277563320394641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1409091758185042213596427 2113637637277563320394641)
          ·
            refine ⟨1585228227958172490295981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2113637637277563320394641 1585228227958172490295981)
            ·
              refine ⟨594460585484314683860993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1585228227958172490295981 594460585484314683860993)
              ·
                refine ⟨445845439113236012895745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 594460585484314683860993 445845439113236012895745)
                ·
                  refine ⟨334384079334927009671809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 445845439113236012895745 334384079334927009671809)
                  ·
                    rfl

theorem cell20_732612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 3, 2, 2].length) (baseStart_732612 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_732612 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_732612 prefixEnd_732612 := by exact prefixLift 732612
  have htrace : WordTrace (prefixWord ++ tailWord_732612) baseStart_732612 baseEnd_732612 := by
    simpa [prefixWord, tailWord_732612, baseEnd_732612] using wordTrace_append hprefix tailTrace_732612
  have hstable : (prefixWord ++ tailWord_732612).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732612).length < 2 ^ (prefixWord ++ tailWord_732612).sum := by decide
  have hdescent : baseEnd_732612 < baseStart_732612 := by decide
  rcases family_descends (prefixWord ++ tailWord_732612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732654 : List Nat := [4, 1, 2, 1, 2, 1, 2, 5, 2]
def baseStart_732654 : Nat := 118140960795 + 732654 * 2 ^ 59
def prefixEnd_732654 : Nat := 4983230072969 + 3 ^ 40 * 732654 * 2
def baseEnd_732654 : Nat := 334403249279361530271637

theorem tailTrace_732654 : CollatzResearch.WordTrace tailWord_732654 prefixEnd_732654 334403249279361530271637 := by
  unfold tailWord_732654
  simp only [CollatzResearch.WordTrace]
  refine ⟨3340260835965895023301627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17814724458484773457608677 3340260835965895023301627)
  ·
    refine ⟨5010391253948842534952441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3340260835965895023301627 5010391253948842534952441)
    ·
      refine ⟨3757793440461631901214331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5010391253948842534952441 3757793440461631901214331)
      ·
        refine ⟨5636690160692447851821497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3757793440461631901214331 5636690160692447851821497)
        ·
          refine ⟨4227517620519335888866123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5636690160692447851821497 4227517620519335888866123)
          ·
            refine ⟨6341276430779003833299185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4227517620519335888866123 6341276430779003833299185)
            ·
              refine ⟨4755957323084252874974389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6341276430779003833299185 4755957323084252874974389)
              ·
                refine ⟨445870999039148707028849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4755957323084252874974389 445870999039148707028849)
                ·
                  refine ⟨334403249279361530271637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 445870999039148707028849 334403249279361530271637)
                  ·
                    rfl

theorem cell20_732654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 5, 2].length) (baseStart_732654 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_732654 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_732654 prefixEnd_732654 := by exact prefixLift 732654
  have htrace : WordTrace (prefixWord ++ tailWord_732654) baseStart_732654 baseEnd_732654 := by
    simpa [prefixWord, tailWord_732654, baseEnd_732654] using wordTrace_append hprefix tailTrace_732654
  have hstable : (prefixWord ++ tailWord_732654).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732654).length < 2 ^ (prefixWord ++ tailWord_732654).sum := by decide
  have hdescent : baseEnd_732654 < baseStart_732654 := by decide
  rcases family_descends (prefixWord ++ tailWord_732654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732682 : List Nat := [3, 1, 2, 2, 2, 2, 3, 5]
def baseStart_732682 : Nat := 118140960795 + 732682 * 2 ^ 59
def prefixEnd_732682 : Nat := 4983230072969 + 3 ^ 40 * 732682 * 2
def baseEnd_732682 : Nat := 111472009747439292446063

theorem tailTrace_732682 : CollatzResearch.WordTrace tailWord_732682 prefixEnd_732682 111472009747439292446063 := by
  unfold tailWord_732682
  simp only [CollatzResearch.WordTrace]
  refine ⟨6680776982906430242108075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17815405287750480645621533 6680776982906430242108075)
  ·
    refine ⟨10021165474359645363162113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6680776982906430242108075 10021165474359645363162113)
    ·
      refine ⟨7515874105769734022371585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10021165474359645363162113 7515874105769734022371585)
      ·
        refine ⟨5636905579327300516778689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7515874105769734022371585 5636905579327300516778689)
        ·
          refine ⟨4227679184495475387584017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5636905579327300516778689 4227679184495475387584017)
          ·
            refine ⟨3170759388371606540688013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4227679184495475387584017 3170759388371606540688013)
            ·
              refine ⟨1189034770639352452758005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3170759388371606540688013 1189034770639352452758005)
              ·
                refine ⟨111472009747439292446063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1189034770639352452758005 111472009747439292446063)
                ·
                  rfl

theorem cell20_732682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 5].length) (baseStart_732682 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_732682 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_732682 prefixEnd_732682 := by exact prefixLift 732682
  have htrace : WordTrace (prefixWord ++ tailWord_732682) baseStart_732682 baseEnd_732682 := by
    simpa [prefixWord, tailWord_732682, baseEnd_732682] using wordTrace_append hprefix tailTrace_732682
  have hstable : (prefixWord ++ tailWord_732682).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732682).length < 2 ^ (prefixWord ++ tailWord_732682).sum := by decide
  have hdescent : baseEnd_732682 < baseStart_732682 := by decide
  rcases family_descends (prefixWord ++ tailWord_732682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732689 : List Nat := [1, 2, 2, 1, 1, 2, 3, 5, 3]
def baseStart_732689 : Nat := 118140960795 + 732689 * 2 ^ 59
def prefixEnd_732689 : Nat := 4983230072969 + 3 ^ 40 * 732689 * 2
def baseEnd_732689 : Nat := 334419224233056964104827

theorem tailTrace_732689 : CollatzResearch.WordTrace tailWord_732689 prefixEnd_732689 334419224233056964104827 := by
  unfold tailWord_732689
  simp only [CollatzResearch.WordTrace]
  refine ⟨26723363242600361163937121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17815575495066907442624747 26723363242600361163937121)
  ·
    refine ⟨20042522431950270872952841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26723363242600361163937121 20042522431950270872952841)
    ·
      refine ⟨15031891823962703154714631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20042522431950270872952841 15031891823962703154714631)
      ·
        refine ⟨22547837735944054732071947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15031891823962703154714631 22547837735944054732071947)
        ·
          refine ⟨33821756603916082098107921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22547837735944054732071947 33821756603916082098107921)
          ·
            refine ⟨25366317452937061573580941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33821756603916082098107921 25366317452937061573580941)
            ·
              refine ⟨9512369044851398090092853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25366317452937061573580941 9512369044851398090092853)
              ·
                refine ⟨891784597954818570946205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9512369044851398090092853 891784597954818570946205)
                ·
                  refine ⟨334419224233056964104827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 891784597954818570946205 334419224233056964104827)
                  ·
                    rfl

theorem cell20_732689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 5, 3].length) (baseStart_732689 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_732689 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_732689 prefixEnd_732689 := by exact prefixLift 732689
  have htrace : WordTrace (prefixWord ++ tailWord_732689) baseStart_732689 baseEnd_732689 := by
    simpa [prefixWord, tailWord_732689, baseEnd_732689] using wordTrace_append hprefix tailTrace_732689
  have hstable : (prefixWord ++ tailWord_732689).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732689).length < 2 ^ (prefixWord ++ tailWord_732689).sum := by decide
  have hdescent : baseEnd_732689 < baseStart_732689 := by decide
  rcases family_descends (prefixWord ++ tailWord_732689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732703 : List Nat := [1, 1, 2, 4, 1, 1, 2, 8]
def baseStart_732703 : Nat := 118140960795 + 732703 * 2 ^ 59
def prefixEnd_732703 : Nat := 4983230072969 + 3 ^ 40 * 732703 * 2
def baseEnd_732703 : Nat := 111475204738178379212701

theorem tailTrace_732703 : CollatzResearch.WordTrace tailWord_732703 prefixEnd_732703 111475204738178379212701 := by
  unfold tailWord_732703
  simp only [CollatzResearch.WordTrace]
  refine ⟨26723873864549641554946763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17815915909699761036631175 26723873864549641554946763)
  ·
    refine ⟨40085810796824462332420145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26723873864549641554946763 40085810796824462332420145)
    ·
      refine ⟨30064358097618346749315109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40085810796824462332420145 30064358097618346749315109)
      ·
        refine ⟨5637067143303440015496583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30064358097618346749315109 5637067143303440015496583)
        ·
          refine ⟨8455600714955160023244875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5637067143303440015496583 8455600714955160023244875)
          ·
            refine ⟨12683401072432740034867313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8455600714955160023244875 12683401072432740034867313)
            ·
              refine ⟨9512550804324555026150485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12683401072432740034867313 9512550804324555026150485)
              ·
                refine ⟨111475204738178379212701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9512550804324555026150485 111475204738178379212701)
                ·
                  rfl

theorem cell20_732703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 8].length) (baseStart_732703 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_732703 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_732703 prefixEnd_732703 := by exact prefixLift 732703
  have htrace : WordTrace (prefixWord ++ tailWord_732703) baseStart_732703 baseEnd_732703 := by
    simpa [prefixWord, tailWord_732703, baseEnd_732703] using wordTrace_append hprefix tailTrace_732703
  have hstable : (prefixWord ++ tailWord_732703).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732703).length < 2 ^ (prefixWord ++ tailWord_732703).sum := by decide
  have hdescent : baseEnd_732703 < baseStart_732703 := by decide
  rcases family_descends (prefixWord ++ tailWord_732703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732727 : List Nat := [1, 1, 3, 1, 2, 5, 1, 1, 5]
def baseStart_732727 : Nat := 118140960795 + 732727 * 2 ^ 59
def prefixEnd_732727 : Nat := 4983230072969 + 3 ^ 40 * 732727 * 2
def baseEnd_732727 : Nat := 334436568468497720838005

theorem tailTrace_732727 : CollatzResearch.WordTrace tailWord_732727 prefixEnd_732727 334436568468497720838005 := by
  unfold tailWord_732727
  simp only [CollatzResearch.WordTrace]
  refine ⟨26724749216462693653820435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17816499477641795769213623 26724749216462693653820435)
  ·
    refine ⟨40087123824694040480730653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26724749216462693653820435 40087123824694040480730653)
    ·
      refine ⟨15032671434260265180273995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40087123824694040480730653 15032671434260265180273995)
      ·
        refine ⟨22549007151390397770410993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15032671434260265180273995 22549007151390397770410993)
        ·
          refine ⟨16911755363542798327808245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22549007151390397770410993 16911755363542798327808245)
          ·
            refine ⟨1585477065332137343232023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16911755363542798327808245 1585477065332137343232023)
            ·
              refine ⟨2378215597998206014848035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1585477065332137343232023 2378215597998206014848035)
              ·
                refine ⟨3567323396997309022272053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2378215597998206014848035 3567323396997309022272053)
                ·
                  refine ⟨334436568468497720838005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3567323396997309022272053 334436568468497720838005)
                  ·
                    rfl

theorem cell20_732727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 5].length) (baseStart_732727 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_732727 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_732727 prefixEnd_732727 := by exact prefixLift 732727
  have htrace : WordTrace (prefixWord ++ tailWord_732727) baseStart_732727 baseEnd_732727 := by
    simpa [prefixWord, tailWord_732727, baseEnd_732727] using wordTrace_append hprefix tailTrace_732727
  have hstable : (prefixWord ++ tailWord_732727).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732727).length < 2 ^ (prefixWord ++ tailWord_732727).sum := by decide
  have hdescent : baseEnd_732727 < baseStart_732727 := by decide
  rcases family_descends (prefixWord ++ tailWord_732727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732741 : List Nat := [1, 3, 1, 1, 1, 4, 2, 7]
def baseStart_732741 : Nat := 118140960795 + 732741 * 2 ^ 59
def prefixEnd_732741 : Nat := 4983230072969 + 3 ^ 40 * 732741 * 2
def baseEnd_732741 : Nat := 111480986149991964790427

theorem tailTrace_732741 : CollatzResearch.WordTrace tailWord_732741 prefixEnd_732741 111480986149991964790427 := by
  unfold tailWord_732741
  simp only [CollatzResearch.WordTrace]
  refine ⟨26725259838411974044830077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17816839892274649363220051 26725259838411974044830077)
  ·
    refine ⟨10021972439404490266811279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26725259838411974044830077 10021972439404490266811279)
    ·
      refine ⟨15032958659106735400216919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10021972439404490266811279 15032958659106735400216919)
      ·
        refine ⟨22549437988660103100325379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15032958659106735400216919 22549437988660103100325379)
        ·
          refine ⟨33824156982990154650488069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22549437988660103100325379 33824156982990154650488069)
          ·
            refine ⟨6342029434310653996966513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33824156982990154650488069 6342029434310653996966513)
            ·
              refine ⟨4756522075732990497724885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6342029434310653996966513 4756522075732990497724885)
              ·
                refine ⟨111480986149991964790427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4756522075732990497724885 111480986149991964790427)
                ·
                  rfl

theorem cell20_732741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 7].length) (baseStart_732741 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_732741 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_732741 prefixEnd_732741 := by exact prefixLift 732741
  have htrace : WordTrace (prefixWord ++ tailWord_732741) baseStart_732741 baseEnd_732741 := by
    simpa [prefixWord, tailWord_732741, baseEnd_732741] using wordTrace_append hprefix tailTrace_732741
  have hstable : (prefixWord ++ tailWord_732741).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732741).length < 2 ^ (prefixWord ++ tailWord_732741).sum := by decide
  have hdescent : baseEnd_732741 < baseStart_732741 := by decide
  rcases family_descends (prefixWord ++ tailWord_732741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732834 : List Nat := [3, 3, 1, 4, 9]
def baseStart_732834 : Nat := 118140960795 + 732834 * 2 ^ 59
def prefixEnd_732834 : Nat := 4983230072969 + 3 ^ 40 * 732834 * 2
def baseEnd_732834 : Nat := 4129449459062727213221

theorem tailTrace_732834 : CollatzResearch.WordTrace tailWord_732834 prefixEnd_732834 4129449459062727213221 := by
  unfold tailWord_732834
  simp only [CollatzResearch.WordTrace]
  refine ⟨6682162956768762731991389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17819101218050033951977037 6682162956768762731991389)
  ·
    refine ⟨2505811108788286024496771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6682162956768762731991389 2505811108788286024496771)
    ·
      refine ⟨3758716663182429036745157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2505811108788286024496771 3758716663182429036745157)
      ·
        refine ⟨704759374346705444389717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3758716663182429036745157 704759374346705444389717)
        ·
          refine ⟨4129449459062727213221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 704759374346705444389717 4129449459062727213221)
          ·
            rfl

theorem cell20_732834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 9].length) (baseStart_732834 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_732834 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_732834 prefixEnd_732834 := by exact prefixLift 732834
  have htrace : WordTrace (prefixWord ++ tailWord_732834) baseStart_732834 baseEnd_732834 := by
    simpa [prefixWord, tailWord_732834, baseEnd_732834] using wordTrace_append hprefix tailTrace_732834
  have hstable : (prefixWord ++ tailWord_732834).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732834).length < 2 ^ (prefixWord ++ tailWord_732834).sum := by decide
  have hdescent : baseEnd_732834 < baseStart_732834 := by decide
  rcases family_descends (prefixWord ++ tailWord_732834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732872 : List Nat := [2, 1, 3, 1, 2, 2, 5, 4]
def baseStart_732872 : Nat := 118140960795 + 732872 * 2 ^ 59
def prefixEnd_732872 : Nat := 4983230072969 + 3 ^ 40 * 732872 * 2
def baseEnd_732872 : Nat := 111500916806507220334693

theorem tailTrace_732872 : CollatzResearch.WordTrace tailWord_732872 prefixEnd_732872 111500916806507220334693 := by
  unfold tailWord_732872
  simp only [CollatzResearch.WordTrace]
  refine ⟨13365018900468691708924435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17820025200624922278565913 13365018900468691708924435)
  ·
    refine ⟨20047528350703037563386653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13365018900468691708924435 20047528350703037563386653)
    ·
      refine ⟨7517823131513639086269995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20047528350703037563386653 7517823131513639086269995)
      ·
        refine ⟨11276734697270458629404993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7517823131513639086269995 11276734697270458629404993)
        ·
          refine ⟨8457551022952843972053745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11276734697270458629404993 8457551022952843972053745)
          ·
            refine ⟨6343163267214632979040309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8457551022952843972053745 6343163267214632979040309)
            ·
              refine ⟨594671556301371841785029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6343163267214632979040309 594671556301371841785029)
              ·
                refine ⟨111500916806507220334693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 594671556301371841785029 111500916806507220334693)
                ·
                  rfl

theorem cell20_732872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 5, 4].length) (baseStart_732872 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_732872 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_732872 prefixEnd_732872 := by exact prefixLift 732872
  have htrace : WordTrace (prefixWord ++ tailWord_732872) baseStart_732872 baseEnd_732872 := by
    simpa [prefixWord, tailWord_732872, baseEnd_732872] using wordTrace_append hprefix tailTrace_732872
  have hstable : (prefixWord ++ tailWord_732872).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732872).length < 2 ^ (prefixWord ++ tailWord_732872).sum := by decide
  have hdescent : baseEnd_732872 < baseStart_732872 := by decide
  rcases family_descends (prefixWord ++ tailWord_732872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732882 : List Nat := [3, 2, 2, 2, 2, 1, 1, 5, 2]
def baseStart_732882 : Nat := 118140960795 + 732882 * 2 ^ 59
def prefixEnd_732882 : Nat := 4983230072969 + 3 ^ 40 * 732882 * 2
def baseEnd_732882 : Nat := 334507314692006070670705

theorem tailTrace_732882 : CollatzResearch.WordTrace tailWord_732882 prefixEnd_732882 334507314692006070670705 := by
  unfold tailWord_732882
  simp only [CollatzResearch.WordTrace]
  refine ⟨6682600632725288781428225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17820268353934103417141933 6682600632725288781428225)
  ·
    refine ⟨5011950474543966586071169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6682600632725288781428225 5011950474543966586071169)
    ·
      refine ⟨3758962855907974939553377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5011950474543966586071169 3758962855907974939553377)
      ·
        refine ⟨2819222141930981204665033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3758962855907974939553377 2819222141930981204665033)
        ·
          refine ⟨2114416606448235903498775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2819222141930981204665033 2114416606448235903498775)
          ·
            refine ⟨3171624909672353855248163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2114416606448235903498775 3171624909672353855248163)
            ·
              refine ⟨4757437364508530782872245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3171624909672353855248163 4757437364508530782872245)
              ·
                refine ⟨446009752922674760894273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4757437364508530782872245 446009752922674760894273)
                ·
                  refine ⟨334507314692006070670705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 446009752922674760894273 334507314692006070670705)
                  ·
                    rfl

theorem cell20_732882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 5, 2].length) (baseStart_732882 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_732882 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_732882 prefixEnd_732882 := by exact prefixLift 732882
  have htrace : WordTrace (prefixWord ++ tailWord_732882) baseStart_732882 baseEnd_732882 := by
    simpa [prefixWord, tailWord_732882, baseEnd_732882] using wordTrace_append hprefix tailTrace_732882
  have hstable : (prefixWord ++ tailWord_732882).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732882).length < 2 ^ (prefixWord ++ tailWord_732882).sum := by decide
  have hdescent : baseEnd_732882 < baseStart_732882 := by decide
  rcases family_descends (prefixWord ++ tailWord_732882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732892 : List Nat := [2, 2, 5, 1, 2, 2, 1, 2, 3]
def baseStart_732892 : Nat := 118140960795 + 732892 * 2 ^ 59
def prefixEnd_732892 : Nat := 4983230072969 + 3 ^ 40 * 732892 * 2
def baseEnd_732892 : Nat := 334511878964490480337331

theorem tailTrace_732892 : CollatzResearch.WordTrace tailWord_732892 prefixEnd_732892 334511878964490480337331 := by
  unfold tailWord_732892
  simp only [CollatzResearch.WordTrace]
  refine ⟨13365383630432463416788465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17820511507243284555717953 13365383630432463416788465)
  ·
    refine ⟨10024037722824347562591349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13365383630432463416788465 10024037722824347562591349)
    ·
      refine ⟨939753536514782583992939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10024037722824347562591349 939753536514782583992939)
      ·
        refine ⟨1409630304772173875989409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 939753536514782583992939 1409630304772173875989409)
        ·
          refine ⟨1057222728579130406992057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1409630304772173875989409 1057222728579130406992057)
          ·
            refine ⟨792917046434347805244043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1057222728579130406992057 792917046434347805244043)
            ·
              refine ⟨1189375569651521707866065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 792917046434347805244043 1189375569651521707866065)
              ·
                refine ⟨892031677238641280899549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1189375569651521707866065 892031677238641280899549)
                ·
                  refine ⟨334511878964490480337331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 892031677238641280899549 334511878964490480337331)
                  ·
                    rfl

theorem cell20_732892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 2, 3].length) (baseStart_732892 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_732892 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_732892 prefixEnd_732892 := by exact prefixLift 732892
  have htrace : WordTrace (prefixWord ++ tailWord_732892) baseStart_732892 baseEnd_732892 := by
    simpa [prefixWord, tailWord_732892, baseEnd_732892] using wordTrace_append hprefix tailTrace_732892
  have hstable : (prefixWord ++ tailWord_732892).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732892).length < 2 ^ (prefixWord ++ tailWord_732892).sum := by decide
  have hdescent : baseEnd_732892 < baseStart_732892 := by decide
  rcases family_descends (prefixWord ++ tailWord_732892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732924 : List Nat := [2, 2, 2, 1, 3, 1, 1, 4, 4]
def baseStart_732924 : Nat := 118140960795 + 732924 * 2 ^ 59
def prefixEnd_732924 : Nat := 4983230072969 + 3 ^ 40 * 732924 * 2
def baseEnd_732924 : Nat := 334526484636440591270533

theorem tailTrace_732924 : CollatzResearch.WordTrace tailWord_732924 prefixEnd_732924 334526484636440591270533 := by
  unfold tailWord_732924
  simp only [CollatzResearch.WordTrace]
  refine ⟨13365967198374498149370913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17821289597832664199161217 13365967198374498149370913)
  ·
    refine ⟨10024475398780873612028185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13365967198374498149370913 10024475398780873612028185)
    ·
      refine ⟨7518356549085655209021139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10024475398780873612028185 7518356549085655209021139)
      ·
        refine ⟨11277534823628482813531709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7518356549085655209021139 11277534823628482813531709)
        ·
          refine ⟨4229075558860681055074391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11277534823628482813531709 4229075558860681055074391)
          ·
            refine ⟨6343613338291021582611587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4229075558860681055074391 6343613338291021582611587)
            ·
              refine ⟨9515420007436532373917381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6343613338291021582611587 9515420007436532373917381)
              ·
                refine ⟨1784141251394349820109509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9515420007436532373917381 1784141251394349820109509)
                ·
                  refine ⟨334526484636440591270533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1784141251394349820109509 334526484636440591270533)
                  ·
                    rfl

theorem cell20_732924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 4, 4].length) (baseStart_732924 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_732924 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_732924 prefixEnd_732924 := by exact prefixLift 732924
  have htrace : WordTrace (prefixWord ++ tailWord_732924) baseStart_732924 baseEnd_732924 := by
    simpa [prefixWord, tailWord_732924, baseEnd_732924] using wordTrace_append hprefix tailTrace_732924
  have hstable : (prefixWord ++ tailWord_732924).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732924).length < 2 ^ (prefixWord ++ tailWord_732924).sum := by decide
  have hdescent : baseEnd_732924 < baseStart_732924 := by decide
  rcases family_descends (prefixWord ++ tailWord_732924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_732972 : List Nat := [2, 2, 1, 1, 1, 5, 4, 1, 3]
def baseStart_732972 : Nat := 118140960795 + 732972 * 2 ^ 59
def prefixEnd_732972 : Nat := 4983230072969 + 3 ^ 40 * 732972 * 2
def baseEnd_732972 : Nat := 334548393144365757670337

theorem tailTrace_732972 : CollatzResearch.WordTrace tailWord_732972 prefixEnd_732972 334548393144365757670337 := by
  unfold tailWord_732972
  simp only [CollatzResearch.WordTrace]
  refine ⟨13366842550287550248244585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17822456733716733664326113 13366842550287550248244585)
  ·
    refine ⟨10025131912715662686183439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13366842550287550248244585 10025131912715662686183439)
    ·
      refine ⟨15037697869073494029275159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10025131912715662686183439 15037697869073494029275159)
      ·
        refine ⟨22556546803610241043912739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15037697869073494029275159 22556546803610241043912739)
        ·
          refine ⟨33834820205415361565869109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22556546803610241043912739 33834820205415361565869109)
          ·
            refine ⟨3172014394257690146800229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33834820205415361565869109 3172014394257690146800229)
            ·
              refine ⟨594752698923316902525043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3172014394257690146800229 594752698923316902525043)
              ·
                refine ⟨892129048384975353787565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 594752698923316902525043 892129048384975353787565)
                ·
                  refine ⟨334548393144365757670337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 892129048384975353787565 334548393144365757670337)
                  ·
                    rfl

theorem cell20_732972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 3].length) (baseStart_732972 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_732972 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_732972 prefixEnd_732972 := by exact prefixLift 732972
  have htrace : WordTrace (prefixWord ++ tailWord_732972) baseStart_732972 baseEnd_732972 := by
    simpa [prefixWord, tailWord_732972, baseEnd_732972] using wordTrace_append hprefix tailTrace_732972
  have hstable : (prefixWord ++ tailWord_732972).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_732972).length < 2 ^ (prefixWord ++ tailWord_732972).sum := by decide
  have hdescent : baseEnd_732972 < baseStart_732972 := by decide
  rcases family_descends (prefixWord ++ tailWord_732972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733010 : List Nat := [3, 2, 2, 1, 1, 4, 2, 2, 3]
def baseStart_733010 : Nat := 118140960795 + 733010 * 2 ^ 59
def prefixEnd_733010 : Nat := 4983230072969 + 3 ^ 40 * 733010 * 2
def baseEnd_733010 : Nat := 334565737379806514403515

theorem tailTrace_733010 : CollatzResearch.WordTrace tailWord_733010 prefixEnd_733010 334565737379806514403515 := by
  unfold tailWord_733010
  simp only [CollatzResearch.WordTrace]
  refine ⟨6683767768609358246593121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17823380716291621990914989 6683767768609358246593121)
  ·
    refine ⟨5012825826457018684944841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6683767768609358246593121 5012825826457018684944841)
    ·
      refine ⟨3759619369842764013708631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5012825826457018684944841 3759619369842764013708631)
      ·
        refine ⟨5639429054764146020562947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3759619369842764013708631 5639429054764146020562947)
        ·
          refine ⟨8459143582146219030844421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5639429054764146020562947 8459143582146219030844421)
          ·
            refine ⟨1586089421652416068283329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8459143582146219030844421 1586089421652416068283329)
            ·
              refine ⟨1189567066239312051212497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1586089421652416068283329 1189567066239312051212497)
              ·
                refine ⟨892175299679484038409373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1189567066239312051212497 892175299679484038409373)
                ·
                  refine ⟨334565737379806514403515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 892175299679484038409373 334565737379806514403515)
                  ·
                    rfl

theorem cell20_733010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 2, 3].length) (baseStart_733010 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_733010 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_733010 prefixEnd_733010 := by exact prefixLift 733010
  have htrace : WordTrace (prefixWord ++ tailWord_733010) baseStart_733010 baseEnd_733010 := by
    simpa [prefixWord, tailWord_733010, baseEnd_733010] using wordTrace_append hprefix tailTrace_733010
  have hstable : (prefixWord ++ tailWord_733010).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733010).length < 2 ^ (prefixWord ++ tailWord_733010).sum := by decide
  have hdescent : baseEnd_733010 < baseStart_733010 := by decide
  rcases family_descends (prefixWord ++ tailWord_733010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733013 : List Nat := [1, 3, 2, 2, 2, 4, 2, 2, 2]
def baseStart_733013 : Nat := 118140960795 + 733013 * 2 ^ 59
def prefixEnd_733013 : Nat := 4983230072969 + 3 ^ 40 * 733013 * 2
def baseEnd_733013 : Nat := 334567106661551837303503

theorem tailTrace_733013 : CollatzResearch.WordTrace tailWord_733013 prefixEnd_733013 334567106661551837303503 := by
  unfold tailWord_733013
  simp only [CollatzResearch.WordTrace]
  refine ⟨26735180493426564498731693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17823453662284376332487795 26735180493426564498731693)
  ·
    refine ⟨10025692685034961687024385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26735180493426564498731693 10025692685034961687024385)
    ·
      refine ⟨7519269513776221265268289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10025692685034961687024385 7519269513776221265268289)
      ·
        refine ⟨5639452135332165948951217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7519269513776221265268289 5639452135332165948951217)
        ·
          refine ⟨4229589101499124461713413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5639452135332165948951217 4229589101499124461713413)
          ·
            refine ⟨793047956531085836571265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4229589101499124461713413 793047956531085836571265)
            ·
              refine ⟨594785967398314377428449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 793047956531085836571265 594785967398314377428449)
              ·
                refine ⟨446089475548735783071337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 594785967398314377428449 446089475548735783071337)
                ·
                  refine ⟨334567106661551837303503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 446089475548735783071337 334567106661551837303503)
                  ·
                    rfl

theorem cell20_733013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 2, 2, 2].length) (baseStart_733013 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_733013 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_733013 prefixEnd_733013 := by exact prefixLift 733013
  have htrace : WordTrace (prefixWord ++ tailWord_733013) baseStart_733013 baseEnd_733013 := by
    simpa [prefixWord, tailWord_733013, baseEnd_733013] using wordTrace_append hprefix tailTrace_733013
  have hstable : (prefixWord ++ tailWord_733013).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733013).length < 2 ^ (prefixWord ++ tailWord_733013).sum := by decide
  have hdescent : baseEnd_733013 < baseStart_733013 := by decide
  rcases family_descends (prefixWord ++ tailWord_733013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733017 : List Nat := [1, 2, 1, 2, 2, 3, 3, 4, 2]
def baseStart_733017 : Nat := 118140960795 + 733017 * 2 ^ 59
def prefixEnd_733017 : Nat := 4983230072969 + 3 ^ 40 * 733017 * 2
def baseEnd_733017 : Nat := 334568932370545601170153

theorem tailTrace_733017 : CollatzResearch.WordTrace tailWord_733017 prefixEnd_733017 334568932370545601170153 := by
  unfold tailWord_733017
  simp only [CollatzResearch.WordTrace]
  refine ⟨26735326385412073181877305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17823550923608048787918203 26735326385412073181877305)
  ·
    refine ⟨20051494789059054886407979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26735326385412073181877305 20051494789059054886407979)
    ·
      refine ⟨30077242183588582329611969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20051494789059054886407979 30077242183588582329611969)
      ·
        refine ⟨22557931637691436747208977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30077242183588582329611969 22557931637691436747208977)
        ·
          refine ⟨16918448728268577560406733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22557931637691436747208977 16918448728268577560406733)
          ·
            refine ⟨6344418273100716585152525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16918448728268577560406733 6344418273100716585152525)
            ·
              refine ⟨2379156852412768719432197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6344418273100716585152525 2379156852412768719432197)
              ·
                refine ⟨446091909827394134893537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2379156852412768719432197 446091909827394134893537)
                ·
                  refine ⟨334568932370545601170153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 446091909827394134893537 334568932370545601170153)
                  ·
                    rfl

theorem cell20_733017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 4, 2].length) (baseStart_733017 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_733017 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_733017 prefixEnd_733017 := by exact prefixLift 733017
  have htrace : WordTrace (prefixWord ++ tailWord_733017) baseStart_733017 baseEnd_733017 := by
    simpa [prefixWord, tailWord_733017, baseEnd_733017] using wordTrace_append hprefix tailTrace_733017
  have hstable : (prefixWord ++ tailWord_733017).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733017).length < 2 ^ (prefixWord ++ tailWord_733017).sum := by decide
  have hdescent : baseEnd_733017 < baseStart_733017 := by decide
  rcases family_descends (prefixWord ++ tailWord_733017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733020 : List Nat := [2, 2, 4, 2, 3, 1, 1, 5]
def baseStart_733020 : Nat := 118140960795 + 733020 * 2 ^ 59
def prefixEnd_733020 : Nat := 4983230072969 + 3 ^ 40 * 733020 * 2
def baseEnd_733020 : Nat := 111523433884096974690047

theorem tailTrace_733020 : CollatzResearch.WordTrace tailWord_733020 prefixEnd_733020 111523433884096974690047 := by
  unfold tailWord_733020
  simp only [CollatzResearch.WordTrace]
  refine ⟨13367717902200602347118257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17823623869600803129491009 13367717902200602347118257)
  ·
    refine ⟨10025788426650451760338693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13367717902200602347118257 10025788426650451760338693)
    ·
      refine ⟨1879835329996959705063505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10025788426650451760338693 1879835329996959705063505)
      ·
        refine ⟨1409876497497719778797629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1879835329996959705063505 1409876497497719778797629)
        ·
          refine ⟨528703686561644917049111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1409876497497719778797629 528703686561644917049111)
          ·
            refine ⟨793055529842467375573667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 528703686561644917049111 793055529842467375573667)
            ·
              refine ⟨1189583294763701063360501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 793055529842467375573667 1189583294763701063360501)
              ·
                refine ⟨111523433884096974690047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1189583294763701063360501 111523433884096974690047)
                ·
                  rfl

theorem cell20_733020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 5].length) (baseStart_733020 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_733020 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_733020 prefixEnd_733020 := by exact prefixLift 733020
  have htrace : WordTrace (prefixWord ++ tailWord_733020) baseStart_733020 baseEnd_733020 := by
    simpa [prefixWord, tailWord_733020, baseEnd_733020] using wordTrace_append hprefix tailTrace_733020
  have hstable : (prefixWord ++ tailWord_733020).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733020).length < 2 ^ (prefixWord ++ tailWord_733020).sum := by decide
  have hdescent : baseEnd_733020 < baseStart_733020 := by decide
  rcases family_descends (prefixWord ++ tailWord_733020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733024 : List Nat := [2, 1, 1, 3, 3, 4, 1, 5]
def baseStart_733024 : Nat := 118140960795 + 733024 * 2 ^ 59
def prefixEnd_733024 : Nat := 4983230072969 + 3 ^ 40 * 733024 * 2
def baseEnd_733024 : Nat := 111524042453761562645597

theorem tailTrace_733024 : CollatzResearch.WordTrace tailWord_733024 prefixEnd_733024 111524042453761562645597 := by
  unfold tailWord_733024
  simp only [CollatzResearch.WordTrace]
  refine ⟨13367790848193356688691063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17823721130924475584921417 13367790848193356688691063)
  ·
    refine ⟨20051686272290035033036595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13367790848193356688691063 20051686272290035033036595)
    ·
      refine ⟨30077529408435052549554893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20051686272290035033036595 30077529408435052549554893)
      ·
        refine ⟨11279073528163144706083085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30077529408435052549554893 11279073528163144706083085)
        ·
          refine ⟨4229652573061179264781157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11279073528163144706083085 4229652573061179264781157)
          ·
            refine ⟨793059857448971112146467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4229652573061179264781157 793059857448971112146467)
            ·
              refine ⟨1189589786173456668219701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 793059857448971112146467 1189589786173456668219701)
              ·
                refine ⟨111524042453761562645597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1189589786173456668219701 111524042453761562645597)
                ·
                  rfl

theorem cell20_733024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 5].length) (baseStart_733024 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_733024 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_733024 prefixEnd_733024 := by exact prefixLift 733024
  have htrace : WordTrace (prefixWord ++ tailWord_733024) baseStart_733024 baseEnd_733024 := by
    simpa [prefixWord, tailWord_733024, baseEnd_733024] using wordTrace_append hprefix tailTrace_733024
  have hstable : (prefixWord ++ tailWord_733024).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733024).length < 2 ^ (prefixWord ++ tailWord_733024).sum := by decide
  have hdescent : baseEnd_733024 < baseStart_733024 := by decide
  rcases family_descends (prefixWord ++ tailWord_733024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733031 : List Nat := [1, 1, 5, 1, 2, 1, 1, 5, 3]
def baseStart_733031 : Nat := 118140960795 + 733031 * 2 ^ 59
def prefixEnd_733031 : Nat := 4983230072969 + 3 ^ 40 * 733031 * 2
def baseEnd_733031 : Nat := 334575322352023774703429

theorem tailTrace_733031 : CollatzResearch.WordTrace tailWord_733031 prefixEnd_733031 334575322352023774703429 := by
  unfold tailWord_733031
  simp only [CollatzResearch.WordTrace]
  refine ⟨26735837007361353572886947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17823891338240902381924631 26735837007361353572886947)
  ·
    refine ⟨40103755511042030359330421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26735837007361353572886947 40103755511042030359330421)
    ·
      refine ⟨3759727079160190346187227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40103755511042030359330421 3759727079160190346187227)
      ·
        refine ⟨5639590618740285519280841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3759727079160190346187227 5639590618740285519280841)
        ·
          refine ⟨4229692964055214139460631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5639590618740285519280841 4229692964055214139460631)
          ·
            refine ⟨6344539446082821209190947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4229692964055214139460631 6344539446082821209190947)
            ·
              refine ⟨9516809169124231813786421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6344539446082821209190947 9516809169124231813786421)
              ·
                refine ⟨892200859605396732542477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9516809169124231813786421 892200859605396732542477)
                ·
                  refine ⟨334575322352023774703429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 892200859605396732542477 334575322352023774703429)
                  ·
                    rfl

theorem cell20_733031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 5, 3].length) (baseStart_733031 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_733031 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_733031 prefixEnd_733031 := by exact prefixLift 733031
  have htrace : WordTrace (prefixWord ++ tailWord_733031) baseStart_733031 baseEnd_733031 := by
    simpa [prefixWord, tailWord_733031, baseEnd_733031] using wordTrace_append hprefix tailTrace_733031
  have hstable : (prefixWord ++ tailWord_733031).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733031).length < 2 ^ (prefixWord ++ tailWord_733031).sum := by decide
  have hdescent : baseEnd_733031 < baseStart_733031 := by decide
  rcases family_descends (prefixWord ++ tailWord_733031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733034 : List Nat := [3, 1, 3, 4, 1, 1, 1, 2, 4]
def baseStart_733034 : Nat := 118140960795 + 733034 * 2 ^ 59
def prefixEnd_733034 : Nat := 4983230072969 + 3 ^ 40 * 733034 * 2
def baseEnd_733034 : Nat := 334576691633769097603417

theorem tailTrace_733034 : CollatzResearch.WordTrace tailWord_733034 prefixEnd_733034 334576691633769097603417 := by
  unfold tailWord_733034
  simp only [CollatzResearch.WordTrace]
  refine ⟨6683986606587621271311539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17823964284233656723497437 6683986606587621271311539)
  ·
    refine ⟨10025979909881431906967309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6683986606587621271311539 10025979909881431906967309)
    ·
      refine ⟨3759742466205536965112741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10025979909881431906967309 3759742466205536965112741)
      ·
        refine ⟨704951712413538180958639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3759742466205536965112741 704951712413538180958639)
        ·
          refine ⟨1057427568620307271437959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 704951712413538180958639 1057427568620307271437959)
          ·
            refine ⟨1586141352930460907156939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1057427568620307271437959 1586141352930460907156939)
            ·
              refine ⟨2379212029395691360735409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1586141352930460907156939 2379212029395691360735409)
              ·
                refine ⟨1784409022046768520551557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2379212029395691360735409 1784409022046768520551557)
                ·
                  refine ⟨334576691633769097603417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1784409022046768520551557 334576691633769097603417)
                  ·
                    rfl

theorem cell20_733034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 2, 4].length) (baseStart_733034 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_733034 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_733034 prefixEnd_733034 := by exact prefixLift 733034
  have htrace : WordTrace (prefixWord ++ tailWord_733034) baseStart_733034 baseEnd_733034 := by
    simpa [prefixWord, tailWord_733034, baseEnd_733034] using wordTrace_append hprefix tailTrace_733034
  have hstable : (prefixWord ++ tailWord_733034).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733034).length < 2 ^ (prefixWord ++ tailWord_733034).sum := by decide
  have hdescent : baseEnd_733034 < baseStart_733034 := by decide
  rcases family_descends (prefixWord ++ tailWord_733034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733097 : List Nat := [1, 2, 1, 1, 1, 1, 4, 3, 6]
def baseStart_733097 : Nat := 118140960795 + 733097 * 2 ^ 59
def prefixEnd_733097 : Nat := 4983230072969 + 3 ^ 40 * 733097 * 2
def baseEnd_733097 : Nat := 334605446550420878503159

theorem tailTrace_733097 : CollatzResearch.WordTrace tailWord_733097 prefixEnd_733097 334605446550420878503159 := by
  unfold tailWord_733097
  simp only [CollatzResearch.WordTrace]
  refine ⟨26738244225122246844789545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17825496150081497896526363 26738244225122246844789545)
  ·
    refine ⟨20053683168841685133592159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26738244225122246844789545 20053683168841685133592159)
    ·
      refine ⟨30080524753262527700388239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20053683168841685133592159 30080524753262527700388239)
      ·
        refine ⟨45120787129893791550582359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30080524753262527700388239 45120787129893791550582359)
        ·
          refine ⟨67681180694840687325873539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45120787129893791550582359 67681180694840687325873539)
          ·
            refine ⟨101521771042261030988810309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67681180694840687325873539 101521771042261030988810309)
            ·
              refine ⟨19035332070423943310401933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101521771042261030988810309 19035332070423943310401933)
              ·
                refine ⟨7138249526408978741400725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19035332070423943310401933 7138249526408978741400725)
                ·
                  refine ⟨334605446550420878503159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7138249526408978741400725 334605446550420878503159)
                  ·
                    rfl

theorem cell20_733097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 6].length) (baseStart_733097 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_733097 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_733097 prefixEnd_733097 := by exact prefixLift 733097
  have htrace : WordTrace (prefixWord ++ tailWord_733097) baseStart_733097 baseEnd_733097 := by
    simpa [prefixWord, tailWord_733097, baseEnd_733097] using wordTrace_append hprefix tailTrace_733097
  have hstable : (prefixWord ++ tailWord_733097).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733097).length < 2 ^ (prefixWord ++ tailWord_733097).sum := by decide
  have hdescent : baseEnd_733097 < baseStart_733097 := by decide
  rcases family_descends (prefixWord ++ tailWord_733097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733102 : List Nat := [4, 1, 5, 1, 2, 1, 1, 3, 2]
def baseStart_733102 : Nat := 118140960795 + 733102 * 2 ^ 59
def prefixEnd_733102 : Nat := 4983230072969 + 3 ^ 40 * 733102 * 2
def baseEnd_733102 : Nat := 334607728686663083336473

theorem tailTrace_733102 : CollatzResearch.WordTrace tailWord_733102 prefixEnd_733102 334607728686663083336473 := by
  unfold tailWord_733102
  simp only [CollatzResearch.WordTrace]
  refine ⟨3342303323763016587340195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17825617726736088465814373 3342303323763016587340195)
  ·
    refine ⟨5013454985644524881010293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3342303323763016587340195 5013454985644524881010293)
    ·
      refine ⟨470011404904174207594715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5013454985644524881010293 470011404904174207594715)
      ·
        refine ⟨705017107356261311392073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 470011404904174207594715 705017107356261311392073)
        ·
          refine ⟨528762830517195983544055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 705017107356261311392073 528762830517195983544055)
          ·
            refine ⟨793144245775793975316083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 528762830517195983544055 793144245775793975316083)
            ·
              refine ⟨1189716368663690962974125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 793144245775793975316083 1189716368663690962974125)
              ·
                refine ⟨446143638248884111115297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1189716368663690962974125 446143638248884111115297)
                ·
                  refine ⟨334607728686663083336473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 446143638248884111115297 334607728686663083336473)
                  ·
                    rfl

theorem cell20_733102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 3, 2].length) (baseStart_733102 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_733102 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_733102 prefixEnd_733102 := by exact prefixLift 733102
  have htrace : WordTrace (prefixWord ++ tailWord_733102) baseStart_733102 baseEnd_733102 := by
    simpa [prefixWord, tailWord_733102, baseEnd_733102] using wordTrace_append hprefix tailTrace_733102
  have hstable : (prefixWord ++ tailWord_733102).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733102).length < 2 ^ (prefixWord ++ tailWord_733102).sum := by decide
  have hdescent : baseEnd_733102 < baseStart_733102 := by decide
  rcases family_descends (prefixWord ++ tailWord_733102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733141 : List Nat := [1, 3, 2, 3, 2, 3, 2, 1, 3]
def baseStart_733141 : Nat := 118140960795 + 733141 * 2 ^ 59
def prefixEnd_733141 : Nat := 4983230072969 + 3 ^ 40 * 733141 * 2
def baseEnd_733141 : Nat := 334625529349352281036313

theorem tailTrace_733141 : CollatzResearch.WordTrace tailWord_733141 prefixEnd_733141 334625529349352281036313 := by
  unfold tailWord_733141
  simp only [CollatzResearch.WordTrace]
  refine ⟨26739849036962842359391277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17826566024641894906260851 26739849036962842359391277)
  ·
    refine ⟨10027443388861065884771729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26739849036962842359391277 10027443388861065884771729)
    ·
      refine ⟨7520582541645799413578797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10027443388861065884771729 7520582541645799413578797)
      ·
        refine ⟨2820218453117174780092049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7520582541645799413578797 2820218453117174780092049)
        ·
          refine ⟨2115163839837881085069037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2820218453117174780092049 2115163839837881085069037)
          ·
            refine ⟨793186439939205406900889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2115163839837881085069037 793186439939205406900889)
            ·
              refine ⟨594889829954404055175667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 793186439939205406900889 594889829954404055175667)
              ·
                refine ⟨892334744931606082763501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 594889829954404055175667 892334744931606082763501)
                ·
                  refine ⟨334625529349352281036313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 892334744931606082763501 334625529349352281036313)
                  ·
                    rfl

theorem cell20_733141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 2, 1, 3].length) (baseStart_733141 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_733141 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_733141 prefixEnd_733141 := by exact prefixLift 733141
  have htrace : WordTrace (prefixWord ++ tailWord_733141) baseStart_733141 baseEnd_733141 := by
    simpa [prefixWord, tailWord_733141, baseEnd_733141] using wordTrace_append hprefix tailTrace_733141
  have hstable : (prefixWord ++ tailWord_733141).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733141).length < 2 ^ (prefixWord ++ tailWord_733141).sum := by decide
  have hdescent : baseEnd_733141 < baseStart_733141 := by decide
  rcases family_descends (prefixWord ++ tailWord_733141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733182 : List Nat := [4, 2, 2, 2, 1, 3, 2, 2, 2]
def baseStart_733182 : Nat := 118140960795 + 733182 * 2 ^ 59
def prefixEnd_733182 : Nat := 4983230072969 + 3 ^ 40 * 733182 * 2
def baseEnd_733182 : Nat := 334644242866538360669479

theorem tailTrace_733182 : CollatzResearch.WordTrace tailWord_733182 prefixEnd_733182 334644242866538360669479 := by
  unfold tailWord_733182
  simp only [CollatzResearch.WordTrace]
  refine ⟨3342668053726788295204225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17827562953209537574422533 3342668053726788295204225)
  ·
    refine ⟨2507001040295091221403169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3342668053726788295204225 2507001040295091221403169)
    ·
      refine ⟨1880250780221318416052377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2507001040295091221403169 1880250780221318416052377)
      ·
        refine ⟨1410188085165988812039283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1880250780221318416052377 1410188085165988812039283)
        ·
          refine ⟨2115282127748983218058925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1410188085165988812039283 2115282127748983218058925)
          ·
            refine ⟨793230797905868706772097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2115282127748983218058925 793230797905868706772097)
            ·
              refine ⟨594923098429401530079073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 793230797905868706772097 594923098429401530079073)
              ·
                refine ⟨446192323822051147559305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 594923098429401530079073 446192323822051147559305)
                ·
                  refine ⟨334644242866538360669479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 446192323822051147559305 334644242866538360669479)
                  ·
                    rfl

theorem cell20_733182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 2, 2, 2].length) (baseStart_733182 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_733182 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_733182 prefixEnd_733182 := by exact prefixLift 733182
  have htrace : WordTrace (prefixWord ++ tailWord_733182) baseStart_733182 baseEnd_733182 := by
    simpa [prefixWord, tailWord_733182, baseEnd_733182] using wordTrace_append hprefix tailTrace_733182
  have hstable : (prefixWord ++ tailWord_733182).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733182).length < 2 ^ (prefixWord ++ tailWord_733182).sum := by decide
  have hdescent : baseEnd_733182 < baseStart_733182 := by decide
  rcases family_descends (prefixWord ++ tailWord_733182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733207 : List Nat := [1, 1, 3, 5, 2, 1, 1, 2, 4]
def baseStart_733207 : Nat := 118140960795 + 733207 * 2 ^ 59
def prefixEnd_733207 : Nat := 4983230072969 + 3 ^ 40 * 733207 * 2
def baseEnd_733207 : Nat := 334655653547749384836043

theorem tailTrace_733207 : CollatzResearch.WordTrace tailWord_733207 prefixEnd_733207 334655653547749384836043 := by
  unfold tailWord_733207
  simp only [CollatzResearch.WordTrace]
  refine ⟨26742256254723735631293875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17828170836482490420862583 26742256254723735631293875)
  ·
    refine ⟨40113384382085603446940813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26742256254723735631293875 40113384382085603446940813)
    ·
      refine ⟨15042519143282101292602805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40113384382085603446940813 15042519143282101292602805)
      ·
        refine ⟨1410236169682696996181513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15042519143282101292602805 1410236169682696996181513)
        ·
          refine ⟨1057677127262022747136135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1410236169682696996181513 1057677127262022747136135)
          ·
            refine ⟨1586515690893034120704203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1057677127262022747136135 1586515690893034120704203)
            ·
              refine ⟨2379773536339551181056305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1586515690893034120704203 2379773536339551181056305)
              ·
                refine ⟨1784830152254663385792229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2379773536339551181056305 1784830152254663385792229)
                ·
                  refine ⟨334655653547749384836043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1784830152254663385792229 334655653547749384836043)
                  ·
                    rfl

theorem cell20_733207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 2, 4].length) (baseStart_733207 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_733207 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_733207 prefixEnd_733207 := by exact prefixLift 733207
  have htrace : WordTrace (prefixWord ++ tailWord_733207) baseStart_733207 baseEnd_733207 := by
    simpa [prefixWord, tailWord_733207, baseEnd_733207] using wordTrace_append hprefix tailTrace_733207
  have hstable : (prefixWord ++ tailWord_733207).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733207).length < 2 ^ (prefixWord ++ tailWord_733207).sum := by decide
  have hdescent : baseEnd_733207 < baseStart_733207 := by decide
  rcases family_descends (prefixWord ++ tailWord_733207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733245 : List Nat := [1, 4, 1, 3, 1, 1, 1, 6, 2]
def baseStart_733245 : Nat := 118140960795 + 733245 * 2 ^ 59
def prefixEnd_733245 : Nat := 4983230072969 + 3 ^ 40 * 733245 * 2
def baseEnd_733245 : Nat := 334672997783190141569221

theorem tailTrace_733245 : CollatzResearch.WordTrace tailWord_733245 prefixEnd_733245 334672997783190141569221 := by
  unfold tailWord_733245
  simp only [CollatzResearch.WordTrace]
  refine ⟨26743642228586068121177189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17829094819057378747451459 26743642228586068121177189)
  ·
    refine ⟨5014432917859887772720723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26743642228586068121177189 5014432917859887772720723)
    ·
      refine ⟨7521649376789831659081085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5014432917859887772720723 7521649376789831659081085)
      ·
        refine ⟨2820618516296186872155407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7521649376789831659081085 2820618516296186872155407)
        ·
          refine ⟨4230927774444280308233111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2820618516296186872155407 4230927774444280308233111)
          ·
            refine ⟨6346391661666420462349667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4230927774444280308233111 6346391661666420462349667)
            ·
              refine ⟨9519587492499630693524501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6346391661666420462349667 9519587492499630693524501)
              ·
                refine ⟨446230663710920188758961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9519587492499630693524501 446230663710920188758961)
                ·
                  refine ⟨334672997783190141569221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 446230663710920188758961 334672997783190141569221)
                  ·
                    rfl

theorem cell20_733245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 6, 2].length) (baseStart_733245 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_733245 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_733245 prefixEnd_733245 := by exact prefixLift 733245
  have htrace : WordTrace (prefixWord ++ tailWord_733245) baseStart_733245 baseEnd_733245 := by
    simpa [prefixWord, tailWord_733245, baseEnd_733245] using wordTrace_append hprefix tailTrace_733245
  have hstable : (prefixWord ++ tailWord_733245).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733245).length < 2 ^ (prefixWord ++ tailWord_733245).sum := by decide
  have hdescent : baseEnd_733245 < baseStart_733245 := by decide
  rcases family_descends (prefixWord ++ tailWord_733245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733280 : List Nat := [2, 1, 1, 3, 2, 3, 1, 2, 5]
def baseStart_733280 : Nat := 118140960795 + 733280 * 2 ^ 59
def prefixEnd_733280 : Nat := 4983230072969 + 3 ^ 40 * 733280 * 2
def baseEnd_733280 : Nat := 334688972736885575402411

theorem tailTrace_733280 : CollatzResearch.WordTrace tailWord_733280 prefixEnd_733280 334688972736885575402411 := by
  unfold tailWord_733280
  simp only [CollatzResearch.WordTrace]
  refine ⟨13372459391729634549350647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17829945855639512732467529 13372459391729634549350647)
  ·
    refine ⟨20058689087594451824025971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13372459391729634549350647 20058689087594451824025971)
    ·
      refine ⟨30088033631391677736038957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20058689087594451824025971 30088033631391677736038957)
      ·
        refine ⟨11283012611771879151014609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30088033631391677736038957 11283012611771879151014609)
        ·
          refine ⟨8462259458828909363260957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11283012611771879151014609 8462259458828909363260957)
          ·
            refine ⟨3173347297060841011222859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8462259458828909363260957 3173347297060841011222859)
            ·
              refine ⟨4760020945591261516834289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3173347297060841011222859 4760020945591261516834289)
              ·
                refine ⟨3570015709193446137625717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4760020945591261516834289 3570015709193446137625717)
                ·
                  refine ⟨334688972736885575402411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3570015709193446137625717 334688972736885575402411)
                  ·
                    rfl

theorem cell20_733280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 5].length) (baseStart_733280 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_733280 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_733280 prefixEnd_733280 := by exact prefixLift 733280
  have htrace : WordTrace (prefixWord ++ tailWord_733280) baseStart_733280 baseEnd_733280 := by
    simpa [prefixWord, tailWord_733280, baseEnd_733280] using wordTrace_append hprefix tailTrace_733280
  have hstable : (prefixWord ++ tailWord_733280).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733280).length < 2 ^ (prefixWord ++ tailWord_733280).sum := by decide
  have hdescent : baseEnd_733280 < baseStart_733280 := by decide
  rcases family_descends (prefixWord ++ tailWord_733280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733283 : List Nat := [1, 1, 1, 5, 1, 1, 5, 3, 2]
def baseStart_733283 : Nat := 118140960795 + 733283 * 2 ^ 59
def prefixEnd_733283 : Nat := 4983230072969 + 3 ^ 40 * 733283 * 2
def baseEnd_733283 : Nat := 334690342018630898302399

theorem tailTrace_733283 : CollatzResearch.WordTrace tailWord_733283 prefixEnd_733283 334690342018630898302399 := by
  unfold tailWord_733283
  simp only [CollatzResearch.WordTrace]
  refine ⟨26745028202448400611060503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17830018801632267074040335 26745028202448400611060503)
  ·
    refine ⟨40117542303672600916590755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26745028202448400611060503 40117542303672600916590755)
    ·
      refine ⟨60176313455508901374886133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40117542303672600916590755 60176313455508901374886133)
      ·
        refine ⟨5641529386453959503895575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60176313455508901374886133 5641529386453959503895575)
        ·
          refine ⟨8462294079680939255843363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5641529386453959503895575 8462294079680939255843363)
          ·
            refine ⟨12693441119521408883765045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8462294079680939255843363 12693441119521408883765045)
            ·
              refine ⟨1190010104955132082852973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12693441119521408883765045 1190010104955132082852973)
              ·
                refine ⟨446253789358174531069865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1190010104955132082852973 446253789358174531069865)
                ·
                  refine ⟨334690342018630898302399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 446253789358174531069865 334690342018630898302399)
                  ·
                    rfl

theorem cell20_733283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 3, 2].length) (baseStart_733283 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_733283 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_733283 prefixEnd_733283 := by exact prefixLift 733283
  have htrace : WordTrace (prefixWord ++ tailWord_733283) baseStart_733283 baseEnd_733283 := by
    simpa [prefixWord, tailWord_733283, baseEnd_733283] using wordTrace_append hprefix tailTrace_733283
  have hstable : (prefixWord ++ tailWord_733283).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733283).length < 2 ^ (prefixWord ++ tailWord_733283).sum := by decide
  have hdescent : baseEnd_733283 < baseStart_733283 := by decide
  rcases family_descends (prefixWord ++ tailWord_733283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733290 : List Nat := [3, 1, 3, 2, 3, 2, 6]
def baseStart_733290 : Nat := 118140960795 + 733290 * 2 ^ 59
def prefixEnd_733290 : Nat := 4983230072969 + 3 ^ 40 * 733290 * 2
def baseEnd_733290 : Nat := 37188170778818887229893

theorem tailTrace_733290 : CollatzResearch.WordTrace tailWord_733290 prefixEnd_733290 37188170778818887229893 := by
  unfold tailWord_733290
  simp only [CollatzResearch.WordTrace]
  refine ⟨6686320878355760201641331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17830189008948693871043549 6686320878355760201641331)
  ·
    refine ⟨10029481317533640302461997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6686320878355760201641331 10029481317533640302461997)
    ·
      refine ⟨3761055494075115113423249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10029481317533640302461997 3761055494075115113423249)
      ·
        refine ⟨2820791620556336335067437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3761055494075115113423249 2820791620556336335067437)
        ·
          refine ⟨1057796857708626125650289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2820791620556336335067437 1057796857708626125650289)
          ·
            refine ⟨793347643281469594237717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1057796857708626125650289 793347643281469594237717)
            ·
              refine ⟨37188170778818887229893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 793347643281469594237717 37188170778818887229893)
              ·
                rfl

theorem cell20_733290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 6].length) (baseStart_733290 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_733290 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_733290 prefixEnd_733290 := by exact prefixLift 733290
  have htrace : WordTrace (prefixWord ++ tailWord_733290) baseStart_733290 baseEnd_733290 := by
    simpa [prefixWord, tailWord_733290, baseEnd_733290] using wordTrace_append hprefix tailTrace_733290
  have hstable : (prefixWord ++ tailWord_733290).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733290).length < 2 ^ (prefixWord ++ tailWord_733290).sum := by decide
  have hdescent : baseEnd_733290 < baseStart_733290 := by decide
  rcases family_descends (prefixWord ++ tailWord_733290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733363 : List Nat := [1, 1, 1, 2, 3, 2, 1, 5, 4]
def baseStart_733363 : Nat := 118140960795 + 733363 * 2 ^ 59
def prefixEnd_733363 : Nat := 4983230072969 + 3 ^ 40 * 733363 * 2
def baseEnd_733363 : Nat := 334726856198506175635405

theorem tailTrace_733363 : CollatzResearch.WordTrace tailWord_733363 prefixEnd_733363 334726856198506175635405 := by
  unfold tailWord_733363
  simp only [CollatzResearch.WordTrace]
  refine ⟨26747946042158574273972743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17831964028105716182648495 26747946042158574273972743)
  ·
    refine ⟨40121919063237861410959115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26747946042158574273972743 40121919063237861410959115)
    ·
      refine ⟨60182878594856792116438673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40121919063237861410959115 60182878594856792116438673)
      ·
        refine ⟨45137158946142594087329005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60182878594856792116438673 45137158946142594087329005)
        ·
          refine ⟨16926434604803472782748377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45137158946142594087329005 16926434604803472782748377)
          ·
            refine ⟨12694825953602604587061283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16926434604803472782748377 12694825953602604587061283)
            ·
              refine ⟨19042238930403906880591925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12694825953602604587061283 19042238930403906880591925)
              ·
                refine ⟨1785209899725366270055493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19042238930403906880591925 1785209899725366270055493)
                ·
                  refine ⟨334726856198506175635405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1785209899725366270055493 334726856198506175635405)
                  ·
                    rfl

theorem cell20_733363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 5, 4].length) (baseStart_733363 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_733363 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_733363 prefixEnd_733363 := by exact prefixLift 733363
  have htrace : WordTrace (prefixWord ++ tailWord_733363) baseStart_733363 baseEnd_733363 := by
    simpa [prefixWord, tailWord_733363, baseEnd_733363] using wordTrace_append hprefix tailTrace_733363
  have hstable : (prefixWord ++ tailWord_733363).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733363).length < 2 ^ (prefixWord ++ tailWord_733363).sum := by decide
  have hdescent : baseEnd_733363 < baseStart_733363 := by decide
  rcases family_descends (prefixWord ++ tailWord_733363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733380 : List Nat := [2, 3, 3, 1, 2, 1, 1, 1, 6]
def baseStart_733380 : Nat := 118140960795 + 733380 * 2 ^ 59
def prefixEnd_733380 : Nat := 4983230072969 + 3 ^ 40 * 733380 * 2
def baseEnd_733380 : Nat := 334734615461729672068669

theorem tailTrace_733380 : CollatzResearch.WordTrace tailWord_733380 prefixEnd_733380 334734615461729672068669 := by
  unfold tailWord_733380
  simp only [CollatzResearch.WordTrace]
  refine ⟨13374283041548493088670797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17832377388731324118227729 13374283041548493088670797)
  ·
    refine ⟨5015356140580684908251549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13374283041548493088670797 5015356140580684908251549)
    ·
      refine ⟨1880758552717756840594331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5015356140580684908251549 1880758552717756840594331)
      ·
        refine ⟨2821137829076635260891497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1880758552717756840594331 2821137829076635260891497)
        ·
          refine ⟨2115853371807476445668623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2821137829076635260891497 2115853371807476445668623)
          ·
            refine ⟨3173780057711214668502935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2115853371807476445668623 3173780057711214668502935)
            ·
              refine ⟨4760670086566822002754403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3173780057711214668502935 4760670086566822002754403)
              ·
                refine ⟨7141005129850233004131605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4760670086566822002754403 7141005129850233004131605)
                ·
                  refine ⟨334734615461729672068669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7141005129850233004131605 334734615461729672068669)
                  ·
                    rfl

theorem cell20_733380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_733380 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_733380 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_733380 prefixEnd_733380 := by exact prefixLift 733380
  have htrace : WordTrace (prefixWord ++ tailWord_733380) baseStart_733380 baseEnd_733380 := by
    simpa [prefixWord, tailWord_733380, baseEnd_733380] using wordTrace_append hprefix tailTrace_733380
  have hstable : (prefixWord ++ tailWord_733380).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733380).length < 2 ^ (prefixWord ++ tailWord_733380).sum := by decide
  have hdescent : baseEnd_733380 < baseStart_733380 := by decide
  rcases family_descends (prefixWord ++ tailWord_733380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733387 : List Nat := [1, 1, 1, 1, 3, 2, 7, 4]
def baseStart_733387 : Nat := 118140960795 + 733387 * 2 ^ 59
def prefixEnd_733387 : Nat := 4983230072969 + 3 ^ 40 * 733387 * 2
def baseEnd_733387 : Nat := 111579270150822919611769

theorem tailTrace_733387 : CollatzResearch.WordTrace tailWord_733387 prefixEnd_733387 111579270150822919611769 := by
  unfold tailWord_733387
  simp only [CollatzResearch.WordTrace]
  refine ⟨26748821394071626372846415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17832547596047750915230943 26748821394071626372846415)
  ·
    refine ⟨40123232091107439559269623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26748821394071626372846415 40123232091107439559269623)
    ·
      refine ⟨60184848136661159338904435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40123232091107439559269623 60184848136661159338904435)
      ·
        refine ⟨90277272204991739008356653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60184848136661159338904435 90277272204991739008356653)
        ·
          refine ⟨33853977076871902128133745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90277272204991739008356653 33853977076871902128133745)
          ·
            refine ⟨25390482807653926596100309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33853977076871902128133745 25390482807653926596100309)
            ·
              refine ⟨595089440804388904596101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 25390482807653926596100309 595089440804388904596101)
              ·
                refine ⟨111579270150822919611769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 595089440804388904596101 111579270150822919611769)
                ·
                  rfl

theorem cell20_733387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 7, 4].length) (baseStart_733387 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_733387 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_733387 prefixEnd_733387 := by exact prefixLift 733387
  have htrace : WordTrace (prefixWord ++ tailWord_733387) baseStart_733387 baseEnd_733387 := by
    simpa [prefixWord, tailWord_733387, baseEnd_733387] using wordTrace_append hprefix tailTrace_733387
  have hstable : (prefixWord ++ tailWord_733387).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733387).length < 2 ^ (prefixWord ++ tailWord_733387).sum := by decide
  have hdescent : baseEnd_733387 < baseStart_733387 := by decide
  rcases family_descends (prefixWord ++ tailWord_733387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733408 : List Nat := [2, 1, 1, 3, 1, 3, 9]
def baseStart_733408 : Nat := 118140960795 + 733408 * 2 ^ 59
def prefixEnd_733408 : Nat := 4983230072969 + 3 ^ 40 * 733408 * 2
def baseEnd_733408 : Nat := 37194155047187335459469

theorem tailTrace_733408 : CollatzResearch.WordTrace tailWord_733408 prefixEnd_733408 37194155047187335459469 := by
  unfold tailWord_733408
  simp only [CollatzResearch.WordTrace]
  refine ⟨13374793663497773479680439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17833058217997031306240585 13374793663497773479680439)
  ·
    refine ⟨20062190495246660219520659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13374793663497773479680439 20062190495246660219520659)
    ·
      refine ⟨30093285742869990329280989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20062190495246660219520659 30093285742869990329280989)
      ·
        refine ⟨11284982153576246373480371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30093285742869990329280989 11284982153576246373480371)
        ·
          refine ⟨16927473230364369560220557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11284982153576246373480371 16927473230364369560220557)
          ·
            refine ⟨6347802461386638585082709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16927473230364369560220557 6347802461386638585082709)
            ·
              refine ⟨37194155047187335459469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6347802461386638585082709 37194155047187335459469)
              ·
                rfl

theorem cell20_733408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 9].length) (baseStart_733408 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_733408 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_733408 prefixEnd_733408 := by exact prefixLift 733408
  have htrace : WordTrace (prefixWord ++ tailWord_733408) baseStart_733408 baseEnd_733408 := by
    simpa [prefixWord, tailWord_733408, baseEnd_733408] using wordTrace_append hprefix tailTrace_733408
  have hstable : (prefixWord ++ tailWord_733408).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733408).length < 2 ^ (prefixWord ++ tailWord_733408).sum := by decide
  have hdescent : baseEnd_733408 < baseStart_733408 := by decide
  rcases family_descends (prefixWord ++ tailWord_733408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733418 : List Nat := [3, 1, 3, 1, 1, 2, 4, 1, 4]
def baseStart_733418 : Nat := 118140960795 + 733418 * 2 ^ 59
def prefixEnd_733418 : Nat := 4983230072969 + 3 ^ 40 * 733418 * 2
def baseEnd_733418 : Nat := 334751959697170428801847

theorem tailTrace_733418 : CollatzResearch.WordTrace tailWord_733418 prefixEnd_733418 334751959697170428801847 := by
  unfold tailWord_733418
  simp only [CollatzResearch.WordTrace]
  refine ⟨6687488014239829666806227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17833301371306212444816605 6687488014239829666806227)
  ·
    refine ⟨10031232021359744500209341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6687488014239829666806227 10031232021359744500209341)
    ·
      refine ⟨3761712008009904187578503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10031232021359744500209341 3761712008009904187578503)
      ·
        refine ⟨5642568012014856281367755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3761712008009904187578503 5642568012014856281367755)
        ·
          refine ⟨8463852018022284422051633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5642568012014856281367755 8463852018022284422051633)
          ·
            refine ⟨6347889013516713316538725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8463852018022284422051633 6347889013516713316538725)
            ·
              refine ⟨1190229190034383746851011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6347889013516713316538725 1190229190034383746851011)
              ·
                refine ⟨1785343785051575620276517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1190229190034383746851011 1785343785051575620276517)
                ·
                  refine ⟨334751959697170428801847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1785343785051575620276517 334751959697170428801847)
                  ·
                    rfl

theorem cell20_733418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 1, 4].length) (baseStart_733418 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_733418 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_733418 prefixEnd_733418 := by exact prefixLift 733418
  have htrace : WordTrace (prefixWord ++ tailWord_733418) baseStart_733418 baseEnd_733418 := by
    simpa [prefixWord, tailWord_733418, baseEnd_733418] using wordTrace_append hprefix tailTrace_733418
  have hstable : (prefixWord ++ tailWord_733418).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733418).length < 2 ^ (prefixWord ++ tailWord_733418).sum := by decide
  have hdescent : baseEnd_733418 < baseStart_733418 := by decide
  rcases family_descends (prefixWord ++ tailWord_733418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733432 : List Nat := [2, 1, 2, 1, 1, 2, 1, 7, 3]
def baseStart_733432 : Nat := 118140960795 + 733432 * 2 ^ 59
def prefixEnd_733432 : Nat := 4983230072969 + 3 ^ 40 * 733432 * 2
def baseEnd_733432 : Nat := 334758349678648602335123

theorem tailTrace_733432 : CollatzResearch.WordTrace tailWord_733432 prefixEnd_733432 334758349678648602335123 := by
  unfold tailWord_733432
  simp only [CollatzResearch.WordTrace]
  refine ⟨13375231339454299529117275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17833641785939066038823033 13375231339454299529117275)
  ·
    refine ⟨20062847009181449293675913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13375231339454299529117275 20062847009181449293675913)
    ·
      refine ⟨15047135256886086970256935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20062847009181449293675913 15047135256886086970256935)
      ·
        refine ⟨22570702885329130455385403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15047135256886086970256935 22570702885329130455385403)
        ·
          refine ⟨33856054327993695683078105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22570702885329130455385403 33856054327993695683078105)
          ·
            refine ⟨25392040745995271762308579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33856054327993695683078105 25392040745995271762308579)
            ·
              refine ⟨38088061118992907643462869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25392040745995271762308579 38088061118992907643462869)
              ·
                refine ⟨892688932476396272893661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 38088061118992907643462869 892688932476396272893661)
                ·
                  refine ⟨334758349678648602335123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 892688932476396272893661 334758349678648602335123)
                  ·
                    rfl

theorem cell20_733432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 7, 3].length) (baseStart_733432 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_733432 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_733432 prefixEnd_733432 := by exact prefixLift 733432
  have htrace : WordTrace (prefixWord ++ tailWord_733432) baseStart_733432 baseEnd_733432 := by
    simpa [prefixWord, tailWord_733432, baseEnd_733432] using wordTrace_append hprefix tailTrace_733432
  have hstable : (prefixWord ++ tailWord_733432).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733432).length < 2 ^ (prefixWord ++ tailWord_733432).sum := by decide
  have hdescent : baseEnd_733432 < baseStart_733432 := by decide
  rcases family_descends (prefixWord ++ tailWord_733432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733439 : List Nat := [1, 1, 2, 2, 1, 4, 1, 4, 4]
def baseStart_733439 : Nat := 118140960795 + 733439 * 2 ^ 59
def prefixEnd_733439 : Nat := 4983230072969 + 3 ^ 40 * 733439 * 2
def baseEnd_733439 : Nat := 334761544669387689101761

theorem tailTrace_733439 : CollatzResearch.WordTrace tailWord_733439 prefixEnd_733439 334761544669387689101761 := by
  unfold tailWord_733439
  simp only [CollatzResearch.WordTrace]
  refine ⟨26750717989883239253739371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17833811993255492835826247 26750717989883239253739371)
  ·
    refine ⟨40126076984824858880609057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26750717989883239253739371 40126076984824858880609057)
    ·
      refine ⟨30094557738618644160456793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40126076984824858880609057 30094557738618644160456793)
      ·
        refine ⟨22570918303963983120342595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30094557738618644160456793 22570918303963983120342595)
        ·
          refine ⟨33856377455945974680513893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22570918303963983120342595 33856377455945974680513893)
          ·
            refine ⟨6348070772989870252596355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33856377455945974680513893 6348070772989870252596355)
            ·
              refine ⟨9522106159484805378894533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6348070772989870252596355 9522106159484805378894533)
              ·
                refine ⟨1785394904903401008542725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9522106159484805378894533 1785394904903401008542725)
                ·
                  refine ⟨334761544669387689101761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1785394904903401008542725 334761544669387689101761)
                  ·
                    rfl

theorem cell20_733439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 4, 4].length) (baseStart_733439 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_733439 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_733439 prefixEnd_733439 := by exact prefixLift 733439
  have htrace : WordTrace (prefixWord ++ tailWord_733439) baseStart_733439 baseEnd_733439 := by
    simpa [prefixWord, tailWord_733439, baseEnd_733439] using wordTrace_append hprefix tailTrace_733439
  have hstable : (prefixWord ++ tailWord_733439).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733439).length < 2 ^ (prefixWord ++ tailWord_733439).sum := by decide
  have hdescent : baseEnd_733439 < baseStart_733439 := by decide
  rcases family_descends (prefixWord ++ tailWord_733439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733442 : List Nat := [3, 4, 1, 1, 2, 2, 1, 6]
def baseStart_733442 : Nat := 118140960795 + 733442 * 2 ^ 59
def prefixEnd_733442 : Nat := 4983230072969 + 3 ^ 40 * 733442 * 2
def baseEnd_733442 : Nat := 111587637983711004000583

theorem tailTrace_733442 : CollatzResearch.WordTrace tailWord_733442 prefixEnd_733442 111587637983711004000583 := by
  unfold tailWord_733442
  simp only [CollatzResearch.WordTrace]
  refine ⟨6687706852218092691524645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17833884939248247177399053 6687706852218092691524645)
  ·
    refine ⟨1253945034790892379660871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6687706852218092691524645 1253945034790892379660871)
    ·
      refine ⟨1880917552186338569491307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1253945034790892379660871 1880917552186338569491307)
      ·
        refine ⟨2821376328279507854236961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1880917552186338569491307 2821376328279507854236961)
        ·
          refine ⟨2116032246209630890677721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2821376328279507854236961 2116032246209630890677721)
          ·
            refine ⟨1587024184657223168008291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2116032246209630890677721 1587024184657223168008291)
            ·
              refine ⟨2380536276985834752012437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1587024184657223168008291 2380536276985834752012437)
              ·
                refine ⟨111587637983711004000583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2380536276985834752012437 111587637983711004000583)
                ·
                  rfl

theorem cell20_733442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 6].length) (baseStart_733442 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_733442 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_733442 prefixEnd_733442 := by exact prefixLift 733442
  have htrace : WordTrace (prefixWord ++ tailWord_733442) baseStart_733442 baseEnd_733442 := by
    simpa [prefixWord, tailWord_733442, baseEnd_733442] using wordTrace_append hprefix tailTrace_733442
  have hstable : (prefixWord ++ tailWord_733442).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733442).length < 2 ^ (prefixWord ++ tailWord_733442).sum := by decide
  have hdescent : baseEnd_733442 < baseStart_733442 := by decide
  rcases family_descends (prefixWord ++ tailWord_733442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733463 : List Nat := [1, 1, 3, 4, 1, 4, 6]
def baseStart_733463 : Nat := 118140960795 + 733463 * 2 ^ 59
def prefixEnd_733463 : Nat := 4983230072969 + 3 ^ 40 * 733463 * 2
def baseEnd_733463 : Nat := 37196944324816696922407

theorem tailTrace_733463 : CollatzResearch.WordTrace tailWord_733463 prefixEnd_733463 37196944324816696922407 := by
  unfold tailWord_733463
  simp only [CollatzResearch.WordTrace]
  refine ⟨26751593341796291352613043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17834395561197527568408695 26751593341796291352613043)
  ·
    refine ⟨40127390012694437028919565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26751593341796291352613043 40127390012694437028919565)
    ·
      refine ⟨15047771254760413885844837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40127390012694437028919565 15047771254760413885844837)
      ·
        refine ⟨2821457110267577603595907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15047771254760413885844837 2821457110267577603595907)
        ·
          refine ⟨4232185665401366405393861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2821457110267577603595907 4232185665401366405393861)
          ·
            refine ⟨793534812262756201011349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4232185665401366405393861 793534812262756201011349)
            ·
              refine ⟨37196944324816696922407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 793534812262756201011349 37196944324816696922407)
              ·
                rfl

theorem cell20_733463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 6].length) (baseStart_733463 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_733463 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_733463 prefixEnd_733463 := by exact prefixLift 733463
  have htrace : WordTrace (prefixWord ++ tailWord_733463) baseStart_733463 baseEnd_733463 := by
    simpa [prefixWord, tailWord_733463, baseEnd_733463] using wordTrace_append hprefix tailTrace_733463
  have hstable : (prefixWord ++ tailWord_733463).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733463).length < 2 ^ (prefixWord ++ tailWord_733463).sum := by decide
  have hdescent : baseEnd_733463 < baseStart_733463 := by decide
  rcases family_descends (prefixWord ++ tailWord_733463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733469 : List Nat := [1, 4, 2, 3, 2, 1, 3, 2, 2]
def baseStart_733469 : Nat := 118140960795 + 733469 * 2 ^ 59
def prefixEnd_733469 : Nat := 4983230072969 + 3 ^ 40 * 733469 * 2
def baseEnd_733469 : Nat := 334775237486840918101639

theorem tailTrace_733469 : CollatzResearch.WordTrace tailWord_733469 prefixEnd_733469 334775237486840918101639 := by
  unfold tailWord_733469
  simp only [CollatzResearch.WordTrace]
  refine ⟨26751812179774554377331461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17834541453183036251554307 26751812179774554377331461)
  ·
    refine ⟨5015964783707728945749649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26751812179774554377331461 5015964783707728945749649)
    ·
      refine ⟨3761973587780796709312237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5015964783707728945749649 3761973587780796709312237)
      ·
        refine ⟨1410740095417798765992089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3761973587780796709312237 1410740095417798765992089)
        ·
          refine ⟨1058055071563349074494067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1410740095417798765992089 1058055071563349074494067)
          ·
            refine ⟨1587082607345023611741101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1058055071563349074494067 1587082607345023611741101)
            ·
              refine ⟨595155977754383854402913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1587082607345023611741101 595155977754383854402913)
              ·
                refine ⟨446366983315787890802185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 595155977754383854402913 446366983315787890802185)
                ·
                  refine ⟨334775237486840918101639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 446366983315787890802185 334775237486840918101639)
                  ·
                    rfl

theorem cell20_733469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 3, 2, 2].length) (baseStart_733469 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_733469 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_733469 prefixEnd_733469 := by exact prefixLift 733469
  have htrace : WordTrace (prefixWord ++ tailWord_733469) baseStart_733469 baseEnd_733469 := by
    simpa [prefixWord, tailWord_733469, baseEnd_733469] using wordTrace_append hprefix tailTrace_733469
  have hstable : (prefixWord ++ tailWord_733469).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733469).length < 2 ^ (prefixWord ++ tailWord_733469).sum := by decide
  have hdescent : baseEnd_733469 < baseStart_733469 := by decide
  rcases family_descends (prefixWord ++ tailWord_733469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733479 : List Nat := [1, 1, 8, 1, 1, 2, 2, 1, 3]
def baseStart_733479 : Nat := 118140960795 + 733479 * 2 ^ 59
def prefixEnd_733479 : Nat := 4983230072969 + 3 ^ 40 * 733479 * 2
def baseEnd_733479 : Nat := 334779801759325327768265

theorem tailTrace_733479 : CollatzResearch.WordTrace tailWord_733479 prefixEnd_733479 334779801759325327768265 := by
  unfold tailWord_733479
  simp only [CollatzResearch.WordTrace]
  refine ⟨26752176909738326085195491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17834784606492217390130327 26752176909738326085195491)
  ·
    refine ⟨40128265364607489127793237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26752176909738326085195491 40128265364607489127793237)
    ·
      refine ⟨470253109741494013216327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 40128265364607489127793237 470253109741494013216327)
      ·
        refine ⟨705379664612241019824491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 470253109741494013216327 705379664612241019824491)
        ·
          refine ⟨1058069496918361529736737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 705379664612241019824491 1058069496918361529736737)
          ·
            refine ⟨793552122688771147302553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1058069496918361529736737 793552122688771147302553)
            ·
              refine ⟨595164092016578360476915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 793552122688771147302553 595164092016578360476915)
              ·
                refine ⟨892746138024867540715373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 595164092016578360476915 892746138024867540715373)
                ·
                  refine ⟨334779801759325327768265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 892746138024867540715373 334779801759325327768265)
                  ·
                    rfl

theorem cell20_733479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 2, 1, 3].length) (baseStart_733479 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_733479 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_733479 prefixEnd_733479 := by exact prefixLift 733479
  have htrace : WordTrace (prefixWord ++ tailWord_733479) baseStart_733479 baseEnd_733479 := by
    simpa [prefixWord, tailWord_733479, baseEnd_733479] using wordTrace_append hprefix tailTrace_733479
  have hstable : (prefixWord ++ tailWord_733479).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733479).length < 2 ^ (prefixWord ++ tailWord_733479).sum := by decide
  have hdescent : baseEnd_733479 < baseStart_733479 := by decide
  rcases family_descends (prefixWord ++ tailWord_733479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733480 : List Nat := [2, 1, 5, 1, 3, 1, 2, 5]
def baseStart_733480 : Nat := 118140960795 + 733480 * 2 ^ 59
def prefixEnd_733480 : Nat := 4983230072969 + 3 ^ 40 * 733480 * 2
def baseEnd_733480 : Nat := 111593419395524589578309

theorem tailTrace_733480 : CollatzResearch.WordTrace tailWord_733480 prefixEnd_733480 111593419395524589578309 := by
  unfold tailWord_733480
  simp only [CollatzResearch.WordTrace]
  refine ⟨13376106691367351627990947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17834808921823135503987929 13376106691367351627990947)
  ·
    refine ⟨20064160037051027441986421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13376106691367351627990947 20064160037051027441986421)
    ·
      refine ⟨1881015003473533822686227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20064160037051027441986421 1881015003473533822686227)
      ·
        refine ⟨2821522505210300734029341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1881015003473533822686227 2821522505210300734029341)
        ·
          refine ⟨1058070939453862775261003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2821522505210300734029341 1058070939453862775261003)
          ·
            refine ⟨1587106409180794162891505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1058070939453862775261003 1587106409180794162891505)
            ·
              refine ⟨1190329806885595622168629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1587106409180794162891505 1190329806885595622168629)
              ·
                refine ⟨111593419395524589578309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1190329806885595622168629 111593419395524589578309)
                ·
                  rfl

theorem cell20_733480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 5].length) (baseStart_733480 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_733480 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_733480 prefixEnd_733480 := by exact prefixLift 733480
  have htrace : WordTrace (prefixWord ++ tailWord_733480) baseStart_733480 baseEnd_733480 := by
    simpa [prefixWord, tailWord_733480, baseEnd_733480] using wordTrace_append hprefix tailTrace_733480
  have hstable : (prefixWord ++ tailWord_733480).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733480).length < 2 ^ (prefixWord ++ tailWord_733480).sum := by decide
  have hdescent : baseEnd_733480 < baseStart_733480 := by decide
  rcases family_descends (prefixWord ++ tailWord_733480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733484 : List Nat := [2, 2, 1, 1, 1, 3, 3, 7]
def baseStart_733484 : Nat := 118140960795 + 733484 * 2 ^ 59
def prefixEnd_733484 : Nat := 4983230072969 + 3 ^ 40 * 733484 * 2
def baseEnd_733484 : Nat := 111594027965189177533859

theorem tailTrace_733484 : CollatzResearch.WordTrace tailWord_733484 prefixEnd_733484 111594027965189177533859 := by
  unfold tailWord_733484
  simp only [CollatzResearch.WordTrace]
  refine ⟨13376179637360105969563753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17834906183146807959418337 13376179637360105969563753)
  ·
    refine ⟨10032134728020079477172815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13376179637360105969563753 10032134728020079477172815)
    ·
      refine ⟨15048202092030119215759223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10032134728020079477172815 15048202092030119215759223)
      ·
        refine ⟨22572303138045178823638835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15048202092030119215759223 22572303138045178823638835)
        ·
          refine ⟨33858454707067768235458253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22572303138045178823638835 33858454707067768235458253)
          ·
            refine ⟨12696920515150413088296845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33858454707067768235458253 12696920515150413088296845)
            ·
              refine ⟨4761345193181404908111317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12696920515150413088296845 4761345193181404908111317)
              ·
                refine ⟨111594027965189177533859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4761345193181404908111317 111594027965189177533859)
                ·
                  rfl

theorem cell20_733484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 7].length) (baseStart_733484 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_733484 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_733484 prefixEnd_733484 := by exact prefixLift 733484
  have htrace : WordTrace (prefixWord ++ tailWord_733484) baseStart_733484 baseEnd_733484 := by
    simpa [prefixWord, tailWord_733484, baseEnd_733484] using wordTrace_append hprefix tailTrace_733484
  have hstable : (prefixWord ++ tailWord_733484).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733484).length < 2 ^ (prefixWord ++ tailWord_733484).sum := by decide
  have hdescent : baseEnd_733484 < baseStart_733484 := by decide
  rcases family_descends (prefixWord ++ tailWord_733484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733487 : List Nat := [1, 1, 2, 1, 2, 1, 8, 1, 3]
def baseStart_733487 : Nat := 118140960795 + 733487 * 2 ^ 59
def prefixEnd_733487 : Nat := 4983230072969 + 3 ^ 40 * 733487 * 2
def baseEnd_733487 : Nat := 334783453177312855501565

theorem tailTrace_733487 : CollatzResearch.WordTrace tailWord_733487 prefixEnd_733487 334783453177312855501565 := by
  unfold tailWord_733487
  simp only [CollatzResearch.WordTrace]
  refine ⟨26752468693709343451486715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17834979129139562300991143 26752468693709343451486715)
  ·
    refine ⟨40128703040564015177230073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26752468693709343451486715 40128703040564015177230073)
    ·
      refine ⟨30096527280423011382922555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40128703040564015177230073 30096527280423011382922555)
      ·
        refine ⟨45144790920634517074383833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30096527280423011382922555 45144790920634517074383833)
        ·
          refine ⟨33858593190475887805787875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45144790920634517074383833 33858593190475887805787875)
          ·
            refine ⟨50787889785713831708681813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33858593190475887805787875 50787889785713831708681813)
            ·
              refine ⟨595170583426333965336115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 50787889785713831708681813 595170583426333965336115)
              ·
                refine ⟨892755875139500948004173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 595170583426333965336115 892755875139500948004173)
                ·
                  refine ⟨334783453177312855501565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 892755875139500948004173 334783453177312855501565)
                  ·
                    rfl

theorem cell20_733487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 8, 1, 3].length) (baseStart_733487 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_733487 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_733487 prefixEnd_733487 := by exact prefixLift 733487
  have htrace : WordTrace (prefixWord ++ tailWord_733487) baseStart_733487 baseEnd_733487 := by
    simpa [prefixWord, tailWord_733487, baseEnd_733487] using wordTrace_append hprefix tailTrace_733487
  have hstable : (prefixWord ++ tailWord_733487).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733487).length < 2 ^ (prefixWord ++ tailWord_733487).sum := by decide
  have hdescent : baseEnd_733487 < baseStart_733487 := by decide
  rcases family_descends (prefixWord ++ tailWord_733487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733567 : List Nat := [1, 1, 2, 2, 1, 1, 2, 3, 7]
def baseStart_733567 : Nat := 118140960795 + 733567 * 2 ^ 59
def prefixEnd_733567 : Nat := 4983230072969 + 3 ^ 40 * 733567 * 2
def baseEnd_733567 : Nat := 334819967357188132834571

theorem tailTrace_733567 : CollatzResearch.WordTrace tailWord_733567 prefixEnd_733567 334819967357188132834571 := by
  unfold tailWord_733567
  simp only [CollatzResearch.WordTrace]
  refine ⟨26755386533419517114398955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17836924355613011409599303 26755386533419517114398955)
  ·
    refine ⟨40133079800129275671598433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26755386533419517114398955 40133079800129275671598433)
    ·
      refine ⟨30099809850096956753698825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40133079800129275671598433 30099809850096956753698825)
      ·
        refine ⟨22574857387572717565274119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30099809850096956753698825 22574857387572717565274119)
        ·
          refine ⟨33862286081359076347911179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22574857387572717565274119 33862286081359076347911179)
          ·
            refine ⟨50793429122038614521866769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33862286081359076347911179 50793429122038614521866769)
            ·
              refine ⟨38095071841528960891400077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50793429122038614521866769 38095071841528960891400077)
              ·
                refine ⟨14285651940573360334275029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38095071841528960891400077 14285651940573360334275029)
                ·
                  refine ⟨334819967357188132834571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14285651940573360334275029 334819967357188132834571)
                  ·
                    rfl

theorem cell20_733567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 7].length) (baseStart_733567 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_733567 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_733567 prefixEnd_733567 := by exact prefixLift 733567
  have htrace : WordTrace (prefixWord ++ tailWord_733567) baseStart_733567 baseEnd_733567 := by
    simpa [prefixWord, tailWord_733567, baseEnd_733567] using wordTrace_append hprefix tailTrace_733567
  have hstable : (prefixWord ++ tailWord_733567).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733567).length < 2 ^ (prefixWord ++ tailWord_733567).sum := by decide
  have hdescent : baseEnd_733567 < baseStart_733567 := by decide
  rcases family_descends (prefixWord ++ tailWord_733567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733591 : List Nat := [1, 1, 3, 3, 1, 1, 3, 3, 4]
def baseStart_733591 : Nat := 118140960795 + 733591 * 2 ^ 59
def prefixEnd_733591 : Nat := 4983230072969 + 3 ^ 40 * 733591 * 2
def baseEnd_733591 : Nat := 334830921611150716034473

theorem tailTrace_733591 : CollatzResearch.WordTrace tailWord_733591 prefixEnd_733591 334830921611150716034473 := by
  unfold tailWord_733591
  simp only [CollatzResearch.WordTrace]
  refine ⟨26756261885332569213272627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17837507923555046142181751 26756261885332569213272627)
  ·
    refine ⟨40134392827998853819908941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26756261885332569213272627 40134392827998853819908941)
    ·
      refine ⟨15050397310499570182465853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40134392827998853819908941 15050397310499570182465853)
      ·
        refine ⟨5643898991437338818424695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15050397310499570182465853 5643898991437338818424695)
        ·
          refine ⟨8465848487156008227637043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5643898991437338818424695 8465848487156008227637043)
          ·
            refine ⟨12698772730734012341455565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8465848487156008227637043 12698772730734012341455565)
            ·
              refine ⟨4762039774025254628045837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12698772730734012341455565 4762039774025254628045837)
              ·
                refine ⟨1785764915259470485517189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4762039774025254628045837 1785764915259470485517189)
                ·
                  refine ⟨334830921611150716034473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1785764915259470485517189 334830921611150716034473)
                  ·
                    rfl

theorem cell20_733591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 3, 4].length) (baseStart_733591 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_733591 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_733591 prefixEnd_733591 := by exact prefixLift 733591
  have htrace : WordTrace (prefixWord ++ tailWord_733591) baseStart_733591 baseEnd_733591 := by
    simpa [prefixWord, tailWord_733591, baseEnd_733591] using wordTrace_append hprefix tailTrace_733591
  have hstable : (prefixWord ++ tailWord_733591).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733591).length < 2 ^ (prefixWord ++ tailWord_733591).sum := by decide
  have hdescent : baseEnd_733591 < baseStart_733591 := by decide
  rcases family_descends (prefixWord ++ tailWord_733591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733621 : List Nat := [1, 3, 3, 2, 4, 1, 1, 3, 2]
def baseStart_733621 : Nat := 118140960795 + 733621 * 2 ^ 59
def prefixEnd_733621 : Nat := 4983230072969 + 3 ^ 40 * 733621 * 2
def baseEnd_733621 : Nat := 334844614428603945034351

theorem tailTrace_733621 : CollatzResearch.WordTrace tailWord_733621 prefixEnd_733621 334844614428603945034351 := by
  unfold tailWord_733621
  simp only [CollatzResearch.WordTrace]
  refine ⟨26757356075223884336864717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17838237383482589557909811 26757356075223884336864717)
  ·
    refine ⟨10034008528208956626324269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26757356075223884336864717 10034008528208956626324269)
    ·
      refine ⟨3762753198078358734871601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10034008528208956626324269 3762753198078358734871601)
      ·
        refine ⟨2822064898558769051153701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3762753198078358734871601 2822064898558769051153701)
        ·
          refine ⟨529137168479769197091319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2822064898558769051153701 529137168479769197091319)
          ·
            refine ⟨793705752719653795636979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 529137168479769197091319 793705752719653795636979)
            ·
              refine ⟨1190558629079480693455469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 793705752719653795636979 1190558629079480693455469)
              ·
                refine ⟨446459485904805260045801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1190558629079480693455469 446459485904805260045801)
                ·
                  refine ⟨334844614428603945034351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 446459485904805260045801 334844614428603945034351)
                  ·
                    rfl

theorem cell20_733621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 3, 2].length) (baseStart_733621 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_733621 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_733621 prefixEnd_733621 := by exact prefixLift 733621
  have htrace : WordTrace (prefixWord ++ tailWord_733621) baseStart_733621 baseEnd_733621 := by
    simpa [prefixWord, tailWord_733621, baseEnd_733621] using wordTrace_append hprefix tailTrace_733621
  have hstable : (prefixWord ++ tailWord_733621).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733621).length < 2 ^ (prefixWord ++ tailWord_733621).sum := by decide
  have hdescent : baseEnd_733621 < baseStart_733621 := by decide
  rcases family_descends (prefixWord ++ tailWord_733621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733625 : List Nat := [1, 2, 1, 4, 3, 1, 3, 3, 2]
def baseStart_733625 : Nat := 118140960795 + 733625 * 2 ^ 59
def prefixEnd_733625 : Nat := 4983230072969 + 3 ^ 40 * 733625 * 2
def baseEnd_733625 : Nat := 334846440137597708901001

theorem tailTrace_733625 : CollatzResearch.WordTrace tailWord_733625 prefixEnd_733625 334846440137597708901001 := by
  unfold tailWord_733625
  simp only [CollatzResearch.WordTrace]
  refine ⟨26757501967209393020010329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17838334644806262013340219 26757501967209393020010329)
  ·
    refine ⟨20068126475407044765007747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26757501967209393020010329 20068126475407044765007747)
    ·
      refine ⟨30102189713110567147511621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20068126475407044765007747 30102189713110567147511621)
      ·
        refine ⟨5644160571208231340158429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30102189713110567147511621 5644160571208231340158429)
        ·
          refine ⟨2116560214203086752559411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5644160571208231340158429 2116560214203086752559411)
          ·
            refine ⟨3174840321304630128839117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2116560214203086752559411 3174840321304630128839117)
            ·
              refine ⟨1190565120489236298314669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3174840321304630128839117 1190565120489236298314669)
              ·
                refine ⟨446461920183463611868001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1190565120489236298314669 446461920183463611868001)
                ·
                  refine ⟨334846440137597708901001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 446461920183463611868001 334846440137597708901001)
                  ·
                    rfl

theorem cell20_733625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 3, 2].length) (baseStart_733625 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_733625 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_733625 prefixEnd_733625 := by exact prefixLift 733625
  have htrace : WordTrace (prefixWord ++ tailWord_733625) baseStart_733625 baseEnd_733625 := by
    simpa [prefixWord, tailWord_733625, baseEnd_733625] using wordTrace_append hprefix tailTrace_733625
  have hstable : (prefixWord ++ tailWord_733625).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733625).length < 2 ^ (prefixWord ++ tailWord_733625).sum := by decide
  have hdescent : baseEnd_733625 < baseStart_733625 := by decide
  rcases family_descends (prefixWord ++ tailWord_733625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733653 : List Nat := [1, 3, 2, 3, 1, 3, 2, 5]
def baseStart_733653 : Nat := 118140960795 + 733653 * 2 ^ 59
def prefixEnd_733653 : Nat := 4983230072969 + 3 ^ 40 * 733653 * 2
def baseEnd_733653 : Nat := 111619740033518018655851

theorem tailTrace_733653 : CollatzResearch.WordTrace tailWord_733653 prefixEnd_733653 111619740033518018655851 := by
  unfold tailWord_733653
  simp only [CollatzResearch.WordTrace]
  refine ⟨26758523211107953802029613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17839015474071969201353075 26758523211107953802029613)
  ·
    refine ⟨10034446204165482675761105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26758523211107953802029613 10034446204165482675761105)
    ·
      refine ⟨7525834653124112006820829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10034446204165482675761105 7525834653124112006820829)
      ·
        refine ⟨2822187994921542002557811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7525834653124112006820829 2822187994921542002557811)
        ·
          refine ⟨4233281992382313003836717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2822187994921542002557811 4233281992382313003836717)
          ·
            refine ⟨1587480747143367376438769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4233281992382313003836717 1587480747143367376438769)
            ·
              refine ⟨1190610560357525532329077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1587480747143367376438769 1190610560357525532329077)
              ·
                refine ⟨111619740033518018655851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1190610560357525532329077 111619740033518018655851)
                ·
                  rfl

theorem cell20_733653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 5].length) (baseStart_733653 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_733653 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_733653 prefixEnd_733653 := by exact prefixLift 733653
  have htrace : WordTrace (prefixWord ++ tailWord_733653) baseStart_733653 baseEnd_733653 := by
    simpa [prefixWord, tailWord_733653, baseEnd_733653] using wordTrace_append hprefix tailTrace_733653
  have hstable : (prefixWord ++ tailWord_733653).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733653).length < 2 ^ (prefixWord ++ tailWord_733653).sum := by decide
  have hdescent : baseEnd_733653 < baseStart_733653 := by decide
  rcases family_descends (prefixWord ++ tailWord_733653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733701 : List Nat := [1, 3, 1, 1, 2, 2, 6, 2, 2]
def baseStart_733701 : Nat := 118140960795 + 733701 * 2 ^ 59
def prefixEnd_733701 : Nat := 4983230072969 + 3 ^ 40 * 733701 * 2
def baseEnd_733701 : Nat := 334881128608479222367357

theorem tailTrace_733701 : CollatzResearch.WordTrace tailWord_733701 prefixEnd_733701 334881128608479222367357 := by
  unfold tailWord_733701
  simp only [CollatzResearch.WordTrace]
  refine ⟨26760273914934057999776957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17840182609956038666517971 26760273914934057999776957)
  ·
    refine ⟨10035102718100271749916359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26760273914934057999776957 10035102718100271749916359)
    ·
      refine ⟨15052654077150407624874539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10035102718100271749916359 15052654077150407624874539)
      ·
        refine ⟨22578981115725611437311809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15052654077150407624874539 22578981115725611437311809)
        ·
          refine ⟨16934235836794208577983857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22578981115725611437311809 16934235836794208577983857)
          ·
            refine ⟨12700676877595656433487893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16934235836794208577983857 12700676877595656433487893)
            ·
              refine ⟨595344228637296395319745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12700676877595656433487893 595344228637296395319745)
              ·
                refine ⟨446508171477972296489809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 595344228637296395319745 446508171477972296489809)
                ·
                  refine ⟨334881128608479222367357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 446508171477972296489809 334881128608479222367357)
                  ·
                    rfl

theorem cell20_733701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 6, 2, 2].length) (baseStart_733701 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_733701 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_733701 prefixEnd_733701 := by exact prefixLift 733701
  have htrace : WordTrace (prefixWord ++ tailWord_733701) baseStart_733701 baseEnd_733701 := by
    simpa [prefixWord, tailWord_733701, baseEnd_733701] using wordTrace_append hprefix tailTrace_733701
  have hstable : (prefixWord ++ tailWord_733701).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733701).length < 2 ^ (prefixWord ++ tailWord_733701).sum := by decide
  have hdescent : baseEnd_733701 < baseStart_733701 := by decide
  rcases family_descends (prefixWord ++ tailWord_733701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733729 : List Nat := [1, 2, 3, 2, 2, 1, 5, 4]
def baseStart_733729 : Nat := 118140960795 + 733729 * 2 ^ 59
def prefixEnd_733729 : Nat := 4983230072969 + 3 ^ 40 * 733729 * 2
def baseEnd_733729 : Nat := 111631302857145189811303

theorem tailTrace_733729 : CollatzResearch.WordTrace tailWord_733729 prefixEnd_733729 111631302857145189811303 := by
  unfold tailWord_733729
  simp only [CollatzResearch.WordTrace]
  refine ⟨26761295158832618781796241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17840863439221745854530827 26761295158832618781796241)
  ·
    refine ⟨20070971369124464086347181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26761295158832618781796241 20070971369124464086347181)
    ·
      refine ⟨7526614263421674032380193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20070971369124464086347181 7526614263421674032380193)
      ·
        refine ⟨5644960697566255524285145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7526614263421674032380193 5644960697566255524285145)
        ·
          refine ⟨4233720523174691643213859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5644960697566255524285145 4233720523174691643213859)
          ·
            refine ⟨6350580784762037464820789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4233720523174691643213859 6350580784762037464820789)
            ·
              refine ⟨595366948571441012326949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6350580784762037464820789 595366948571441012326949)
              ·
                refine ⟨111631302857145189811303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 595366948571441012326949 111631302857145189811303)
                ·
                  rfl

theorem cell20_733729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 5, 4].length) (baseStart_733729 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_733729 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_733729 prefixEnd_733729 := by exact prefixLift 733729
  have htrace : WordTrace (prefixWord ++ tailWord_733729) baseStart_733729 baseEnd_733729 := by
    simpa [prefixWord, tailWord_733729, baseEnd_733729] using wordTrace_append hprefix tailTrace_733729
  have hstable : (prefixWord ++ tailWord_733729).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733729).length < 2 ^ (prefixWord ++ tailWord_733729).sum := by decide
  have hdescent : baseEnd_733729 < baseStart_733729 := by decide
  rcases family_descends (prefixWord ++ tailWord_733729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733735 : List Nat := [1, 1, 7, 2, 1, 1, 2, 3, 2]
def baseStart_733735 : Nat := 118140960795 + 733735 * 2 ^ 59
def prefixEnd_733735 : Nat := 4983230072969 + 3 ^ 40 * 733735 * 2
def baseEnd_733735 : Nat := 334896647134926215233885

theorem tailTrace_733735 : CollatzResearch.WordTrace tailWord_733735 prefixEnd_733735 334896647134926215233885 := by
  unfold tailWord_733735
  simp only [CollatzResearch.WordTrace]
  refine ⟨26761513996810881806514659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17841009331207254537676439 26761513996810881806514659)
  ·
    refine ⟨40142270995216322709771989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26761513996810881806514659 40142270995216322709771989)
    ·
      refine ⟨940834476450382563510281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 40142270995216322709771989 940834476450382563510281)
      ·
        refine ⟨705625857337786922632711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 940834476450382563510281 705625857337786922632711)
        ·
          refine ⟨1058438786006680383949067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 705625857337786922632711 1058438786006680383949067)
          ·
            refine ⟨1587658179010020575923601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1058438786006680383949067 1587658179010020575923601)
            ·
              refine ⟨1190743634257515431942701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1587658179010020575923601 1190743634257515431942701)
              ·
                refine ⟨446528862846568286978513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1190743634257515431942701 446528862846568286978513)
                ·
                  refine ⟨334896647134926215233885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 446528862846568286978513 334896647134926215233885)
                  ·
                    rfl

theorem cell20_733735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 3, 2].length) (baseStart_733735 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_733735 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_733735 prefixEnd_733735 := by exact prefixLift 733735
  have htrace : WordTrace (prefixWord ++ tailWord_733735) baseStart_733735 baseEnd_733735 := by
    simpa [prefixWord, tailWord_733735, baseEnd_733735] using wordTrace_append hprefix tailTrace_733735
  have hstable : (prefixWord ++ tailWord_733735).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733735).length < 2 ^ (prefixWord ++ tailWord_733735).sum := by decide
  have hdescent : baseEnd_733735 < baseStart_733735 := by decide
  rcases family_descends (prefixWord ++ tailWord_733735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733760 : List Nat := [2, 1, 1, 2, 2, 2, 4, 4, 2]
def baseStart_733760 : Nat := 118140960795 + 733760 * 2 ^ 59
def prefixEnd_733760 : Nat := 4983230072969 + 3 ^ 40 * 733760 * 2
def baseEnd_733760 : Nat := 334908057816137239400449

theorem tailTrace_733760 : CollatzResearch.WordTrace tailWord_733760 prefixEnd_733760 334908057816137239400449 := by
  unfold tailWord_733760
  simp only [CollatzResearch.WordTrace]
  refine ⟨13381212910860155538087367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17841617214480207384116489 13381212910860155538087367)
  ·
    refine ⟨20071819366290233307131051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13381212910860155538087367 20071819366290233307131051)
    ·
      refine ⟨30107729049435349960696577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20071819366290233307131051 30107729049435349960696577)
      ·
        refine ⟨22580796787076512470522433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30107729049435349960696577 22580796787076512470522433)
        ·
          refine ⟨16935597590307384352891825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22580796787076512470522433 16935597590307384352891825)
          ·
            refine ⟨12701698192730538264668869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16935597590307384352891825 12701698192730538264668869)
            ·
              refine ⟨2381568411136975924625413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12701698192730538264668869 2381568411136975924625413)
              ·
                refine ⟨446544077088182985867265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2381568411136975924625413 446544077088182985867265)
                ·
                  refine ⟨334908057816137239400449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 446544077088182985867265 334908057816137239400449)
                  ·
                    rfl

theorem cell20_733760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 4, 2].length) (baseStart_733760 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_733760 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_733760 prefixEnd_733760 := by exact prefixLift 733760
  have htrace : WordTrace (prefixWord ++ tailWord_733760) baseStart_733760 baseEnd_733760 := by
    simpa [prefixWord, tailWord_733760, baseEnd_733760] using wordTrace_append hprefix tailTrace_733760
  have hstable : (prefixWord ++ tailWord_733760).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733760).length < 2 ^ (prefixWord ++ tailWord_733760).sum := by decide
  have hdescent : baseEnd_733760 < baseStart_733760 := by decide
  rcases family_descends (prefixWord ++ tailWord_733760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733774 : List Nat := [4, 1, 1, 1, 1, 2, 2, 5, 3]
def baseStart_733774 : Nat := 118140960795 + 733774 * 2 ^ 59
def prefixEnd_733774 : Nat := 4983230072969 + 3 ^ 40 * 733774 * 2
def baseEnd_733774 : Nat := 334914447797615412933725

theorem tailTrace_733774 : CollatzResearch.WordTrace tailWord_733774 prefixEnd_733774 334914447797615412933725 := by
  unfold tailWord_733774
  simp only [CollatzResearch.WordTrace]
  refine ⟨3345367055458698933398047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17841957629113060978122917 3345367055458698933398047)
  ·
    refine ⟨5018050583188048400097071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3345367055458698933398047 5018050583188048400097071)
    ·
      refine ⟨7527075874782072600145607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5018050583188048400097071 7527075874782072600145607)
      ·
        refine ⟨11290613812173108900218411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7527075874782072600145607 11290613812173108900218411)
        ·
          refine ⟨16935920718259663350327617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11290613812173108900218411 16935920718259663350327617)
          ·
            refine ⟨12701940538694747512745713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16935920718259663350327617 12701940538694747512745713)
            ·
              refine ⟨9526455404021060634559285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12701940538694747512745713 9526455404021060634559285)
              ·
                refine ⟨893105194126974434489933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9526455404021060634559285 893105194126974434489933)
                ·
                  refine ⟨334914447797615412933725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 893105194126974434489933 334914447797615412933725)
                  ·
                    rfl

theorem cell20_733774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 5, 3].length) (baseStart_733774 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_733774 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_733774 prefixEnd_733774 := by exact prefixLift 733774
  have htrace : WordTrace (prefixWord ++ tailWord_733774) baseStart_733774 baseEnd_733774 := by
    simpa [prefixWord, tailWord_733774, baseEnd_733774] using wordTrace_append hprefix tailTrace_733774
  have hstable : (prefixWord ++ tailWord_733774).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733774).length < 2 ^ (prefixWord ++ tailWord_733774).sum := by decide
  have hdescent : baseEnd_733774 < baseStart_733774 := by decide
  rcases family_descends (prefixWord ++ tailWord_733774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733781 : List Nat := [1, 3, 2, 2, 1, 1, 4, 2, 4]
def baseStart_733781 : Nat := 118140960795 + 733781 * 2 ^ 59
def prefixEnd_733781 : Nat := 4983230072969 + 3 ^ 40 * 733781 * 2
def baseEnd_733781 : Nat := 334917642788354499700363

theorem tailTrace_733781 : CollatzResearch.WordTrace tailWord_733781 prefixEnd_733781 334917642788354499700363 := by
  unfold tailWord_733781
  simp only [CollatzResearch.WordTrace]
  refine ⟨26763191754644231662689197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17842127836429487775126131 26763191754644231662689197)
  ·
    refine ⟨10036196907991586873508449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26763191754644231662689197 10036196907991586873508449)
    ·
      refine ⟨7527147680993690155131337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10036196907991586873508449 7527147680993690155131337)
      ·
        refine ⟨5645360760745267616348503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7527147680993690155131337 5645360760745267616348503)
        ·
          refine ⟨8468041141117901424522755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5645360760745267616348503 8468041141117901424522755)
          ·
            refine ⟨12702061711676852136784133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8468041141117901424522755 12702061711676852136784133)
            ·
              refine ⟨2381636570939409775647025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12702061711676852136784133 2381636570939409775647025)
              ·
                refine ⟨1786227428204557331735269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2381636570939409775647025 1786227428204557331735269)
                ·
                  refine ⟨334917642788354499700363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1786227428204557331735269 334917642788354499700363)
                  ·
                    rfl

theorem cell20_733781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 2, 4].length) (baseStart_733781 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_733781 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_733781 prefixEnd_733781 := by exact prefixLift 733781
  have htrace : WordTrace (prefixWord ++ tailWord_733781) baseStart_733781 baseEnd_733781 := by
    simpa [prefixWord, tailWord_733781, baseEnd_733781] using wordTrace_append hprefix tailTrace_733781
  have hstable : (prefixWord ++ tailWord_733781).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733781).length < 2 ^ (prefixWord ++ tailWord_733781).sum := by decide
  have hdescent : baseEnd_733781 < baseStart_733781 := by decide
  rcases family_descends (prefixWord ++ tailWord_733781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733795 : List Nat := [1, 1, 1, 5, 1, 2, 1, 1, 7]
def baseStart_733795 : Nat := 118140960795 + 733795 * 2 ^ 59
def prefixEnd_733795 : Nat := 4983230072969 + 3 ^ 40 * 733795 * 2
def baseEnd_733795 : Nat := 334924032769832673233639

theorem tailTrace_733795 : CollatzResearch.WordTrace tailWord_733795 prefixEnd_733795 334924032769832673233639 := by
  unfold tailWord_733795
  simp only [CollatzResearch.WordTrace]
  refine ⟨26763702376593512053698839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17842468251062341369132559 26763702376593512053698839)
  ·
    refine ⟨40145553564890268080548259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26763702376593512053698839 40145553564890268080548259)
    ·
      refine ⟨60218330347335402120822389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40145553564890268080548259 60218330347335402120822389)
      ·
        refine ⟨5645468470062693948827099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60218330347335402120822389 5645468470062693948827099)
        ·
          refine ⟨8468202705094040923240649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5645468470062693948827099 8468202705094040923240649)
          ·
            refine ⟨6351152028820530692430487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8468202705094040923240649 6351152028820530692430487)
            ·
              refine ⟨9526728043230796038645731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6351152028820530692430487 9526728043230796038645731)
              ·
                refine ⟨14290092064846194057968597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9526728043230796038645731 14290092064846194057968597)
                ·
                  refine ⟨334924032769832673233639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14290092064846194057968597 334924032769832673233639)
                  ·
                    rfl

theorem cell20_733795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 7].length) (baseStart_733795 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_733795 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_733795 prefixEnd_733795 := by exact prefixLift 733795
  have htrace : WordTrace (prefixWord ++ tailWord_733795) baseStart_733795 baseEnd_733795 := by
    simpa [prefixWord, tailWord_733795, baseEnd_733795] using wordTrace_append hprefix tailTrace_733795
  have hstable : (prefixWord ++ tailWord_733795).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733795).length < 2 ^ (prefixWord ++ tailWord_733795).sum := by decide
  have hdescent : baseEnd_733795 < baseStart_733795 := by decide
  rcases family_descends (prefixWord ++ tailWord_733795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733805 : List Nat := [1, 5, 1, 1, 3, 3, 6]
def baseStart_733805 : Nat := 118140960795 + 733805 * 2 ^ 59
def prefixEnd_733805 : Nat := 4983230072969 + 3 ^ 40 * 733805 * 2
def baseEnd_733805 : Nat := 37214288560257453655585

theorem tailTrace_733805 : CollatzResearch.WordTrace tailWord_733805 prefixEnd_733805 37214288560257453655585 := by
  unfold tailWord_733805
  simp only [CollatzResearch.WordTrace]
  refine ⟨26764067106557283761562869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17842711404371522507708579 26764067106557283761562869)
  ·
    refine ⟨2509131291239745352646519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26764067106557283761562869 2509131291239745352646519)
    ·
      refine ⟨3763696936859618028969779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2509131291239745352646519 3763696936859618028969779)
      ·
        refine ⟨5645545405289427043454669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3763696936859618028969779 5645545405289427043454669)
        ·
          refine ⟨2117079526983535141295501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5645545405289427043454669 2117079526983535141295501)
          ·
            refine ⟨793904822618825677985813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2117079526983535141295501 793904822618825677985813)
            ·
              refine ⟨37214288560257453655585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 793904822618825677985813 37214288560257453655585)
              ·
                rfl

theorem cell20_733805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 6].length) (baseStart_733805 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_733805 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_733805 prefixEnd_733805 := by exact prefixLift 733805
  have htrace : WordTrace (prefixWord ++ tailWord_733805) baseStart_733805 baseEnd_733805 := by
    simpa [prefixWord, tailWord_733805, baseEnd_733805] using wordTrace_append hprefix tailTrace_733805
  have hstable : (prefixWord ++ tailWord_733805).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733805).length < 2 ^ (prefixWord ++ tailWord_733805).sum := by decide
  have hdescent : baseEnd_733805 < baseStart_733805 := by decide
  rcases family_descends (prefixWord ++ tailWord_733805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733829 : List Nat := [1, 3, 1, 1, 4, 2, 4, 1, 3]
def baseStart_733829 : Nat := 118140960795 + 733829 * 2 ^ 59
def prefixEnd_733829 : Nat := 4983230072969 + 3 ^ 40 * 733829 * 2
def baseEnd_733829 : Nat := 334939551296279666100167

theorem tailTrace_733829 : CollatzResearch.WordTrace tailWord_733829 prefixEnd_733829 334939551296279666100167 := by
  unfold tailWord_733829
  simp only [CollatzResearch.WordTrace]
  refine ⟨26764942458470335860436541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17843294972313557240291027 26764942458470335860436541)
  ·
    refine ⟨10036853421926375947663703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26764942458470335860436541 10036853421926375947663703)
    ·
      refine ⟨15055280132889563921495555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10036853421926375947663703 15055280132889563921495555)
      ·
        refine ⟨22582920199334345882243333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15055280132889563921495555 22582920199334345882243333)
        ·
          refine ⟨4234297537375189852920625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22582920199334345882243333 4234297537375189852920625)
          ·
            refine ⟨3175723153031392389690469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4234297537375189852920625 3175723153031392389690469)
            ·
              refine ⟨595448091193386073066963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3175723153031392389690469 595448091193386073066963)
              ·
                refine ⟨893172136790079109600445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 595448091193386073066963 893172136790079109600445)
                ·
                  refine ⟨334939551296279666100167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 893172136790079109600445 334939551296279666100167)
                  ·
                    rfl

theorem cell20_733829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 4, 1, 3].length) (baseStart_733829 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_733829 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_733829 prefixEnd_733829 := by exact prefixLift 733829
  have htrace : WordTrace (prefixWord ++ tailWord_733829) baseStart_733829 baseEnd_733829 := by
    simpa [prefixWord, tailWord_733829, baseEnd_733829] using wordTrace_append hprefix tailTrace_733829
  have hstable : (prefixWord ++ tailWord_733829).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733829).length < 2 ^ (prefixWord ++ tailWord_733829).sum := by decide
  have hdescent : baseEnd_733829 < baseStart_733829 := by decide
  rcases family_descends (prefixWord ++ tailWord_733829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733866 : List Nat := [3, 1, 5, 2, 1, 2, 2, 2, 2]
def baseStart_733866 : Nat := 118140960795 + 733866 * 2 ^ 59
def prefixEnd_733866 : Nat := 4983230072969 + 3 ^ 40 * 733866 * 2
def baseEnd_733866 : Nat := 334956439104471981866683

theorem tailTrace_733866 : CollatzResearch.WordTrace tailWord_733866 prefixEnd_733866 334956439104471981866683 := by
  unfold tailWord_733866
  simp only [CollatzResearch.WordTrace]
  refine ⟨6691572989834072794883363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17844194639557527453022301 6691572989834072794883363)
  ·
    refine ⟨10037359484751109192325045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6691572989834072794883363 10037359484751109192325045)
    ·
      refine ⟨941002451695416486780473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10037359484751109192325045 941002451695416486780473)
      ·
        refine ⟨705751838771562365085355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 941002451695416486780473 705751838771562365085355)
        ·
          refine ⟨1058627758157343547628033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 705751838771562365085355 1058627758157343547628033)
          ·
            refine ⟨793970818618007660721025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1058627758157343547628033 793970818618007660721025)
            ·
              refine ⟨595478113963505745540769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 793970818618007660721025 595478113963505745540769)
              ·
                refine ⟨446608585472629309155577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 595478113963505745540769 446608585472629309155577)
                ·
                  refine ⟨334956439104471981866683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 446608585472629309155577 334956439104471981866683)
                  ·
                    rfl

theorem cell20_733866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 2, 2, 2].length) (baseStart_733866 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_733866 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_733866 prefixEnd_733866 := by exact prefixLift 733866
  have htrace : WordTrace (prefixWord ++ tailWord_733866) baseStart_733866 baseEnd_733866 := by
    simpa [prefixWord, tailWord_733866, baseEnd_733866] using wordTrace_append hprefix tailTrace_733866
  have hstable : (prefixWord ++ tailWord_733866).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733866).length < 2 ^ (prefixWord ++ tailWord_733866).sum := by decide
  have hdescent : baseEnd_733866 < baseStart_733866 := by decide
  rcases family_descends (prefixWord ++ tailWord_733866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733870 : List Nat := [4, 1, 4, 1, 1, 2, 1, 4, 2]
def baseStart_733870 : Nat := 118140960795 + 733870 * 2 ^ 59
def prefixEnd_733870 : Nat := 4983230072969 + 3 ^ 40 * 733870 * 2
def baseEnd_733870 : Nat := 334958264813465745733333

theorem tailTrace_733870 : CollatzResearch.WordTrace tailWord_733870 prefixEnd_733870 334958264813465745733333 := by
  unfold tailWord_733870
  simp only [CollatzResearch.WordTrace]
  refine ⟨3345804731415224982834883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17844291900881199908452709 3345804731415224982834883)
  ·
    refine ⟨5018707097122837474252325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3345804731415224982834883 5018707097122837474252325)
    ·
      refine ⟨941007580710532026422311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5018707097122837474252325 941007580710532026422311)
      ·
        refine ⟨1411511371065798039633467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 941007580710532026422311 1411511371065798039633467)
        ·
          refine ⟨2117267056598697059450201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1411511371065798039633467 2117267056598697059450201)
          ·
            refine ⟨1587950292449022794587651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2117267056598697059450201 1587950292449022794587651)
            ·
              refine ⟨2381925438673534191881477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1587950292449022794587651 2381925438673534191881477)
              ·
                refine ⟨446611019751287660977777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2381925438673534191881477 446611019751287660977777)
                ·
                  refine ⟨334958264813465745733333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 446611019751287660977777 334958264813465745733333)
                  ·
                    rfl

theorem cell20_733870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 4, 2].length) (baseStart_733870 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_733870 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_733870 prefixEnd_733870 := by exact prefixLift 733870
  have htrace : WordTrace (prefixWord ++ tailWord_733870) baseStart_733870 baseEnd_733870 := by
    simpa [prefixWord, tailWord_733870, baseEnd_733870] using wordTrace_append hprefix tailTrace_733870
  have hstable : (prefixWord ++ tailWord_733870).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733870).length < 2 ^ (prefixWord ++ tailWord_733870).sum := by decide
  have hdescent : baseEnd_733870 < baseStart_733870 := by decide
  rcases family_descends (prefixWord ++ tailWord_733870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733888 : List Nat := [2, 1, 1, 2, 4, 2, 2, 3, 3]
def baseStart_733888 : Nat := 118140960795 + 733888 * 2 ^ 59
def prefixEnd_733888 : Nat := 4983230072969 + 3 ^ 40 * 733888 * 2
def baseEnd_733888 : Nat := 334966480503937683133259

theorem tailTrace_733888 : CollatzResearch.WordTrace tailWord_733888 prefixEnd_733888 334966480503937683133259 := by
  unfold tailWord_733888
  simp only [CollatzResearch.WordTrace]
  refine ⟨13383547182628294468417159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17844729576837725957889545 13383547182628294468417159)
  ·
    refine ⟨20075320773942441702625739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13383547182628294468417159 20075320773942441702625739)
    ·
      refine ⟨30112981160913662553938609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20075320773942441702625739 30112981160913662553938609)
      ·
        refine ⟨22584735870685246915453957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30112981160913662553938609 22584735870685246915453957)
        ·
          refine ⟨4234637975753483796647617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22584735870685246915453957 4234637975753483796647617)
          ·
            refine ⟨3175978481815112847485713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4234637975753483796647617 3175978481815112847485713)
            ·
              refine ⟨2381983861361334635614285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3175978481815112847485713 2381983861361334635614285)
              ·
                refine ⟨893243948010500488355357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2381983861361334635614285 893243948010500488355357)
                ·
                  refine ⟨334966480503937683133259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 893243948010500488355357 334966480503937683133259)
                  ·
                    rfl

theorem cell20_733888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 3, 3].length) (baseStart_733888 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_733888 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_733888 prefixEnd_733888 := by exact prefixLift 733888
  have htrace : WordTrace (prefixWord ++ tailWord_733888) baseStart_733888 baseEnd_733888 := by
    simpa [prefixWord, tailWord_733888, baseEnd_733888] using wordTrace_append hprefix tailTrace_733888
  have hstable : (prefixWord ++ tailWord_733888).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733888).length < 2 ^ (prefixWord ++ tailWord_733888).sum := by decide
  have hdescent : baseEnd_733888 < baseStart_733888 := by decide
  rcases family_descends (prefixWord ++ tailWord_733888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733894 : List Nat := [6, 1, 2, 1, 2, 1, 3, 4]
def baseStart_733894 : Nat := 118140960795 + 733894 * 2 ^ 59
def prefixEnd_733894 : Nat := 4983230072969 + 3 ^ 40 * 733894 * 2
def baseEnd_733894 : Nat := 111656406355809442977745

theorem tailTrace_733894 : CollatzResearch.WordTrace tailWord_733894 prefixEnd_733894 111656406355809442977745 := by
  unfold tailWord_733894
  simp only [CollatzResearch.WordTrace]
  refine ⟨836478537601089123798523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 17844875468823234641035157 836478537601089123798523)
  ·
    refine ⟨1254717806401633685697785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 836478537601089123798523 1254717806401633685697785)
    ·
      refine ⟨941038354801225264273339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1254717806401633685697785 941038354801225264273339)
      ·
        refine ⟨1411557532201837896410009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 941038354801225264273339 1411557532201837896410009)
        ·
          refine ⟨1058668149151378422307507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1411557532201837896410009 1058668149151378422307507)
          ·
            refine ⟨1588002223727067633461261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1058668149151378422307507 1588002223727067633461261)
            ·
              refine ⟨595500833897650362547973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1588002223727067633461261 595500833897650362547973)
              ·
                refine ⟨111656406355809442977745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 595500833897650362547973 111656406355809442977745)
                ·
                  rfl

theorem cell20_733894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_733894 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_733894 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_733894 prefixEnd_733894 := by exact prefixLift 733894
  have htrace : WordTrace (prefixWord ++ tailWord_733894) baseStart_733894 baseEnd_733894 := by
    simpa [prefixWord, tailWord_733894, baseEnd_733894] using wordTrace_append hprefix tailTrace_733894
  have hstable : (prefixWord ++ tailWord_733894).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733894).length < 2 ^ (prefixWord ++ tailWord_733894).sum := by decide
  have hdescent : baseEnd_733894 < baseStart_733894 := by decide
  rcases family_descends (prefixWord ++ tailWord_733894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733908 : List Nat := [2, 4, 1, 3, 2, 1, 2, 3, 2]
def baseStart_733908 : Nat := 118140960795 + 733908 * 2 ^ 59
def prefixEnd_733908 : Nat := 4983230072969 + 3 ^ 40 * 733908 * 2
def baseEnd_733908 : Nat := 334975609048906502466511

theorem tailTrace_733908 : CollatzResearch.WordTrace tailWord_733908 prefixEnd_733908 334975609048906502466511 := by
  unfold tailWord_733908
  simp only [CollatzResearch.WordTrace]
  refine ⟨13383911912592066176281189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17845215883456088235041585 13383911912592066176281189)
  ·
    refine ⟨2509483483611012408052723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13383911912592066176281189 2509483483611012408052723)
    ·
      refine ⟨3764225225416518612079085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2509483483611012408052723 3764225225416518612079085)
      ·
        refine ⟨1411584459531194479529657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3764225225416518612079085 1411584459531194479529657)
        ·
          refine ⟨1058688344648395859647243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1411584459531194479529657 1058688344648395859647243)
          ·
            refine ⟨1588032516972593789470865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1058688344648395859647243 1588032516972593789470865)
            ·
              refine ⟨1191024387729445342103149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1588032516972593789470865 1191024387729445342103149)
              ·
                refine ⟨446634145398542003288681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1191024387729445342103149 446634145398542003288681)
                ·
                  refine ⟨334975609048906502466511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 446634145398542003288681 334975609048906502466511)
                  ·
                    rfl

theorem cell20_733908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 3, 2].length) (baseStart_733908 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_733908 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_733908 prefixEnd_733908 := by exact prefixLift 733908
  have htrace : WordTrace (prefixWord ++ tailWord_733908) baseStart_733908 baseEnd_733908 := by
    simpa [prefixWord, tailWord_733908, baseEnd_733908] using wordTrace_append hprefix tailTrace_733908
  have hstable : (prefixWord ++ tailWord_733908).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733908).length < 2 ^ (prefixWord ++ tailWord_733908).sum := by decide
  have hdescent : baseEnd_733908 < baseStart_733908 := by decide
  rcases family_descends (prefixWord ++ tailWord_733908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733912 : List Nat := [2, 1, 2, 2, 3, 2, 1, 5, 2]
def baseStart_733912 : Nat := 118140960795 + 733912 * 2 ^ 59
def prefixEnd_733912 : Nat := 4983230072969 + 3 ^ 40 * 733912 * 2
def baseEnd_733912 : Nat := 334977434757900266333161

theorem tailTrace_733912 : CollatzResearch.WordTrace tailWord_733912 prefixEnd_733912 334977434757900266333161 := by
  unfold tailWord_733912
  simp only [CollatzResearch.WordTrace]
  refine ⟨13383984858584820517853995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17845313144779760690471993 13383984858584820517853995)
  ·
    refine ⟨20075977287877230776780993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13383984858584820517853995 20075977287877230776780993)
    ·
      refine ⟨15056982965907923082585745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20075977287877230776780993 15056982965907923082585745)
      ·
        refine ⟨11292737224430942311939309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15056982965907923082585745 11292737224430942311939309)
        ·
          refine ⟨4234776459161603366977241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11292737224430942311939309 4234776459161603366977241)
          ·
            refine ⟨3176082344371202525232931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4234776459161603366977241 3176082344371202525232931)
            ·
              refine ⟨4764123516556803787849397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3176082344371202525232931 4764123516556803787849397)
              ·
                refine ⟨446636579677200355110881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4764123516556803787849397 446636579677200355110881)
                ·
                  refine ⟨334977434757900266333161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 446636579677200355110881 334977434757900266333161)
                  ·
                    rfl

theorem cell20_733912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 5, 2].length) (baseStart_733912 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_733912 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_733912 prefixEnd_733912 := by exact prefixLift 733912
  have htrace : WordTrace (prefixWord ++ tailWord_733912) baseStart_733912 baseEnd_733912 := by
    simpa [prefixWord, tailWord_733912, baseEnd_733912] using wordTrace_append hprefix tailTrace_733912
  have hstable : (prefixWord ++ tailWord_733912).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733912).length < 2 ^ (prefixWord ++ tailWord_733912).sum := by decide
  have hdescent : baseEnd_733912 < baseStart_733912 := by decide
  rcases family_descends (prefixWord ++ tailWord_733912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733950 : List Nat := [4, 2, 2, 1, 2, 1, 2, 2, 4]
def baseStart_733950 : Nat := 118140960795 + 733950 * 2 ^ 59
def prefixEnd_733950 : Nat := 4983230072969 + 3 ^ 40 * 733950 * 2
def baseEnd_733950 : Nat := 334994778993341023066339

theorem tailTrace_733950 : CollatzResearch.WordTrace tailWord_733950 prefixEnd_733950 334994778993341023066339 := by
  unfold tailWord_733950
  simp only [CollatzResearch.WordTrace]
  refine ⟨3346169461378996690698913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17846237127354649017060869 3346169461378996690698913)
  ·
    refine ⟨2509627096034247518024185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3346169461378996690698913 2509627096034247518024185)
    ·
      refine ⟨1882220322025685638518139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2509627096034247518024185 1882220322025685638518139)
      ·
        refine ⟨2823330483038528457777209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1882220322025685638518139 2823330483038528457777209)
        ·
          refine ⟨2117497862278896343332907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2823330483038528457777209 2117497862278896343332907)
          ·
            refine ⟨3176246793418344514999361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2117497862278896343332907 3176246793418344514999361)
            ·
              refine ⟨2382185095063758386249521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3176246793418344514999361 2382185095063758386249521)
              ·
                refine ⟨1786638821297818789687141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2382185095063758386249521 1786638821297818789687141)
                ·
                  refine ⟨334994778993341023066339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1786638821297818789687141 334994778993341023066339)
                  ·
                    rfl

theorem cell20_733950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_733950 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_733950 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_733950 prefixEnd_733950 := by exact prefixLift 733950
  have htrace : WordTrace (prefixWord ++ tailWord_733950) baseStart_733950 baseEnd_733950 := by
    simpa [prefixWord, tailWord_733950, baseEnd_733950] using wordTrace_append hprefix tailTrace_733950
  have hstable : (prefixWord ++ tailWord_733950).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733950).length < 2 ^ (prefixWord ++ tailWord_733950).sum := by decide
  have hdescent : baseEnd_733950 < baseStart_733950 := by decide
  rcases family_descends (prefixWord ++ tailWord_733950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733985 : List Nat := [1, 2, 3, 2, 1, 2, 1, 3, 5]
def baseStart_733985 : Nat := 118140960795 + 733985 * 2 ^ 59
def prefixEnd_733985 : Nat := 4983230072969 + 3 ^ 40 * 733985 * 2
def baseEnd_733985 : Nat := 335010753947036456899529

theorem tailTrace_733985 : CollatzResearch.WordTrace tailWord_733985 prefixEnd_733985 335010753947036456899529 := by
  unfold tailWord_733985
  simp only [CollatzResearch.WordTrace]
  refine ⟨26770632245905174503115409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17847088163936783002076939 26770632245905174503115409)
  ·
    refine ⟨20077974184428880877336557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26770632245905174503115409 20077974184428880877336557)
    ·
      refine ⟨7529240319160830329001209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20077974184428880877336557 7529240319160830329001209)
      ·
        refine ⟨5646930239370622746750907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7529240319160830329001209 5646930239370622746750907)
        ·
          refine ⟨8470395359055934120126361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5646930239370622746750907 8470395359055934120126361)
          ·
            refine ⟨6352796519291950590094771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8470395359055934120126361 6352796519291950590094771)
            ·
              refine ⟨9529194778937925885142157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6352796519291950590094771 9529194778937925885142157)
              ·
                refine ⟨3573448042101722206928309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9529194778937925885142157 3573448042101722206928309)
                ·
                  refine ⟨335010753947036456899529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3573448042101722206928309 335010753947036456899529)
                  ·
                    rfl

theorem cell20_733985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 5].length) (baseStart_733985 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_733985 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_733985 prefixEnd_733985 := by exact prefixLift 733985
  have htrace : WordTrace (prefixWord ++ tailWord_733985) baseStart_733985 baseEnd_733985 := by
    simpa [prefixWord, tailWord_733985, baseEnd_733985] using wordTrace_append hprefix tailTrace_733985
  have hstable : (prefixWord ++ tailWord_733985).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733985).length < 2 ^ (prefixWord ++ tailWord_733985).sum := by decide
  have hdescent : baseEnd_733985 < baseStart_733985 := by decide
  rcases family_descends (prefixWord ++ tailWord_733985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733994 : List Nat := [3, 1, 4, 3, 2, 1, 2, 1, 3]
def baseStart_733994 : Nat := 118140960795 + 733994 * 2 ^ 59
def prefixEnd_733994 : Nat := 4983230072969 + 3 ^ 40 * 733994 * 2
def baseEnd_733994 : Nat := 335014861792272425599493

theorem tailTrace_733994 : CollatzResearch.WordTrace tailWord_733994 prefixEnd_733994 335014861792272425599493 := by
  unfold tailWord_733994
  simp only [CollatzResearch.WordTrace]
  refine ⟨6692740125718142260048259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17847307001915046026795357 6692740125718142260048259)
  ·
    refine ⟨10039110188577213390072389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6692740125718142260048259 10039110188577213390072389)
    ·
      refine ⟨1882333160358227510638573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10039110188577213390072389 1882333160358227510638573)
      ·
        refine ⟨705874935134335316489465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1882333160358227510638573 705874935134335316489465)
        ·
          refine ⟨529406201350751487367099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 705874935134335316489465 529406201350751487367099)
          ·
            refine ⟨794109302026127231050649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 529406201350751487367099 794109302026127231050649)
            ·
              refine ⟨595581976519595423287987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 794109302026127231050649 595581976519595423287987)
              ·
                refine ⟨893372964779393134931981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 595581976519595423287987 893372964779393134931981)
                ·
                  refine ⟨335014861792272425599493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 893372964779393134931981 335014861792272425599493)
                  ·
                    rfl

theorem cell20_733994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 2, 1, 3].length) (baseStart_733994 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_733994 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_733994 prefixEnd_733994 := by exact prefixLift 733994
  have htrace : WordTrace (prefixWord ++ tailWord_733994) baseStart_733994 baseEnd_733994 := by
    simpa [prefixWord, tailWord_733994, baseEnd_733994] using wordTrace_append hprefix tailTrace_733994
  have hstable : (prefixWord ++ tailWord_733994).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733994).length < 2 ^ (prefixWord ++ tailWord_733994).sum := by decide
  have hdescent : baseEnd_733994 < baseStart_733994 := by decide
  rcases family_descends (prefixWord ++ tailWord_733994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_733998 : List Nat := [4, 1, 3, 2, 1, 1, 4, 1, 3]
def baseStart_733998 : Nat := 118140960795 + 733998 * 2 ^ 59
def prefixEnd_733998 : Nat := 4983230072969 + 3 ^ 40 * 733998 * 2
def baseEnd_733998 : Nat := 335016687501266189466143

theorem tailTrace_733998 : CollatzResearch.WordTrace tailWord_733998 prefixEnd_733998 335016687501266189466143 := by
  unfold tailWord_733998
  simp only [CollatzResearch.WordTrace]
  refine ⟨3346388299357259715417331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17847404263238718482225765 3346388299357259715417331)
  ·
    refine ⟨5019582449035889573125997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3346388299357259715417331 5019582449035889573125997)
    ·
      refine ⟨1882343418388458589922249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5019582449035889573125997 1882343418388458589922249)
      ·
        refine ⟨1411757563791343942441687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1882343418388458589922249 1411757563791343942441687)
        ·
          refine ⟨2117636345687015913662531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1411757563791343942441687 2117636345687015913662531)
          ·
            refine ⟨3176454518530523870493797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2117636345687015913662531 3176454518530523870493797)
            ·
              refine ⟨595585222224473225717587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3176454518530523870493797 595585222224473225717587)
              ·
                refine ⟨893377833336709838576381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 595585222224473225717587 893377833336709838576381)
                ·
                  refine ⟨335016687501266189466143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 893377833336709838576381 335016687501266189466143)
                  ·
                    rfl

theorem cell20_733998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 4, 1, 3].length) (baseStart_733998 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_733998 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_733998 prefixEnd_733998 := by exact prefixLift 733998
  have htrace : WordTrace (prefixWord ++ tailWord_733998) baseStart_733998 baseEnd_733998 := by
    simpa [prefixWord, tailWord_733998, baseEnd_733998] using wordTrace_append hprefix tailTrace_733998
  have hstable : (prefixWord ++ tailWord_733998).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_733998).length < 2 ^ (prefixWord ++ tailWord_733998).sum := by decide
  have hdescent : baseEnd_733998 < baseStart_733998 := by decide
  rcases family_descends (prefixWord ++ tailWord_733998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734002 : List Nat := [3, 2, 1, 1, 3, 1, 3, 3, 3]
def baseStart_734002 : Nat := 118140960795 + 734002 * 2 ^ 59
def prefixEnd_734002 : Nat := 4983230072969 + 3 ^ 40 * 734002 * 2
def baseEnd_734002 : Nat := 335018513210259953332793

theorem tailTrace_734002 : CollatzResearch.WordTrace tailWord_734002 prefixEnd_734002 335018513210259953332793 := by
  unfold tailWord_734002
  simp only [CollatzResearch.WordTrace]
  refine ⟨6692813071710896601621065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17847501524562390937656173 6692813071710896601621065)
  ·
    refine ⟨5019609803783172451215799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6692813071710896601621065 5019609803783172451215799)
    ·
      refine ⟨7529414705674758676823699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5019609803783172451215799 7529414705674758676823699)
      ·
        refine ⟨11294122058512138015235549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7529414705674758676823699 11294122058512138015235549)
        ·
          refine ⟨4235295771942051755713331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11294122058512138015235549 4235295771942051755713331)
          ·
            refine ⟨6352943657913077633569997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4235295771942051755713331 6352943657913077633569997)
            ·
              refine ⟨2382353871717404112588749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6352943657913077633569997 2382353871717404112588749)
              ·
                refine ⟨893382701894026542220781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2382353871717404112588749 893382701894026542220781)
                ·
                  refine ⟨335018513210259953332793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 893382701894026542220781 335018513210259953332793)
                  ·
                    rfl

theorem cell20_734002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 3, 3].length) (baseStart_734002 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_734002 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_734002 prefixEnd_734002 := by exact prefixLift 734002
  have htrace : WordTrace (prefixWord ++ tailWord_734002) baseStart_734002 baseEnd_734002 := by
    simpa [prefixWord, tailWord_734002, baseEnd_734002] using wordTrace_append hprefix tailTrace_734002
  have hstable : (prefixWord ++ tailWord_734002).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734002).length < 2 ^ (prefixWord ++ tailWord_734002).sum := by decide
  have hdescent : baseEnd_734002 < baseStart_734002 := by decide
  rcases family_descends (prefixWord ++ tailWord_734002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734050 : List Nat := [3, 3, 2, 1, 3, 2, 1, 5]
def baseStart_734050 : Nat := 118140960795 + 734050 * 2 ^ 59
def prefixEnd_734050 : Nat := 4983230072969 + 3 ^ 40 * 734050 * 2
def baseEnd_734050 : Nat := 111680140572728373244199

theorem tailTrace_734050 : CollatzResearch.WordTrace tailWord_734050 prefixEnd_734050 111680140572728373244199 := by
  unfold tailWord_734050
  simp only [CollatzResearch.WordTrace]
  refine ⟨6693250747667422651057901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17848668660446460402821069 6693250747667422651057901)
  ·
    refine ⟨2509969030375283494146713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6693250747667422651057901 2509969030375283494146713)
    ·
      refine ⟨1882476772781462620610035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2509969030375283494146713 1882476772781462620610035)
      ·
        refine ⟨2823715159172193930915053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1882476772781462620610035 2823715159172193930915053)
        ·
          refine ⟨1058893184689572724093145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2823715159172193930915053 1058893184689572724093145)
          ·
            refine ⟨794169888517179543069859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1058893184689572724093145 794169888517179543069859)
            ·
              refine ⟨1191254832775769314604789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 794169888517179543069859 1191254832775769314604789)
              ·
                refine ⟨111680140572728373244199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1191254832775769314604789 111680140572728373244199)
                ·
                  rfl

theorem cell20_734050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 5].length) (baseStart_734050 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_734050 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_734050 prefixEnd_734050 := by exact prefixLift 734050
  have htrace : WordTrace (prefixWord ++ tailWord_734050) baseStart_734050 baseEnd_734050 := by
    simpa [prefixWord, tailWord_734050, baseEnd_734050] using wordTrace_append hprefix tailTrace_734050
  have hstable : (prefixWord ++ tailWord_734050).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734050).length < 2 ^ (prefixWord ++ tailWord_734050).sum := by decide
  have hdescent : baseEnd_734050 < baseStart_734050 := by decide
  rcases family_descends (prefixWord ++ tailWord_734050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734061 : List Nat := [1, 5, 1, 1, 1, 1, 1, 2, 7]
def baseStart_734061 : Nat := 118140960795 + 734061 * 2 ^ 59
def prefixEnd_734061 : Nat := 4983230072969 + 3 ^ 40 * 734061 * 2
def baseEnd_734061 : Nat := 335045442417917970365885

theorem tailTrace_734061 : CollatzResearch.WordTrace tailWord_734061 prefixEnd_734061 335045442417917970365885 := by
  unfold tailWord_734061
  simp only [CollatzResearch.WordTrace]
  refine ⟨26773404193629839482882037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17848936129086559655254691 26773404193629839482882037)
  ·
    refine ⟨2510006643152797451520191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26773404193629839482882037 2510006643152797451520191)
    ·
      refine ⟨3765009964729196177280287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2510006643152797451520191 3765009964729196177280287)
      ·
        refine ⟨5647514947093794265920431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3765009964729196177280287 5647514947093794265920431)
        ·
          refine ⟨8471272420640691398880647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5647514947093794265920431 8471272420640691398880647)
          ·
            refine ⟨12706908630961037098320971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8471272420640691398880647 12706908630961037098320971)
            ·
              refine ⟨19060362946441555647481457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12706908630961037098320971 19060362946441555647481457)
              ·
                refine ⟨14295272209831166735611093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19060362946441555647481457 14295272209831166735611093)
                ·
                  refine ⟨335045442417917970365885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14295272209831166735611093 335045442417917970365885)
                  ·
                    rfl

theorem cell20_734061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_734061 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_734061 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_734061 prefixEnd_734061 := by exact prefixLift 734061
  have htrace : WordTrace (prefixWord ++ tailWord_734061) baseStart_734061 baseEnd_734061 := by
    simpa [prefixWord, tailWord_734061, baseEnd_734061] using wordTrace_append hprefix tailTrace_734061
  have hstable : (prefixWord ++ tailWord_734061).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734061).length < 2 ^ (prefixWord ++ tailWord_734061).sum := by decide
  have hdescent : baseEnd_734061 < baseStart_734061 := by decide
  rcases family_descends (prefixWord ++ tailWord_734061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734075 : List Nat := [1, 1, 1, 1, 1, 5, 2, 8]
def baseStart_734075 : Nat := 118140960795 + 734075 * 2 ^ 59
def prefixEnd_734075 : Nat := 4983230072969 + 3 ^ 40 * 734075 * 2
def baseEnd_734075 : Nat := 111683944133132047966387

theorem tailTrace_734075 : CollatzResearch.WordTrace tailWord_734075 prefixEnd_734075 111683944133132047966387 := by
  unfold tailWord_734075
  simp only [CollatzResearch.WordTrace]
  refine ⟨26773914815579119873891679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17849276543719413249261119 26773914815579119873891679)
  ·
    refine ⟨40160872223368679810837519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26773914815579119873891679 40160872223368679810837519)
    ·
      refine ⟨60241308335053019716256279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40160872223368679810837519 60241308335053019716256279)
      ·
        refine ⟨90361962502579529574384419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60241308335053019716256279 90361962502579529574384419)
        ·
          refine ⟨135542943753869294361576629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90361962502579529574384419 135542943753869294361576629)
          ·
            refine ⟨12707150976925246346397809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 135542943753869294361576629 12707150976925246346397809)
            ·
              refine ⟨9530363232693934759798357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12707150976925246346397809 9530363232693934759798357)
              ·
                refine ⟨111683944133132047966387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9530363232693934759798357 111683944133132047966387)
                ·
                  rfl

theorem cell20_734075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 8].length) (baseStart_734075 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_734075 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_734075 prefixEnd_734075 := by exact prefixLift 734075
  have htrace : WordTrace (prefixWord ++ tailWord_734075) baseStart_734075 baseEnd_734075 := by
    simpa [prefixWord, tailWord_734075, baseEnd_734075] using wordTrace_append hprefix tailTrace_734075
  have hstable : (prefixWord ++ tailWord_734075).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734075).length < 2 ^ (prefixWord ++ tailWord_734075).sum := by decide
  have hdescent : baseEnd_734075 < baseStart_734075 := by decide
  rcases family_descends (prefixWord ++ tailWord_734075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734099 : List Nat := [1, 1, 1, 2, 1, 2, 1, 8, 3]
def baseStart_734099 : Nat := 118140960795 + 734099 * 2 ^ 59
def prefixEnd_734099 : Nat := 4983230072969 + 3 ^ 40 * 734099 * 2
def baseEnd_734099 : Nat := 335062786653358727099063

theorem tailTrace_734099 : CollatzResearch.WordTrace tailWord_734099 prefixEnd_734099 335062786653358727099063 := by
  unfold tailWord_734099
  simp only [CollatzResearch.WordTrace]
  refine ⟨26774790167492171972765351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17849860111661447981843567 26774790167492171972765351)
  ·
    refine ⟨40162185251238257959148027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26774790167492171972765351 40162185251238257959148027)
    ·
      refine ⟨60243277876857386938722041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40162185251238257959148027 60243277876857386938722041)
      ·
        refine ⟨45182458407643040204041531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60243277876857386938722041 45182458407643040204041531)
        ·
          refine ⟨67773687611464560306062297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45182458407643040204041531 67773687611464560306062297)
          ·
            refine ⟨50830265708598420229546723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67773687611464560306062297 50830265708598420229546723)
            ·
              refine ⟨76245398562897630344320085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50830265708598420229546723 76245398562897630344320085)
              ·
                refine ⟨893500764408956605597501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 76245398562897630344320085 893500764408956605597501)
                ·
                  refine ⟨335062786653358727099063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 893500764408956605597501 335062786653358727099063)
                  ·
                    rfl

theorem cell20_734099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 8, 3].length) (baseStart_734099 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_734099 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_734099 prefixEnd_734099 := by exact prefixLift 734099
  have htrace : WordTrace (prefixWord ++ tailWord_734099) baseStart_734099 baseEnd_734099 := by
    simpa [prefixWord, tailWord_734099, baseEnd_734099] using wordTrace_append hprefix tailTrace_734099
  have hstable : (prefixWord ++ tailWord_734099).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734099).length < 2 ^ (prefixWord ++ tailWord_734099).sum := by decide
  have hdescent : baseEnd_734099 < baseStart_734099 := by decide
  rcases family_descends (prefixWord ++ tailWord_734099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734137 : List Nat := [1, 2, 1, 4, 2, 2, 1, 2, 5]
def baseStart_734137 : Nat := 118140960795 + 734137 * 2 ^ 59
def prefixEnd_734137 : Nat := 4983230072969 + 3 ^ 40 * 734137 * 2
def baseEnd_734137 : Nat := 335080130888799483832241

theorem tailTrace_734137 : CollatzResearch.WordTrace tailWord_734137 prefixEnd_734137 335080130888799483832241 := by
  unfold tailWord_734137
  simp only [CollatzResearch.WordTrace]
  refine ⟨26776176141354504462648665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17850784094236336308432443 26776176141354504462648665)
  ·
    refine ⟨20082132106015878346986499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26776176141354504462648665 20082132106015878346986499)
    ·
      refine ⟨30123198159023817520479749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20082132106015878346986499 30123198159023817520479749)
      ·
        refine ⟨5648099654816965785089953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30123198159023817520479749 5648099654816965785089953)
        ·
          refine ⟨4236074741112724338817465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5648099654816965785089953 4236074741112724338817465)
          ·
            refine ⟨3177056055834543254113099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4236074741112724338817465 3177056055834543254113099)
            ·
              refine ⟨4765584083751814881169649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3177056055834543254113099 4765584083751814881169649)
              ·
                refine ⟨3574188062813861160877237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4765584083751814881169649 3574188062813861160877237)
                ·
                  refine ⟨335080130888799483832241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3574188062813861160877237 335080130888799483832241)
                  ·
                    rfl

theorem cell20_734137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 5].length) (baseStart_734137 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_734137 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_734137 prefixEnd_734137 := by exact prefixLift 734137
  have htrace : WordTrace (prefixWord ++ tailWord_734137) baseStart_734137 baseEnd_734137 := by
    simpa [prefixWord, tailWord_734137, baseEnd_734137] using wordTrace_append hprefix tailTrace_734137
  have hstable : (prefixWord ++ tailWord_734137).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734137).length < 2 ^ (prefixWord ++ tailWord_734137).sum := by decide
  have hdescent : baseEnd_734137 < baseStart_734137 := by decide
  rcases family_descends (prefixWord ++ tailWord_734137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734151 : List Nat := [1, 1, 4, 1, 1, 2, 10]
def baseStart_734151 : Nat := 118140960795 + 734151 * 2 ^ 59
def prefixEnd_734151 : Nat := 4983230072969 + 3 ^ 40 * 734151 * 2
def baseEnd_734151 : Nat := 37231835652253073040613

theorem tailTrace_734151 : CollatzResearch.WordTrace tailWord_734151 prefixEnd_734151 37231835652253073040613 := by
  unfold tailWord_734151
  simp only [CollatzResearch.WordTrace]
  refine ⟨26776686763303784853658307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17851124508869189902438871 26776686763303784853658307)
  ·
    refine ⟨40165030144955677280487461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26776686763303784853658307 40165030144955677280487461)
    ·
      refine ⟨7530943152179189490091399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40165030144955677280487461 7530943152179189490091399)
      ·
        refine ⟨11296414728268784235137099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7530943152179189490091399 11296414728268784235137099)
        ·
          refine ⟨16944622092403176352705649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11296414728268784235137099 16944622092403176352705649)
          ·
            refine ⟨12708466569302382264529237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16944622092403176352705649 12708466569302382264529237)
            ·
              refine ⟨37231835652253073040613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12708466569302382264529237 37231835652253073040613)
              ·
                rfl

theorem cell20_734151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 10].length) (baseStart_734151 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_734151 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_734151 prefixEnd_734151 := by exact prefixLift 734151
  have htrace : WordTrace (prefixWord ++ tailWord_734151) baseStart_734151 baseEnd_734151 := by
    simpa [prefixWord, tailWord_734151, baseEnd_734151] using wordTrace_append hprefix tailTrace_734151
  have hstable : (prefixWord ++ tailWord_734151).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734151).length < 2 ^ (prefixWord ++ tailWord_734151).sum := by decide
  have hdescent : baseEnd_734151 < baseStart_734151 := by decide
  rcases family_descends (prefixWord ++ tailWord_734151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734168 : List Nat := [2, 1, 2, 2, 2, 4, 2, 5]
def baseStart_734168 : Nat := 118140960795 + 734168 * 2 ^ 59
def prefixEnd_734168 : Nat := 4983230072969 + 3 ^ 40 * 734168 * 2
def baseEnd_734168 : Nat := 111698093377833717932927

theorem tailTrace_734168 : CollatzResearch.WordTrace tailWord_734168 prefixEnd_734168 111698093377833717932927 := by
  unfold tailWord_734168
  simp only [CollatzResearch.WordTrace]
  refine ⟨13388653402121098378513579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17851537869494797838018105 13388653402121098378513579)
  ·
    refine ⟨20082980103181647567770369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13388653402121098378513579 20082980103181647567770369)
    ·
      refine ⟨15062235077386235675827777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20082980103181647567770369 15062235077386235675827777)
      ·
        refine ⟨11296676308039676756870833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15062235077386235675827777 11296676308039676756870833)
        ·
          refine ⟨8472507231029757567653125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11296676308039676756870833 8472507231029757567653125)
          ·
            refine ⟨1588595105818079543934961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8472507231029757567653125 1588595105818079543934961)
            ·
              refine ⟨1191446329363559657951221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1588595105818079543934961 1191446329363559657951221)
              ·
                refine ⟨111698093377833717932927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1191446329363559657951221 111698093377833717932927)
                ·
                  rfl

theorem cell20_734168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 5].length) (baseStart_734168 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_734168 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_734168 prefixEnd_734168 := by exact prefixLift 734168
  have htrace : WordTrace (prefixWord ++ tailWord_734168) baseStart_734168 baseEnd_734168 := by
    simpa [prefixWord, tailWord_734168, baseEnd_734168] using wordTrace_append hprefix tailTrace_734168
  have hstable : (prefixWord ++ tailWord_734168).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734168).length < 2 ^ (prefixWord ++ tailWord_734168).sum := by decide
  have hdescent : baseEnd_734168 < baseStart_734168 := by decide
  rcases family_descends (prefixWord ++ tailWord_734168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734206 : List Nat := [4, 2, 2, 2, 10]
def baseStart_734206 : Nat := 118140960795 + 734206 * 2 ^ 59
def prefixEnd_734206 : Nat := 4983230072969 + 3 ^ 40 * 734206 * 2
def baseEnd_734206 : Nat := 4137180547764714944839

theorem tailTrace_734206 : CollatzResearch.WordTrace tailWord_734206 prefixEnd_734206 4137180547764714944839 := by
  unfold tailWord_734206
  simp only [CollatzResearch.WordTrace]
  refine ⟨3347336597263066155863809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17852461852069686164606981 3347336597263066155863809)
  ·
    refine ⟨2510502447947299616897857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3347336597263066155863809 2510502447947299616897857)
    ·
      refine ⟨1882876835960474712673393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2510502447947299616897857 1882876835960474712673393)
      ·
        refine ⟨1412157626970356034505045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1882876835960474712673393 1412157626970356034505045)
        ·
          refine ⟨4137180547764714944839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1412157626970356034505045 4137180547764714944839)
          ·
            rfl

theorem cell20_734206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 10].length) (baseStart_734206 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_734206 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_734206 prefixEnd_734206 := by exact prefixLift 734206
  have htrace : WordTrace (prefixWord ++ tailWord_734206) baseStart_734206 baseEnd_734206 := by
    simpa [prefixWord, tailWord_734206, baseEnd_734206] using wordTrace_append hprefix tailTrace_734206
  have hstable : (prefixWord ++ tailWord_734206).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734206).length < 2 ^ (prefixWord ++ tailWord_734206).sum := by decide
  have hdescent : baseEnd_734206 < baseStart_734206 := by decide
  rcases family_descends (prefixWord ++ tailWord_734206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734216 : List Nat := [2, 1, 3, 2, 1, 4, 1, 4, 2]
def baseStart_734216 : Nat := 118140960795 + 734216 * 2 ^ 59
def prefixEnd_734216 : Nat := 4983230072969 + 3 ^ 40 * 734216 * 2
def baseEnd_734216 : Nat := 335116188641426320198585

theorem tailTrace_734216 : CollatzResearch.WordTrace tailWord_734216 prefixEnd_734216 335116188641426320198585 := by
  unfold tailWord_734216
  simp only [CollatzResearch.WordTrace]
  refine ⟨13389528754034150477387251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17852705005378867303183001 13389528754034150477387251)
  ·
    refine ⟨20084293131051225716080877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13389528754034150477387251 20084293131051225716080877)
    ·
      refine ⟨7531609924144209643530329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20084293131051225716080877 7531609924144209643530329)
      ·
        refine ⟨5648707443108157232647747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7531609924144209643530329 5648707443108157232647747)
        ·
          refine ⟨8473061164662235848971621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5648707443108157232647747 8473061164662235848971621)
          ·
            refine ⟨1588698968374169221682179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8473061164662235848971621 1588698968374169221682179)
            ·
              refine ⟨2383048452561253832523269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1588698968374169221682179 2383048452561253832523269)
              ·
                refine ⟨446821584855235093598113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2383048452561253832523269 446821584855235093598113)
                ·
                  refine ⟨335116188641426320198585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 446821584855235093598113 335116188641426320198585)
                  ·
                    rfl

theorem cell20_734216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 4, 2].length) (baseStart_734216 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_734216 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_734216 prefixEnd_734216 := by exact prefixLift 734216
  have htrace : WordTrace (prefixWord ++ tailWord_734216) baseStart_734216 baseEnd_734216 := by
    simpa [prefixWord, tailWord_734216, baseEnd_734216] using wordTrace_append hprefix tailTrace_734216
  have hstable : (prefixWord ++ tailWord_734216).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734216).length < 2 ^ (prefixWord ++ tailWord_734216).sum := by decide
  have hdescent : baseEnd_734216 < baseStart_734216 := by decide
  rcases family_descends (prefixWord ++ tailWord_734216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734240 : List Nat := [2, 1, 1, 7, 1, 1, 3, 4]
def baseStart_734240 : Nat := 118140960795 + 734240 * 2 ^ 59
def prefixEnd_734240 : Nat := 4983230072969 + 3 ^ 40 * 734240 * 2
def baseEnd_734240 : Nat := 111709047631796301132829

theorem tailTrace_734240 : CollatzResearch.WordTrace tailWord_734240 prefixEnd_734240 111709047631796301132829 := by
  unfold tailWord_734240
  simp only [CollatzResearch.WordTrace]
  refine ⟨13389966429990676526824087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17853288573320902035765449 13389966429990676526824087)
  ·
    refine ⟨20084949644986014790236131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13389966429990676526824087 20084949644986014790236131)
    ·
      refine ⟨30127424467479022185354197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20084949644986014790236131 30127424467479022185354197)
      ·
        refine ⟨706111510956539582469239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 30127424467479022185354197 706111510956539582469239)
        ·
          refine ⟨1059167266434809373703859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 706111510956539582469239 1059167266434809373703859)
          ·
            refine ⟨1588750899652214060555789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1059167266434809373703859 1588750899652214060555789)
            ·
              refine ⟨595781587369580272708421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1588750899652214060555789 595781587369580272708421)
              ·
                refine ⟨111709047631796301132829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 595781587369580272708421 111709047631796301132829)
                ·
                  rfl

theorem cell20_734240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 3, 4].length) (baseStart_734240 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_734240 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_734240 prefixEnd_734240 := by exact prefixLift 734240
  have htrace : WordTrace (prefixWord ++ tailWord_734240) baseStart_734240 baseEnd_734240 := by
    simpa [prefixWord, tailWord_734240, baseEnd_734240] using wordTrace_append hprefix tailTrace_734240
  have hstable : (prefixWord ++ tailWord_734240).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734240).length < 2 ^ (prefixWord ++ tailWord_734240).sum := by decide
  have hdescent : baseEnd_734240 < baseStart_734240 := by decide
  rcases family_descends (prefixWord ++ tailWord_734240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734258 : List Nat := [3, 2, 1, 1, 2, 2, 1, 2, 6]
def baseStart_734258 : Nat := 118140960795 + 734258 * 2 ^ 59
def prefixEnd_734258 : Nat := 4983230072969 + 3 ^ 40 * 734258 * 2
def baseEnd_734258 : Nat := 335135358585860840798413

theorem tailTrace_734258 : CollatzResearch.WordTrace tailWord_734258 prefixEnd_734258 335135358585860840798413 := by
  unfold tailWord_734258
  simp only [CollatzResearch.WordTrace]
  refine ⟨6695147343479035531950857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17853726249277428085202285 6695147343479035531950857)
  ·
    refine ⟨5021360507609276648963143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6695147343479035531950857 5021360507609276648963143)
    ·
      refine ⟨7532040761413914973444715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5021360507609276648963143 7532040761413914973444715)
      ·
        refine ⟨11298061142120872460167073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7532040761413914973444715 11298061142120872460167073)
        ·
          refine ⟨8473545856590654345125305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11298061142120872460167073 8473545856590654345125305)
          ·
            refine ⟨6355159392442990758843979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8473545856590654345125305 6355159392442990758843979)
            ·
              refine ⟨9532739088664486138265969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6355159392442990758843979 9532739088664486138265969)
              ·
                refine ⟨7149554316498364603699477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9532739088664486138265969 7149554316498364603699477)
                ·
                  refine ⟨335135358585860840798413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7149554316498364603699477 335135358585860840798413)
                  ·
                    rfl

theorem cell20_734258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_734258 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_734258 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_734258 prefixEnd_734258 := by exact prefixLift 734258
  have htrace : WordTrace (prefixWord ++ tailWord_734258) baseStart_734258 baseEnd_734258 := by
    simpa [prefixWord, tailWord_734258, baseEnd_734258] using wordTrace_append hprefix tailTrace_734258
  have hstable : (prefixWord ++ tailWord_734258).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734258).length < 2 ^ (prefixWord ++ tailWord_734258).sum := by decide
  have hdescent : baseEnd_734258 < baseStart_734258 := by decide
  rcases family_descends (prefixWord ++ tailWord_734258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734268 : List Nat := [2, 2, 2, 2, 2, 2, 3, 2, 3]
def baseStart_734268 : Nat := 118140960795 + 734268 * 2 ^ 59
def prefixEnd_734268 : Nat := 4983230072969 + 3 ^ 40 * 734268 * 2
def baseEnd_734268 : Nat := 335139922858345250465039

theorem tailTrace_734268 : CollatzResearch.WordTrace tailWord_734268 prefixEnd_734268 335139922858345250465039 := by
  unfold tailWord_734268
  simp only [CollatzResearch.WordTrace]
  refine ⟨13390477051939956917833729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17853969402586609223778305 13390477051939956917833729)
  ·
    refine ⟨10042857788954967688375297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13390477051939956917833729 10042857788954967688375297)
    ·
      refine ⟨7532143341716225766281473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10042857788954967688375297 7532143341716225766281473)
      ·
        refine ⟨5649107506287169324711105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7532143341716225766281473 5649107506287169324711105)
        ·
          refine ⟨4236830629715376993533329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5649107506287169324711105 4236830629715376993533329)
          ·
            refine ⟨3177622972286532745149997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4236830629715376993533329 3177622972286532745149997)
            ·
              refine ⟨1191608614607449779431249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3177622972286532745149997 1191608614607449779431249)
              ·
                refine ⟨893706460955587334573437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1191608614607449779431249 893706460955587334573437)
                ·
                  refine ⟨335139922858345250465039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 893706460955587334573437 335139922858345250465039)
                  ·
                    rfl

theorem cell20_734268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 2, 3].length) (baseStart_734268 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_734268 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_734268 prefixEnd_734268 := by exact prefixLift 734268
  have htrace : WordTrace (prefixWord ++ tailWord_734268) baseStart_734268 baseEnd_734268 := by
    simpa [prefixWord, tailWord_734268, baseEnd_734268] using wordTrace_append hprefix tailTrace_734268
  have hstable : (prefixWord ++ tailWord_734268).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734268).length < 2 ^ (prefixWord ++ tailWord_734268).sum := by decide
  have hdescent : baseEnd_734268 < baseStart_734268 := by decide
  rcases family_descends (prefixWord ++ tailWord_734268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734275 : List Nat := [1, 1, 1, 3, 1, 2, 3, 6, 2]
def baseStart_734275 : Nat := 118140960795 + 734275 * 2 ^ 59
def prefixEnd_734275 : Nat := 4983230072969 + 3 ^ 40 * 734275 * 2
def baseEnd_734275 : Nat := 335143117849084337231677

theorem tailTrace_734275 : CollatzResearch.WordTrace tailWord_734275 prefixEnd_734275 335143117849084337231677 := by
  unfold tailWord_734275
  simp only [CollatzResearch.WordTrace]
  refine ⟨26781209414854554031172279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17854139609903036020781519 26781209414854554031172279)
  ·
    refine ⟨40171814122281831046758419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26781209414854554031172279 40171814122281831046758419)
    ·
      refine ⟨60257721183422746570137629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40171814122281831046758419 60257721183422746570137629)
      ·
        refine ⟨22596645443783529963801611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60257721183422746570137629 22596645443783529963801611)
        ·
          refine ⟨33894968165675294945702417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22596645443783529963801611 33894968165675294945702417)
          ·
            refine ⟨25421226124256471209276813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33894968165675294945702417 25421226124256471209276813)
            ·
              refine ⟨9532959796596176703478805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25421226124256471209276813 9532959796596176703478805)
              ·
                refine ⟨446857490465445782975569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9532959796596176703478805 446857490465445782975569)
                ·
                  refine ⟨335143117849084337231677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 446857490465445782975569 335143117849084337231677)
                  ·
                    rfl

theorem cell20_734275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 6, 2].length) (baseStart_734275 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_734275 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_734275 prefixEnd_734275 := by exact prefixLift 734275
  have htrace : WordTrace (prefixWord ++ tailWord_734275) baseStart_734275 baseEnd_734275 := by
    simpa [prefixWord, tailWord_734275, baseEnd_734275] using wordTrace_append hprefix tailTrace_734275
  have hstable : (prefixWord ++ tailWord_734275).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734275).length < 2 ^ (prefixWord ++ tailWord_734275).sum := by decide
  have hdescent : baseEnd_734275 < baseStart_734275 := by decide
  rcases family_descends (prefixWord ++ tailWord_734275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734289 : List Nat := [1, 2, 2, 1, 3, 1, 2, 5, 3]
def baseStart_734289 : Nat := 118140960795 + 734289 * 2 ^ 59
def prefixEnd_734289 : Nat := 4983230072969 + 3 ^ 40 * 734289 * 2
def baseEnd_734289 : Nat := 335149507830562510764953

theorem tailTrace_734289 : CollatzResearch.WordTrace tailWord_734289 prefixEnd_734289 335149507830562510764953 := by
  unfold tailWord_734289
  simp only [CollatzResearch.WordTrace]
  refine ⟨26781720036803834422181921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17854480024535889614787947 26781720036803834422181921)
  ·
    refine ⟨20086290027602875816636441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26781720036803834422181921 20086290027602875816636441)
    ·
      refine ⟨15064717520702156862477331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20086290027602875816636441 15064717520702156862477331)
      ·
        refine ⟨22597076281053235293715997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15064717520702156862477331 22597076281053235293715997)
        ·
          refine ⟨8473903605394963235143499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22597076281053235293715997 8473903605394963235143499)
          ·
            refine ⟨12710855408092444852715249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8473903605394963235143499 12710855408092444852715249)
            ·
              refine ⟨9533141556069333639536437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12710855408092444852715249 9533141556069333639536437)
              ·
                refine ⟨893732020881500028706541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9533141556069333639536437 893732020881500028706541)
                ·
                  refine ⟨335149507830562510764953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 893732020881500028706541 335149507830562510764953)
                  ·
                    rfl

theorem cell20_734289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 5, 3].length) (baseStart_734289 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_734289 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_734289 prefixEnd_734289 := by exact prefixLift 734289
  have htrace : WordTrace (prefixWord ++ tailWord_734289) baseStart_734289 baseEnd_734289 := by
    simpa [prefixWord, tailWord_734289, baseEnd_734289] using wordTrace_append hprefix tailTrace_734289
  have hstable : (prefixWord ++ tailWord_734289).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734289).length < 2 ^ (prefixWord ++ tailWord_734289).sum := by decide
  have hdescent : baseEnd_734289 < baseStart_734289 := by decide
  rcases family_descends (prefixWord ++ tailWord_734289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734296 : List Nat := [2, 1, 2, 2, 1, 3, 1, 4, 4]
def baseStart_734296 : Nat := 118140960795 + 734296 * 2 ^ 59
def prefixEnd_734296 : Nat := 4983230072969 + 3 ^ 40 * 734296 * 2
def baseEnd_734296 : Nat := 335152702821301597531591

theorem tailTrace_734296 : CollatzResearch.WordTrace tailWord_734296 prefixEnd_734296 335152702821301597531591 := by
  unfold tailWord_734296
  simp only [CollatzResearch.WordTrace]
  refine ⟨13390987673889237308843371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17854650231852316411791161 13390987673889237308843371)
  ·
    refine ⟨20086481510833855963265057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13390987673889237308843371 20086481510833855963265057)
    ·
      refine ⟨15064861133125391972448793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20086481510833855963265057 15064861133125391972448793)
      ·
        refine ⟨11298645849844043979336595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15064861133125391972448793 11298645849844043979336595)
        ·
          refine ⟨16947968774766065969004893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11298645849844043979336595 16947968774766065969004893)
          ·
            refine ⟨6355488290537274738376835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16947968774766065969004893 6355488290537274738376835)
            ·
              refine ⟨9533232435805912107565253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6355488290537274738376835 9533232435805912107565253)
              ·
                refine ⟨1787481081713608520168485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9533232435805912107565253 1787481081713608520168485)
                ·
                  refine ⟨335152702821301597531591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1787481081713608520168485 335152702821301597531591)
                  ·
                    rfl

theorem cell20_734296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 4, 4].length) (baseStart_734296 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_734296 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_734296 prefixEnd_734296 := by exact prefixLift 734296
  have htrace : WordTrace (prefixWord ++ tailWord_734296) baseStart_734296 baseEnd_734296 := by
    simpa [prefixWord, tailWord_734296, baseEnd_734296] using wordTrace_append hprefix tailTrace_734296
  have hstable : (prefixWord ++ tailWord_734296).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734296).length < 2 ^ (prefixWord ++ tailWord_734296).sum := by decide
  have hdescent : baseEnd_734296 < baseStart_734296 := by decide
  rcases family_descends (prefixWord ++ tailWord_734296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734303 : List Nat := [1, 1, 2, 3, 1, 1, 5, 6]
def baseStart_734303 : Nat := 118140960795 + 734303 * 2 ^ 59
def prefixEnd_734303 : Nat := 4983230072969 + 3 ^ 40 * 734303 * 2
def baseEnd_734303 : Nat := 111718632604013561432743

theorem tailTrace_734303 : CollatzResearch.WordTrace tailWord_734303 prefixEnd_734303 111718632604013561432743 := by
  unfold tailWord_734303
  simp only [CollatzResearch.WordTrace]
  refine ⟨26782230658753114813191563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17854820439168743208794375 26782230658753114813191563)
  ·
    refine ⟨40173345988129672219787345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26782230658753114813191563 40173345988129672219787345)
    ·
      refine ⟨30130009491097254164840509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40173345988129672219787345 30130009491097254164840509)
      ·
        refine ⟨11298753559161470311815191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30130009491097254164840509 11298753559161470311815191)
        ·
          refine ⟨16948130338742205467722787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11298753559161470311815191 16948130338742205467722787)
          ·
            refine ⟨25422195508113308201584181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16948130338742205467722787 25422195508113308201584181)
            ·
              refine ⟨2383330828885622643898517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25422195508113308201584181 2383330828885622643898517)
              ·
                refine ⟨111718632604013561432743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2383330828885622643898517 111718632604013561432743)
                ·
                  rfl

theorem cell20_734303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 6].length) (baseStart_734303 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_734303 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_734303 prefixEnd_734303 := by exact prefixLift 734303
  have htrace : WordTrace (prefixWord ++ tailWord_734303) baseStart_734303 baseEnd_734303 := by
    simpa [prefixWord, tailWord_734303, baseEnd_734303] using wordTrace_append hprefix tailTrace_734303
  have hstable : (prefixWord ++ tailWord_734303).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734303).length < 2 ^ (prefixWord ++ tailWord_734303).sum := by decide
  have hdescent : baseEnd_734303 < baseStart_734303 := by decide
  rcases family_descends (prefixWord ++ tailWord_734303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734306 : List Nat := [3, 3, 2, 2, 1, 1, 1, 2, 5]
def baseStart_734306 : Nat := 118140960795 + 734306 * 2 ^ 59
def prefixEnd_734306 : Nat := 4983230072969 + 3 ^ 40 * 734306 * 2
def baseEnd_734306 : Nat := 335157267093786007198217

theorem tailTrace_734306 : CollatzResearch.WordTrace tailWord_734306 prefixEnd_734306 335157267093786007198217 := by
  unfold tailWord_734306
  simp only [CollatzResearch.WordTrace]
  refine ⟨6695585019435561581387693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17854893385161497550367181 6695585019435561581387693)
  ·
    refine ⟨2510844382288335593020385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6695585019435561581387693 2510844382288335593020385)
    ·
      refine ⟨1883133286716251694765289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2510844382288335593020385 1883133286716251694765289)
      ·
        refine ⟨1412349965037188771073967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1883133286716251694765289 1412349965037188771073967)
        ·
          refine ⟨2118524947555783156610951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1412349965037188771073967 2118524947555783156610951)
          ·
            refine ⟨3177787421333674734916427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2118524947555783156610951 3177787421333674734916427)
            ·
              refine ⟨4766681132000512102374641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3177787421333674734916427 4766681132000512102374641)
              ·
                refine ⟨3575010849000384076780981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4766681132000512102374641 3575010849000384076780981)
                ·
                  refine ⟨335157267093786007198217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3575010849000384076780981 335157267093786007198217)
                  ·
                    rfl

theorem cell20_734306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_734306 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_734306 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_734306 prefixEnd_734306 := by exact prefixLift 734306
  have htrace : WordTrace (prefixWord ++ tailWord_734306) baseStart_734306 baseEnd_734306 := by
    simpa [prefixWord, tailWord_734306, baseEnd_734306] using wordTrace_append hprefix tailTrace_734306
  have hstable : (prefixWord ++ tailWord_734306).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734306).length < 2 ^ (prefixWord ++ tailWord_734306).sum := by decide
  have hdescent : baseEnd_734306 < baseStart_734306 := by decide
  rcases family_descends (prefixWord ++ tailWord_734306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734327 : List Nat := [1, 1, 3, 1, 1, 4, 2, 4, 3]
def baseStart_734327 : Nat := 118140960795 + 734327 * 2 ^ 59
def prefixEnd_734327 : Nat := 4983230072969 + 3 ^ 40 * 734327 * 2
def baseEnd_734327 : Nat := 335166852066003267498131

theorem tailTrace_734327 : CollatzResearch.WordTrace tailWord_734327 prefixEnd_734327 335166852066003267498131 := by
  unfold tailWord_734327
  simp only [CollatzResearch.WordTrace]
  refine ⟨26783106010666166912065235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17855404007110777941376823 26783106010666166912065235)
  ·
    refine ⟨40174659015999250368097853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26783106010666166912065235 40174659015999250368097853)
    ·
      refine ⟨15065497130999718888036695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40174659015999250368097853 15065497130999718888036695)
      ·
        refine ⟨22598245696499578332055043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15065497130999718888036695 22598245696499578332055043)
        ·
          refine ⟨33897368544749367498082565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22598245696499578332055043 33897368544749367498082565)
          ·
            refine ⟨6355756602140506405890481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33897368544749367498082565 6355756602140506405890481)
            ·
              refine ⟨4766817451605379804417861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6355756602140506405890481 4766817451605379804417861)
              ·
                refine ⟨893778272176008713328349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4766817451605379804417861 893778272176008713328349)
                ·
                  refine ⟨335166852066003267498131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 893778272176008713328349 335166852066003267498131)
                  ·
                    rfl

theorem cell20_734327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 4, 3].length) (baseStart_734327 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_734327 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_734327 prefixEnd_734327 := by exact prefixLift 734327
  have htrace : WordTrace (prefixWord ++ tailWord_734327) baseStart_734327 baseEnd_734327 := by
    simpa [prefixWord, tailWord_734327, baseEnd_734327] using wordTrace_append hprefix tailTrace_734327
  have hstable : (prefixWord ++ tailWord_734327).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734327).length < 2 ^ (prefixWord ++ tailWord_734327).sum := by decide
  have hdescent : baseEnd_734327 < baseStart_734327 := by decide
  rcases family_descends (prefixWord ++ tailWord_734327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734381 : List Nat := [1, 5, 2, 1, 4, 1, 2, 2, 2]
def baseStart_734381 : Nat := 118140960795 + 734381 * 2 ^ 59
def prefixEnd_734381 : Nat := 4983230072969 + 3 ^ 40 * 734381 * 2
def baseEnd_734381 : Nat := 335191499137419079697911

theorem tailTrace_734381 : CollatzResearch.WordTrace tailWord_734381 prefixEnd_734381 335191499137419079697911 := by
  unfold tailWord_734381
  simp only [CollatzResearch.WordTrace]
  refine ⟨26785075552470534134530997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17856717034980356089687331 26785075552470534134530997)
  ·
    refine ⟨2511100833044112575112281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26785075552470534134530997 2511100833044112575112281)
    ·
      refine ⟨1883325624783084431334211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2511100833044112575112281 1883325624783084431334211)
      ·
        refine ⟨2824988437174626647001317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1883325624783084431334211 2824988437174626647001317)
        ·
          refine ⟨529685331970242496312747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2824988437174626647001317 529685331970242496312747)
          ·
            refine ⟨794527997955363744469121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 529685331970242496312747 794527997955363744469121)
            ·
              refine ⟨595895998466522808351841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 794527997955363744469121 595895998466522808351841)
              ·
                refine ⟨446921998849892106263881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 595895998466522808351841 446921998849892106263881)
                ·
                  refine ⟨335191499137419079697911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 446921998849892106263881 335191499137419079697911)
                  ·
                    rfl

theorem cell20_734381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 2, 2, 2].length) (baseStart_734381 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_734381 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_734381 prefixEnd_734381 := by exact prefixLift 734381
  have htrace : WordTrace (prefixWord ++ tailWord_734381) baseStart_734381 baseEnd_734381 := by
    simpa [prefixWord, tailWord_734381, baseEnd_734381] using wordTrace_append hprefix tailTrace_734381
  have hstable : (prefixWord ++ tailWord_734381).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734381).length < 2 ^ (prefixWord ++ tailWord_734381).sum := by decide
  have hdescent : baseEnd_734381 < baseStart_734381 := by decide
  rcases family_descends (prefixWord ++ tailWord_734381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734385 : List Nat := [1, 2, 2, 5, 1, 1, 4, 2, 2]
def baseStart_734385 : Nat := 118140960795 + 734385 * 2 ^ 59
def prefixEnd_734385 : Nat := 4983230072969 + 3 ^ 40 * 734385 * 2
def baseEnd_734385 : Nat := 335193324846412843564561

theorem tailTrace_734385 : CollatzResearch.WordTrace tailWord_734385 prefixEnd_734385 335193324846412843564561 := by
  unfold tailWord_734385
  simp only [CollatzResearch.WordTrace]
  refine ⟨26785221444456042817676609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17856814296304028545117739 26785221444456042817676609)
  ·
    refine ⟨20088916083342032113257457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26785221444456042817676609 20088916083342032113257457)
    ·
      refine ⟨15066687062506524084943093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20088916083342032113257457 15066687062506524084943093)
      ·
        refine ⟨1412501912109986632963415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15066687062506524084943093 1412501912109986632963415)
        ·
          refine ⟨2118752868164979949445123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1412501912109986632963415 2118752868164979949445123)
          ·
            refine ⟨3178129302247469924167685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2118752868164979949445123 3178129302247469924167685)
            ·
              refine ⟨595899244171400610781441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3178129302247469924167685 595899244171400610781441)
              ·
                refine ⟨446924433128550458086081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 595899244171400610781441 446924433128550458086081)
                ·
                  refine ⟨335193324846412843564561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 446924433128550458086081 335193324846412843564561)
                  ·
                    rfl

theorem cell20_734385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 4, 2, 2].length) (baseStart_734385 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_734385 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_734385 prefixEnd_734385 := by exact prefixLift 734385
  have htrace : WordTrace (prefixWord ++ tailWord_734385) baseStart_734385 baseEnd_734385 := by
    simpa [prefixWord, tailWord_734385, baseEnd_734385] using wordTrace_append hprefix tailTrace_734385
  have hstable : (prefixWord ++ tailWord_734385).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734385).length < 2 ^ (prefixWord ++ tailWord_734385).sum := by decide
  have hdescent : baseEnd_734385 < baseStart_734385 := by decide
  rcases family_descends (prefixWord ++ tailWord_734385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734396 : List Nat := [2, 2, 2, 3, 2, 1, 3, 5]
def baseStart_734396 : Nat := 118140960795 + 734396 * 2 ^ 59
def prefixEnd_734396 : Nat := 4983230072969 + 3 ^ 40 * 734396 * 2
def baseEnd_734396 : Nat := 111732781848715231399283

theorem tailTrace_734396 : CollatzResearch.WordTrace tailWord_734396 prefixEnd_734396 111732781848715231399283 := by
  unfold tailWord_734396
  simp only [CollatzResearch.WordTrace]
  refine ⟨13392811323708095848163521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17857081764944127797551361 13392811323708095848163521)
  ·
    refine ⟨10044608492781071886122641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13392811323708095848163521 10044608492781071886122641)
    ·
      refine ⟨7533456369585803914591981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10044608492781071886122641 7533456369585803914591981)
      ·
        refine ⟨2825046138594676467971993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7533456369585803914591981 2825046138594676467971993)
        ·
          refine ⟨2118784603946007350978995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2825046138594676467971993 2118784603946007350978995)
          ·
            refine ⟨3178176905919011026468493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2118784603946007350978995 3178176905919011026468493)
            ·
              refine ⟨1191816339719629134925685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3178176905919011026468493 1191816339719629134925685)
              ·
                refine ⟨111732781848715231399283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1191816339719629134925685 111732781848715231399283)
                ·
                  rfl

theorem cell20_734396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 5].length) (baseStart_734396 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_734396 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_734396 prefixEnd_734396 := by exact prefixLift 734396
  have htrace : WordTrace (prefixWord ++ tailWord_734396) baseStart_734396 baseEnd_734396 := by
    simpa [prefixWord, tailWord_734396, baseEnd_734396] using wordTrace_append hprefix tailTrace_734396
  have hstable : (prefixWord ++ tailWord_734396).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734396).length < 2 ^ (prefixWord ++ tailWord_734396).sum := by decide
  have hdescent : baseEnd_734396 < baseStart_734396 := by decide
  rcases family_descends (prefixWord ++ tailWord_734396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734410 : List Nat := [3, 1, 2, 1, 3, 2, 1, 1, 6]
def baseStart_734410 : Nat := 118140960795 + 734410 * 2 ^ 59
def prefixEnd_734410 : Nat := 4983230072969 + 3 ^ 40 * 734410 * 2
def baseEnd_734410 : Nat := 335204735527623867731125

theorem tailTrace_734410 : CollatzResearch.WordTrace tailWord_734410 prefixEnd_734410 335204735527623867731125 := by
  unfold tailWord_734410
  simp only [CollatzResearch.WordTrace]
  refine ⟨6696533317341368021834171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17857422179576981391557789 6696533317341368021834171)
  ·
    refine ⟨10044799976012052032751257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6696533317341368021834171 10044799976012052032751257)
    ·
      refine ⟨7533599982009039024563443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10044799976012052032751257 7533599982009039024563443)
      ·
        refine ⟨11300399973013558536845165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7533599982009039024563443 11300399973013558536845165)
        ·
          refine ⟨4237649989880084451316937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11300399973013558536845165 4237649989880084451316937)
          ·
            refine ⟨3178237492410063338487703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4237649989880084451316937 3178237492410063338487703)
            ·
              refine ⟨4767356238615095007731555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3178237492410063338487703 4767356238615095007731555)
              ·
                refine ⟨7151034357922642511597333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4767356238615095007731555 7151034357922642511597333)
                ·
                  refine ⟨335204735527623867731125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7151034357922642511597333 335204735527623867731125)
                  ·
                    rfl

theorem cell20_734410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 6].length) (baseStart_734410 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_734410 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_734410 prefixEnd_734410 := by exact prefixLift 734410
  have htrace : WordTrace (prefixWord ++ tailWord_734410) baseStart_734410 baseEnd_734410 := by
    simpa [prefixWord, tailWord_734410, baseEnd_734410] using wordTrace_append hprefix tailTrace_734410
  have hstable : (prefixWord ++ tailWord_734410).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734410).length < 2 ^ (prefixWord ++ tailWord_734410).sum := by decide
  have hdescent : baseEnd_734410 < baseStart_734410 := by decide
  rcases family_descends (prefixWord ++ tailWord_734410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734437 : List Nat := [1, 3, 1, 4, 3, 2, 1, 2, 3]
def baseStart_734437 : Nat := 118140960795 + 734437 * 2 ^ 59
def prefixEnd_734437 : Nat := 4983230072969 + 3 ^ 40 * 734437 * 2
def baseEnd_734437 : Nat := 335217059063331773831015

theorem tailTrace_734437 : CollatzResearch.WordTrace tailWord_734437 prefixEnd_734437 335217059063331773831015 := by
  unfold tailWord_734437
  simp only [CollatzResearch.WordTrace]
  refine ⟨26787118040267655698569565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17858078693511770465713043 26787118040267655698569565)
  ·
    refine ⟨10045169265100370886963587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26787118040267655698569565 10045169265100370886963587)
    ·
      refine ⟨15067753897650556330445381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10045169265100370886963587 15067753897650556330445381)
      ·
        refine ⟨2825203855809479311958509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15067753897650556330445381 2825203855809479311958509)
        ·
          refine ⟨1059451445928554741984441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2825203855809479311958509 1059451445928554741984441)
          ·
            refine ⟨794588584446416056488331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1059451445928554741984441 794588584446416056488331)
            ·
              refine ⟨1191882876669624084732497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 794588584446416056488331 1191882876669624084732497)
              ·
                refine ⟨893912157502218063549373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1191882876669624084732497 893912157502218063549373)
                ·
                  refine ⟨335217059063331773831015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 893912157502218063549373 335217059063331773831015)
                  ·
                    rfl

theorem cell20_734437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 2, 3].length) (baseStart_734437 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_734437 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_734437 prefixEnd_734437 := by exact prefixLift 734437
  have htrace : WordTrace (prefixWord ++ tailWord_734437) baseStart_734437 baseEnd_734437 := by
    simpa [prefixWord, tailWord_734437, baseEnd_734437] using wordTrace_append hprefix tailTrace_734437
  have hstable : (prefixWord ++ tailWord_734437).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734437).length < 2 ^ (prefixWord ++ tailWord_734437).sum := by decide
  have hdescent : baseEnd_734437 < baseStart_734437 := by decide
  rcases family_descends (prefixWord ++ tailWord_734437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734458 : List Nat := [3, 1, 1, 1, 1, 4, 5, 1, 3]
def baseStart_734458 : Nat := 118140960795 + 734458 * 2 ^ 59
def prefixEnd_734458 : Nat := 4983230072969 + 3 ^ 40 * 734458 * 2
def baseEnd_734458 : Nat := 335226644035549034130929

theorem tailTrace_734458 : CollatzResearch.WordTrace tailWord_734458 prefixEnd_734458 335226644035549034130929 := by
  unfold tailWord_734458
  simp only [CollatzResearch.WordTrace]
  refine ⟨6696970993297894071271007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17858589315461050856722685 6696970993297894071271007)
  ·
    refine ⟨10045456489946841106906511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6696970993297894071271007 10045456489946841106906511)
    ·
      refine ⟨15068184734920261660359767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10045456489946841106906511 15068184734920261660359767)
      ·
        refine ⟨22602277102380392490539651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15068184734920261660359767 22602277102380392490539651)
        ·
          refine ⟨33903415653570588735809477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22602277102380392490539651 33903415653570588735809477)
          ·
            refine ⟨6356890435044485387964277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33903415653570588735809477 6356890435044485387964277)
            ·
              refine ⟨595958478285420505121651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6356890435044485387964277 595958478285420505121651)
              ·
                refine ⟨893937717428130757682477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 595958478285420505121651 893937717428130757682477)
                ·
                  refine ⟨335226644035549034130929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 893937717428130757682477 335226644035549034130929)
                  ·
                    rfl

theorem cell20_734458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 5, 1, 3].length) (baseStart_734458 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_734458 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_734458 prefixEnd_734458 := by exact prefixLift 734458
  have htrace : WordTrace (prefixWord ++ tailWord_734458) baseStart_734458 baseEnd_734458 := by
    simpa [prefixWord, tailWord_734458, baseEnd_734458] using wordTrace_append hprefix tailTrace_734458
  have hstable : (prefixWord ++ tailWord_734458).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734458).length < 2 ^ (prefixWord ++ tailWord_734458).sum := by decide
  have hdescent : baseEnd_734458 < baseStart_734458 := by decide
  rcases family_descends (prefixWord ++ tailWord_734458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734472 : List Nat := [2, 1, 3, 2, 4, 1, 1, 6]
def baseStart_734472 : Nat := 118140960795 + 734472 * 2 ^ 59
def prefixEnd_734472 : Nat := 4983230072969 + 3 ^ 40 * 734472 * 2
def baseEnd_734472 : Nat := 111744344672342402554735

theorem tailTrace_734472 : CollatzResearch.WordTrace tailWord_734472 prefixEnd_734472 111744344672342402554735 := by
  unfold tailWord_734472
  simp only [CollatzResearch.WordTrace]
  refine ⟨13394197297570428338046835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17858929730093904450729113 13394197297570428338046835)
  ·
    refine ⟨20091295946355642507070253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13394197297570428338046835 20091295946355642507070253)
    ·
      refine ⟨7534235979883365940151345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20091295946355642507070253 7534235979883365940151345)
      ·
        refine ⟨5650676984912524455113509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7534235979883365940151345 5650676984912524455113509)
        ·
          refine ⟨1059501934671098335333783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5650676984912524455113509 1059501934671098335333783)
          ·
            refine ⟨1589252902006647503000675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1059501934671098335333783 1589252902006647503000675)
            ·
              refine ⟨2383879353009971254501013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1589252902006647503000675 2383879353009971254501013)
              ·
                refine ⟨111744344672342402554735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2383879353009971254501013 111744344672342402554735)
                ·
                  rfl

theorem cell20_734472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 6].length) (baseStart_734472 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_734472 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_734472 prefixEnd_734472 := by exact prefixLift 734472
  have htrace : WordTrace (prefixWord ++ tailWord_734472) baseStart_734472 baseEnd_734472 := by
    simpa [prefixWord, tailWord_734472, baseEnd_734472] using wordTrace_append hprefix tailTrace_734472
  have hstable : (prefixWord ++ tailWord_734472).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734472).length < 2 ^ (prefixWord ++ tailWord_734472).sum := by decide
  have hdescent : baseEnd_734472 < baseStart_734472 := by decide
  rcases family_descends (prefixWord ++ tailWord_734472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734507 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 10]
def baseStart_734507 : Nat := 118140960795 + 734507 * 2 ^ 59
def prefixEnd_734507 : Nat := 4983230072969 + 3 ^ 40 * 734507 * 2
def baseEnd_734507 : Nat := 335249008970722641497395

theorem tailTrace_734507 : CollatzResearch.WordTrace tailWord_734507 prefixEnd_734507 335249008970722641497395 := by
  unfold tailWord_734507
  simp only [CollatzResearch.WordTrace]
  refine ⟨26789671150014057653617775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17859780766676038435745183 26789671150014057653617775)
  ·
    refine ⟨40184506725021086480426663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26789671150014057653617775 40184506725021086480426663)
    ·
      refine ⟨60276760087531629720639995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40184506725021086480426663 60276760087531629720639995)
      ·
        refine ⟨90415140131297444580959993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60276760087531629720639995 90415140131297444580959993)
        ·
          refine ⟨67811355098473083435719995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90415140131297444580959993 67811355098473083435719995)
          ·
            refine ⟨101717032647709625153579993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67811355098473083435719995 101717032647709625153579993)
            ·
              refine ⟨76287774485782218865184995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101717032647709625153579993 76287774485782218865184995)
              ·
                refine ⟨114431661728673328297777493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76287774485782218865184995 114431661728673328297777493)
                ·
                  refine ⟨335249008970722641497395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 114431661728673328297777493 335249008970722641497395)
                  ·
                    rfl

theorem cell20_734507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 10].length) (baseStart_734507 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_734507 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_734507 prefixEnd_734507 := by exact prefixLift 734507
  have htrace : WordTrace (prefixWord ++ tailWord_734507) baseStart_734507 baseEnd_734507 := by
    simpa [prefixWord, tailWord_734507, baseEnd_734507] using wordTrace_append hprefix tailTrace_734507
  have hstable : (prefixWord ++ tailWord_734507).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734507).length < 2 ^ (prefixWord ++ tailWord_734507).sum := by decide
  have hdescent : baseEnd_734507 < baseStart_734507 := by decide
  rcases family_descends (prefixWord ++ tailWord_734507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734513 : List Nat := [1, 2, 2, 3, 3, 3, 2, 1, 3]
def baseStart_734513 : Nat := 118140960795 + 734513 * 2 ^ 59
def prefixEnd_734513 : Nat := 4983230072969 + 3 ^ 40 * 734513 * 2
def baseEnd_734513 : Nat := 335251747534213287297371

theorem tailTrace_734513 : CollatzResearch.WordTrace tailWord_734513 prefixEnd_734513 335251747534213287297371 := by
  unfold tailWord_734513
  simp only [CollatzResearch.WordTrace]
  refine ⟨26789889987992320678336193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17859926658661547118890795 26789889987992320678336193)
  ·
    refine ⟨20092417490994240508752145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26789889987992320678336193 20092417490994240508752145)
    ·
      refine ⟨15069313118245680381564109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20092417490994240508752145 15069313118245680381564109)
      ·
        refine ⟨5650992419342130143086541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15069313118245680381564109 5650992419342130143086541)
        ·
          refine ⟨2119122157253298803657453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5650992419342130143086541 2119122157253298803657453)
          ·
            refine ⟨794670808969987051371545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2119122157253298803657453 794670808969987051371545)
            ·
              refine ⟨596003106727490288528659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 794670808969987051371545 596003106727490288528659)
              ·
                refine ⟨894004660091235432792989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 596003106727490288528659 894004660091235432792989)
                ·
                  refine ⟨335251747534213287297371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 894004660091235432792989 335251747534213287297371)
                  ·
                    rfl

theorem cell20_734513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 2, 1, 3].length) (baseStart_734513 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_734513 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_734513 prefixEnd_734513 := by exact prefixLift 734513
  have htrace : WordTrace (prefixWord ++ tailWord_734513) baseStart_734513 baseEnd_734513 := by
    simpa [prefixWord, tailWord_734513, baseEnd_734513] using wordTrace_append hprefix tailTrace_734513
  have hstable : (prefixWord ++ tailWord_734513).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734513).length < 2 ^ (prefixWord ++ tailWord_734513).sum := by decide
  have hdescent : baseEnd_734513 < baseStart_734513 := by decide
  rcases family_descends (prefixWord ++ tailWord_734513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734538 : List Nat := [3, 1, 2, 1, 1, 1, 1, 3, 7]
def baseStart_734538 : Nat := 118140960795 + 734538 * 2 ^ 59
def prefixEnd_734538 : Nat := 4983230072969 + 3 ^ 40 * 734538 * 2
def baseEnd_734538 : Nat := 335263158215424311463935

theorem tailTrace_734538 : CollatzResearch.WordTrace tailWord_734538 prefixEnd_734538 335263158215424311463935 := by
  unfold tailWord_734538
  simp only [CollatzResearch.WordTrace]
  refine ⟨6697700453225437486999067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17860534541934499965330845 6697700453225437486999067)
  ·
    refine ⟨10046550679838156230498601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6697700453225437486999067 10046550679838156230498601)
    ·
      refine ⟨7534913009878617172873951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10046550679838156230498601 7534913009878617172873951)
      ·
        refine ⟨11302369514817925759310927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7534913009878617172873951 11302369514817925759310927)
        ·
          refine ⟨16953554272226888638966391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11302369514817925759310927 16953554272226888638966391)
          ·
            refine ⟨25430331408340332958449587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16953554272226888638966391 25430331408340332958449587)
            ·
              refine ⟨38145497112510499437674381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25430331408340332958449587 38145497112510499437674381)
              ·
                refine ⟨14304561417191437289127893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38145497112510499437674381 14304561417191437289127893)
                ·
                  refine ⟨335263158215424311463935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14304561417191437289127893 335263158215424311463935)
                  ·
                    rfl

theorem cell20_734538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_734538 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_734538 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_734538 prefixEnd_734538 := by exact prefixLift 734538
  have htrace : WordTrace (prefixWord ++ tailWord_734538) baseStart_734538 baseEnd_734538 := by
    simpa [prefixWord, tailWord_734538, baseEnd_734538] using wordTrace_append hprefix tailTrace_734538
  have hstable : (prefixWord ++ tailWord_734538).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734538).length < 2 ^ (prefixWord ++ tailWord_734538).sum := by decide
  have hdescent : baseEnd_734538 < baseStart_734538 := by decide
  rcases family_descends (prefixWord ++ tailWord_734538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734596 : List Nat := [2, 3, 2, 1, 1, 4, 2, 3, 2]
def baseStart_734596 : Nat := 118140960795 + 734596 * 2 ^ 59
def prefixEnd_734596 : Nat := 4983230072969 + 3 ^ 40 * 734596 * 2
def baseEnd_734596 : Nat := 335289630995833887530365

theorem tailTrace_734596 : CollatzResearch.WordTrace tailWord_734596 prefixEnd_734596 335289630995833887530365 := by
  unfold tailWord_734596
  simp only [CollatzResearch.WordTrace]
  refine ⟨13396458623345812926803821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17861944831127750569071761 13396458623345812926803821)
  ·
    refine ⟨5023671983754679847551433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13396458623345812926803821 5023671983754679847551433)
    ·
      refine ⟨3767753987816009885663575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5023671983754679847551433 3767753987816009885663575)
      ·
        refine ⟨5651630981724014828495363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3767753987816009885663575 5651630981724014828495363)
        ·
          refine ⟨8477446472586022242743045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5651630981724014828495363 8477446472586022242743045)
          ·
            refine ⟨1589521213609879170514321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8477446472586022242743045 1589521213609879170514321)
            ·
              refine ⟨1192140910207409377885741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1589521213609879170514321 1192140910207409377885741)
              ·
                refine ⟨447052841327778516707153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1192140910207409377885741 447052841327778516707153)
                ·
                  refine ⟨335289630995833887530365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 447052841327778516707153 335289630995833887530365)
                  ·
                    rfl

theorem cell20_734596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 3, 2].length) (baseStart_734596 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_734596 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_734596 prefixEnd_734596 := by exact prefixLift 734596
  have htrace : WordTrace (prefixWord ++ tailWord_734596) baseStart_734596 baseEnd_734596 := by
    simpa [prefixWord, tailWord_734596, baseEnd_734596] using wordTrace_append hprefix tailTrace_734596
  have hstable : (prefixWord ++ tailWord_734596).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734596).length < 2 ^ (prefixWord ++ tailWord_734596).sum := by decide
  have hdescent : baseEnd_734596 < baseStart_734596 := by decide
  rcases family_descends (prefixWord ++ tailWord_734596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734606 : List Nat := [4, 1, 1, 4, 3, 1, 1, 2, 3]
def baseStart_734606 : Nat := 118140960795 + 734606 * 2 ^ 59
def prefixEnd_734606 : Nat := 4983230072969 + 3 ^ 40 * 734606 * 2
def baseEnd_734606 : Nat := 335294195268318297196991

theorem tailTrace_734606 : CollatzResearch.WordTrace tailWord_734606 prefixEnd_734606 335294195268318297196991 := by
  unfold tailWord_734606
  simp only [CollatzResearch.WordTrace]
  refine ⟨3349160247081924695183959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17862187984436931707647781 3349160247081924695183959)
  ·
    refine ⟨5023740370622887042775939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3349160247081924695183959 5023740370622887042775939)
    ·
      refine ⟨7535610555934330564163909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5023740370622887042775939 7535610555934330564163909)
      ·
        refine ⟨1412926979237686980780733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7535610555934330564163909 1412926979237686980780733)
        ·
          refine ⟨529847617214132617792775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1412926979237686980780733 529847617214132617792775)
          ·
            refine ⟨794771425821198926689163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 529847617214132617792775 794771425821198926689163)
            ·
              refine ⟨1192157138731798390033745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 794771425821198926689163 1192157138731798390033745)
              ·
                refine ⟨894117854048848792525309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1192157138731798390033745 894117854048848792525309)
                ·
                  refine ⟨335294195268318297196991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 894117854048848792525309 335294195268318297196991)
                  ·
                    rfl

theorem cell20_734606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 2, 3].length) (baseStart_734606 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_734606 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_734606 prefixEnd_734606 := by exact prefixLift 734606
  have htrace : WordTrace (prefixWord ++ tailWord_734606) baseStart_734606 baseEnd_734606 := by
    simpa [prefixWord, tailWord_734606, baseEnd_734606] using wordTrace_append hprefix tailTrace_734606
  have hstable : (prefixWord ++ tailWord_734606).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734606).length < 2 ^ (prefixWord ++ tailWord_734606).sum := by decide
  have hdescent : baseEnd_734606 < baseStart_734606 := by decide
  rcases family_descends (prefixWord ++ tailWord_734606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734617 : List Nat := [1, 2, 1, 2, 1, 5, 2, 4, 2]
def baseStart_734617 : Nat := 118140960795 + 734617 * 2 ^ 59
def prefixEnd_734617 : Nat := 4983230072969 + 3 ^ 40 * 734617 * 2
def baseEnd_734617 : Nat := 335299215968051147830279

theorem tailTrace_734617 : CollatzResearch.WordTrace tailWord_734617 prefixEnd_734617 335299215968051147830279 := by
  unfold tailWord_734617
  simp only [CollatzResearch.WordTrace]
  refine ⟨26793683179615546440122105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17862455453077030960081403 26793683179615546440122105)
  ·
    refine ⟨20095262384711659830091579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26793683179615546440122105 20095262384711659830091579)
    ·
      refine ⟨30142893577067489745137369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20095262384711659830091579 30142893577067489745137369)
      ·
        refine ⟨22607170182800617308853027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30142893577067489745137369 22607170182800617308853027)
        ·
          refine ⟨33910755274200925963279541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22607170182800617308853027 33910755274200925963279541)
          ·
            refine ⟨3179133306956336809057457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33910755274200925963279541 3179133306956336809057457)
            ·
              refine ⟨2384349980217252606793093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3179133306956336809057457 2384349980217252606793093)
              ·
                refine ⟨447065621290734863773705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2384349980217252606793093 447065621290734863773705)
                ·
                  refine ⟨335299215968051147830279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 447065621290734863773705 335299215968051147830279)
                  ·
                    rfl

theorem cell20_734617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 4, 2].length) (baseStart_734617 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_734617 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_734617 prefixEnd_734617 := by exact prefixLift 734617
  have htrace : WordTrace (prefixWord ++ tailWord_734617) baseStart_734617 baseEnd_734617 := by
    simpa [prefixWord, tailWord_734617, baseEnd_734617] using wordTrace_append hprefix tailTrace_734617
  have hstable : (prefixWord ++ tailWord_734617).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734617).length < 2 ^ (prefixWord ++ tailWord_734617).sum := by decide
  have hdescent : baseEnd_734617 < baseStart_734617 := by decide
  rcases family_descends (prefixWord ++ tailWord_734617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734659 : List Nat := [1, 1, 1, 3, 1, 1, 4, 2, 6]
def baseStart_734659 : Nat := 118140960795 + 734659 * 2 ^ 59
def prefixEnd_734659 : Nat := 4983230072969 + 3 ^ 40 * 734659 * 2
def baseEnd_734659 : Nat := 335318385912485668430107

theorem tailTrace_734659 : CollatzResearch.WordTrace tailWord_734659 prefixEnd_734659 335318385912485668430107 := by
  unfold tailWord_734659
  simp only [CollatzResearch.WordTrace]
  refine ⟨26795215045463387613151031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17863476696975591742100687 26795215045463387613151031)
  ·
    refine ⟨40192822568195081419726547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26795215045463387613151031 40192822568195081419726547)
    ·
      refine ⟨60289233852292622129589821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40192822568195081419726547 60289233852292622129589821)
      ·
        refine ⟨22608462694609733298596183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60289233852292622129589821 22608462694609733298596183)
        ·
          refine ⟨33912694041914599947894275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22608462694609733298596183 33912694041914599947894275)
          ·
            refine ⟨50869041062871899921841413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33912694041914599947894275 50869041062871899921841413)
            ·
              refine ⟨9537945199288481235345265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50869041062871899921841413 9537945199288481235345265)
              ·
                refine ⟨7153458899466360926508949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9537945199288481235345265 7153458899466360926508949)
                ·
                  refine ⟨335318385912485668430107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7153458899466360926508949 335318385912485668430107)
                  ·
                    rfl

theorem cell20_734659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 6].length) (baseStart_734659 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_734659 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_734659 prefixEnd_734659 := by exact prefixLift 734659
  have htrace : WordTrace (prefixWord ++ tailWord_734659) baseStart_734659 baseEnd_734659 := by
    simpa [prefixWord, tailWord_734659, baseEnd_734659] using wordTrace_append hprefix tailTrace_734659
  have hstable : (prefixWord ++ tailWord_734659).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734659).length < 2 ^ (prefixWord ++ tailWord_734659).sum := by decide
  have hdescent : baseEnd_734659 < baseStart_734659 := by decide
  rcases family_descends (prefixWord ++ tailWord_734659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734721 : List Nat := [1, 2, 4, 1, 4, 8]
def baseStart_734721 : Nat := 118140960795 + 734721 * 2 ^ 59
def prefixEnd_734721 : Nat := 4983230072969 + 3 ^ 40 * 734721 * 2
def baseEnd_734721 : Nat := 12420247570440333643081

theorem tailTrace_734721 : CollatzResearch.WordTrace tailWord_734721 prefixEnd_734721 12420247570440333643081 := by
  unfold tailWord_734721
  simp only [CollatzResearch.WordTrace]
  refine ⟨26797476371238772201908017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17864984247492514801272011 26797476371238772201908017)
  ·
    refine ⟨20098107278429079151431013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26797476371238772201908017 20098107278429079151431013)
    ·
      refine ⟨3768395114705452340893315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20098107278429079151431013 3768395114705452340893315)
      ·
        refine ⟨5652592672058178511339973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3768395114705452340893315 5652592672058178511339973)
        ·
          refine ⟨1059861126010908470876245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5652592672058178511339973 1059861126010908470876245)
          ·
            refine ⟨12420247570440333643081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1059861126010908470876245 12420247570440333643081)
            ·
              rfl

theorem cell20_734721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 8].length) (baseStart_734721 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_734721 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_734721 prefixEnd_734721 := by exact prefixLift 734721
  have htrace : WordTrace (prefixWord ++ tailWord_734721) baseStart_734721 baseEnd_734721 := by
    simpa [prefixWord, tailWord_734721, baseEnd_734721] using wordTrace_append hprefix tailTrace_734721
  have hstable : (prefixWord ++ tailWord_734721).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734721).length < 2 ^ (prefixWord ++ tailWord_734721).sum := by decide
  have hdescent : baseEnd_734721 < baseStart_734721 := by decide
  rcases family_descends (prefixWord ++ tailWord_734721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734727 : List Nat := [1, 1, 4, 3, 2, 3, 2, 2, 2]
def baseStart_734727 : Nat := 118140960795 + 734727 * 2 ^ 59
def prefixEnd_734727 : Nat := 4983230072969 + 3 ^ 40 * 734727 * 2
def baseEnd_734727 : Nat := 335349422965379654163163

theorem tailTrace_734727 : CollatzResearch.WordTrace tailWord_734727 prefixEnd_734727 335349422965379654163163 := by
  unfold tailWord_734727
  simp only [CollatzResearch.WordTrace]
  refine ⟨26797695209217035226626435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17865130139478023484417623 26797695209217035226626435)
  ·
    refine ⟨40196542813825552839939653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26797695209217035226626435 40196542813825552839939653)
    ·
      refine ⟨7536851777592291157488685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40196542813825552839939653 7536851777592291157488685)
      ·
        refine ⟨2826319416597109184058257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7536851777592291157488685 2826319416597109184058257)
        ·
          refine ⟨2119739562447831888043693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2826319416597109184058257 2119739562447831888043693)
          ·
            refine ⟨794902335917936958016385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2119739562447831888043693 794902335917936958016385)
            ·
              refine ⟨596176751938452718512289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 794902335917936958016385 596176751938452718512289)
              ·
                refine ⟨447132563953839538884217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 596176751938452718512289 447132563953839538884217)
                ·
                  refine ⟨335349422965379654163163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 447132563953839538884217 335349422965379654163163)
                  ·
                    rfl

theorem cell20_734727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 2, 2, 2].length) (baseStart_734727 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_734727 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_734727 prefixEnd_734727 := by exact prefixLift 734727
  have htrace : WordTrace (prefixWord ++ tailWord_734727) baseStart_734727 baseEnd_734727 := by
    simpa [prefixWord, tailWord_734727, baseEnd_734727] using wordTrace_append hprefix tailTrace_734727
  have hstable : (prefixWord ++ tailWord_734727).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734727).length < 2 ^ (prefixWord ++ tailWord_734727).sum := by decide
  have hdescent : baseEnd_734727 < baseStart_734727 := by decide
  rcases family_descends (prefixWord ++ tailWord_734727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734728 : List Nat := [2, 1, 3, 2, 1, 1, 2, 3, 5]
def baseStart_734728 : Nat := 118140960795 + 734728 * 2 ^ 59
def prefixEnd_734728 : Nat := 4983230072969 + 3 ^ 40 * 734728 * 2
def baseEnd_734728 : Nat := 335349879392628095129825

theorem tailTrace_734728 : CollatzResearch.WordTrace tailWord_734728 prefixEnd_734728 335349879392628095129825 := by
  unfold tailWord_734728
  simp only [CollatzResearch.WordTrace]
  refine ⟨13398865841106706198706419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17865154454808941598275225 13398865841106706198706419)
  ·
    refine ⟨20098298761660059298059629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13398865841106706198706419 20098298761660059298059629)
    ·
      refine ⟨7536862035622522236772361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20098298761660059298059629 7536862035622522236772361)
      ·
        refine ⟨5652646526716891677579271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7536862035622522236772361 5652646526716891677579271)
        ·
          refine ⟨8478969790075337516368907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5652646526716891677579271 8478969790075337516368907)
          ·
            refine ⟨12718454685113006274553361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8478969790075337516368907 12718454685113006274553361)
            ·
              refine ⟨9538841013834754705915021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12718454685113006274553361 9538841013834754705915021)
              ·
                refine ⟨3577065380188033014718133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9538841013834754705915021 3577065380188033014718133)
                ·
                  refine ⟨335349879392628095129825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3577065380188033014718133 335349879392628095129825)
                  ·
                    rfl

theorem cell20_734728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 5].length) (baseStart_734728 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_734728 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_734728 prefixEnd_734728 := by exact prefixLift 734728
  have htrace : WordTrace (prefixWord ++ tailWord_734728) baseStart_734728 baseEnd_734728 := by
    simpa [prefixWord, tailWord_734728, baseEnd_734728] using wordTrace_append hprefix tailTrace_734728
  have hstable : (prefixWord ++ tailWord_734728).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734728).length < 2 ^ (prefixWord ++ tailWord_734728).sum := by decide
  have hdescent : baseEnd_734728 < baseStart_734728 := by decide
  rcases family_descends (prefixWord ++ tailWord_734728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734752 : List Nat := [2, 1, 1, 6, 1, 1, 1, 1, 6]
def baseStart_734752 : Nat := 118140960795 + 734752 * 2 ^ 59
def prefixEnd_734752 : Nat := 4983230072969 + 3 ^ 40 * 734752 * 2
def baseEnd_734752 : Nat := 335360833646590678329727

theorem tailTrace_734752 : CollatzResearch.WordTrace tailWord_734752 prefixEnd_734752 335360833646590678329727 := by
  unfold tailWord_734752
  simp only [CollatzResearch.WordTrace]
  refine ⟨13399303517063232248143255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17865738022750976330857673 13399303517063232248143255)
  ·
    refine ⟨20098955275594848372214883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13399303517063232248143255 20098955275594848372214883)
    ·
      refine ⟨30148432913392272558322325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20098955275594848372214883 30148432913392272558322325)
      ·
        refine ⟨1413207792815262776171359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 30148432913392272558322325 1413207792815262776171359)
        ·
          refine ⟨2119811689222894164257039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1413207792815262776171359 2119811689222894164257039)
          ·
            refine ⟨3179717533834341246385559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2119811689222894164257039 3179717533834341246385559)
            ·
              refine ⟨4769576300751511869578339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3179717533834341246385559 4769576300751511869578339)
              ·
                refine ⟨7154364451127267804367509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4769576300751511869578339 7154364451127267804367509)
                ·
                  refine ⟨335360833646590678329727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7154364451127267804367509 335360833646590678329727)
                  ·
                    rfl

theorem cell20_734752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 6].length) (baseStart_734752 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_734752 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_734752 prefixEnd_734752 := by exact prefixLift 734752
  have htrace : WordTrace (prefixWord ++ tailWord_734752) baseStart_734752 baseEnd_734752 := by
    simpa [prefixWord, tailWord_734752, baseEnd_734752] using wordTrace_append hprefix tailTrace_734752
  have hstable : (prefixWord ++ tailWord_734752).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734752).length < 2 ^ (prefixWord ++ tailWord_734752).sum := by decide
  have hdescent : baseEnd_734752 < baseStart_734752 := by decide
  rcases family_descends (prefixWord ++ tailWord_734752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734783 : List Nat := [1, 1, 2, 2, 3, 3, 3, 2, 3]
def baseStart_734783 : Nat := 118140960795 + 734783 * 2 ^ 59
def prefixEnd_734783 : Nat := 4983230072969 + 3 ^ 40 * 734783 * 2
def baseEnd_734783 : Nat := 335374982891292348296267

theorem tailTrace_734783 : CollatzResearch.WordTrace tailWord_734783 prefixEnd_734783 335374982891292348296267 := by
  unfold tailWord_734783
  simp only [CollatzResearch.WordTrace]
  refine ⟨26799737697014156790665003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17866491798009437860443335 26799737697014156790665003)
  ·
    refine ⟨40199606545521235185997505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26799737697014156790665003 40199606545521235185997505)
    ·
      refine ⟨30149704909140926389498129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40199606545521235185997505 30149704909140926389498129)
      ·
        refine ⟨22612278681855694792123597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30149704909140926389498129 22612278681855694792123597)
        ·
          refine ⟨8479604505695885547046349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22612278681855694792123597 8479604505695885547046349)
          ·
            refine ⟨3179851689635957080142381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8479604505695885547046349 3179851689635957080142381)
            ·
              refine ⟨1192444383613483905053393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3179851689635957080142381 1192444383613483905053393)
              ·
                refine ⟨894333287710112928790045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1192444383613483905053393 894333287710112928790045)
                ·
                  refine ⟨335374982891292348296267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 894333287710112928790045 335374982891292348296267)
                  ·
                    rfl

theorem cell20_734783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 2, 3].length) (baseStart_734783 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_734783 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_734783 prefixEnd_734783 := by exact prefixLift 734783
  have htrace : WordTrace (prefixWord ++ tailWord_734783) baseStart_734783 baseEnd_734783 := by
    simpa [prefixWord, tailWord_734783, baseEnd_734783] using wordTrace_append hprefix tailTrace_734783
  have hstable : (prefixWord ++ tailWord_734783).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734783).length < 2 ^ (prefixWord ++ tailWord_734783).sum := by decide
  have hdescent : baseEnd_734783 < baseStart_734783 := by decide
  rcases family_descends (prefixWord ++ tailWord_734783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734806 : List Nat := [5, 2, 2, 2, 2, 1, 2, 4]
def baseStart_734806 : Nat := 118140960795 + 734806 * 2 ^ 59
def prefixEnd_734806 : Nat := 4983230072969 + 3 ^ 40 * 734806 * 2
def baseEnd_734806 : Nat := 111795160239335496843169

theorem tailTrace_734806 : CollatzResearch.WordTrace tailWord_734806 prefixEnd_734806 111795160239335496843169 := by
  unfold tailWord_734806
  simp only [CollatzResearch.WordTrace]
  refine ⟨1675036035995676982422017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17867051050620554479168181 1675036035995676982422017)
  ·
    refine ⟨1256277026996757736816513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1675036035995676982422017 1256277026996757736816513)
    ·
      refine ⟨942207770247568302612385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1256277026996757736816513 942207770247568302612385)
      ·
        refine ⟨706655827685676226959289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 942207770247568302612385 706655827685676226959289)
        ·
          refine ⟨529991870764257170219467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 706655827685676226959289 529991870764257170219467)
          ·
            refine ⟨794987806146385755329201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 529991870764257170219467 794987806146385755329201)
            ·
              refine ⟨596240854609789316496901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 794987806146385755329201 596240854609789316496901)
              ·
                refine ⟨111795160239335496843169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 596240854609789316496901 111795160239335496843169)
                ·
                  rfl

theorem cell20_734806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_734806 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_734806 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_734806 prefixEnd_734806 := by exact prefixLift 734806
  have htrace : WordTrace (prefixWord ++ tailWord_734806) baseStart_734806 baseEnd_734806 := by
    simpa [prefixWord, tailWord_734806, baseEnd_734806] using wordTrace_append hprefix tailTrace_734806
  have hstable : (prefixWord ++ tailWord_734806).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734806).length < 2 ^ (prefixWord ++ tailWord_734806).sum := by decide
  have hdescent : baseEnd_734806 < baseStart_734806 := by decide
  rcases family_descends (prefixWord ++ tailWord_734806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734824 : List Nat := [2, 1, 4, 3, 1, 1, 3, 3, 2]
def baseStart_734824 : Nat := 118140960795 + 734824 * 2 ^ 59
def prefixEnd_734824 : Nat := 4983230072969 + 3 ^ 40 * 734824 * 2
def baseEnd_734824 : Nat := 335393696408478427929433

theorem tailTrace_734824 : CollatzResearch.WordTrace tailWord_734824 prefixEnd_734824 335393696408478427929433 := by
  unfold tailWord_734824
  simp only [CollatzResearch.WordTrace]
  refine ⟨13400616544932810396453763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17867488726577080528605017 13400616544932810396453763)
  ·
    refine ⟨20100924817399215594680645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13400616544932810396453763 20100924817399215594680645)
    ·
      refine ⟨3768923403262352924002621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20100924817399215594680645 3768923403262352924002621)
      ·
        refine ⟨1413346276223382346500983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3768923403262352924002621 1413346276223382346500983)
        ·
          refine ⟨2120019414335073519751475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1413346276223382346500983 2120019414335073519751475)
          ·
            refine ⟨3180029121502610279627213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2120019414335073519751475 3180029121502610279627213)
            ·
              refine ⟨1192510920563478854860205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3180029121502610279627213 1192510920563478854860205)
              ·
                refine ⟨447191595211304570572577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1192510920563478854860205 447191595211304570572577)
                ·
                  refine ⟨335393696408478427929433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 447191595211304570572577 335393696408478427929433)
                  ·
                    rfl

theorem cell20_734824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 3, 2].length) (baseStart_734824 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_734824 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_734824 prefixEnd_734824 := by exact prefixLift 734824
  have htrace : WordTrace (prefixWord ++ tailWord_734824) baseStart_734824 baseEnd_734824 := by
    simpa [prefixWord, tailWord_734824, baseEnd_734824] using wordTrace_append hprefix tailTrace_734824
  have hstable : (prefixWord ++ tailWord_734824).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734824).length < 2 ^ (prefixWord ++ tailWord_734824).sum := by decide
  have hdescent : baseEnd_734824 < baseStart_734824 := by decide
  rcases family_descends (prefixWord ++ tailWord_734824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734845 : List Nat := [1, 4, 1, 1, 4, 3, 1, 1, 4]
def baseStart_734845 : Nat := 118140960795 + 734845 * 2 ^ 59
def prefixEnd_734845 : Nat := 4983230072969 + 3 ^ 40 * 734845 * 2
def baseEnd_734845 : Nat := 335403281380695688229347

theorem tailTrace_734845 : CollatzResearch.WordTrace tailWord_734845 prefixEnd_734845 335403281380695688229347 := by
  unfold tailWord_734845
  simp only [CollatzResearch.WordTrace]
  refine ⟨26801999022789541379421989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17867999348526360919614659 26801999022789541379421989)
  ·
    refine ⟨5025374816773039008641623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26801999022789541379421989 5025374816773039008641623)
    ·
      refine ⟨7538062225159558512962435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5025374816773039008641623 7538062225159558512962435)
      ·
        refine ⟨11307093337739337769443653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7538062225159558512962435 11307093337739337769443653)
        ·
          refine ⟨2120080000826125831770685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11307093337739337769443653 2120080000826125831770685)
          ·
            refine ⟨795030000309797186914007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2120080000826125831770685 795030000309797186914007)
            ·
              refine ⟨1192545000464695780371011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 795030000309797186914007 1192545000464695780371011)
              ·
                refine ⟨1788817500697043670556517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1192545000464695780371011 1788817500697043670556517)
                ·
                  refine ⟨335403281380695688229347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1788817500697043670556517 335403281380695688229347)
                  ·
                    rfl

theorem cell20_734845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 1, 4].length) (baseStart_734845 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_734845 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_734845 prefixEnd_734845 := by exact prefixLift 734845
  have htrace : WordTrace (prefixWord ++ tailWord_734845) baseStart_734845 baseEnd_734845 := by
    simpa [prefixWord, tailWord_734845, baseEnd_734845] using wordTrace_append hprefix tailTrace_734845
  have hstable : (prefixWord ++ tailWord_734845).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734845).length < 2 ^ (prefixWord ++ tailWord_734845).sum := by decide
  have hdescent : baseEnd_734845 < baseStart_734845 := by decide
  rcases family_descends (prefixWord ++ tailWord_734845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734852 : List Nat := [2, 3, 2, 1, 4, 1, 2, 5]
def baseStart_734852 : Nat := 118140960795 + 734852 * 2 ^ 59
def prefixEnd_734852 : Nat := 4983230072969 + 3 ^ 40 * 734852 * 2
def baseEnd_734852 : Nat := 111802158790478258331995

theorem tailTrace_734852 : CollatzResearch.WordTrace tailWord_734852 prefixEnd_734852 111802158790478258331995 := by
  unfold tailWord_734852
  simp only [CollatzResearch.WordTrace]
  refine ⟨13401127166882090787463405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17868169555842787716617873 13401127166882090787463405)
  ·
    refine ⟨5025422687580784045298777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13401127166882090787463405 5025422687580784045298777)
    ·
      refine ⟨3769067015685588033974083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5025422687580784045298777 3769067015685588033974083)
      ·
        refine ⟨5653600523528382050961125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3769067015685588033974083 5653600523528382050961125)
        ·
          refine ⟨1060050098161571634555211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5653600523528382050961125 1060050098161571634555211)
          ·
            refine ⟨1590075147242357451832817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1060050098161571634555211 1590075147242357451832817)
            ·
              refine ⟨1192556360431768088874613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1590075147242357451832817 1192556360431768088874613)
              ·
                refine ⟨111802158790478258331995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1192556360431768088874613 111802158790478258331995)
                ·
                  rfl

theorem cell20_734852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 5].length) (baseStart_734852 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_734852 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_734852 prefixEnd_734852 := by exact prefixLift 734852
  have htrace : WordTrace (prefixWord ++ tailWord_734852) baseStart_734852 baseEnd_734852 := by
    simpa [prefixWord, tailWord_734852, baseEnd_734852] using wordTrace_append hprefix tailTrace_734852
  have hstable : (prefixWord ++ tailWord_734852).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734852).length < 2 ^ (prefixWord ++ tailWord_734852).sum := by decide
  have hdescent : baseEnd_734852 < baseStart_734852 := by decide
  rcases family_descends (prefixWord ++ tailWord_734852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734934 : List Nat := [5, 2, 1, 3, 1, 1, 2, 3, 2]
def baseStart_734934 : Nat := 118140960795 + 734934 * 2 ^ 59
def prefixEnd_734934 : Nat := 4983230072969 + 3 ^ 40 * 734934 * 2
def baseEnd_734934 : Nat := 335443903405806934262317

theorem tailTrace_734934 : CollatzResearch.WordTrace tailWord_734934 prefixEnd_734934 335443903405806934262317 := by
  unfold tailWord_734934
  simp only [CollatzResearch.WordTrace]
  refine ⟨1675327819966694348713241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17870163412978073052941237 1675327819966694348713241)
  ·
    refine ⟨1256495864975020761534931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1675327819966694348713241 1256495864975020761534931)
    ·
      refine ⟨1884743797462531142302397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1256495864975020761534931 1884743797462531142302397)
      ·
        refine ⟨706778924048449178363399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1884743797462531142302397 706778924048449178363399)
        ·
          refine ⟨1060168386072673767545099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 706778924048449178363399 1060168386072673767545099)
          ·
            refine ⟨1590252579109010651317649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1060168386072673767545099 1590252579109010651317649)
            ·
              refine ⟨1192689434331757988488237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1590252579109010651317649 1192689434331757988488237)
              ·
                refine ⟨447258537874409245683089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1192689434331757988488237 447258537874409245683089)
                ·
                  refine ⟨335443903405806934262317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 447258537874409245683089 335443903405806934262317)
                  ·
                    rfl

theorem cell20_734934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_734934 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_734934 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_734934 prefixEnd_734934 := by exact prefixLift 734934
  have htrace : WordTrace (prefixWord ++ tailWord_734934) baseStart_734934 baseEnd_734934 := by
    simpa [prefixWord, tailWord_734934, baseEnd_734934] using wordTrace_append hprefix tailTrace_734934
  have hstable : (prefixWord ++ tailWord_734934).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734934).length < 2 ^ (prefixWord ++ tailWord_734934).sum := by decide
  have hdescent : baseEnd_734934 < baseStart_734934 := by decide
  rcases family_descends (prefixWord ++ tailWord_734934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734952 : List Nat := [2, 1, 4, 1, 3, 3, 1, 2, 3]
def baseStart_734952 : Nat := 118140960795 + 734952 * 2 ^ 59
def prefixEnd_734952 : Nat := 4983230072969 + 3 ^ 40 * 734952 * 2
def baseEnd_734952 : Nat := 335452119096278871662243

theorem tailTrace_734952 : CollatzResearch.WordTrace tailWord_734952 prefixEnd_734952 335452119096278871662243 := by
  unfold tailWord_734952
  simp only [CollatzResearch.WordTrace]
  refine ⟨13402950816700949326783555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17870601088934599102378073 13402950816700949326783555)
  ·
    refine ⟨20104426225051423990175333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13402950816700949326783555 20104426225051423990175333)
    ·
      refine ⟨3769579917197141998157875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20104426225051423990175333 3769579917197141998157875)
      ·
        refine ⟨5654369875795712997236813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3769579917197141998157875 5654369875795712997236813)
        ·
          refine ⟨2120388703423392373963805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5654369875795712997236813 2120388703423392373963805)
          ·
            refine ⟨795145763783772140236427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2120388703423392373963805 795145763783772140236427)
            ·
              refine ⟨1192718645675658210354641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 795145763783772140236427 1192718645675658210354641)
              ·
                refine ⟨894538984256743657765981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1192718645675658210354641 894538984256743657765981)
                ·
                  refine ⟨335452119096278871662243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 894538984256743657765981 335452119096278871662243)
                  ·
                    rfl

theorem cell20_734952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 2, 3].length) (baseStart_734952 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_734952 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_734952 prefixEnd_734952 := by exact prefixLift 734952
  have htrace : WordTrace (prefixWord ++ tailWord_734952) baseStart_734952 baseEnd_734952 := by
    simpa [prefixWord, tailWord_734952, baseEnd_734952] using wordTrace_append hprefix tailTrace_734952
  have hstable : (prefixWord ++ tailWord_734952).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734952).length < 2 ^ (prefixWord ++ tailWord_734952).sum := by decide
  have hdescent : baseEnd_734952 < baseStart_734952 := by decide
  rcases family_descends (prefixWord ++ tailWord_734952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734963 : List Nat := [1, 1, 1, 2, 2, 3, 3, 3, 4]
def baseStart_734963 : Nat := 118140960795 + 734963 * 2 ^ 59
def prefixEnd_734963 : Nat := 4983230072969 + 3 ^ 40 * 734963 * 2
def baseEnd_734963 : Nat := 335457139796011722295531

theorem tailTrace_734963 : CollatzResearch.WordTrace tailWord_734963 prefixEnd_734963 335457139796011722295531 := by
  unfold tailWord_734963
  simp only [CollatzResearch.WordTrace]
  refine ⟨26806302836362047532217543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17870868557574698354811695 26806302836362047532217543)
  ·
    refine ⟨40209454254543071298326315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26806302836362047532217543 40209454254543071298326315)
    ·
      refine ⟨60314181381814606947489473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40209454254543071298326315 60314181381814606947489473)
      ·
        refine ⟨45235636036360955210617105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60314181381814606947489473 45235636036360955210617105)
        ·
          refine ⟨33926727027270716407962829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45235636036360955210617105 33926727027270716407962829)
          ·
            refine ⟨12722522635226518652986061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33926727027270716407962829 12722522635226518652986061)
            ·
              refine ⟨4770945988209944494869773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12722522635226518652986061 4770945988209944494869773)
              ·
                refine ⟨1789104745578729185576165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4770945988209944494869773 1789104745578729185576165)
                ·
                  refine ⟨335457139796011722295531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1789104745578729185576165 335457139796011722295531)
                  ·
                    rfl

theorem cell20_734963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 4].length) (baseStart_734963 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_734963 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_734963 prefixEnd_734963 := by exact prefixLift 734963
  have htrace : WordTrace (prefixWord ++ tailWord_734963) baseStart_734963 baseEnd_734963 := by
    simpa [prefixWord, tailWord_734963, baseEnd_734963] using wordTrace_append hprefix tailTrace_734963
  have hstable : (prefixWord ++ tailWord_734963).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734963).length < 2 ^ (prefixWord ++ tailWord_734963).sum := by decide
  have hdescent : baseEnd_734963 < baseStart_734963 := by decide
  rcases family_descends (prefixWord ++ tailWord_734963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734970 : List Nat := [3, 1, 1, 1, 1, 3, 1, 9]
def baseStart_734970 : Nat := 118140960795 + 734970 * 2 ^ 59
def prefixEnd_734970 : Nat := 4983230072969 + 3 ^ 40 * 734970 * 2
def baseEnd_734970 : Nat := 111820111595583603020723

theorem tailTrace_734970 : CollatzResearch.WordTrace tailWord_734970 prefixEnd_734970 111820111595583603020723 := by
  unfold tailWord_734970
  simp only [CollatzResearch.WordTrace]
  refine ⟨6701639536834171931930591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17871038764891125151814909 6701639536834171931930591)
  ·
    refine ⟨10052459305251257897895887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6701639536834171931930591 10052459305251257897895887)
    ·
      refine ⟨15078688957876886846843831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10052459305251257897895887 15078688957876886846843831)
      ·
        refine ⟨22618033436815330270265747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15078688957876886846843831 22618033436815330270265747)
        ·
          refine ⟨33927050155222995405398621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22618033436815330270265747 33927050155222995405398621)
          ·
            refine ⟨12722643808208623277024483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33927050155222995405398621 12722643808208623277024483)
            ·
              refine ⟨19083965712312934915536725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12722643808208623277024483 19083965712312934915536725)
              ·
                refine ⟨111820111595583603020723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19083965712312934915536725 111820111595583603020723)
                ·
                  rfl

theorem cell20_734970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 9].length) (baseStart_734970 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_734970 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_734970 prefixEnd_734970 := by exact prefixLift 734970
  have htrace : WordTrace (prefixWord ++ tailWord_734970) baseStart_734970 baseEnd_734970 := by
    simpa [prefixWord, tailWord_734970, baseEnd_734970] using wordTrace_append hprefix tailTrace_734970
  have hstable : (prefixWord ++ tailWord_734970).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734970).length < 2 ^ (prefixWord ++ tailWord_734970).sum := by decide
  have hdescent : baseEnd_734970 < baseStart_734970 := by decide
  rcases family_descends (prefixWord ++ tailWord_734970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734980 : List Nat := [2, 3, 2, 2, 1, 2, 2, 2, 4]
def baseStart_734980 : Nat := 118140960795 + 734980 * 2 ^ 59
def prefixEnd_734980 : Nat := 4983230072969 + 3 ^ 40 * 734980 * 2
def baseEnd_734980 : Nat := 335464899059235218728795

theorem tailTrace_734980 : CollatzResearch.WordTrace tailWord_734980 prefixEnd_734980 335464899059235218728795 := by
  unfold tailWord_734980
  simp only [CollatzResearch.WordTrace]
  refine ⟨13403461438650229717793197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17871281918200306290390929 13403461438650229717793197)
  ·
    refine ⟨5026298039493836144172449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13403461438650229717793197 5026298039493836144172449)
    ·
      refine ⟨3769723529620377108129337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5026298039493836144172449 3769723529620377108129337)
      ·
        refine ⟨2827292647215282831097003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3769723529620377108129337 2827292647215282831097003)
        ·
          refine ⟨4240938970822924246645505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2827292647215282831097003 4240938970822924246645505)
          ·
            refine ⟨3180704228117193184984129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4240938970822924246645505 3180704228117193184984129)
            ·
              refine ⟨2385528171087894888738097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3180704228117193184984129 2385528171087894888738097)
              ·
                refine ⟨1789146128315921166553573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2385528171087894888738097 1789146128315921166553573)
                ·
                  refine ⟨335464899059235218728795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1789146128315921166553573 335464899059235218728795)
                  ·
                    rfl

theorem cell20_734980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_734980 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_734980 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_734980 prefixEnd_734980 := by exact prefixLift 734980
  have htrace : WordTrace (prefixWord ++ tailWord_734980) baseStart_734980 baseEnd_734980 := by
    simpa [prefixWord, tailWord_734980, baseEnd_734980] using wordTrace_append hprefix tailTrace_734980
  have hstable : (prefixWord ++ tailWord_734980).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734980).length < 2 ^ (prefixWord ++ tailWord_734980).sum := by decide
  have hdescent : baseEnd_734980 < baseStart_734980 := by decide
  rcases family_descends (prefixWord ++ tailWord_734980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734983 : List Nat := [1, 1, 4, 4, 2, 2, 2, 4]
def baseStart_734983 : Nat := 118140960795 + 734983 * 2 ^ 59
def prefixEnd_734983 : Nat := 4983230072969 + 3 ^ 40 * 734983 * 2
def baseEnd_734983 : Nat := 111822089446993513876261

theorem tailTrace_734983 : CollatzResearch.WordTrace tailWord_734983 prefixEnd_734983 111822089446993513876261 := by
  unfold tailWord_734983
  simp only [CollatzResearch.WordTrace]
  refine ⟨26807032296289590947945603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17871354864193060631963735 26807032296289590947945603)
  ·
    refine ⟨40210548444434386421918405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26807032296289590947945603 40210548444434386421918405)
    ·
      refine ⟨7539477833331447454109701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40210548444434386421918405 7539477833331447454109701)
      ·
        refine ⟨1413652093749646397645569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7539477833331447454109701 1413652093749646397645569)
        ·
          refine ⟨1060239070312234798234177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1413652093749646397645569 1060239070312234798234177)
          ·
            refine ⟨795179302734176098675633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1060239070312234798234177 795179302734176098675633)
            ·
              refine ⟨596384477050632074006725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 795179302734176098675633 596384477050632074006725)
              ·
                refine ⟨111822089446993513876261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 596384477050632074006725 111822089446993513876261)
                ·
                  rfl

theorem cell20_734983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 2, 4].length) (baseStart_734983 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_734983 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_734983 prefixEnd_734983 := by exact prefixLift 734983
  have htrace : WordTrace (prefixWord ++ tailWord_734983) baseStart_734983 baseEnd_734983 := by
    simpa [prefixWord, tailWord_734983, baseEnd_734983] using wordTrace_append hprefix tailTrace_734983
  have hstable : (prefixWord ++ tailWord_734983).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734983).length < 2 ^ (prefixWord ++ tailWord_734983).sum := by decide
  have hdescent : baseEnd_734983 < baseStart_734983 := by decide
  rcases family_descends (prefixWord ++ tailWord_734983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734987 : List Nat := [1, 1, 1, 1, 5, 1, 6, 4]
def baseStart_734987 : Nat := 118140960795 + 734987 * 2 ^ 59
def prefixEnd_734987 : Nat := 4983230072969 + 3 ^ 40 * 734987 * 2
def baseEnd_734987 : Nat := 111822698016658101831811

theorem tailTrace_734987 : CollatzResearch.WordTrace tailWord_734987 prefixEnd_734987 111822698016658101831811 := by
  unfold tailWord_734987
  simp only [CollatzResearch.WordTrace]
  refine ⟨26807178188275099631091215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17871452125516733087394143 26807178188275099631091215)
  ·
    refine ⟨40210767282412649446636823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26807178188275099631091215 40210767282412649446636823)
    ·
      refine ⟨60316150923618974169955235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40210767282412649446636823 60316150923618974169955235)
      ·
        refine ⟨90474226385428461254932853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60316150923618974169955235 90474226385428461254932853)
        ·
          refine ⟨8481958723633918242649955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 90474226385428461254932853 8481958723633918242649955)
          ·
            refine ⟨12722938085450877363974933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8481958723633918242649955 12722938085450877363974933)
            ·
              refine ⟨596387722755509876436325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12722938085450877363974933 596387722755509876436325)
              ·
                refine ⟨111822698016658101831811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 596387722755509876436325 111822698016658101831811)
                ·
                  rfl

theorem cell20_734987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 6, 4].length) (baseStart_734987 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_734987 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_734987 prefixEnd_734987 := by exact prefixLift 734987
  have htrace : WordTrace (prefixWord ++ tailWord_734987) baseStart_734987 baseEnd_734987 := by
    simpa [prefixWord, tailWord_734987, baseEnd_734987] using wordTrace_append hprefix tailTrace_734987
  have hstable : (prefixWord ++ tailWord_734987).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734987).length < 2 ^ (prefixWord ++ tailWord_734987).sum := by decide
  have hdescent : baseEnd_734987 < baseStart_734987 := by decide
  rcases family_descends (prefixWord ++ tailWord_734987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_734997 : List Nat := [1, 3, 2, 1, 2, 3, 3, 3, 2]
def baseStart_734997 : Nat := 118140960795 + 734997 * 2 ^ 59
def prefixEnd_734997 : Nat := 4983230072969 + 3 ^ 40 * 734997 * 2
def baseEnd_734997 : Nat := 335472658322458715162059

theorem tailTrace_734997 : CollatzResearch.WordTrace tailWord_734997 prefixEnd_734997 335472658322458715162059 := by
  unfold tailWord_734997
  simp only [CollatzResearch.WordTrace]
  refine ⟨26807542918238871338955245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17871695278825914225970163 26807542918238871338955245)
  ·
    refine ⟨10052828594339576752108217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26807542918238871338955245 10052828594339576752108217)
    ·
      refine ⟨7539621445754682564081163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10052828594339576752108217 7539621445754682564081163)
      ·
        refine ⟨11309432168632023846121745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7539621445754682564081163 11309432168632023846121745)
        ·
          refine ⟨8482074126474017884591309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11309432168632023846121745 8482074126474017884591309)
          ·
            refine ⟨3180777797427756706721741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8482074126474017884591309 3180777797427756706721741)
            ·
              refine ⟨1192791674035408765020653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3180777797427756706721741 1192791674035408765020653)
              ·
                refine ⟨447296877763278286882745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1192791674035408765020653 447296877763278286882745)
                ·
                  refine ⟨335472658322458715162059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 447296877763278286882745 335472658322458715162059)
                  ·
                    rfl

theorem cell20_734997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 3, 2].length) (baseStart_734997 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_734997 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_734997 prefixEnd_734997 := by exact prefixLift 734997
  have htrace : WordTrace (prefixWord ++ tailWord_734997) baseStart_734997 baseEnd_734997 := by
    simpa [prefixWord, tailWord_734997, baseEnd_734997] using wordTrace_append hprefix tailTrace_734997
  have hstable : (prefixWord ++ tailWord_734997).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_734997).length < 2 ^ (prefixWord ++ tailWord_734997).sum := by decide
  have hdescent : baseEnd_734997 < baseStart_734997 := by decide
  rcases family_descends (prefixWord ++ tailWord_734997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735025 : List Nat := [1, 2, 2, 3, 2, 3, 2, 5]
def baseStart_735025 : Nat := 118140960795 + 735025 * 2 ^ 59
def prefixEnd_735025 : Nat := 4983230072969 + 3 ^ 40 * 735025 * 2
def baseEnd_735025 : Nat := 111828479428471687409537

theorem tailTrace_735025 : CollatzResearch.WordTrace tailWord_735025 prefixEnd_735025 111828479428471687409537 := by
  unfold tailWord_735025
  simp only [CollatzResearch.WordTrace]
  refine ⟨26808564162137432120974529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17872376108091621413983019 26808564162137432120974529)
  ·
    refine ⟨20106423121603074090730897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26808564162137432120974529 20106423121603074090730897)
    ·
      refine ⟨15079817341202305568048173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20106423121603074090730897 15079817341202305568048173)
      ·
        refine ⟨5654931502950864588018065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15079817341202305568048173 5654931502950864588018065)
        ·
          refine ⟨4241198627213148441013549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5654931502950864588018065 4241198627213148441013549)
          ·
            refine ⟨1590449485204930665380081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4241198627213148441013549 1590449485204930665380081)
            ·
              refine ⟨1192837113903697999035061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1590449485204930665380081 1192837113903697999035061)
              ·
                refine ⟨111828479428471687409537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1192837113903697999035061 111828479428471687409537)
                ·
                  rfl

theorem cell20_735025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 5].length) (baseStart_735025 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_735025 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_735025 prefixEnd_735025 := by exact prefixLift 735025
  have htrace : WordTrace (prefixWord ++ tailWord_735025) baseStart_735025 baseEnd_735025 := by
    simpa [prefixWord, tailWord_735025, baseEnd_735025] using wordTrace_append hprefix tailTrace_735025
  have hstable : (prefixWord ++ tailWord_735025).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735025).length < 2 ^ (prefixWord ++ tailWord_735025).sum := by decide
  have hdescent : baseEnd_735025 < baseStart_735025 := by decide
  rcases family_descends (prefixWord ++ tailWord_735025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735028 : List Nat := [2, 5, 1, 1, 2, 2, 1, 3, 3]
def baseStart_735028 : Nat := 118140960795 + 735028 * 2 ^ 59
def prefixEnd_735028 : Nat := 4983230072969 + 3 ^ 40 * 735028 * 2
def baseEnd_735028 : Nat := 335486807567160385128599

theorem tailTrace_735028 : CollatzResearch.WordTrace tailWord_735028 prefixEnd_735028 335486807567160385128599 := by
  unfold tailWord_735028
  simp only [CollatzResearch.WordTrace]
  refine ⟨13404336790563281816666869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17872449054084375755555825 13404336790563281816666869)
  ·
    refine ⟨1256656574115307670312519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13404336790563281816666869 1256656574115307670312519)
    ·
      refine ⟨1884984861172961505468779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1256656574115307670312519 1884984861172961505468779)
      ·
        refine ⟨2827477291759442258203169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1884984861172961505468779 2827477291759442258203169)
        ·
          refine ⟨2120607968819581693652377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2827477291759442258203169 2120607968819581693652377)
          ·
            refine ⟨1590455976614686270239283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2120607968819581693652377 1590455976614686270239283)
            ·
              refine ⟨2385683964922029405358925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1590455976614686270239283 2385683964922029405358925)
              ·
                refine ⟨894631486845761027009597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2385683964922029405358925 894631486845761027009597)
                ·
                  refine ⟨335486807567160385128599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 894631486845761027009597 335486807567160385128599)
                  ·
                    rfl

theorem cell20_735028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_735028 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_735028 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_735028 prefixEnd_735028 := by exact prefixLift 735028
  have htrace : WordTrace (prefixWord ++ tailWord_735028) baseStart_735028 baseEnd_735028 := by
    simpa [prefixWord, tailWord_735028, baseEnd_735028] using wordTrace_append hprefix tailTrace_735028
  have hstable : (prefixWord ++ tailWord_735028).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735028).length < 2 ^ (prefixWord ++ tailWord_735028).sum := by decide
  have hdescent : baseEnd_735028 < baseStart_735028 := by decide
  rcases family_descends (prefixWord ++ tailWord_735028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735056 : List Nat := [2, 1, 1, 1, 1, 4, 1, 7, 2]
def baseStart_735056 : Nat := 118140960795 + 735056 * 2 ^ 59
def prefixEnd_735056 : Nat := 4983230072969 + 3 ^ 40 * 735056 * 2
def baseEnd_735056 : Nat := 335499587530116732195151

theorem tailTrace_735056 : CollatzResearch.WordTrace tailWord_735056 prefixEnd_735056 335499587530116732195151 := by
  unfold tailWord_735056
  simp only [CollatzResearch.WordTrace]
  refine ⟨13404847412512562207676511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17873129883350082943568681 13404847412512562207676511)
  ·
    refine ⟨20107271118768843311514767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13404847412512562207676511 20107271118768843311514767)
    ·
      refine ⟨30160906678153264967272151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20107271118768843311514767 30160906678153264967272151)
      ·
        refine ⟨45241360017229897450908227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30160906678153264967272151 45241360017229897450908227)
        ·
          refine ⟨67862040025844846176362341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45241360017229897450908227 67862040025844846176362341)
          ·
            refine ⟨12724132504845908658067939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67862040025844846176362341 12724132504845908658067939)
            ·
              refine ⟨19086198757268862987101909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12724132504845908658067939 19086198757268862987101909)
              ·
                refine ⟨447332783373488976260201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 19086198757268862987101909 447332783373488976260201)
                ·
                  refine ⟨335499587530116732195151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 447332783373488976260201 335499587530116732195151)
                  ·
                    rfl

theorem cell20_735056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 7, 2].length) (baseStart_735056 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_735056 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_735056 prefixEnd_735056 := by exact prefixLift 735056
  have htrace : WordTrace (prefixWord ++ tailWord_735056) baseStart_735056 baseEnd_735056 := by
    simpa [prefixWord, tailWord_735056, baseEnd_735056] using wordTrace_append hprefix tailTrace_735056
  have hstable : (prefixWord ++ tailWord_735056).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735056).length < 2 ^ (prefixWord ++ tailWord_735056).sum := by decide
  have hdescent : baseEnd_735056 < baseStart_735056 := by decide
  rcases family_descends (prefixWord ++ tailWord_735056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735063 : List Nat := [1, 1, 3, 2, 6, 7]
def baseStart_735063 : Nat := 118140960795 + 735063 * 2 ^ 59
def prefixEnd_735063 : Nat := 4983230072969 + 3 ^ 40 * 735063 * 2
def baseEnd_735063 : Nat := 12426028982253919220807

theorem tailTrace_735063 : CollatzResearch.WordTrace tailWord_735063 prefixEnd_735063 12426028982253919220807 := by
  unfold tailWord_735063
  simp only [CollatzResearch.WordTrace]
  refine ⟨26809950135999764610857843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17873300090666509740571895 26809950135999764610857843)
  ·
    refine ⟨40214925203999646916286765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26809950135999764610857843 40214925203999646916286765)
    ·
      refine ⟨15080596951499867593607537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40214925203999646916286765 15080596951499867593607537)
      ·
        refine ⟨11310447713624900695205653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15080596951499867593607537 11310447713624900695205653)
        ·
          refine ⟨530177236576167220087765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 11310447713624900695205653 530177236576167220087765)
          ·
            refine ⟨12426028982253919220807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 530177236576167220087765 12426028982253919220807)
            ·
              rfl

theorem cell20_735063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 7].length) (baseStart_735063 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_735063 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_735063 prefixEnd_735063 := by exact prefixLift 735063
  have htrace : WordTrace (prefixWord ++ tailWord_735063) baseStart_735063 baseEnd_735063 := by
    simpa [prefixWord, tailWord_735063, baseEnd_735063] using wordTrace_append hprefix tailTrace_735063
  have hstable : (prefixWord ++ tailWord_735063).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735063).length < 2 ^ (prefixWord ++ tailWord_735063).sum := by decide
  have hdescent : baseEnd_735063 < baseStart_735063 := by decide
  rcases family_descends (prefixWord ++ tailWord_735063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735077 : List Nat := [1, 3, 1, 3, 1, 1, 1, 5, 4]
def baseStart_735077 : Nat := 118140960795 + 735077 * 2 ^ 59
def prefixEnd_735077 : Nat := 4983230072969 + 3 ^ 40 * 735077 * 2
def baseEnd_735077 : Nat := 335509172502333992495065

theorem tailTrace_735077 : CollatzResearch.WordTrace tailWord_735077 prefixEnd_735077 335509172502333992495065 := by
  unfold tailWord_735077
  simp only [CollatzResearch.WordTrace]
  refine ⟨26810460757949045001867485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17873640505299363334578323 26810460757949045001867485)
  ·
    refine ⟨10053922784230891875700307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26810460757949045001867485 10053922784230891875700307)
    ·
      refine ⟨15080884176346337813550461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10053922784230891875700307 15080884176346337813550461)
      ·
        refine ⟨5655331566129876680081423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15080884176346337813550461 5655331566129876680081423)
        ·
          refine ⟨8482997349194815020122135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5655331566129876680081423 8482997349194815020122135)
          ·
            refine ⟨12724496023792222530183203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8482997349194815020122135 12724496023792222530183203)
            ·
              refine ⟨19086744035688333795274805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12724496023792222530183203 19086744035688333795274805)
              ·
                refine ⟨1789382253345781293307013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19086744035688333795274805 1789382253345781293307013)
                ·
                  refine ⟨335509172502333992495065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1789382253345781293307013 335509172502333992495065)
                  ·
                    rfl

theorem cell20_735077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 5, 4].length) (baseStart_735077 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_735077 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_735077 prefixEnd_735077 := by exact prefixLift 735077
  have htrace : WordTrace (prefixWord ++ tailWord_735077) baseStart_735077 baseEnd_735077 := by
    simpa [prefixWord, tailWord_735077, baseEnd_735077] using wordTrace_append hprefix tailTrace_735077
  have hstable : (prefixWord ++ tailWord_735077).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735077).length < 2 ^ (prefixWord ++ tailWord_735077).sum := by decide
  have hdescent : baseEnd_735077 < baseStart_735077 := by decide
  rcases family_descends (prefixWord ++ tailWord_735077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735091 : List Nat := [1, 1, 1, 2, 2, 1, 3, 2, 7]
def baseStart_735091 : Nat := 118140960795 + 735091 * 2 ^ 59
def prefixEnd_735091 : Nat := 4983230072969 + 3 ^ 40 * 735091 * 2
def baseEnd_735091 : Nat := 335515562483812166028341

theorem tailTrace_735091 : CollatzResearch.WordTrace tailWord_735091 prefixEnd_735091 335515562483812166028341 := by
  unfold tailWord_735091
  simp only [CollatzResearch.WordTrace]
  refine ⟨26810971379898325392877127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17873980919932216928584751 26810971379898325392877127)
  ·
    refine ⟨40216457069847488089315691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26810971379898325392877127 40216457069847488089315691)
    ·
      refine ⟨60324685604771232133973537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40216457069847488089315691 60324685604771232133973537)
      ·
        refine ⟨45243514203578424100480153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60324685604771232133973537 45243514203578424100480153)
        ·
          refine ⟨33932635652683818075360115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45243514203578424100480153 33932635652683818075360115)
          ·
            refine ⟨50898953479025727113040173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33932635652683818075360115 50898953479025727113040173)
            ·
              refine ⟨19087107554634647667390065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50898953479025727113040173 19087107554634647667390065)
              ·
                refine ⟨14315330665975985750542549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19087107554634647667390065 14315330665975985750542549)
                ·
                  refine ⟨335515562483812166028341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14315330665975985750542549 335515562483812166028341)
                  ·
                    rfl

theorem cell20_735091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 7].length) (baseStart_735091 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_735091 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_735091 prefixEnd_735091 := by exact prefixLift 735091
  have htrace : WordTrace (prefixWord ++ tailWord_735091) baseStart_735091 baseEnd_735091 := by
    simpa [prefixWord, tailWord_735091, baseEnd_735091] using wordTrace_append hprefix tailTrace_735091
  have hstable : (prefixWord ++ tailWord_735091).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735091).length < 2 ^ (prefixWord ++ tailWord_735091).sum := by decide
  have hdescent : baseEnd_735091 < baseStart_735091 := by decide
  rcases family_descends (prefixWord ++ tailWord_735091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735118 : List Nat := [4, 1, 1, 5, 1, 1, 7]
def baseStart_735118 : Nat := 118140960795 + 735118 * 2 ^ 59
def prefixEnd_735118 : Nat := 4983230072969 + 3 ^ 40 * 735118 * 2
def baseEnd_735118 : Nat := 37280876224391119125359

theorem tailTrace_735118 : CollatzResearch.WordTrace tailWord_735118 prefixEnd_735118 37280876224391119125359 := by
  unfold tailWord_735118
  simp only [CollatzResearch.WordTrace]
  refine ⟨3351494518850063625513751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17874637433867006002740005 3351494518850063625513751)
  ·
    refine ⟨5027241778275095438270627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3351494518850063625513751 5027241778275095438270627)
    ·
      refine ⟨7540862667412643157405941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5027241778275095438270627 7540862667412643157405941)
      ·
        refine ⟨706955875069935296006807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7540862667412643157405941 706955875069935296006807)
        ·
          refine ⟨1060433812604902944010211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 706955875069935296006807 1060433812604902944010211)
          ·
            refine ⟨1590650718907354416015317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1060433812604902944010211 1590650718907354416015317)
            ·
              refine ⟨37280876224391119125359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1590650718907354416015317 37280876224391119125359)
              ·
                rfl

theorem cell20_735118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 7].length) (baseStart_735118 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_735118 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_735118 prefixEnd_735118 := by exact prefixLift 735118
  have htrace : WordTrace (prefixWord ++ tailWord_735118) baseStart_735118 baseEnd_735118 := by
    simpa [prefixWord, tailWord_735118, baseEnd_735118] using wordTrace_append hprefix tailTrace_735118
  have hstable : (prefixWord ++ tailWord_735118).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735118).length < 2 ^ (prefixWord ++ tailWord_735118).sum := by decide
  have hdescent : baseEnd_735118 < baseStart_735118 := by decide
  rcases family_descends (prefixWord ++ tailWord_735118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735132 : List Nat := [2, 2, 3, 3, 1, 1, 1, 3, 4]
def baseStart_735132 : Nat := 118140960795 + 735132 * 2 ^ 59
def prefixEnd_735132 : Nat := 4983230072969 + 3 ^ 40 * 735132 * 2
def baseEnd_735132 : Nat := 335534276000998245661507

theorem tailTrace_735132 : CollatzResearch.WordTrace tailWord_735132 prefixEnd_735132 335534276000998245661507 := by
  unfold tailWord_735132
  simp only [CollatzResearch.WordTrace]
  refine ⟨13406233386374894697559825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17874977848499859596746433 13406233386374894697559825)
  ·
    refine ⟨10054675039781171023169869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13406233386374894697559825 10054675039781171023169869)
    ·
      refine ⟨3770503139917939133688701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10054675039781171023169869 3770503139917939133688701)
      ·
        refine ⟨1413938677469227175133263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3770503139917939133688701 1413938677469227175133263)
        ·
          refine ⟨2120908016203840762699895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1413938677469227175133263 2120908016203840762699895)
          ·
            refine ⟨3181362024305761144049843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2120908016203840762699895 3181362024305761144049843)
            ·
              refine ⟨4772043036458641716074765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3181362024305761144049843 4772043036458641716074765)
              ·
                refine ⟨1789516138671990643528037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4772043036458641716074765 1789516138671990643528037)
                ·
                  refine ⟨335534276000998245661507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1789516138671990643528037 335534276000998245661507)
                  ·
                    rfl

theorem cell20_735132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 3, 4].length) (baseStart_735132 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_735132 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_735132 prefixEnd_735132 := by exact prefixLift 735132
  have htrace : WordTrace (prefixWord ++ tailWord_735132) baseStart_735132 baseEnd_735132 := by
    simpa [prefixWord, tailWord_735132, baseEnd_735132] using wordTrace_append hprefix tailTrace_735132
  have hstable : (prefixWord ++ tailWord_735132).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735132).length < 2 ^ (prefixWord ++ tailWord_735132).sum := by decide
  have hdescent : baseEnd_735132 < baseStart_735132 := by decide
  rcases family_descends (prefixWord ++ tailWord_735132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735160 : List Nat := [2, 1, 2, 1, 2, 3, 3, 6]
def baseStart_735160 : Nat := 118140960795 + 735160 * 2 ^ 59
def prefixEnd_735160 : Nat := 4983230072969 + 3 ^ 40 * 735160 * 2
def baseEnd_735160 : Nat := 111849018654651530909353

theorem tailTrace_735160 : CollatzResearch.WordTrace tailWord_735160 prefixEnd_735160 111849018654651530909353 := by
  unfold tailWord_735160
  simp only [CollatzResearch.WordTrace]
  refine ⟨13406744008324175088569467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17875658677765566784759289 13406744008324175088569467)
  ·
    refine ⟨20110116012486262632854201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13406744008324175088569467 20110116012486262632854201)
    ·
      refine ⟨15082587009364696974640651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20110116012486262632854201 15082587009364696974640651)
      ·
        refine ⟨22623880514047045461960977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15082587009364696974640651 22623880514047045461960977)
        ·
          refine ⟨16967910385535284096470733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22623880514047045461960977 16967910385535284096470733)
          ·
            refine ⟨6362966394575731536176525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16967910385535284096470733 6362966394575731536176525)
            ·
              refine ⟨2386112397965899326066197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6362966394575731536176525 2386112397965899326066197)
              ·
                refine ⟨111849018654651530909353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2386112397965899326066197 111849018654651530909353)
                ·
                  rfl

theorem cell20_735160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 6].length) (baseStart_735160 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_735160 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_735160 prefixEnd_735160 := by exact prefixLift 735160
  have htrace : WordTrace (prefixWord ++ tailWord_735160) baseStart_735160 baseEnd_735160 := by
    simpa [prefixWord, tailWord_735160, baseEnd_735160] using wordTrace_append hprefix tailTrace_735160
  have hstable : (prefixWord ++ tailWord_735160).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735160).length < 2 ^ (prefixWord ++ tailWord_735160).sum := by decide
  have hdescent : baseEnd_735160 < baseStart_735160 := by decide
  rcases family_descends (prefixWord ++ tailWord_735160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735166 : List Nat := [4, 2, 1, 1, 1, 5, 1, 3, 2]
def baseStart_735166 : Nat := 118140960795 + 735166 * 2 ^ 59
def prefixEnd_735166 : Nat := 4983230072969 + 3 ^ 40 * 735166 * 2
def baseEnd_735166 : Nat := 335549794527445238528035

theorem tailTrace_735166 : CollatzResearch.WordTrace tailWord_735166 prefixEnd_735166 335549794527445238528035 := by
  unfold tailWord_735166
  simp only [CollatzResearch.WordTrace]
  refine ⟨3351713356828326650232169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17875804569751075467904901 3351713356828326650232169)
  ·
    refine ⟨2513785017621244987674127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3351713356828326650232169 2513785017621244987674127)
    ·
      refine ⟨3770677526431867481511191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2513785017621244987674127 3770677526431867481511191)
      ·
        refine ⟨5656016289647801222266787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3770677526431867481511191 5656016289647801222266787)
        ·
          refine ⟨8484024434471701833400181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5656016289647801222266787 8484024434471701833400181)
          ·
            refine ⟨795377290731722046881267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8484024434471701833400181 795377290731722046881267)
            ·
              refine ⟨1193065936097583070321901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 795377290731722046881267 1193065936097583070321901)
              ·
                refine ⟨447399726036593651370713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1193065936097583070321901 447399726036593651370713)
                ·
                  refine ⟨335549794527445238528035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 447399726036593651370713 335549794527445238528035)
                  ·
                    rfl

theorem cell20_735166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 3, 2].length) (baseStart_735166 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_735166 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_735166 prefixEnd_735166 := by exact prefixLift 735166
  have htrace : WordTrace (prefixWord ++ tailWord_735166) baseStart_735166 baseEnd_735166 := by
    simpa [prefixWord, tailWord_735166, baseEnd_735166] using wordTrace_append hprefix tailTrace_735166
  have hstable : (prefixWord ++ tailWord_735166).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735166).length < 2 ^ (prefixWord ++ tailWord_735166).sum := by decide
  have hdescent : baseEnd_735166 < baseStart_735166 := by decide
  rcases family_descends (prefixWord ++ tailWord_735166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735167 : List Nat := [1, 1, 2, 2, 2, 1, 3, 1, 7]
def baseStart_735167 : Nat := 118140960795 + 735167 * 2 ^ 59
def prefixEnd_735167 : Nat := 4983230072969 + 3 ^ 40 * 735167 * 2
def baseEnd_735167 : Nat := 335550250954693679494697

theorem tailTrace_735167 : CollatzResearch.WordTrace tailWord_735167 prefixEnd_735167 335550250954693679494697 := by
  unfold tailWord_735167
  simp only [CollatzResearch.WordTrace]
  refine ⟨26813743327622990372643755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17875828885081993581762503 26813743327622990372643755)
  ·
    refine ⟨40220614991434485558965633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26813743327622990372643755 40220614991434485558965633)
    ·
      refine ⟨30165461243575864169224225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40220614991434485558965633 30165461243575864169224225)
      ·
        refine ⟨22624095932681898126918169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30165461243575864169224225 22624095932681898126918169)
        ·
          refine ⟨16968071949511423595188627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22624095932681898126918169 16968071949511423595188627)
          ·
            refine ⟨25452107924267135392782941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16968071949511423595188627 25452107924267135392782941)
            ·
              refine ⟨9544540471600175772293603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25452107924267135392782941 9544540471600175772293603)
              ·
                refine ⟨14316810707400263658440405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9544540471600175772293603 14316810707400263658440405)
                ·
                  refine ⟨335550250954693679494697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14316810707400263658440405 335550250954693679494697)
                  ·
                    rfl

theorem cell20_735167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 7].length) (baseStart_735167 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_735167 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_735167 prefixEnd_735167 := by exact prefixLift 735167
  have htrace : WordTrace (prefixWord ++ tailWord_735167) baseStart_735167 baseEnd_735167 := by
    simpa [prefixWord, tailWord_735167, baseEnd_735167] using wordTrace_append hprefix tailTrace_735167
  have hstable : (prefixWord ++ tailWord_735167).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735167).length < 2 ^ (prefixWord ++ tailWord_735167).sum := by decide
  have hdescent : baseEnd_735167 < baseStart_735167 := by decide
  rcases family_descends (prefixWord ++ tailWord_735167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735197 : List Nat := [1, 4, 3, 1, 3, 2, 2, 1, 3]
def baseStart_735197 : Nat := 118140960795 + 735197 * 2 ^ 59
def prefixEnd_735197 : Nat := 4983230072969 + 3 ^ 40 * 735197 * 2
def baseEnd_735197 : Nat := 335563943772146908494575

theorem tailTrace_735197 : CollatzResearch.WordTrace tailWord_735197 prefixEnd_735197 335563943772146908494575 := by
  unfold tailWord_735197
  simp only [CollatzResearch.WordTrace]
  refine ⟨26814837517514305496235845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17876558345009536997490563 26814837517514305496235845)
  ·
    refine ⟨5027782034533932280544221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26814837517514305496235845 5027782034533932280544221)
    ·
      refine ⟨1885418262950224605204083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5027782034533932280544221 1885418262950224605204083)
      ·
        refine ⟨2828127394425336907806125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1885418262950224605204083 2828127394425336907806125)
        ·
          refine ⟨1060547772909501340427297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2828127394425336907806125 1060547772909501340427297)
          ·
            refine ⟨795410829682126005320473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1060547772909501340427297 795410829682126005320473)
            ·
              refine ⟨596558122261594503990355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 795410829682126005320473 596558122261594503990355)
              ·
                refine ⟨894837183392391755985533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 596558122261594503990355 894837183392391755985533)
                ·
                  refine ⟨335563943772146908494575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 894837183392391755985533 335563943772146908494575)
                  ·
                    rfl

theorem cell20_735197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 2, 1, 3].length) (baseStart_735197 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_735197 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_735197 prefixEnd_735197 := by exact prefixLift 735197
  have htrace : WordTrace (prefixWord ++ tailWord_735197) baseStart_735197 baseEnd_735197 := by
    simpa [prefixWord, tailWord_735197, baseEnd_735197] using wordTrace_append hprefix tailTrace_735197
  have hstable : (prefixWord ++ tailWord_735197).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735197).length < 2 ^ (prefixWord ++ tailWord_735197).sum := by decide
  have hdescent : baseEnd_735197 < baseStart_735197 := by decide
  rcases family_descends (prefixWord ++ tailWord_735197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
