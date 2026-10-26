import V185TrunkScan22Chunk034

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_313706 : List Nat := [3, 1, 3, 3, 1, 2, 1, 1, 4, 3]
def baseStart_313706 : Nat := 118140960795 + 313706 * 2 ^ 59
def prefixEnd_313706 : Nat := 4983230072969 + 3 ^ 40 * 313706 * 2
def baseEnd_313706 : Nat := 107387974799636571688199

theorem tailTrace_313706 : CollatzResearch.WordTrace tailWord_313706 prefixEnd_313706 107387974799636571688199 := by
  unfold tailWord_313706
  simp only [CollatzResearch.WordTrace]
  refine ⟨2860449450376053391112243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7627865201002809042965981 2860449450376053391112243)
  ·
    refine ⟨4290674175564080086668365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2860449450376053391112243 4290674175564080086668365)
    ·
      refine ⟨1609002815836530032500637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4290674175564080086668365 1609002815836530032500637)
      ·
        refine ⟨603376055938698762187739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1609002815836530032500637 603376055938698762187739)
        ·
          refine ⟨905064083908048143281609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 603376055938698762187739 905064083908048143281609)
          ·
            refine ⟨678798062931036107461207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 905064083908048143281609 678798062931036107461207)
            ·
              refine ⟨1018197094396554161191811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 678798062931036107461207 1018197094396554161191811)
              ·
                refine ⟨1527295641594831241787717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1018197094396554161191811 1527295641594831241787717)
                ·
                  refine ⟨286367932799030857835197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1527295641594831241787717 286367932799030857835197)
                  ·
                    refine ⟨107387974799636571688199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 286367932799030857835197 107387974799636571688199)
                    ·
                      rfl

theorem cell22_313706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 4, 3].length) (baseStart_313706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_313706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_313706 prefixEnd_313706 := by exact prefixLift 313706
  have htrace : WordTrace (prefixWord ++ tailWord_313706) baseStart_313706 baseEnd_313706 := by
    simpa [prefixWord, tailWord_313706, baseEnd_313706] using wordTrace_append hprefix tailTrace_313706
  have hstable : (prefixWord ++ tailWord_313706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313706).length < 2 ^ (prefixWord ++ tailWord_313706).sum := by decide
  have hdescent : baseEnd_313706 < baseStart_313706 := by decide
  rcases family_descends (prefixWord ++ tailWord_313706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313768 : List Nat := [2, 1, 6, 1, 1, 1, 3, 1, 3, 3]
def baseStart_313768 : Nat := 118140960795 + 313768 * 2 ^ 59
def prefixEnd_313768 : Nat := 4983230072969 + 3 ^ 40 * 313768 * 2
def baseEnd_313768 : Nat := 107409198666689076638009

theorem tailTrace_313768 : CollatzResearch.WordTrace tailWord_313768 prefixEnd_313768 107409198666689076638009 := by
  unfold tailWord_313768
  simp only [CollatzResearch.WordTrace]
  refine ⟨5722029563639799076602979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7629372751519732102137305 5722029563639799076602979)
  ·
    refine ⟨8583044345459698614904469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5722029563639799076602979 8583044345459698614904469)
    ·
      refine ⟨402330203693423372573647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 8583044345459698614904469 402330203693423372573647)
      ·
        refine ⟨603495305540135058860471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 402330203693423372573647 603495305540135058860471)
        ·
          refine ⟨905242958310202588290707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 603495305540135058860471 905242958310202588290707)
          ·
            refine ⟨1357864437465303882436061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 905242958310202588290707 1357864437465303882436061)
            ·
              refine ⟨509199164049488955913523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1357864437465303882436061 509199164049488955913523)
              ·
                refine ⟨763798746074233433870285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 509199164049488955913523 763798746074233433870285)
                ·
                  refine ⟨286424529777837537701357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 763798746074233433870285 286424529777837537701357)
                  ·
                    refine ⟨107409198666689076638009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 286424529777837537701357 107409198666689076638009)
                    ·
                      rfl

theorem cell22_313768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_313768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_313768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_313768 prefixEnd_313768 := by exact prefixLift 313768
  have htrace : WordTrace (prefixWord ++ tailWord_313768) baseStart_313768 baseEnd_313768 := by
    simpa [prefixWord, tailWord_313768, baseEnd_313768] using wordTrace_append hprefix tailTrace_313768
  have hstable : (prefixWord ++ tailWord_313768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313768).length < 2 ^ (prefixWord ++ tailWord_313768).sum := by decide
  have hdescent : baseEnd_313768 < baseStart_313768 := by decide
  rcases family_descends (prefixWord ++ tailWord_313768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313781 : List Nat := [1, 3, 3, 2, 3, 1, 1, 3, 5]
def baseStart_313781 : Nat := 118140960795 + 313781 * 2 ^ 59
def prefixEnd_313781 : Nat := 4983230072969 + 3 ^ 40 * 313781 * 2
def baseEnd_313781 : Nat := 35804549610787125354323

theorem tailTrace_313781 : CollatzResearch.WordTrace tailWord_313781 prefixEnd_313781 35804549610787125354323 := by
  unfold tailWord_313781
  simp only [CollatzResearch.WordTrace]
  refine ⟨11444533276232501373429197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7629688850821667582286131 11444533276232501373429197)
  ·
    refine ⟨4291699978587188015035949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11444533276232501373429197 4291699978587188015035949)
    ·
      refine ⟨1609387491970195505638481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4291699978587188015035949 1609387491970195505638481)
      ·
        refine ⟨1207040618977646629228861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1609387491970195505638481 1207040618977646629228861)
        ·
          refine ⟨452640232116617485960823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1207040618977646629228861 452640232116617485960823)
          ·
            refine ⟨678960348174926228941235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 452640232116617485960823 678960348174926228941235)
            ·
              refine ⟨1018440522262389343411853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 678960348174926228941235 1018440522262389343411853)
              ·
                refine ⟨381915195848396003779445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1018440522262389343411853 381915195848396003779445)
                ·
                  refine ⟨35804549610787125354323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 381915195848396003779445 35804549610787125354323)
                  ·
                    rfl

theorem cell22_313781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 3, 5].length) (baseStart_313781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_313781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_313781 prefixEnd_313781 := by exact prefixLift 313781
  have htrace : WordTrace (prefixWord ++ tailWord_313781) baseStart_313781 baseEnd_313781 := by
    simpa [prefixWord, tailWord_313781, baseEnd_313781] using wordTrace_append hprefix tailTrace_313781
  have hstable : (prefixWord ++ tailWord_313781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313781).length < 2 ^ (prefixWord ++ tailWord_313781).sum := by decide
  have hdescent : baseEnd_313781 < baseStart_313781 := by decide
  rcases family_descends (prefixWord ++ tailWord_313781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313792 : List Nat := [2, 1, 1, 2, 3, 1, 1, 3, 8]
def baseStart_313792 : Nat := 118140960795 + 313792 * 2 ^ 59
def prefixEnd_313792 : Nat := 4983230072969 + 3 ^ 40 * 313792 * 2
def baseEnd_313792 : Nat := 35805804785720338012645

theorem tailTrace_313792 : CollatzResearch.WordTrace tailWord_313792 prefixEnd_313792 35805804785720338012645 := by
  unfold tailWord_313792
  simp only [CollatzResearch.WordTrace]
  refine ⟨5722467239596325126039815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7629956319461766834719753 5722467239596325126039815)
  ·
    refine ⟨8583700859394487689059723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5722467239596325126039815 8583700859394487689059723)
    ·
      refine ⟨12875551289091731533589585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8583700859394487689059723 12875551289091731533589585)
      ·
        refine ⟨9656663466818798650192189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12875551289091731533589585 9656663466818798650192189)
        ·
          refine ⟨3621248800057049493822071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9656663466818798650192189 3621248800057049493822071)
          ·
            refine ⟨5431873200085574240733107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3621248800057049493822071 5431873200085574240733107)
            ·
              refine ⟨8147809800128361361099661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5431873200085574240733107 8147809800128361361099661)
              ·
                refine ⟨3055428675048135510412373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8147809800128361361099661 3055428675048135510412373)
                ·
                  refine ⟨35805804785720338012645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3055428675048135510412373 35805804785720338012645)
                  ·
                    rfl

theorem cell22_313792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 8].length) (baseStart_313792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_313792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_313792 prefixEnd_313792 := by exact prefixLift 313792
  have htrace : WordTrace (prefixWord ++ tailWord_313792) baseStart_313792 baseEnd_313792 := by
    simpa [prefixWord, tailWord_313792, baseEnd_313792] using wordTrace_append hprefix tailTrace_313792
  have hstable : (prefixWord ++ tailWord_313792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313792).length < 2 ^ (prefixWord ++ tailWord_313792).sum := by decide
  have hdescent : baseEnd_313792 < baseStart_313792 := by decide
  rcases family_descends (prefixWord ++ tailWord_313792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313841 : List Nat := [1, 2, 2, 2, 3, 1, 1, 5, 2, 3]
def baseStart_313841 : Nat := 118140960795 + 313841 * 2 ^ 59
def prefixEnd_313841 : Nat := 4983230072969 + 3 ^ 40 * 313841 * 2
def baseEnd_313841 : Nat := 107434188058541219562785

theorem tailTrace_313841 : CollatzResearch.WordTrace tailWord_313841 prefixEnd_313841 107434188058541219562785 := by
  unfold tailWord_313841
  simp only [CollatzResearch.WordTrace]
  refine ⟨11446721656015131620613377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7631147770676754413742251 11446721656015131620613377)
  ·
    refine ⟨8585041242011348715460033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11446721656015131620613377 8585041242011348715460033)
    ·
      refine ⟨6438780931508511536595025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8585041242011348715460033 6438780931508511536595025)
      ·
        refine ⟨4829085698631383652446269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6438780931508511536595025 4829085698631383652446269)
        ·
          refine ⟨1810907136986768869667351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4829085698631383652446269 1810907136986768869667351)
          ·
            refine ⟨2716360705480153304501027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1810907136986768869667351 2716360705480153304501027)
            ·
              refine ⟨4074541058220229956751541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2716360705480153304501027 4074541058220229956751541)
              ·
                refine ⟨381988224208146558445457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4074541058220229956751541 381988224208146558445457)
                ·
                  refine ⟨286491168156109918834093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 381988224208146558445457 286491168156109918834093)
                  ·
                    refine ⟨107434188058541219562785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 286491168156109918834093 107434188058541219562785)
                    ·
                      rfl

theorem cell22_313841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 5, 2, 3].length) (baseStart_313841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_313841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_313841 prefixEnd_313841 := by exact prefixLift 313841
  have htrace : WordTrace (prefixWord ++ tailWord_313841) baseStart_313841 baseEnd_313841 := by
    simpa [prefixWord, tailWord_313841, baseEnd_313841] using wordTrace_append hprefix tailTrace_313841
  have hstable : (prefixWord ++ tailWord_313841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313841).length < 2 ^ (prefixWord ++ tailWord_313841).sum := by decide
  have hdescent : baseEnd_313841 < baseStart_313841 := by decide
  rcases family_descends (prefixWord ++ tailWord_313841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313862 : List Nat := [6, 2, 1, 1, 1, 2, 1, 3, 1, 4]
def baseStart_313862 : Nat := 118140960795 + 313862 * 2 ^ 59
def prefixEnd_313862 : Nat := 4983230072969 + 3 ^ 40 * 313862 * 2
def baseEnd_313862 : Nat := 107441376787704164787721

theorem tailTrace_313862 : CollatzResearch.WordTrace tailWord_313862 prefixEnd_313862 107441376787704164787721 := by
  unfold tailWord_313862
  simp only [CollatzResearch.WordTrace]
  refine ⟨357733987154345381472745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7631658392626034804751893 357733987154345381472745)
  ·
    refine ⟨268300490365759036104559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 357733987154345381472745 268300490365759036104559)
    ·
      refine ⟨402450735548638554156839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268300490365759036104559 402450735548638554156839)
      ·
        refine ⟨603676103322957831235259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 402450735548638554156839 603676103322957831235259)
        ·
          refine ⟨905514154984436746852889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 603676103322957831235259 905514154984436746852889)
          ·
            refine ⟨679135616238327560139667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 905514154984436746852889 679135616238327560139667)
            ·
              refine ⟨1018703424357491340209501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 679135616238327560139667 1018703424357491340209501)
              ·
                refine ⟨382013784134059252578563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1018703424357491340209501 382013784134059252578563)
                ·
                  refine ⟨573020676201088878867845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 382013784134059252578563 573020676201088878867845)
                  ·
                    refine ⟨107441376787704164787721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 573020676201088878867845 107441376787704164787721)
                    ·
                      rfl

theorem cell22_313862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_313862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_313862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_313862 prefixEnd_313862 := by exact prefixLift 313862
  have htrace : WordTrace (prefixWord ++ tailWord_313862) baseStart_313862 baseEnd_313862 := by
    simpa [prefixWord, tailWord_313862, baseEnd_313862] using wordTrace_append hprefix tailTrace_313862
  have hstable : (prefixWord ++ tailWord_313862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313862).length < 2 ^ (prefixWord ++ tailWord_313862).sum := by decide
  have hdescent : baseEnd_313862 < baseStart_313862 := by decide
  rcases family_descends (prefixWord ++ tailWord_313862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313892 : List Nat := [2, 3, 1, 5, 1, 1, 3, 1, 2, 3]
def baseStart_313892 : Nat := 118140960795 + 313892 * 2 ^ 59
def prefixEnd_313892 : Nat := 4983230072969 + 3 ^ 40 * 313892 * 2
def baseEnd_313892 : Nat := 107451646400794086537629

theorem tailTrace_313892 : CollatzResearch.WordTrace tailWord_313892 prefixEnd_313892 107451646400794086537629 := by
  unfold tailWord_313892
  simp only [CollatzResearch.WordTrace]
  refine ⟨5724290889415183665359965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7632387852553578220479953 5724290889415183665359965)
  ·
    refine ⟨2146609083530693874509987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5724290889415183665359965 2146609083530693874509987)
    ·
      refine ⟨3219913625296040811764981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2146609083530693874509987 3219913625296040811764981)
      ·
        refine ⟨301866902371503826102967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3219913625296040811764981 301866902371503826102967)
        ·
          refine ⟨452800353557255739154451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 301866902371503826102967 452800353557255739154451)
          ·
            refine ⟨679200530335883608731677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 452800353557255739154451 679200530335883608731677)
            ·
              refine ⟨254700198875956353274379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 679200530335883608731677 254700198875956353274379)
              ·
                refine ⟨382050298313934529911569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 254700198875956353274379 382050298313934529911569)
                ·
                  refine ⟨286537723735450897433677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 382050298313934529911569 286537723735450897433677)
                  ·
                    refine ⟨107451646400794086537629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 286537723735450897433677 107451646400794086537629)
                    ·
                      rfl

theorem cell22_313892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 3, 1, 2, 3].length) (baseStart_313892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_313892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_313892 prefixEnd_313892 := by exact prefixLift 313892
  have htrace : WordTrace (prefixWord ++ tailWord_313892) baseStart_313892 baseEnd_313892 := by
    simpa [prefixWord, tailWord_313892, baseEnd_313892] using wordTrace_append hprefix tailTrace_313892
  have hstable : (prefixWord ++ tailWord_313892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313892).length < 2 ^ (prefixWord ++ tailWord_313892).sum := by decide
  have hdescent : baseEnd_313892 < baseStart_313892 := by decide
  rcases family_descends (prefixWord ++ tailWord_313892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313899 : List Nat := [1, 1, 1, 1, 2, 1, 3, 7, 5]
def baseStart_313899 : Nat := 118140960795 + 313899 * 2 ^ 59
def prefixEnd_313899 : Nat := 4983230072969 + 3 ^ 40 * 313899 * 2
def baseEnd_313899 : Nat := 35818014214616133870869

theorem tailTrace_313899 : CollatzResearch.WordTrace tailWord_313899 prefixEnd_313899 35818014214616133870869 := by
  unfold tailWord_313899
  simp only [CollatzResearch.WordTrace]
  refine ⟨11448837089805007526224751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7632558059870005017483167 11448837089805007526224751)
  ·
    refine ⟨17173255634707511289337127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11448837089805007526224751 17173255634707511289337127)
    ·
      refine ⟨25759883452061266934005691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17173255634707511289337127 25759883452061266934005691)
      ·
        refine ⟨38639825178091900401008537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25759883452061266934005691 38639825178091900401008537)
        ·
          refine ⟨28979868883568925300756403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38639825178091900401008537 28979868883568925300756403)
          ·
            refine ⟨43469803325353387951134605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28979868883568925300756403 43469803325353387951134605)
            ·
              refine ⟨16301176247007520481675477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43469803325353387951134605 16301176247007520481675477)
              ·
                refine ⟨382058818289238761289269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 16301176247007520481675477 382058818289238761289269)
                ·
                  refine ⟨35818014214616133870869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 382058818289238761289269 35818014214616133870869)
                  ·
                    rfl

theorem cell22_313899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 7, 5].length) (baseStart_313899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_313899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_313899 prefixEnd_313899 := by exact prefixLift 313899
  have htrace : WordTrace (prefixWord ++ tailWord_313899) baseStart_313899 baseEnd_313899 := by
    simpa [prefixWord, tailWord_313899, baseEnd_313899] using wordTrace_append hprefix tailTrace_313899
  have hstable : (prefixWord ++ tailWord_313899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313899).length < 2 ^ (prefixWord ++ tailWord_313899).sum := by decide
  have hdescent : baseEnd_313899 < baseStart_313899 := by decide
  rcases family_descends (prefixWord ++ tailWord_313899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313929 : List Nat := [1, 2, 1, 1, 2, 2, 1, 1, 7, 4]
def baseStart_313929 : Nat := 118140960795 + 313929 * 2 ^ 59
def prefixEnd_313929 : Nat := 4983230072969 + 3 ^ 40 * 313929 * 2
def baseEnd_313929 : Nat := 107464312256938323362515

theorem tailTrace_313929 : CollatzResearch.WordTrace tailWord_313929 prefixEnd_313929 107464312256938323362515 := by
  unfold tailWord_313929
  simp only [CollatzResearch.WordTrace]
  refine ⟨11449931279696322649816841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7633287519797548433211227 11449931279696322649816841)
  ·
    refine ⟨8587448459772241987362631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11449931279696322649816841 8587448459772241987362631)
    ·
      refine ⟨12881172689658362981043947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8587448459772241987362631 12881172689658362981043947)
      ·
        refine ⟨19321759034487544471565921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12881172689658362981043947 19321759034487544471565921)
        ·
          refine ⟨14491319275865658353674441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19321759034487544471565921 14491319275865658353674441)
          ·
            refine ⟨10868489456899243765255831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14491319275865658353674441 10868489456899243765255831)
            ·
              refine ⟨16302734185348865647883747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10868489456899243765255831 16302734185348865647883747)
              ·
                refine ⟨24454101278023298471825621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16302734185348865647883747 24454101278023298471825621)
                ·
                  refine ⟨573142998703671057933413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 24454101278023298471825621 573142998703671057933413)
                  ·
                    refine ⟨107464312256938323362515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 573142998703671057933413 107464312256938323362515)
                    ·
                      rfl

theorem cell22_313929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 7, 4].length) (baseStart_313929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_313929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_313929 prefixEnd_313929 := by exact prefixLift 313929
  have htrace : WordTrace (prefixWord ++ tailWord_313929) baseStart_313929 baseEnd_313929 := by
    simpa [prefixWord, tailWord_313929, baseEnd_313929] using wordTrace_append hprefix tailTrace_313929
  have hstable : (prefixWord ++ tailWord_313929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313929).length < 2 ^ (prefixWord ++ tailWord_313929).sum := by decide
  have hdescent : baseEnd_313929 < baseStart_313929 := by decide
  rcases family_descends (prefixWord ++ tailWord_313929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313989 : List Nat := [1, 3, 1, 1, 4, 12]
def baseStart_313989 : Nat := 118140960795 + 313989 * 2 ^ 59
def prefixEnd_313989 : Nat := 4983230072969 + 3 ^ 40 * 313989 * 2
def baseEnd_313989 : Nat := 1326973475100224282251

theorem tailTrace_313989 : CollatzResearch.WordTrace tailWord_313989 prefixEnd_313989 1326973475100224282251 := by
  unfold tailWord_313989
  simp only [CollatzResearch.WordTrace]
  refine ⟨11452119659478952897001021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7634746439652635264667347 11452119659478952897001021)
  ·
    refine ⟨4294544872304607336375383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11452119659478952897001021 4294544872304607336375383)
    ·
      refine ⟨6441817308456911004563075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4294544872304607336375383 6441817308456911004563075)
      ·
        refine ⟨9662725962685366506844613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6441817308456911004563075 9662725962685366506844613)
        ·
          refine ⟨1811761118003506220033365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9662725962685366506844613 1811761118003506220033365)
          ·
            refine ⟨1326973475100224282251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 1811761118003506220033365 1326973475100224282251)
            ·
              rfl

theorem cell22_313989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 12].length) (baseStart_313989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_313989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_313989 prefixEnd_313989 := by exact prefixLift 313989
  have htrace : WordTrace (prefixWord ++ tailWord_313989) baseStart_313989 baseEnd_313989 := by
    simpa [prefixWord, tailWord_313989, baseEnd_313989] using wordTrace_append hprefix tailTrace_313989
  have hstable : (prefixWord ++ tailWord_313989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313989).length < 2 ^ (prefixWord ++ tailWord_313989).sum := by decide
  have hdescent : baseEnd_313989 < baseStart_313989 := by decide
  rcases family_descends (prefixWord ++ tailWord_313989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313991 : List Nat := [1, 1, 4, 2, 1, 2, 1, 4, 2, 4]
def baseStart_313991 : Nat := 118140960795 + 313991 * 2 ^ 59
def prefixEnd_313991 : Nat := 4983230072969 + 3 ^ 40 * 313991 * 2
def baseEnd_313991 : Nat := 107485536123990828312325

theorem tailTrace_313991 : CollatzResearch.WordTrace tailWord_313991 prefixEnd_313991 107485536123990828312325 := by
  unfold tailWord_313991
  simp only [CollatzResearch.WordTrace]
  refine ⟨11452192605471707238573827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7634795070314471492382551 11452192605471707238573827)
  ·
    refine ⟨17178288908207560857860741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11452192605471707238573827 17178288908207560857860741)
    ·
      refine ⟨3220929170288917660848889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17178288908207560857860741 3220929170288917660848889)
      ·
        refine ⟨2415696877716688245636667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3220929170288917660848889 2415696877716688245636667)
        ·
          refine ⟨3623545316575032368455001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2415696877716688245636667 3623545316575032368455001)
          ·
            refine ⟨2717658987431274276341251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3623545316575032368455001 2717658987431274276341251)
            ·
              refine ⟨4076488481146911414511877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2717658987431274276341251 4076488481146911414511877)
              ·
                refine ⟨764341590215045890220977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4076488481146911414511877 764341590215045890220977)
                ·
                  refine ⟨573256192661284417665733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 764341590215045890220977 573256192661284417665733)
                  ·
                    refine ⟨107485536123990828312325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 573256192661284417665733 107485536123990828312325)
                    ·
                      rfl

theorem cell22_313991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 4, 2, 4].length) (baseStart_313991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_313991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_313991 prefixEnd_313991 := by exact prefixLift 313991
  have htrace : WordTrace (prefixWord ++ tailWord_313991) baseStart_313991 baseEnd_313991 := by
    simpa [prefixWord, tailWord_313991, baseEnd_313991] using wordTrace_append hprefix tailTrace_313991
  have hstable : (prefixWord ++ tailWord_313991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313991).length < 2 ^ (prefixWord ++ tailWord_313991).sum := by decide
  have hdescent : baseEnd_313991 < baseStart_313991 := by decide
  rcases family_descends (prefixWord ++ tailWord_313991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314010 : List Nat := [3, 1, 1, 6, 1, 1, 2, 1, 1, 5]
def baseStart_314010 : Nat := 118140960795 + 314010 * 2 ^ 59
def prefixEnd_314010 : Nat := 4983230072969 + 3 ^ 40 * 314010 * 2
def baseEnd_314010 : Nat := 107492040212281112087267

theorem tailTrace_314010 : CollatzResearch.WordTrace tailWord_314010 prefixEnd_314010 107492040212281112087267 := by
  unfold tailWord_314010
  simp only [CollatzResearch.WordTrace]
  refine ⟨2863221398100718370878871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7635257061601915655676989 2863221398100718370878871)
  ·
    refine ⟨4294832097151077556318307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2863221398100718370878871 4294832097151077556318307)
    ·
      refine ⟨6442248145726616334477461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4294832097151077556318307 6442248145726616334477461)
      ·
        refine ⟨301980381830935140678631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6442248145726616334477461 301980381830935140678631)
        ·
          refine ⟨452970572746402711017947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 301980381830935140678631 452970572746402711017947)
          ·
            refine ⟨679455859119604066526921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 452970572746402711017947 679455859119604066526921)
            ·
              refine ⟨509591894339703049895191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 679455859119604066526921 509591894339703049895191)
              ·
                refine ⟨764387841509554574842787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 509591894339703049895191 764387841509554574842787)
                ·
                  refine ⟨1146581762264331862264181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 764387841509554574842787 1146581762264331862264181)
                  ·
                    refine ⟨107492040212281112087267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1146581762264331862264181 107492040212281112087267)
                    ·
                      rfl

theorem cell22_314010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 1, 1, 5].length) (baseStart_314010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_314010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_314010 prefixEnd_314010 := by exact prefixLift 314010
  have htrace : WordTrace (prefixWord ++ tailWord_314010) baseStart_314010 baseEnd_314010 := by
    simpa [prefixWord, tailWord_314010, baseEnd_314010] using wordTrace_append hprefix tailTrace_314010
  have hstable : (prefixWord ++ tailWord_314010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314010).length < 2 ^ (prefixWord ++ tailWord_314010).sum := by decide
  have hdescent : baseEnd_314010 < baseStart_314010 := by decide
  rcases family_descends (prefixWord ++ tailWord_314010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314143 : List Nat := [1, 1, 2, 4, 2, 2, 1, 3, 2, 4]
def baseStart_314143 : Nat := 118140960795 + 314143 * 2 ^ 59
def prefixEnd_314143 : Nat := 4983230072969 + 3 ^ 40 * 314143 * 2
def baseEnd_314143 : Nat := 107537568830313098511859

theorem tailTrace_314143 : CollatzResearch.WordTrace tailWord_314143 prefixEnd_314143 107537568830313098511859 := by
  unfold tailWord_314143
  simp only [CollatzResearch.WordTrace]
  refine ⟨11457736500921037198107083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7638491000614024798738055 11457736500921037198107083)
  ·
    refine ⟨17186604751381555797160625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11457736500921037198107083 17186604751381555797160625)
    ·
      refine ⟨12889953563536166847870469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17186604751381555797160625 12889953563536166847870469)
      ·
        refine ⟨2416866293163031283975713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12889953563536166847870469 2416866293163031283975713)
        ·
          refine ⟨1812649719872273462981785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2416866293163031283975713 1812649719872273462981785)
          ·
            refine ⟨1359487289904205097236339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1812649719872273462981785 1359487289904205097236339)
            ·
              refine ⟨2039230934856307645854509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1359487289904205097236339 2039230934856307645854509)
              ·
                refine ⟨764711600571115367195441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2039230934856307645854509 764711600571115367195441)
                ·
                  refine ⟨573533700428336525396581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 764711600571115367195441 573533700428336525396581)
                  ·
                    refine ⟨107537568830313098511859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 573533700428336525396581 107537568830313098511859)
                    ·
                      rfl

theorem cell22_314143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 3, 2, 4].length) (baseStart_314143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_314143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_314143 prefixEnd_314143 := by exact prefixLift 314143
  have htrace : WordTrace (prefixWord ++ tailWord_314143) baseStart_314143 baseEnd_314143 := by
    simpa [prefixWord, tailWord_314143, baseEnd_314143] using wordTrace_append hprefix tailTrace_314143
  have hstable : (prefixWord ++ tailWord_314143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314143).length < 2 ^ (prefixWord ++ tailWord_314143).sum := by decide
  have hdescent : baseEnd_314143 < baseStart_314143 := by decide
  rcases family_descends (prefixWord ++ tailWord_314143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314158 : List Nat := [4, 1, 3, 2, 1, 11]
def baseStart_314158 : Nat := 118140960795 + 314158 * 2 ^ 59
def prefixEnd_314158 : Nat := 4983230072969 + 3 ^ 40 * 314158 * 2
def baseEnd_314158 : Nat := 1327687699220469868973

theorem tailTrace_314158 : CollatzResearch.WordTrace tailWord_314158 prefixEnd_314158 1327687699220469868973 := by
  unfold tailWord_314158
  simp only [CollatzResearch.WordTrace]
  refine ⟨1432285449483336844987891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7638855730577796506602085 1432285449483336844987891)
  ·
    refine ⟨2148428174225005267481837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1432285449483336844987891 2148428174225005267481837)
    ·
      refine ⟨805660565334376975305689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2148428174225005267481837 805660565334376975305689)
      ·
        refine ⟨604245424000782731479267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 805660565334376975305689 604245424000782731479267)
        ·
          refine ⟨906368136001174097218901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 604245424000782731479267 906368136001174097218901)
          ·
            refine ⟨1327687699220469868973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 906368136001174097218901 1327687699220469868973)
            ·
              rfl

theorem cell22_314158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 11].length) (baseStart_314158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_314158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_314158 prefixEnd_314158 := by exact prefixLift 314158
  have htrace : WordTrace (prefixWord ++ tailWord_314158) baseStart_314158 baseEnd_314158 := by
    simpa [prefixWord, tailWord_314158, baseEnd_314158] using wordTrace_append hprefix tailTrace_314158
  have hstable : (prefixWord ++ tailWord_314158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314158).length < 2 ^ (prefixWord ++ tailWord_314158).sum := by decide
  have hdescent : baseEnd_314158 < baseStart_314158 := by decide
  rcases family_descends (prefixWord ++ tailWord_314158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314207 : List Nat := [1, 1, 2, 3, 1, 3, 4, 3, 1, 3]
def baseStart_314207 : Nat := 118140960795 + 314207 * 2 ^ 59
def prefixEnd_314207 : Nat := 4983230072969 + 3 ^ 40 * 314207 * 2
def baseEnd_314207 : Nat := 107559477338238264911663

theorem tailTrace_314207 : CollatzResearch.WordTrace tailWord_314207 prefixEnd_314207 107559477338238264911663 := by
  unfold tailWord_314207
  simp only [CollatzResearch.WordTrace]
  refine ⟨11460070772689176128436875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7640047181792784085624583 11460070772689176128436875)
  ·
    refine ⟨17190106159033764192655313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11460070772689176128436875 17190106159033764192655313)
    ·
      refine ⟨12892579619275323144491485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17190106159033764192655313 12892579619275323144491485)
      ·
        refine ⟨4834717357228246179184307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12892579619275323144491485 4834717357228246179184307)
        ·
          refine ⟨7252076035842369268776461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4834717357228246179184307 7252076035842369268776461)
          ·
            refine ⟨2719528513440888475791173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7252076035842369268776461 2719528513440888475791173)
            ·
              refine ⟨509911596270166589210845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2719528513440888475791173 509911596270166589210845)
              ·
                refine ⟨191216848601312470954067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 509911596270166589210845 191216848601312470954067)
                ·
                  refine ⟨286825272901968706431101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 191216848601312470954067 286825272901968706431101)
                  ·
                    refine ⟨107559477338238264911663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 286825272901968706431101 107559477338238264911663)
                    ·
                      rfl

theorem cell22_314207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 3, 1, 3].length) (baseStart_314207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_314207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_314207 prefixEnd_314207 := by exact prefixLift 314207
  have htrace : WordTrace (prefixWord ++ tailWord_314207) baseStart_314207 baseEnd_314207 := by
    simpa [prefixWord, tailWord_314207, baseEnd_314207] using wordTrace_append hprefix tailTrace_314207
  have hstable : (prefixWord ++ tailWord_314207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314207).length < 2 ^ (prefixWord ++ tailWord_314207).sum := by decide
  have hdescent : baseEnd_314207 < baseStart_314207 := by decide
  rcases family_descends (prefixWord ++ tailWord_314207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314258 : List Nat := [3, 2, 3, 2, 3, 1, 1, 3, 1, 3]
def baseStart_314258 : Nat := 118140960795 + 314258 * 2 ^ 59
def prefixEnd_314258 : Nat := 4983230072969 + 3 ^ 40 * 314258 * 2
def baseEnd_314258 : Nat := 107576935680491131886507

theorem tailTrace_314258 : CollatzResearch.WordTrace tailWord_314258 prefixEnd_314258 107576935680491131886507 := by
  unfold tailWord_314258
  simp only [CollatzResearch.WordTrace]
  refine ⟨2865482723876102959635857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7641287263669607892362285 2865482723876102959635857)
  ·
    refine ⟨2149112042907077219726893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2865482723876102959635857 2149112042907077219726893)
    ·
      refine ⟨805917016090153957397585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2149112042907077219726893 805917016090153957397585)
      ·
        refine ⟨604437762067615468048189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 805917016090153957397585 604437762067615468048189)
        ·
          refine ⟨226664160775355800518071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 604437762067615468048189 226664160775355800518071)
          ·
            refine ⟨339996241163033700777107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226664160775355800518071 339996241163033700777107)
            ·
              refine ⟨509994361744550551165661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 339996241163033700777107 509994361744550551165661)
              ·
                refine ⟨191247885654206456687123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 509994361744550551165661 191247885654206456687123)
                ·
                  refine ⟨286871828481309685030685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 191247885654206456687123 286871828481309685030685)
                  ·
                    refine ⟨107576935680491131886507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 286871828481309685030685 107576935680491131886507)
                    ·
                      rfl

theorem cell22_314258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_314258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_314258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_314258 prefixEnd_314258 := by exact prefixLift 314258
  have htrace : WordTrace (prefixWord ++ tailWord_314258) baseStart_314258 baseEnd_314258 := by
    simpa [prefixWord, tailWord_314258, baseEnd_314258] using wordTrace_append hprefix tailTrace_314258
  have hstable : (prefixWord ++ tailWord_314258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314258).length < 2 ^ (prefixWord ++ tailWord_314258).sum := by decide
  have hdescent : baseEnd_314258 < baseStart_314258 := by decide
  rcases family_descends (prefixWord ++ tailWord_314258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314263 : List Nat := [1, 1, 3, 3, 1, 2, 2, 1, 3, 5]
def baseStart_314263 : Nat := 118140960795 + 314263 * 2 ^ 59
def prefixEnd_314263 : Nat := 4983230072969 + 3 ^ 40 * 314263 * 2
def baseEnd_314263 : Nat := 107578647282672785511491

theorem tailTrace_314263 : CollatzResearch.WordTrace tailWord_314263 prefixEnd_314263 107578647282672785511491 := by
  unfold tailWord_314263
  simp only [CollatzResearch.WordTrace]
  refine ⟨11462113260486297692475443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7641408840324198461650295 11462113260486297692475443)
  ·
    refine ⟨17193169890729446538713165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11462113260486297692475443 17193169890729446538713165)
    ·
      refine ⟨6447438709023542452017437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17193169890729446538713165 6447438709023542452017437)
      ·
        refine ⟨2417789515883828419506539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6447438709023542452017437 2417789515883828419506539)
        ·
          refine ⟨3626684273825742629259809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2417789515883828419506539 3626684273825742629259809)
          ·
            refine ⟨2720013205369306971944857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3626684273825742629259809 2720013205369306971944857)
            ·
              refine ⟨2040009904026980228958643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2720013205369306971944857 2040009904026980228958643)
              ·
                refine ⟨3060014856040470343437965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2040009904026980228958643 3060014856040470343437965)
                ·
                  refine ⟨1147505571015176378789237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3060014856040470343437965 1147505571015176378789237)
                  ·
                    refine ⟨107578647282672785511491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1147505571015176378789237 107578647282672785511491)
                    ·
                      rfl

theorem cell22_314263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 3, 5].length) (baseStart_314263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_314263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_314263 prefixEnd_314263 := by exact prefixLift 314263
  have htrace : WordTrace (prefixWord ++ tailWord_314263) baseStart_314263 baseEnd_314263 := by
    simpa [prefixWord, tailWord_314263, baseEnd_314263] using wordTrace_append hprefix tailTrace_314263
  have hstable : (prefixWord ++ tailWord_314263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314263).length < 2 ^ (prefixWord ++ tailWord_314263).sum := by decide
  have hdescent : baseEnd_314263 < baseStart_314263 := by decide
  rcases family_descends (prefixWord ++ tailWord_314263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314297 : List Nat := [1, 2, 1, 4, 2, 3, 1, 3, 2, 3]
def baseStart_314297 : Nat := 118140960795 + 314297 * 2 ^ 59
def prefixEnd_314297 : Nat := 4983230072969 + 3 ^ 40 * 314297 * 2
def baseEnd_314297 : Nat := 107590286177508030161387

theorem tailTrace_314297 : CollatzResearch.WordTrace tailWord_314297 prefixEnd_314297 107590286177508030161387 := by
  unfold tailWord_314297
  simp only [CollatzResearch.WordTrace]
  refine ⟨11463353342363121499213145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7642235561575414332808763 11463353342363121499213145)
  ·
    refine ⟨8597515006772341124409859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11463353342363121499213145 8597515006772341124409859)
    ·
      refine ⟨12896272510158511686614789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8597515006772341124409859 12896272510158511686614789)
      ·
        refine ⟨2418051095654720941240273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12896272510158511686614789 2418051095654720941240273)
        ·
          refine ⟨1813538321741040705930205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2418051095654720941240273 1813538321741040705930205)
          ·
            refine ⟨680076870652890264723827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1813538321741040705930205 680076870652890264723827)
            ·
              refine ⟨1020115305979335397085741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 680076870652890264723827 1020115305979335397085741)
              ·
                refine ⟨382543239742250773907153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1020115305979335397085741 382543239742250773907153)
                ·
                  refine ⟨286907429806688080430365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 382543239742250773907153 286907429806688080430365)
                  ·
                    refine ⟨107590286177508030161387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 286907429806688080430365 107590286177508030161387)
                    ·
                      rfl

theorem cell22_314297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 3, 2, 3].length) (baseStart_314297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_314297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_314297 prefixEnd_314297 := by exact prefixLift 314297
  have htrace : WordTrace (prefixWord ++ tailWord_314297) baseStart_314297 baseEnd_314297 := by
    simpa [prefixWord, tailWord_314297, baseEnd_314297] using wordTrace_append hprefix tailTrace_314297
  have hstable : (prefixWord ++ tailWord_314297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314297).length < 2 ^ (prefixWord ++ tailWord_314297).sum := by decide
  have hdescent : baseEnd_314297 < baseStart_314297 := by decide
  rcases family_descends (prefixWord ++ tailWord_314297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314312 : List Nat := [2, 1, 3, 1, 5, 1, 2, 1, 2, 4]
def baseStart_314312 : Nat := 118140960795 + 314312 * 2 ^ 59
def prefixEnd_314312 : Nat := 4983230072969 + 3 ^ 40 * 314312 * 2
def baseEnd_314312 : Nat := 107595420984052991036341

theorem tailTrace_314312 : CollatzResearch.WordTrace tailWord_314312 prefixEnd_314312 107595420984052991036341 := by
  unfold tailWord_314312
  simp only [CollatzResearch.WordTrace]
  refine ⟨5731950218654389530504595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7642600291539186040672793 5731950218654389530504595)
  ·
    refine ⟨8597925327981584295756893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5731950218654389530504595 8597925327981584295756893)
    ·
      refine ⟨3224221997993094110908835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8597925327981584295756893 3224221997993094110908835)
      ·
        refine ⟨4836332996989641166363253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3224221997993094110908835 4836332996989641166363253)
        ·
          refine ⟨453406218467778859346555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4836332996989641166363253 453406218467778859346555)
          ·
            refine ⟨680109327701668289019833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 453406218467778859346555 680109327701668289019833)
            ·
              refine ⟨510081995776251216764875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 680109327701668289019833 510081995776251216764875)
              ·
                refine ⟨765122993664376825147313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 510081995776251216764875 765122993664376825147313)
                ·
                  refine ⟨573842245248282618860485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 765122993664376825147313 573842245248282618860485)
                  ·
                    refine ⟨107595420984052991036341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 573842245248282618860485 107595420984052991036341)
                    ·
                      rfl

theorem cell22_314312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 1, 2, 4].length) (baseStart_314312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_314312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_314312 prefixEnd_314312 := by exact prefixLift 314312
  have htrace : WordTrace (prefixWord ++ tailWord_314312) baseStart_314312 baseEnd_314312 := by
    simpa [prefixWord, tailWord_314312, baseEnd_314312] using wordTrace_append hprefix tailTrace_314312
  have hstable : (prefixWord ++ tailWord_314312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314312).length < 2 ^ (prefixWord ++ tailWord_314312).sum := by decide
  have hdescent : baseEnd_314312 < baseStart_314312 := by decide
  rcases family_descends (prefixWord ++ tailWord_314312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314466 : List Nat := [3, 3, 2, 2, 1, 2, 1, 3, 2, 3]
def baseStart_314466 : Nat := 118140960795 + 314466 * 2 ^ 59
def prefixEnd_314466 : Nat := 4983230072969 + 3 ^ 40 * 314466 * 2
def baseEnd_314466 : Nat := 107648138331247922685869

theorem tailTrace_314466 : CollatzResearch.WordTrace tailWord_314466 prefixEnd_314466 107648138331247922685869 := by
  unfold tailWord_314466
  simp only [CollatzResearch.WordTrace]
  refine ⟨2867379319687715840528813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7646344852500575574743501 2867379319687715840528813)
  ·
    refine ⟨1075267244882893440198305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2867379319687715840528813 1075267244882893440198305)
    ·
      refine ⟨806450433662170080148729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1075267244882893440198305 806450433662170080148729)
      ·
        refine ⟨604837825246627560111547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 806450433662170080148729 604837825246627560111547)
        ·
          refine ⟨907256737869941340167321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 604837825246627560111547 907256737869941340167321)
          ·
            refine ⟨680442553402456005125491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 907256737869941340167321 680442553402456005125491)
            ·
              refine ⟨1020663830103684007688237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 680442553402456005125491 1020663830103684007688237)
              ·
                refine ⟨382748936288881502883089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1020663830103684007688237 382748936288881502883089)
                ·
                  refine ⟨287061702216661127162317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 382748936288881502883089 287061702216661127162317)
                  ·
                    refine ⟨107648138331247922685869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 287061702216661127162317 107648138331247922685869)
                    ·
                      rfl

theorem cell22_314466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_314466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_314466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_314466 prefixEnd_314466 := by exact prefixLift 314466
  have htrace : WordTrace (prefixWord ++ tailWord_314466) baseStart_314466 baseEnd_314466 := by
    simpa [prefixWord, tailWord_314466, baseEnd_314466] using wordTrace_append hprefix tailTrace_314466
  have hstable : (prefixWord ++ tailWord_314466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314466).length < 2 ^ (prefixWord ++ tailWord_314466).sum := by decide
  have hdescent : baseEnd_314466 < baseStart_314466 := by decide
  rcases family_descends (prefixWord ++ tailWord_314466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314522 : List Nat := [3, 1, 1, 5, 1, 1, 1, 1, 1, 7]
def baseStart_314522 : Nat := 118140960795 + 314522 * 2 ^ 59
def prefixEnd_314522 : Nat := 4983230072969 + 3 ^ 40 * 314522 * 2
def baseEnd_314522 : Nat := 107667308275682443285697

theorem tailTrace_314522 : CollatzResearch.WordTrace tailWord_314522 prefixEnd_314522 107667308275682443285697 := by
  unfold tailWord_314522
  simp only [CollatzResearch.WordTrace]
  refine ⟨2867889941636996231538455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7647706511031989950769213 2867889941636996231538455)
  ·
    refine ⟨4301834912455494347307683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2867889941636996231538455 4301834912455494347307683)
    ·
      refine ⟨6452752368683241520961525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4301834912455494347307683 6452752368683241520961525)
      ·
        refine ⟨604945534564053892590143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6452752368683241520961525 604945534564053892590143)
        ·
          refine ⟨907418301846080838885215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 604945534564053892590143 907418301846080838885215)
          ·
            refine ⟨1361127452769121258327823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 907418301846080838885215 1361127452769121258327823)
            ·
              refine ⟨2041691179153681887491735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1361127452769121258327823 2041691179153681887491735)
              ·
                refine ⟨3062536768730522831237603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2041691179153681887491735 3062536768730522831237603)
                ·
                  refine ⟨4593805153095784246856405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3062536768730522831237603 4593805153095784246856405)
                  ·
                    refine ⟨107667308275682443285697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4593805153095784246856405 107667308275682443285697)
                    ·
                      rfl

theorem cell22_314522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 1, 7].length) (baseStart_314522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_314522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_314522 prefixEnd_314522 := by exact prefixLift 314522
  have htrace : WordTrace (prefixWord ++ tailWord_314522) baseStart_314522 baseEnd_314522 := by
    simpa [prefixWord, tailWord_314522, baseEnd_314522] using wordTrace_append hprefix tailTrace_314522
  have hstable : (prefixWord ++ tailWord_314522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314522).length < 2 ^ (prefixWord ++ tailWord_314522).sum := by decide
  have hdescent : baseEnd_314522 < baseStart_314522 := by decide
  rcases family_descends (prefixWord ++ tailWord_314522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314657 : List Nat := [1, 2, 3, 2, 1, 1, 1, 2, 4, 5]
def baseStart_314657 : Nat := 118140960795 + 314657 * 2 ^ 59
def prefixEnd_314657 : Nat := 4983230072969 + 3 ^ 40 * 314657 * 2
def baseEnd_314657 : Nat := 107713521534587091160283

theorem tailTrace_314657 : CollatzResearch.WordTrace tailWord_314657 prefixEnd_314657 107713521534587091160283 := by
  unfold tailWord_314657
  simp only [CollatzResearch.WordTrace]
  refine ⟨11476483621058902982318225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7650989080705935321545483 11476483621058902982318225)
  ·
    refine ⟨8607362715794177236738669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11476483621058902982318225 8607362715794177236738669)
    ·
      refine ⟨3227761018422816463777001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8607362715794177236738669 3227761018422816463777001)
      ·
        refine ⟨2420820763817112347832751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3227761018422816463777001 2420820763817112347832751)
        ·
          refine ⟨3631231145725668521749127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2420820763817112347832751 3631231145725668521749127)
          ·
            refine ⟨5446846718588502782623691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3631231145725668521749127 5446846718588502782623691)
            ·
              refine ⟨8170270077882754173935537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5446846718588502782623691 8170270077882754173935537)
              ·
                refine ⟨6127702558412065630451653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8170270077882754173935537 6127702558412065630451653)
                ·
                  refine ⟨1148944229702262305709685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6127702558412065630451653 1148944229702262305709685)
                  ·
                    refine ⟨107713521534587091160283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1148944229702262305709685 107713521534587091160283)
                    ·
                      rfl

theorem cell22_314657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_314657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_314657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_314657 prefixEnd_314657 := by exact prefixLift 314657
  have htrace : WordTrace (prefixWord ++ tailWord_314657) baseStart_314657 baseEnd_314657 := by
    simpa [prefixWord, tailWord_314657, baseEnd_314657] using wordTrace_append hprefix tailTrace_314657
  have hstable : (prefixWord ++ tailWord_314657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314657).length < 2 ^ (prefixWord ++ tailWord_314657).sum := by decide
  have hdescent : baseEnd_314657 < baseStart_314657 := by decide
  rcases family_descends (prefixWord ++ tailWord_314657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314676 : List Nat := [2, 5, 1, 1, 1, 1, 4, 2, 5]
def baseStart_314676 : Nat := 118140960795 + 314676 * 2 ^ 59
def prefixEnd_314676 : Nat := 4983230072969 + 3 ^ 40 * 314676 * 2
def baseEnd_314676 : Nat := 35906675207625791645075

theorem tailTrace_314676 : CollatzResearch.WordTrace tailWord_314676 prefixEnd_314676 35906675207625791645075 := by
  unfold tailWord_314676
  simp only [CollatzResearch.WordTrace]
  refine ⟨5738588303995034613629941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7651451071993379484839921 5738588303995034613629941)
  ·
    refine ⟨537992653499534495027807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5738588303995034613629941 537992653499534495027807)
    ·
      refine ⟨806988980249301742541711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 537992653499534495027807 806988980249301742541711)
      ·
        refine ⟨1210483470373952613812567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 806988980249301742541711 1210483470373952613812567)
        ·
          refine ⟨1815725205560928920718851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1210483470373952613812567 1815725205560928920718851)
          ·
            refine ⟨2723587808341393381078277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1815725205560928920718851 2723587808341393381078277)
            ·
              refine ⟨510672714064011258952177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2723587808341393381078277 510672714064011258952177)
              ·
                refine ⟨383004535548008444214133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 510672714064011258952177 383004535548008444214133)
                ·
                  refine ⟨35906675207625791645075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 383004535548008444214133 35906675207625791645075)
                  ·
                    rfl

theorem cell22_314676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_314676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_314676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_314676 prefixEnd_314676 := by exact prefixLift 314676
  have htrace : WordTrace (prefixWord ++ tailWord_314676) baseStart_314676 baseEnd_314676 := by
    simpa [prefixWord, tailWord_314676, baseEnd_314676] using wordTrace_append hprefix tailTrace_314676
  have hstable : (prefixWord ++ tailWord_314676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314676).length < 2 ^ (prefixWord ++ tailWord_314676).sum := by decide
  have hdescent : baseEnd_314676 < baseStart_314676 := by decide
  rcases family_descends (prefixWord ++ tailWord_314676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314719 : List Nat := [1, 1, 2, 3, 1, 2, 1, 4, 4, 3]
def baseStart_314719 : Nat := 118140960795 + 314719 * 2 ^ 59
def prefixEnd_314719 : Nat := 4983230072969 + 3 ^ 40 * 314719 * 2
def baseEnd_314719 : Nat := 107734745401639596110093

theorem tailTrace_314719 : CollatzResearch.WordTrace tailWord_314719 prefixEnd_314719 107734745401639596110093 := by
  unfold tailWord_314719
  simp only [CollatzResearch.WordTrace]
  refine ⟨11478744946834287571075211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7652496631222858380716807 11478744946834287571075211)
  ·
    refine ⟨17218117420251431356612817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11478744946834287571075211 17218117420251431356612817)
    ·
      refine ⟨12913588065188573517459613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17218117420251431356612817 12913588065188573517459613)
      ·
        refine ⟨4842595524445715069047355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12913588065188573517459613 4842595524445715069047355)
        ·
          refine ⟨7263893286668572603571033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4842595524445715069047355 7263893286668572603571033)
          ·
            refine ⟨5447919965001429452678275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7263893286668572603571033 5447919965001429452678275)
            ·
              refine ⟨8171879947502144179017413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5447919965001429452678275 8171879947502144179017413)
              ·
                refine ⟨1532227490156652033565765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8171879947502144179017413 1532227490156652033565765)
                ·
                  refine ⟨287292654404372256293581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1532227490156652033565765 287292654404372256293581)
                  ·
                    refine ⟨107734745401639596110093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 287292654404372256293581 107734745401639596110093)
                    ·
                      rfl

theorem cell22_314719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 4, 3].length) (baseStart_314719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_314719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_314719 prefixEnd_314719 := by exact prefixLift 314719
  have htrace : WordTrace (prefixWord ++ tailWord_314719) baseStart_314719 baseEnd_314719 := by
    simpa [prefixWord, tailWord_314719, baseEnd_314719] using wordTrace_append hprefix tailTrace_314719
  have hstable : (prefixWord ++ tailWord_314719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314719).length < 2 ^ (prefixWord ++ tailWord_314719).sum := by decide
  have hdescent : baseEnd_314719 < baseStart_314719 := by decide
  rcases family_descends (prefixWord ++ tailWord_314719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314723 : List Nat := [1, 1, 1, 5, 2, 4, 2, 1, 1, 4]
def baseStart_314723 : Nat := 118140960795 + 314723 * 2 ^ 59
def prefixEnd_314723 : Nat := 4983230072969 + 3 ^ 40 * 314723 * 2
def baseEnd_314723 : Nat := 107736114683384919010081

theorem tailTrace_314723 : CollatzResearch.WordTrace tailWord_314723 prefixEnd_314723 107736114683384919010081 := by
  unfold tailWord_314723
  simp only [CollatzResearch.WordTrace]
  refine ⟨11478890838819796254220823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7652593892546530836147215 11478890838819796254220823)
  ·
    refine ⟨17218336258229694381331235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11478890838819796254220823 17218336258229694381331235)
    ·
      refine ⟨25827504387344541571996853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17218336258229694381331235 25827504387344541571996853)
      ·
        refine ⟨2421328536313550772374705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25827504387344541571996853 2421328536313550772374705)
        ·
          refine ⟨1815996402235163079281029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2421328536313550772374705 1815996402235163079281029)
          ·
            refine ⟨340499325419093077365193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1815996402235163079281029 340499325419093077365193)
            ·
              refine ⟨255374494064319808023895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 340499325419093077365193 255374494064319808023895)
              ·
                refine ⟨383061741096479712035843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 255374494064319808023895 383061741096479712035843)
                ·
                  refine ⟨574592611644719568053765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 383061741096479712035843 574592611644719568053765)
                  ·
                    refine ⟨107736114683384919010081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 574592611644719568053765 107736114683384919010081)
                    ·
                      rfl

theorem cell22_314723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 2, 1, 1, 4].length) (baseStart_314723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_314723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_314723 prefixEnd_314723 := by exact prefixLift 314723
  have htrace : WordTrace (prefixWord ++ tailWord_314723) baseStart_314723 baseEnd_314723 := by
    simpa [prefixWord, tailWord_314723, baseEnd_314723] using wordTrace_append hprefix tailTrace_314723
  have hstable : (prefixWord ++ tailWord_314723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314723).length < 2 ^ (prefixWord ++ tailWord_314723).sum := by decide
  have hdescent : baseEnd_314723 < baseStart_314723 := by decide
  rcases family_descends (prefixWord ++ tailWord_314723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314753 : List Nat := [1, 2, 4, 3, 2, 2, 1, 1, 1, 5]
def baseStart_314753 : Nat := 118140960795 + 314753 * 2 ^ 59
def prefixEnd_314753 : Nat := 4983230072969 + 3 ^ 40 * 314753 * 2
def baseEnd_314753 : Nat := 107746384296474840759989

theorem tailTrace_314753 : CollatzResearch.WordTrace tailWord_314753 prefixEnd_314753 107746384296474840759989 := by
  unfold tailWord_314753
  simp only [CollatzResearch.WordTrace]
  refine ⟨11479985028711111377812913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7653323352474074251875275 11479985028711111377812913)
  ·
    refine ⟨8609988771533333533359685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11479985028711111377812913 8609988771533333533359685)
    ·
      refine ⟨1614372894662500037504941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8609988771533333533359685 1614372894662500037504941)
      ·
        refine ⟨605389835498437514064353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1614372894662500037504941 605389835498437514064353)
        ·
          refine ⟨454042376623828135548265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 605389835498437514064353 454042376623828135548265)
          ·
            refine ⟨340531782467871101661199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 454042376623828135548265 340531782467871101661199)
            ·
              refine ⟨510797673701806652491799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 340531782467871101661199 510797673701806652491799)
              ·
                refine ⟨766196510552709978737699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 510797673701806652491799 766196510552709978737699)
                ·
                  refine ⟨1149294765829064968106549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 766196510552709978737699 1149294765829064968106549)
                  ·
                    refine ⟨107746384296474840759989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1149294765829064968106549 107746384296474840759989)
                    ·
                      rfl

theorem cell22_314753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 1, 1, 5].length) (baseStart_314753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_314753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_314753 prefixEnd_314753 := by exact prefixLift 314753
  have htrace : WordTrace (prefixWord ++ tailWord_314753) baseStart_314753 baseEnd_314753 := by
    simpa [prefixWord, tailWord_314753, baseEnd_314753] using wordTrace_append hprefix tailTrace_314753
  have hstable : (prefixWord ++ tailWord_314753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314753).length < 2 ^ (prefixWord ++ tailWord_314753).sum := by decide
  have hdescent : baseEnd_314753 < baseStart_314753 := by decide
  rcases family_descends (prefixWord ++ tailWord_314753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314766 : List Nat := [4, 1, 1, 4, 2, 1, 1, 8]
def baseStart_314766 : Nat := 118140960795 + 314766 * 2 ^ 59
def prefixEnd_314766 : Nat := 4983230072969 + 3 ^ 40 * 314766 * 2
def baseEnd_314766 : Nat := 11972314940238571131661

theorem tailTrace_314766 : CollatzResearch.WordTrace tailWord_314766 prefixEnd_314766 11972314940238571131661 := by
  unfold tailWord_314766
  simp only [CollatzResearch.WordTrace]
  refine ⟨1435057397208001824754519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7653639451776009732024101 1435057397208001824754519)
  ·
    refine ⟨2152586095812002737131779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1435057397208001824754519 2152586095812002737131779)
    ·
      refine ⟨3228879143718004105697669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2152586095812002737131779 3228879143718004105697669)
      ·
        refine ⟨605414839447125769818313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3228879143718004105697669 605414839447125769818313)
        ·
          refine ⟨454061129585344327363735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 605414839447125769818313 454061129585344327363735)
          ·
            refine ⟨681091694378016491045603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 454061129585344327363735 681091694378016491045603)
            ·
              refine ⟨1021637541567024736568405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 681091694378016491045603 1021637541567024736568405)
              ·
                refine ⟨11972314940238571131661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1021637541567024736568405 11972314940238571131661)
                ·
                  rfl

theorem cell22_314766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 8].length) (baseStart_314766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_314766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_314766 prefixEnd_314766 := by exact prefixLift 314766
  have htrace : WordTrace (prefixWord ++ tailWord_314766) baseStart_314766 baseEnd_314766 := by
    simpa [prefixWord, tailWord_314766, baseEnd_314766] using wordTrace_append hprefix tailTrace_314766
  have hstable : (prefixWord ++ tailWord_314766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314766).length < 2 ^ (prefixWord ++ tailWord_314766).sum := by decide
  have hdescent : baseEnd_314766 < baseStart_314766 := by decide
  rcases family_descends (prefixWord ++ tailWord_314766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314892 : List Nat := [2, 2, 1, 2, 6, 1, 2, 1, 1, 4]
def baseStart_314892 : Nat := 118140960795 + 314892 * 2 ^ 59
def prefixEnd_314892 : Nat := 4983230072969 + 3 ^ 40 * 314892 * 2
def baseEnd_314892 : Nat := 107793966837124811534563

theorem tailTrace_314892 : CollatzResearch.WordTrace tailWord_314892 prefixEnd_314892 107793966837124811534563 := by
  unfold tailWord_314892
  simp only [CollatzResearch.WordTrace]
  refine ⟨5742527387603769058561465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7656703183471692078081953 5742527387603769058561465)
  ·
    refine ⟨4306895540702826793921099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5742527387603769058561465 4306895540702826793921099)
    ·
      refine ⟨6460343311054240190881649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4306895540702826793921099 6460343311054240190881649)
      ·
        refine ⟨4845257483290680143161237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6460343311054240190881649 4845257483290680143161237)
        ·
          refine ⟨227121444529250631710683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4845257483290680143161237 227121444529250631710683)
          ·
            refine ⟨340682166793875947566025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227121444529250631710683 340682166793875947566025)
            ·
              refine ⟨255511625095406960674519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 340682166793875947566025 255511625095406960674519)
              ·
                refine ⟨383267437643110441011779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 255511625095406960674519 383267437643110441011779)
                ·
                  refine ⟨574901156464665661517669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 383267437643110441011779 574901156464665661517669)
                  ·
                    refine ⟨107793966837124811534563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 574901156464665661517669 107793966837124811534563)
                    ·
                      rfl

theorem cell22_314892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 2, 1, 1, 4].length) (baseStart_314892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_314892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_314892 prefixEnd_314892 := by exact prefixLift 314892
  have htrace : WordTrace (prefixWord ++ tailWord_314892) baseStart_314892 baseEnd_314892 := by
    simpa [prefixWord, tailWord_314892, baseEnd_314892] using wordTrace_append hprefix tailTrace_314892
  have hstable : (prefixWord ++ tailWord_314892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314892).length < 2 ^ (prefixWord ++ tailWord_314892).sum := by decide
  have hdescent : baseEnd_314892 < baseStart_314892 := by decide
  rcases family_descends (prefixWord ++ tailWord_314892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314933 : List Nat := [1, 3, 3, 1, 1, 3, 2, 2, 3, 3]
def baseStart_314933 : Nat := 118140960795 + 314933 * 2 ^ 59
def prefixEnd_314933 : Nat := 4983230072969 + 3 ^ 40 * 314933 * 2
def baseEnd_314933 : Nat := 107808001975014371259437

theorem tailTrace_314933 : CollatzResearch.WordTrace tailWord_314933 prefixEnd_314933 107808001975014371259437 := by
  unfold tailWord_314933
  simp only [CollatzResearch.WordTrace]
  refine ⟨11486550168059002119365453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7657700112039334746243635 11486550168059002119365453)
  ·
    refine ⟨4307456313022125794762045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11486550168059002119365453 4307456313022125794762045)
    ·
      refine ⟨1615296117383297173035767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4307456313022125794762045 1615296117383297173035767)
      ·
        refine ⟨2422944176074945759553651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1615296117383297173035767 2422944176074945759553651)
        ·
          refine ⟨3634416264112418639330477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2422944176074945759553651 3634416264112418639330477)
          ·
            refine ⟨1362906099042156989748929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3634416264112418639330477 1362906099042156989748929)
            ·
              refine ⟨1022179574281617742311697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1362906099042156989748929 1022179574281617742311697)
              ·
                refine ⟨766634680711213306733773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1022179574281617742311697 766634680711213306733773)
                ·
                  refine ⟨287488005266704990025165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 766634680711213306733773 287488005266704990025165)
                  ·
                    refine ⟨107808001975014371259437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 287488005266704990025165 107808001975014371259437)
                    ·
                      rfl

theorem cell22_314933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 2, 3, 3].length) (baseStart_314933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_314933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_314933 prefixEnd_314933 := by exact prefixLift 314933
  have htrace : WordTrace (prefixWord ++ tailWord_314933) baseStart_314933 baseEnd_314933 := by
    simpa [prefixWord, tailWord_314933, baseEnd_314933] using wordTrace_append hprefix tailTrace_314933
  have hstable : (prefixWord ++ tailWord_314933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314933).length < 2 ^ (prefixWord ++ tailWord_314933).sum := by decide
  have hdescent : baseEnd_314933 < baseStart_314933 := by decide
  rcases family_descends (prefixWord ++ tailWord_314933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314967 : List Nat := [1, 1, 3, 2, 2, 4, 3, 2, 1, 3]
def baseStart_314967 : Nat := 118140960795 + 314967 * 2 ^ 59
def prefixEnd_314967 : Nat := 4983230072969 + 3 ^ 40 * 314967 * 2
def baseEnd_314967 : Nat := 107819640869849615909333

theorem tailTrace_314967 : CollatzResearch.WordTrace tailWord_314967 prefixEnd_314967 107819640869849615909333 := by
  unfold tailWord_314967
  simp only [CollatzResearch.WordTrace]
  refine ⟨11487790249935825926103155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7658526833290550617402103 11487790249935825926103155)
  ·
    refine ⟨17231685374903738889154733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11487790249935825926103155 17231685374903738889154733)
    ·
      refine ⟨6461882015588902083433025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17231685374903738889154733 6461882015588902083433025)
      ·
        refine ⟨4846411511691676562574769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6461882015588902083433025 4846411511691676562574769)
        ·
          refine ⟨3634808633768757421931077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4846411511691676562574769 3634808633768757421931077)
          ·
            refine ⟨681526618831642016612077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3634808633768757421931077 681526618831642016612077)
            ·
              refine ⟨255572482061865756229529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 681526618831642016612077 255572482061865756229529)
              ·
                refine ⟨191679361546399317172147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 255572482061865756229529 191679361546399317172147)
                ·
                  refine ⟨287519042319598975758221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 191679361546399317172147 287519042319598975758221)
                  ·
                    refine ⟨107819640869849615909333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 287519042319598975758221 107819640869849615909333)
                    ·
                      rfl

theorem cell22_314967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 3, 2, 1, 3].length) (baseStart_314967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_314967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_314967 prefixEnd_314967 := by exact prefixLift 314967
  have htrace : WordTrace (prefixWord ++ tailWord_314967) baseStart_314967 baseEnd_314967 := by
    simpa [prefixWord, tailWord_314967, baseEnd_314967] using wordTrace_append hprefix tailTrace_314967
  have hstable : (prefixWord ++ tailWord_314967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314967).length < 2 ^ (prefixWord ++ tailWord_314967).sum := by decide
  have hdescent : baseEnd_314967 < baseStart_314967 := by decide
  rcases family_descends (prefixWord ++ tailWord_314967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314976 : List Nat := [2, 1, 1, 3, 2, 1, 1, 4, 3, 4]
def baseStart_314976 : Nat := 118140960795 + 314976 * 2 ^ 59
def prefixEnd_314976 : Nat := 4983230072969 + 3 ^ 40 * 314976 * 2
def baseEnd_314976 : Nat := 107822721753776592434305

theorem tailTrace_314976 : CollatzResearch.WordTrace tailWord_314976 prefixEnd_314976 107822721753776592434305 := by
  unfold tailWord_314976
  simp only [CollatzResearch.WordTrace]
  refine ⟨5744059253451610231590391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7658745671268813642120521 5744059253451610231590391)
  ·
    refine ⟨8616088880177415347385587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5744059253451610231590391 8616088880177415347385587)
    ·
      refine ⟨12924133320266123021078381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8616088880177415347385587 12924133320266123021078381)
      ·
        refine ⟨4846549995099796132904393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12924133320266123021078381 4846549995099796132904393)
        ·
          refine ⟨3634912496324847099678295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4846549995099796132904393 3634912496324847099678295)
          ·
            refine ⟨5452368744487270649517443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3634912496324847099678295 5452368744487270649517443)
            ·
              refine ⟨8178553116730905974276165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5452368744487270649517443 8178553116730905974276165)
              ·
                refine ⟨1533478709387044870176781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8178553116730905974276165 1533478709387044870176781)
                ·
                  refine ⟨575054516020141826316293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1533478709387044870176781 575054516020141826316293)
                  ·
                    refine ⟨107822721753776592434305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 575054516020141826316293 107822721753776592434305)
                    ·
                      rfl

theorem cell22_314976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 3, 4].length) (baseStart_314976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_314976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_314976 prefixEnd_314976 := by exact prefixLift 314976
  have htrace : WordTrace (prefixWord ++ tailWord_314976) baseStart_314976 baseEnd_314976 := by
    simpa [prefixWord, tailWord_314976, baseEnd_314976] using wordTrace_append hprefix tailTrace_314976
  have hstable : (prefixWord ++ tailWord_314976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314976).length < 2 ^ (prefixWord ++ tailWord_314976).sum := by decide
  have hdescent : baseEnd_314976 < baseStart_314976 := by decide
  rcases family_descends (prefixWord ++ tailWord_314976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314980 : List Nat := [2, 3, 1, 1, 2, 5, 2, 1, 5]
def baseStart_314980 : Nat := 118140960795 + 314980 * 2 ^ 59
def prefixEnd_314980 : Nat := 4983230072969 + 3 ^ 40 * 314980 * 2
def baseEnd_314980 : Nat := 35941363678507305111431

theorem tailTrace_314980 : CollatzResearch.WordTrace tailWord_314980 prefixEnd_314980 35941363678507305111431 := by
  unfold tailWord_314980
  simp only [CollatzResearch.WordTrace]
  refine ⟨5744132199444364573163197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7658842932592486097550929 5744132199444364573163197)
  ·
    refine ⟨2154049574791636714936199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5744132199444364573163197 2154049574791636714936199)
    ·
      refine ⟨3231074362187455072404299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2154049574791636714936199 3231074362187455072404299)
      ·
        refine ⟨4846611543281182608606449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3231074362187455072404299 4846611543281182608606449)
        ·
          refine ⟨3634958657460886956454837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4846611543281182608606449 3634958657460886956454837)
          ·
            refine ⟨340777374136958152167641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3634958657460886956454837 340777374136958152167641)
            ·
              refine ⟨255583030602718614125731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 340777374136958152167641 255583030602718614125731)
              ·
                refine ⟨383374545904077921188597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 255583030602718614125731 383374545904077921188597)
                ·
                  refine ⟨35941363678507305111431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 383374545904077921188597 35941363678507305111431)
                  ·
                    rfl

theorem cell22_314980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 2, 1, 5].length) (baseStart_314980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_314980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_314980 prefixEnd_314980 := by exact prefixLift 314980
  have htrace : WordTrace (prefixWord ++ tailWord_314980) baseStart_314980 baseEnd_314980 := by
    simpa [prefixWord, tailWord_314980, baseEnd_314980] using wordTrace_append hprefix tailTrace_314980
  have hstable : (prefixWord ++ tailWord_314980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314980).length < 2 ^ (prefixWord ++ tailWord_314980).sum := by decide
  have hdescent : baseEnd_314980 < baseStart_314980 := by decide
  rcases family_descends (prefixWord ++ tailWord_314980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315008 : List Nat := [2, 1, 1, 2, 1, 4, 2, 5, 4]
def baseStart_315008 : Nat := 118140960795 + 315008 * 2 ^ 59
def prefixEnd_315008 : Nat := 4983230072969 + 3 ^ 40 * 315008 * 2
def baseEnd_315008 : Nat := 35944558669246391878069

theorem tailTrace_315008 : CollatzResearch.WordTrace tailWord_315008 prefixEnd_315008 35944558669246391878069 := by
  unfold tailWord_315008
  simp only [CollatzResearch.WordTrace]
  refine ⟨5744642821393644964172839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7659523761858193285563785 5744642821393644964172839)
  ·
    refine ⟨8616964232090467446259259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5744642821393644964172839 8616964232090467446259259)
    ·
      refine ⟨12925446348135701169388889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8616964232090467446259259 12925446348135701169388889)
      ·
        refine ⟨9694084761101775877041667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12925446348135701169388889 9694084761101775877041667)
        ·
          refine ⟨14541127141652663815562501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9694084761101775877041667 14541127141652663815562501)
          ·
            refine ⟨2726461339059874465417969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14541127141652663815562501 2726461339059874465417969)
            ·
              refine ⟨2044846004294905849063477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2726461339059874465417969 2044846004294905849063477)
              ·
                refine ⟨191704312902647423349701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2044846004294905849063477 191704312902647423349701)
                ·
                  refine ⟨35944558669246391878069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 191704312902647423349701 35944558669246391878069)
                  ·
                    rfl

theorem cell22_315008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 5, 4].length) (baseStart_315008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_315008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_315008 prefixEnd_315008 := by exact prefixLift 315008
  have htrace : WordTrace (prefixWord ++ tailWord_315008) baseStart_315008 baseEnd_315008 := by
    simpa [prefixWord, tailWord_315008, baseEnd_315008] using wordTrace_append hprefix tailTrace_315008
  have hstable : (prefixWord ++ tailWord_315008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315008).length < 2 ^ (prefixWord ++ tailWord_315008).sum := by decide
  have hdescent : baseEnd_315008 < baseStart_315008 := by decide
  rcases family_descends (prefixWord ++ tailWord_315008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315040 : List Nat := [2, 1, 1, 4, 3, 1, 2, 3, 2, 3]
def baseStart_315040 : Nat := 118140960795 + 315040 * 2 ^ 59
def prefixEnd_315040 : Nat := 4983230072969 + 3 ^ 40 * 315040 * 2
def baseEnd_315040 : Nat := 107844630261701758834109

theorem tailTrace_315040 : CollatzResearch.WordTrace tailWord_315040 prefixEnd_315040 107844630261701758834109 := by
  unfold tailWord_315040
  simp only [CollatzResearch.WordTrace]
  refine ⟨5745226389335679696755287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7660301852447572929007049 5745226389335679696755287)
  ·
    refine ⟨8617839584003519545132931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5745226389335679696755287 8617839584003519545132931)
    ·
      refine ⟨12926759376005279317699397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8617839584003519545132931 12926759376005279317699397)
      ·
        refine ⟨2423767383000989872068637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12926759376005279317699397 2423767383000989872068637)
        ·
          refine ⟨908912768625371202025739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2423767383000989872068637 908912768625371202025739)
          ·
            refine ⟨1363369152938056803038609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 908912768625371202025739 1363369152938056803038609)
            ·
              refine ⟨1022526864703542602278957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1363369152938056803038609 1022526864703542602278957)
              ·
                refine ⟨383447574263828475854609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1022526864703542602278957 383447574263828475854609)
                ·
                  refine ⟨287585680697871356890957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 383447574263828475854609 287585680697871356890957)
                  ·
                    refine ⟨107844630261701758834109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 287585680697871356890957 107844630261701758834109)
                    ·
                      rfl

theorem cell22_315040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 3, 2, 3].length) (baseStart_315040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_315040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_315040 prefixEnd_315040 := by exact prefixLift 315040
  have htrace : WordTrace (prefixWord ++ tailWord_315040) baseStart_315040 baseEnd_315040 := by
    simpa [prefixWord, tailWord_315040, baseEnd_315040] using wordTrace_append hprefix tailTrace_315040
  have hstable : (prefixWord ++ tailWord_315040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315040).length < 2 ^ (prefixWord ++ tailWord_315040).sum := by decide
  have hdescent : baseEnd_315040 < baseStart_315040 := by decide
  rcases family_descends (prefixWord ++ tailWord_315040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315142 : List Nat := [6, 2, 2, 1, 1, 2, 2, 1, 2, 3]
def baseStart_315142 : Nat := 118140960795 + 315142 * 2 ^ 59
def prefixEnd_315142 : Nat := 4983230072969 + 3 ^ 40 * 315142 * 2
def baseEnd_315142 : Nat := 107879546946207492783797

theorem tailTrace_315142 : CollatzResearch.WordTrace tailWord_315142 prefixEnd_315142 107879546946207492783797 := by
  unfold tailWord_315142
  simp only [CollatzResearch.WordTrace]
  refine ⟨359192907009432212928865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7662782016201220542482453 359192907009432212928865)
  ·
    refine ⟨269394680257074159696649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 359192907009432212928865 269394680257074159696649)
    ·
      refine ⟨202046010192805619772487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 269394680257074159696649 202046010192805619772487)
      ·
        refine ⟨303069015289208429658731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202046010192805619772487 303069015289208429658731)
        ·
          refine ⟨454603522933812644488097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 303069015289208429658731 454603522933812644488097)
          ·
            refine ⟨340952642200359483366073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 454603522933812644488097 340952642200359483366073)
            ·
              refine ⟨255714481650269612524555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 340952642200359483366073 255714481650269612524555)
              ·
                refine ⟨383571722475404418786833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 255714481650269612524555 383571722475404418786833)
                ·
                  refine ⟨287678791856553314090125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 383571722475404418786833 287678791856553314090125)
                  ·
                    refine ⟨107879546946207492783797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 287678791856553314090125 107879546946207492783797)
                    ·
                      rfl

theorem cell22_315142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_315142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_315142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_315142 prefixEnd_315142 := by exact prefixLift 315142
  have htrace : WordTrace (prefixWord ++ tailWord_315142) baseStart_315142 baseEnd_315142 := by
    simpa [prefixWord, tailWord_315142, baseEnd_315142] using wordTrace_append hprefix tailTrace_315142
  have hstable : (prefixWord ++ tailWord_315142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315142).length < 2 ^ (prefixWord ++ tailWord_315142).sum := by decide
  have hdescent : baseEnd_315142 < baseStart_315142 := by decide
  rcases family_descends (prefixWord ++ tailWord_315142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315162 : List Nat := [3, 1, 1, 3, 2, 4, 1, 2, 1, 4]
def baseStart_315162 : Nat := 118140960795 + 315162 * 2 ^ 59
def prefixEnd_315162 : Nat := 4983230072969 + 3 ^ 40 * 315162 * 2
def baseEnd_315162 : Nat := 107886393354934107283735

theorem tailTrace_315162 : CollatzResearch.WordTrace tailWord_315162 prefixEnd_315162 107886393354934107283735 := by
  unfold tailWord_315162
  simp only [CollatzResearch.WordTrace]
  refine ⟨2873725621057343557362935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7663268322819582819634493 2873725621057343557362935)
  ·
    refine ⟨4310588431586015336044403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2873725621057343557362935 4310588431586015336044403)
    ·
      refine ⟨6465882647379023004066605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4310588431586015336044403 6465882647379023004066605)
      ·
        refine ⟨2424705992767133626524977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6465882647379023004066605 2424705992767133626524977)
        ·
          refine ⟨1818529494575350219893733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2424705992767133626524977 1818529494575350219893733)
          ·
            refine ⟨340974280232878166230075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1818529494575350219893733 340974280232878166230075)
            ·
              refine ⟨511461420349317249345113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 340974280232878166230075 511461420349317249345113)
              ·
                refine ⟨383596065261987937008835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 511461420349317249345113 383596065261987937008835)
                ·
                  refine ⟨575394097892981905513253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 383596065261987937008835 575394097892981905513253)
                  ·
                    refine ⟨107886393354934107283735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 575394097892981905513253 107886393354934107283735)
                    ·
                      rfl

theorem cell22_315162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 2, 1, 4].length) (baseStart_315162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_315162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_315162 prefixEnd_315162 := by exact prefixLift 315162
  have htrace : WordTrace (prefixWord ++ tailWord_315162) baseStart_315162 baseEnd_315162 := by
    simpa [prefixWord, tailWord_315162, baseEnd_315162] using wordTrace_append hprefix tailTrace_315162
  have hstable : (prefixWord ++ tailWord_315162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315162).length < 2 ^ (prefixWord ++ tailWord_315162).sum := by decide
  have hdescent : baseEnd_315162 < baseStart_315162 := by decide
  rcases family_descends (prefixWord ++ tailWord_315162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315192 : List Nat := [2, 1, 2, 1, 3, 4, 2, 2, 2, 3]
def baseStart_315192 : Nat := 118140960795 + 315192 * 2 ^ 59
def prefixEnd_315192 : Nat := 4983230072969 + 3 ^ 40 * 315192 * 2
def baseEnd_315192 : Nat := 107896662968024029033643

theorem tailTrace_315192 : CollatzResearch.WordTrace tailWord_315192 prefixEnd_315192 107896662968024029033643 := by
  unfold tailWord_315192
  simp only [CollatzResearch.WordTrace]
  refine ⟨5747998337060344676521915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7663997782747126235362553 5747998337060344676521915)
  ·
    refine ⟨8621997505590517014782873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5747998337060344676521915 8621997505590517014782873)
    ·
      refine ⟨6466498129192887761087155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8621997505590517014782873 6466498129192887761087155)
      ·
        refine ⟨9699747193789331641630733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6466498129192887761087155 9699747193789331641630733)
        ·
          refine ⟨3637405197670999365611525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9699747193789331641630733 3637405197670999365611525)
          ·
            refine ⟨682013474563312381052161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3637405197670999365611525 682013474563312381052161)
            ·
              refine ⟨511510105922484285789121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 682013474563312381052161 511510105922484285789121)
              ·
                refine ⟨383632579441863214341841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 511510105922484285789121 383632579441863214341841)
                ·
                  refine ⟨287724434581397410756381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 383632579441863214341841 287724434581397410756381)
                  ·
                    refine ⟨107896662968024029033643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 287724434581397410756381 107896662968024029033643)
                    ·
                      rfl

theorem cell22_315192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 2, 2, 3].length) (baseStart_315192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_315192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_315192 prefixEnd_315192 := by exact prefixLift 315192
  have htrace : WordTrace (prefixWord ++ tailWord_315192) baseStart_315192 baseEnd_315192 := by
    simpa [prefixWord, tailWord_315192, baseEnd_315192] using wordTrace_append hprefix tailTrace_315192
  have hstable : (prefixWord ++ tailWord_315192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315192).length < 2 ^ (prefixWord ++ tailWord_315192).sum := by decide
  have hdescent : baseEnd_315192 < baseStart_315192 := by decide
  rcases family_descends (prefixWord ++ tailWord_315192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315194 : List Nat := [3, 1, 1, 1, 5, 3, 2, 2, 4]
def baseStart_315194 : Nat := 118140960795 + 315194 * 2 ^ 59
def prefixEnd_315194 : Nat := 4983230072969 + 3 ^ 40 * 315194 * 2
def baseEnd_315194 : Nat := 35965782536298896827879

theorem tailTrace_315194 : CollatzResearch.WordTrace tailWord_315194 prefixEnd_315194 35965782536298896827879 := by
  unfold tailWord_315194
  simp only [CollatzResearch.WordTrace]
  refine ⟨2874017405028360923654159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7664046413408962463077757 2874017405028360923654159)
  ·
    refine ⟨4311026107542541385481239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2874017405028360923654159 4311026107542541385481239)
    ·
      refine ⟨6466539161313812078221859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4311026107542541385481239 6466539161313812078221859)
      ·
        refine ⟨9699808741970718117332789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6466539161313812078221859 9699808741970718117332789)
        ·
          refine ⟨909357069559754823499949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9699808741970718117332789 909357069559754823499949)
          ·
            refine ⟨341008901084908058812481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 909357069559754823499949 341008901084908058812481)
            ·
              refine ⟨255756675813681044109361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 341008901084908058812481 255756675813681044109361)
              ·
                refine ⟨191817506860260783082021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 255756675813681044109361 191817506860260783082021)
                ·
                  refine ⟨35965782536298896827879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 191817506860260783082021 35965782536298896827879)
                  ·
                    rfl

theorem cell22_315194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 2, 2, 4].length) (baseStart_315194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_315194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_315194 prefixEnd_315194 := by exact prefixLift 315194
  have htrace : WordTrace (prefixWord ++ tailWord_315194) baseStart_315194 baseEnd_315194 := by
    simpa [prefixWord, tailWord_315194, baseEnd_315194] using wordTrace_append hprefix tailTrace_315194
  have hstable : (prefixWord ++ tailWord_315194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315194).length < 2 ^ (prefixWord ++ tailWord_315194).sum := by decide
  have hdescent : baseEnd_315194 < baseStart_315194 := by decide
  rcases family_descends (prefixWord ++ tailWord_315194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315233 : List Nat := [1, 2, 3, 1, 1, 1, 4, 2, 7]
def baseStart_315233 : Nat := 118140960795 + 315233 * 2 ^ 59
def prefixEnd_315233 : Nat := 4983230072969 + 3 ^ 40 * 315233 * 2
def baseEnd_315233 : Nat := 35970232701971196252839

theorem tailTrace_315233 : CollatzResearch.WordTrace tailWord_315233 prefixEnd_315233 35970232701971196252839 := by
  unfold tailWord_315233
  simp only [CollatzResearch.WordTrace]
  refine ⟨11497492066972153355286353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7664994711314768903524235 11497492066972153355286353)
  ·
    refine ⟨8623119050229115016464765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11497492066972153355286353 8623119050229115016464765)
    ·
      refine ⟨3233669643835918131174287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8623119050229115016464765 3233669643835918131174287)
      ·
        refine ⟨4850504465753877196761431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3233669643835918131174287 4850504465753877196761431)
        ·
          refine ⟨7275756698630815795142147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4850504465753877196761431 7275756698630815795142147)
          ·
            refine ⟨10913635047946223692713221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7275756698630815795142147 10913635047946223692713221)
            ·
              refine ⟨2046306571489916942383729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10913635047946223692713221 2046306571489916942383729)
              ·
                refine ⟨1534729928617437706787797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2046306571489916942383729 1534729928617437706787797)
                ·
                  refine ⟨35970232701971196252839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1534729928617437706787797 35970232701971196252839)
                  ·
                    rfl

theorem cell22_315233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 7].length) (baseStart_315233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_315233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_315233 prefixEnd_315233 := by exact prefixLift 315233
  have htrace : WordTrace (prefixWord ++ tailWord_315233) baseStart_315233 baseEnd_315233 := by
    simpa [prefixWord, tailWord_315233, baseEnd_315233] using wordTrace_append hprefix tailTrace_315233
  have hstable : (prefixWord ++ tailWord_315233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315233).length < 2 ^ (prefixWord ++ tailWord_315233).sum := by decide
  have hdescent : baseEnd_315233 < baseStart_315233 := by decide
  rcases family_descends (prefixWord ++ tailWord_315233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315267 : List Nat := [1, 1, 1, 3, 4, 3, 3, 1, 5]
def baseStart_315267 : Nat := 118140960795 + 315267 * 2 ^ 59
def prefixEnd_315267 : Nat := 4983230072969 + 3 ^ 40 * 315267 * 2
def baseEnd_315267 : Nat := 35974112333582944469471

theorem tailTrace_315267 : CollatzResearch.WordTrace tailWord_315267 prefixEnd_315267 35974112333582944469471 := by
  unfold tailWord_315267
  simp only [CollatzResearch.WordTrace]
  refine ⟨11498732148848977162024055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7665821432565984774682703 11498732148848977162024055)
  ·
    refine ⟨17248098223273465743036083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11498732148848977162024055 17248098223273465743036083)
    ·
      refine ⟨25872147334910198614554125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17248098223273465743036083 25872147334910198614554125)
      ·
        refine ⟨9702055250591324480457797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25872147334910198614554125 9702055250591324480457797)
        ·
          refine ⟨1819135359485873340085837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9702055250591324480457797 1819135359485873340085837)
          ·
            refine ⟨682175759807202502532189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1819135359485873340085837 682175759807202502532189)
            ·
              refine ⟨255815909927700938449571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 682175759807202502532189 255815909927700938449571)
              ·
                refine ⟨383723864891551407674357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 255815909927700938449571 383723864891551407674357)
                ·
                  refine ⟨35974112333582944469471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 383723864891551407674357 35974112333582944469471)
                  ·
                    rfl

theorem cell22_315267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 3, 1, 5].length) (baseStart_315267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_315267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_315267 prefixEnd_315267 := by exact prefixLift 315267
  have htrace : WordTrace (prefixWord ++ tailWord_315267) baseStart_315267 baseEnd_315267 := by
    simpa [prefixWord, tailWord_315267, baseEnd_315267] using wordTrace_append hprefix tailTrace_315267
  have hstable : (prefixWord ++ tailWord_315267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315267).length < 2 ^ (prefixWord ++ tailWord_315267).sum := by decide
  have hdescent : baseEnd_315267 < baseStart_315267 := by decide
  rcases family_descends (prefixWord ++ tailWord_315267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315280 : List Nat := [2, 1, 1, 1, 1, 1, 2, 8, 1, 4]
def baseStart_315280 : Nat := 118140960795 + 315280 * 2 ^ 59
def prefixEnd_315280 : Nat := 4983230072969 + 3 ^ 40 * 315280 * 2
def baseEnd_315280 : Nat := 107926787166421132833373

theorem tailTrace_315280 : CollatzResearch.WordTrace tailWord_315280 prefixEnd_315280 107926787166421132833373 := by
  unfold tailWord_315280
  simp only [CollatzResearch.WordTrace]
  refine ⟨5749603148900940191123647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7666137531867920254831529 5749603148900940191123647)
  ·
    refine ⟨8624404723351410286685471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5749603148900940191123647 8624404723351410286685471)
    ·
      refine ⟨12936607085027115430028207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8624404723351410286685471 12936607085027115430028207)
      ·
        refine ⟨19404910627540673145042311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12936607085027115430028207 19404910627540673145042311)
        ·
          refine ⟨29107365941311009717563467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19404910627540673145042311 29107365941311009717563467)
          ·
            refine ⟨43661048911966514576345201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29107365941311009717563467 43661048911966514576345201)
            ·
              refine ⟨32745786683974885932258901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43661048911966514576345201 32745786683974885932258901)
              ·
                refine ⟨383739687702830694518659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 32745786683974885932258901 383739687702830694518659)
                ·
                  refine ⟨575609531554246041777989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 383739687702830694518659 575609531554246041777989)
                  ·
                    refine ⟨107926787166421132833373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 575609531554246041777989 107926787166421132833373)
                    ·
                      rfl

theorem cell22_315280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 8, 1, 4].length) (baseStart_315280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_315280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_315280 prefixEnd_315280 := by exact prefixLift 315280
  have htrace : WordTrace (prefixWord ++ tailWord_315280) baseStart_315280 baseEnd_315280 := by
    simpa [prefixWord, tailWord_315280, baseEnd_315280] using wordTrace_append hprefix tailTrace_315280
  have hstable : (prefixWord ++ tailWord_315280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315280).length < 2 ^ (prefixWord ++ tailWord_315280).sum := by decide
  have hdescent : baseEnd_315280 < baseStart_315280 := by decide
  rcases family_descends (prefixWord ++ tailWord_315280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315288 : List Nat := [2, 1, 2, 6, 1, 2, 1, 3, 1, 3]
def baseStart_315288 : Nat := 118140960795 + 315288 * 2 ^ 59
def prefixEnd_315288 : Nat := 4983230072969 + 3 ^ 40 * 315288 * 2
def baseEnd_315288 : Nat := 107929525729911778633349

theorem tailTrace_315288 : CollatzResearch.WordTrace tailWord_315288 prefixEnd_315288 107929525729911778633349 := by
  unfold tailWord_315288
  simp only [CollatzResearch.WordTrace]
  refine ⟨5749749040886448874269259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7666332054515265165692345 5749749040886448874269259)
  ·
    refine ⟨8624623561329673311403889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5749749040886448874269259 8624623561329673311403889)
    ·
      refine ⟨6468467670997254983552917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8624623561329673311403889 6468467670997254983552917)
      ·
        refine ⟨303209422077996327354043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6468467670997254983552917 303209422077996327354043)
        ·
          refine ⟨454814133116994491031065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 303209422077996327354043 454814133116994491031065)
          ·
            refine ⟨341110599837745868273299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 454814133116994491031065 341110599837745868273299)
            ·
              refine ⟨511665899756618802409949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 341110599837745868273299 511665899756618802409949)
              ·
                refine ⟨191874712408732050903731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 511665899756618802409949 191874712408732050903731)
                ·
                  refine ⟨287812068613098076355597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 191874712408732050903731 287812068613098076355597)
                  ·
                    refine ⟨107929525729911778633349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 287812068613098076355597 107929525729911778633349)
                    ·
                      rfl

theorem cell22_315288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 3, 1, 3].length) (baseStart_315288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_315288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_315288 prefixEnd_315288 := by exact prefixLift 315288
  have htrace : WordTrace (prefixWord ++ tailWord_315288) baseStart_315288 baseEnd_315288 := by
    simpa [prefixWord, tailWord_315288, baseEnd_315288] using wordTrace_append hprefix tailTrace_315288
  have hstable : (prefixWord ++ tailWord_315288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315288).length < 2 ^ (prefixWord ++ tailWord_315288).sum := by decide
  have hdescent : baseEnd_315288 < baseStart_315288 := by decide
  rcases family_descends (prefixWord ++ tailWord_315288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315323 : List Nat := [1, 1, 1, 1, 1, 2, 2, 13]
def baseStart_315323 : Nat := 118140960795 + 315323 * 2 ^ 59
def prefixEnd_315323 : Nat := 4983230072969 + 3 ^ 40 * 315323 * 2
def baseEnd_315323 : Nat := 11993500771687039334249

theorem tailTrace_315323 : CollatzResearch.WordTrace tailWord_315323 prefixEnd_315323 11993500771687039334249 := by
  unfold tailWord_315323
  simp only [CollatzResearch.WordTrace]
  refine ⟨11500774636646098726062623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7667183091097399150708415 11500774636646098726062623)
  ·
    refine ⟨17251161954969148089093935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11500774636646098726062623 17251161954969148089093935)
    ·
      refine ⟨25876742932453722133640903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17251161954969148089093935 25876742932453722133640903)
      ·
        refine ⟨38815114398680583200461355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25876742932453722133640903 38815114398680583200461355)
        ·
          refine ⟨58222671598020874800692033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38815114398680583200461355 58222671598020874800692033)
          ·
            refine ⟨43667003698515656100519025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58222671598020874800692033 43667003698515656100519025)
            ·
              refine ⟨32750252773886742075389269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43667003698515656100519025 32750252773886742075389269)
              ·
                refine ⟨11993500771687039334249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 32750252773886742075389269 11993500771687039334249)
                ·
                  rfl

theorem cell22_315323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 13].length) (baseStart_315323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_315323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_315323 prefixEnd_315323 := by exact prefixLift 315323
  have htrace : WordTrace (prefixWord ++ tailWord_315323) baseStart_315323 baseEnd_315323 := by
    simpa [prefixWord, tailWord_315323, baseEnd_315323] using wordTrace_append hprefix tailTrace_315323
  have hstable : (prefixWord ++ tailWord_315323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315323).length < 2 ^ (prefixWord ++ tailWord_315323).sum := by decide
  have hdescent : baseEnd_315323 < baseStart_315323 := by decide
  rcases family_descends (prefixWord ++ tailWord_315323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315327 : List Nat := [1, 1, 2, 2, 2, 1, 5, 3, 2, 3]
def baseStart_315327 : Nat := 118140960795 + 315327 * 2 ^ 59
def prefixEnd_315327 : Nat := 4983230072969 + 3 ^ 40 * 315327 * 2
def baseEnd_315327 : Nat := 107942876226928676908229

theorem tailTrace_315327 : CollatzResearch.WordTrace tailWord_315327 prefixEnd_315327 107942876226928676908229 := by
  unfold tailWord_315327
  simp only [CollatzResearch.WordTrace]
  refine ⟨11500920528631607409208235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7667280352421071606138823 11500920528631607409208235)
  ·
    refine ⟨17251380792947411113812353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11500920528631607409208235 17251380792947411113812353)
    ·
      refine ⟨12938535594710558335359265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17251380792947411113812353 12938535594710558335359265)
      ·
        refine ⟨9703901696032918751519449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12938535594710558335359265 9703901696032918751519449)
        ·
          refine ⟨7277926272024689063639587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9703901696032918751519449 7277926272024689063639587)
          ·
            refine ⟨10916889408037033595459381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7277926272024689063639587 10916889408037033595459381)
            ·
              refine ⟨1023458382003471899574317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10916889408037033595459381 1023458382003471899574317)
              ·
                refine ⟨383796893251301962340369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1023458382003471899574317 383796893251301962340369)
                ·
                  refine ⟨287847669938476471755277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 383796893251301962340369 287847669938476471755277)
                  ·
                    refine ⟨107942876226928676908229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 287847669938476471755277 107942876226928676908229)
                    ·
                      rfl

theorem cell22_315327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 3, 2, 3].length) (baseStart_315327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_315327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_315327 prefixEnd_315327 := by exact prefixLift 315327
  have htrace : WordTrace (prefixWord ++ tailWord_315327) baseStart_315327 baseEnd_315327 := by
    simpa [prefixWord, tailWord_315327, baseEnd_315327] using wordTrace_append hprefix tailTrace_315327
  have hstable : (prefixWord ++ tailWord_315327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315327).length < 2 ^ (prefixWord ++ tailWord_315327).sum := by decide
  have hdescent : baseEnd_315327 < baseStart_315327 := by decide
  rcases family_descends (prefixWord ++ tailWord_315327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315340 : List Nat := [2, 2, 1, 4, 1, 2, 2, 8]
def baseStart_315340 : Nat := 118140960795 + 315340 * 2 ^ 59
def prefixEnd_315340 : Nat := 4983230072969 + 3 ^ 40 * 315340 * 2
def baseEnd_315340 : Nat := 11994147376955664037021

theorem tailTrace_315340 : CollatzResearch.WordTrace tailWord_315340 prefixEnd_315340 11994147376955664037021 := by
  unfold tailWord_315340
  simp only [CollatzResearch.WordTrace]
  refine ⟨5750697338792255314715737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7667596451723007086287649 5750697338792255314715737)
  ·
    refine ⟨4313023004094191486036803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5750697338792255314715737 4313023004094191486036803)
    ·
      refine ⟨6469534506141287229055205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4313023004094191486036803 6469534506141287229055205)
      ·
        refine ⟨1213037719901491355447851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6469534506141287229055205 1213037719901491355447851)
        ·
          refine ⟨1819556579852237033171777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1213037719901491355447851 1819556579852237033171777)
          ·
            refine ⟨1364667434889177774878833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1819556579852237033171777 1364667434889177774878833)
            ·
              refine ⟨1023500576166883331159125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1364667434889177774878833 1023500576166883331159125)
              ·
                refine ⟨11994147376955664037021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1023500576166883331159125 11994147376955664037021)
                ·
                  rfl

theorem cell22_315340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 8].length) (baseStart_315340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_315340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_315340 prefixEnd_315340 := by exact prefixLift 315340
  have htrace : WordTrace (prefixWord ++ tailWord_315340) baseStart_315340 baseEnd_315340 := by
    simpa [prefixWord, tailWord_315340, baseEnd_315340] using wordTrace_append hprefix tailTrace_315340
  have hstable : (prefixWord ++ tailWord_315340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315340).length < 2 ^ (prefixWord ++ tailWord_315340).sum := by decide
  have hdescent : baseEnd_315340 < baseStart_315340 := by decide
  rcases family_descends (prefixWord ++ tailWord_315340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315342 : List Nat := [4, 1, 1, 1, 2, 2, 4, 1, 2, 4]
def baseStart_315342 : Nat := 118140960795 + 315342 * 2 ^ 59
def prefixEnd_315342 : Nat := 4983230072969 + 3 ^ 40 * 315342 * 2
def baseEnd_315342 : Nat := 107948011033473637783183

theorem tailTrace_315342 : CollatzResearch.WordTrace tailWord_315342 prefixEnd_315342 107948011033473637783183 := by
  unfold tailWord_315342
  simp only [CollatzResearch.WordTrace]
  refine ⟨1437683452947158121375535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7667645082384843314002853 1437683452947158121375535)
  ·
    refine ⟨2156525179420737182063303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1437683452947158121375535 2156525179420737182063303)
    ·
      refine ⟨3234787769131105773094955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2156525179420737182063303 3234787769131105773094955)
      ·
        refine ⟨4852181653696658659642433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3234787769131105773094955 4852181653696658659642433)
        ·
          refine ⟨3639136240272493994731825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4852181653696658659642433 3639136240272493994731825)
          ·
            refine ⟨2729352180204370496048869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3639136240272493994731825 2729352180204370496048869)
            ·
              refine ⟨511753533788319468009163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2729352180204370496048869 511753533788319468009163)
              ·
                refine ⟨767630300682479202013745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 511753533788319468009163 767630300682479202013745)
                ·
                  refine ⟨575722725511859401510309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 767630300682479202013745 575722725511859401510309)
                  ·
                    refine ⟨107948011033473637783183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 575722725511859401510309 107948011033473637783183)
                    ·
                      rfl

theorem cell22_315342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 1, 2, 4].length) (baseStart_315342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_315342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_315342 prefixEnd_315342 := by exact prefixLift 315342
  have htrace : WordTrace (prefixWord ++ tailWord_315342) baseStart_315342 baseEnd_315342 := by
    simpa [prefixWord, tailWord_315342, baseEnd_315342] using wordTrace_append hprefix tailTrace_315342
  have hstable : (prefixWord ++ tailWord_315342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315342).length < 2 ^ (prefixWord ++ tailWord_315342).sum := by decide
  have hdescent : baseEnd_315342 < baseStart_315342 := by decide
  rcases family_descends (prefixWord ++ tailWord_315342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315357 : List Nat := [1, 4, 3, 1, 4, 9]
def baseStart_315357 : Nat := 118140960795 + 315357 * 2 ^ 59
def prefixEnd_315357 : Nat := 4983230072969 + 3 ^ 40 * 315357 * 2
def baseEnd_315357 : Nat := 1332754886913809859977

theorem tailTrace_315357 : CollatzResearch.WordTrace tailWord_315357 prefixEnd_315357 1332754886913809859977 := by
  unfold tailWord_315357
  simp only [CollatzResearch.WordTrace]
  refine ⟨11502014718522922532800325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7668009812348615021866883 11502014718522922532800325)
  ·
    refine ⟨2156627759723047974900061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11502014718522922532800325 2156627759723047974900061)
    ·
      refine ⟨808735409896142990587523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2156627759723047974900061 808735409896142990587523)
      ·
        refine ⟨1213103114844214485881285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 808735409896142990587523 1213103114844214485881285)
        ·
          refine ⟨227456834033290216102741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1213103114844214485881285 227456834033290216102741)
          ·
            refine ⟨1332754886913809859977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 227456834033290216102741 1332754886913809859977)
            ·
              rfl

theorem cell22_315357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 9].length) (baseStart_315357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_315357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_315357 prefixEnd_315357 := by exact prefixLift 315357
  have htrace : WordTrace (prefixWord ++ tailWord_315357) baseStart_315357 baseEnd_315357 := by
    simpa [prefixWord, tailWord_315357, baseEnd_315357] using wordTrace_append hprefix tailTrace_315357
  have hstable : (prefixWord ++ tailWord_315357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315357).length < 2 ^ (prefixWord ++ tailWord_315357).sum := by decide
  have hdescent : baseEnd_315357 < baseStart_315357 := by decide
  rcases family_descends (prefixWord ++ tailWord_315357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315370 : List Nat := [3, 1, 3, 1, 2, 1, 1, 1, 1, 8]
def baseStart_315370 : Nat := 118140960795 + 315370 * 2 ^ 59
def prefixEnd_315370 : Nat := 4983230072969 + 3 ^ 40 * 315370 * 2
def baseEnd_315370 : Nat := 107957596005690898083097

theorem tailTrace_315370 : CollatzResearch.WordTrace tailWord_315370 prefixEnd_315370 107957596005690898083097 := by
  unfold tailWord_315370
  simp only [CollatzResearch.WordTrace]
  refine ⟨2875622216868956438255891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7668325911650550502015709 2875622216868956438255891)
  ·
    refine ⟨4313433325303434657383837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2875622216868956438255891 4313433325303434657383837)
    ·
      refine ⟨1617537496988787996518939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4313433325303434657383837 1617537496988787996518939)
      ·
        refine ⟨2426306245483181994778409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1617537496988787996518939 2426306245483181994778409)
        ·
          refine ⟨1819729684112386496083807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2426306245483181994778409 1819729684112386496083807)
          ·
            refine ⟨2729594526168579744125711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1819729684112386496083807 2729594526168579744125711)
            ·
              refine ⟨4094391789252869616188567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2729594526168579744125711 4094391789252869616188567)
              ·
                refine ⟨6141587683879304424282851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4094391789252869616188567 6141587683879304424282851)
                ·
                  refine ⟨9212381525818956636424277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6141587683879304424282851 9212381525818956636424277)
                  ·
                    refine ⟨107957596005690898083097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 9212381525818956636424277 107957596005690898083097)
                    ·
                      rfl

theorem cell22_315370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_315370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_315370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_315370 prefixEnd_315370 := by exact prefixLift 315370
  have htrace : WordTrace (prefixWord ++ tailWord_315370) baseStart_315370 baseEnd_315370 := by
    simpa [prefixWord, tailWord_315370, baseEnd_315370] using wordTrace_append hprefix tailTrace_315370
  have hstable : (prefixWord ++ tailWord_315370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315370).length < 2 ^ (prefixWord ++ tailWord_315370).sum := by decide
  have hdescent : baseEnd_315370 < baseStart_315370 := by decide
  rcases family_descends (prefixWord ++ tailWord_315370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315400 : List Nat := [2, 1, 3, 2, 1, 2, 1, 2, 1, 7]
def baseStart_315400 : Nat := 118140960795 + 315400 * 2 ^ 59
def prefixEnd_315400 : Nat := 4983230072969 + 3 ^ 40 * 315400 * 2
def baseEnd_315400 : Nat := 107967865618780819833005

theorem tailTrace_315400 : CollatzResearch.WordTrace tailWord_315400 prefixEnd_315400 107967865618780819833005 := by
  unfold tailWord_315400
  simp only [CollatzResearch.WordTrace]
  refine ⟨5751791528683570438307827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7669055371578093917743769 5751791528683570438307827)
  ·
    refine ⟨8627687293025355657461741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5751791528683570438307827 8627687293025355657461741)
    ·
      refine ⟨3235382734884508371548153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8627687293025355657461741 3235382734884508371548153)
      ·
        refine ⟨2426537051163381278661115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3235382734884508371548153 2426537051163381278661115)
        ·
          refine ⟨3639805576745071917991673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2426537051163381278661115 3639805576745071917991673)
          ·
            refine ⟨2729854182558803938493755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3639805576745071917991673 2729854182558803938493755)
            ·
              refine ⟨4094781273838205907740633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2729854182558803938493755 4094781273838205907740633)
              ·
                refine ⟨3071085955378654430805475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4094781273838205907740633 3071085955378654430805475)
                ·
                  refine ⟨4606628933067981646208213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3071085955378654430805475 4606628933067981646208213)
                  ·
                    refine ⟨107967865618780819833005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4606628933067981646208213 107967865618780819833005)
                    ·
                      rfl

theorem cell22_315400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_315400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_315400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_315400 prefixEnd_315400 := by exact prefixLift 315400
  have htrace : WordTrace (prefixWord ++ tailWord_315400) baseStart_315400 baseEnd_315400 := by
    simpa [prefixWord, tailWord_315400, baseEnd_315400] using wordTrace_append hprefix tailTrace_315400
  have hstable : (prefixWord ++ tailWord_315400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315400).length < 2 ^ (prefixWord ++ tailWord_315400).sum := by decide
  have hdescent : baseEnd_315400 < baseStart_315400 := by decide
  rcases family_descends (prefixWord ++ tailWord_315400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315406 : List Nat := [4, 1, 1, 2, 2, 1, 4, 3, 1, 3]
def baseStart_315406 : Nat := 118140960795 + 315406 * 2 ^ 59
def prefixEnd_315406 : Nat := 4983230072969 + 3 ^ 40 * 315406 * 2
def baseEnd_315406 : Nat := 107969919541398804182987

theorem tailTrace_315406 : CollatzResearch.WordTrace tailWord_315406 prefixEnd_315406 107969919541398804182987 := by
  unfold tailWord_315406
  simp only [CollatzResearch.WordTrace]
  refine ⟨1437975236918175487666759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7669201263563602600889381 1437975236918175487666759)
  ·
    refine ⟨2156962855377263231500139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1437975236918175487666759 2156962855377263231500139)
    ·
      refine ⟨3235444283065894847250209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2156962855377263231500139 3235444283065894847250209)
      ·
        refine ⟨2426583212299421135437657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3235444283065894847250209 2426583212299421135437657)
        ·
          refine ⟨1819937409224565851578243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2426583212299421135437657 1819937409224565851578243)
          ·
            refine ⟨2729906113836848777367365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1819937409224565851578243 2729906113836848777367365)
            ·
              refine ⟨511857396344409145756381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2729906113836848777367365 511857396344409145756381)
              ·
                refine ⟨191946523629153429658643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 511857396344409145756381 191946523629153429658643)
                ·
                  refine ⟨287919785443730144487965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 191946523629153429658643 287919785443730144487965)
                  ·
                    refine ⟨107969919541398804182987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 287919785443730144487965 107969919541398804182987)
                    ·
                      rfl

theorem cell22_315406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 3, 1, 3].length) (baseStart_315406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_315406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_315406 prefixEnd_315406 := by exact prefixLift 315406
  have htrace : WordTrace (prefixWord ++ tailWord_315406) baseStart_315406 baseEnd_315406 := by
    simpa [prefixWord, tailWord_315406, baseEnd_315406] using wordTrace_append hprefix tailTrace_315406
  have hstable : (prefixWord ++ tailWord_315406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315406).length < 2 ^ (prefixWord ++ tailWord_315406).sum := by decide
  have hdescent : baseEnd_315406 < baseStart_315406 := by decide
  rcases family_descends (prefixWord ++ tailWord_315406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315477 : List Nat := [1, 3, 2, 2, 1, 3, 1, 1, 4, 4]
def baseStart_315477 : Nat := 118140960795 + 315477 * 2 ^ 59
def prefixEnd_315477 : Nat := 4983230072969 + 3 ^ 40 * 315477 * 2
def baseEnd_315477 : Nat := 107994224292378285657769

theorem tailTrace_315477 : CollatzResearch.WordTrace tailWord_315477 prefixEnd_315477 107994224292378285657769 := by
  unfold tailWord_315477
  simp only [CollatzResearch.WordTrace]
  refine ⟨11506391478088183027168685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7670927652058788684779123 11506391478088183027168685)
  ·
    refine ⟨4314896804283068635188257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11506391478088183027168685 4314896804283068635188257)
    ·
      refine ⟨3236172603212301476391193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4314896804283068635188257 3236172603212301476391193)
      ·
        refine ⟨2427129452409226107293395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3236172603212301476391193 2427129452409226107293395)
        ·
          refine ⟨3640694178613839160940093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2427129452409226107293395 3640694178613839160940093)
          ·
            refine ⟨1365260316980189685352535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3640694178613839160940093 1365260316980189685352535)
            ·
              refine ⟨2047890475470284528028803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1365260316980189685352535 2047890475470284528028803)
              ·
                refine ⟨3071835713205426792043205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2047890475470284528028803 3071835713205426792043205)
                ·
                  refine ⟨575969196226017523508101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3071835713205426792043205 575969196226017523508101)
                  ·
                    refine ⟨107994224292378285657769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 575969196226017523508101 107994224292378285657769)
                    ·
                      rfl

theorem cell22_315477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 4, 4].length) (baseStart_315477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_315477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_315477 prefixEnd_315477 := by exact prefixLift 315477
  have htrace : WordTrace (prefixWord ++ tailWord_315477) baseStart_315477 baseEnd_315477 := by
    simpa [prefixWord, tailWord_315477, baseEnd_315477] using wordTrace_append hprefix tailTrace_315477
  have hstable : (prefixWord ++ tailWord_315477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315477).length < 2 ^ (prefixWord ++ tailWord_315477).sum := by decide
  have hdescent : baseEnd_315477 < baseStart_315477 := by decide
  rcases family_descends (prefixWord ++ tailWord_315477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315541 : List Nat := [1, 3, 2, 1, 1, 1, 5, 4, 1, 3]
def baseStart_315541 : Nat := 118140960795 + 315541 * 2 ^ 59
def prefixEnd_315541 : Nat := 4983230072969 + 3 ^ 40 * 315541 * 2
def baseEnd_315541 : Nat := 108016132800303452057573

theorem tailTrace_315541 : CollatzResearch.WordTrace tailWord_315541 prefixEnd_315541 108016132800303452057573 := by
  unfold tailWord_315541
  simp only [CollatzResearch.WordTrace]
  refine ⟨11508725749856321957498477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7672483833237547971665651 11508725749856321957498477)
  ·
    refine ⟨4315772156196120734061929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11508725749856321957498477 4315772156196120734061929)
    ·
      refine ⟨3236829117147090550546447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4315772156196120734061929 3236829117147090550546447)
      ·
        refine ⟨4855243675720635825819671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3236829117147090550546447 4855243675720635825819671)
        ·
          refine ⟨7282865513580953738729507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4855243675720635825819671 7282865513580953738729507)
          ·
            refine ⟨10924298270371430608094261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7282865513580953738729507 10924298270371430608094261)
            ·
              refine ⟨1024152962847321619508837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10924298270371430608094261 1024152962847321619508837)
              ·
                refine ⟨192028680533872803657907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1024152962847321619508837 192028680533872803657907)
                ·
                  refine ⟨288043020800809205486861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 192028680533872803657907 288043020800809205486861)
                  ·
                    refine ⟨108016132800303452057573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 288043020800809205486861 108016132800303452057573)
                    ·
                      rfl

theorem cell22_315541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 4, 1, 3].length) (baseStart_315541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_315541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_315541 prefixEnd_315541 := by exact prefixLift 315541
  have htrace : WordTrace (prefixWord ++ tailWord_315541) baseStart_315541 baseEnd_315541 := by
    simpa [prefixWord, tailWord_315541, baseEnd_315541] using wordTrace_append hprefix tailTrace_315541
  have hstable : (prefixWord ++ tailWord_315541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315541).length < 2 ^ (prefixWord ++ tailWord_315541).sum := by decide
  have hdescent : baseEnd_315541 < baseStart_315541 := by decide
  rcases family_descends (prefixWord ++ tailWord_315541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315552 : List Nat := [2, 1, 1, 4, 2, 2, 1, 1, 1, 7]
def baseStart_315552 : Nat := 118140960795 + 315552 * 2 ^ 59
def prefixEnd_315552 : Nat := 4983230072969 + 3 ^ 40 * 315552 * 2
def baseEnd_315552 : Nat := 108019898325103090032539

theorem tailTrace_315552 : CollatzResearch.WordTrace tailWord_315552 prefixEnd_315552 108019898325103090032539 := by
  unfold tailWord_315552
  simp only [CollatzResearch.WordTrace]
  refine ⟨5754563476408235418074455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7672751301877647224099273 5754563476408235418074455)
  ·
    refine ⟨8631845214612353127111683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5754563476408235418074455 8631845214612353127111683)
    ·
      refine ⟨12947767821918529690667525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8631845214612353127111683 12947767821918529690667525)
      ·
        refine ⟨2427706466609724317000161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12947767821918529690667525 2427706466609724317000161)
        ·
          refine ⟨1820779849957293237750121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2427706466609724317000161 1820779849957293237750121)
          ·
            refine ⟨1365584887467969928312591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1820779849957293237750121 1365584887467969928312591)
            ·
              refine ⟨2048377331201954892468887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1365584887467969928312591 2048377331201954892468887)
              ·
                refine ⟨3072565996802932338703331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2048377331201954892468887 3072565996802932338703331)
                ·
                  refine ⟨4608848995204398508054997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3072565996802932338703331 4608848995204398508054997)
                  ·
                    refine ⟨108019898325103090032539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4608848995204398508054997 108019898325103090032539)
                    ·
                      rfl

theorem cell22_315552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 1, 7].length) (baseStart_315552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_315552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_315552 prefixEnd_315552 := by exact prefixLift 315552
  have htrace : WordTrace (prefixWord ++ tailWord_315552) baseStart_315552 baseEnd_315552 := by
    simpa [prefixWord, tailWord_315552, baseEnd_315552] using wordTrace_append hprefix tailTrace_315552
  have hstable : (prefixWord ++ tailWord_315552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315552).length < 2 ^ (prefixWord ++ tailWord_315552).sum := by decide
  have hdescent : baseEnd_315552 < baseStart_315552 := by decide
  rcases family_descends (prefixWord ++ tailWord_315552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315599 : List Nat := [1, 1, 2, 1, 1, 3, 3, 6, 4]
def baseStart_315599 : Nat := 118140960795 + 315599 * 2 ^ 59
def prefixEnd_315599 : Nat := 4983230072969 + 3 ^ 40 * 315599 * 2
def baseEnd_315599 : Nat := 36011995795203544702465

theorem tailTrace_315599 : CollatzResearch.WordTrace tailWord_315599 prefixEnd_315599 36011995795203544702465 := by
  unfold tailWord_315599
  simp only [CollatzResearch.WordTrace]
  refine ⟨11510841183646197863109851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7673894122430798575406567 11510841183646197863109851)
  ·
    refine ⟨17266261775469296794664777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11510841183646197863109851 17266261775469296794664777)
    ·
      refine ⟨12949696331601972595998583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17266261775469296794664777 12949696331601972595998583)
      ·
        refine ⟨19424544497402958893997875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12949696331601972595998583 19424544497402958893997875)
        ·
          refine ⟨29136816746104438340996813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19424544497402958893997875 29136816746104438340996813)
          ·
            refine ⟨10926306279789164377873805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29136816746104438340996813 10926306279789164377873805)
            ·
              refine ⟨4097364854920936641702677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10926306279789164377873805 4097364854920936641702677)
              ·
                refine ⟨192063977574418905079813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4097364854920936641702677 192063977574418905079813)
                ·
                  refine ⟨36011995795203544702465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 192063977574418905079813 36011995795203544702465)
                  ·
                    rfl

theorem cell22_315599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 6, 4].length) (baseStart_315599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_315599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_315599 prefixEnd_315599 := by exact prefixLift 315599
  have htrace : WordTrace (prefixWord ++ tailWord_315599) baseStart_315599 baseEnd_315599 := by
    simpa [prefixWord, tailWord_315599, baseEnd_315599] using wordTrace_append hprefix tailTrace_315599
  have hstable : (prefixWord ++ tailWord_315599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315599).length < 2 ^ (prefixWord ++ tailWord_315599).sum := by decide
  have hdescent : baseEnd_315599 < baseStart_315599 := by decide
  rcases family_descends (prefixWord ++ tailWord_315599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315627 : List Nat := [1, 1, 1, 1, 2, 5, 3, 8]
def baseStart_315627 : Nat := 118140960795 + 315627 * 2 ^ 59
def prefixEnd_315627 : Nat := 4983230072969 + 3 ^ 40 * 315627 * 2
def baseEnd_315627 : Nat := 12005063595314210489701

theorem tailTrace_315627 : CollatzResearch.WordTrace tailWord_315627 prefixEnd_315627 12005063595314210489701 := by
  unfold tailWord_315627
  simp only [CollatzResearch.WordTrace]
  refine ⟨11511862427544758645129135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7674574951696505763419423 11511862427544758645129135)
  ·
    refine ⟨17267793641317137967693703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11511862427544758645129135 17267793641317137967693703)
    ·
      refine ⟨25901690461975706951540555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17267793641317137967693703 25901690461975706951540555)
      ·
        refine ⟨38852535692963560427310833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25901690461975706951540555 38852535692963560427310833)
        ·
          refine ⟨29139401769722670320483125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38852535692963560427310833 29139401769722670320483125)
          ·
            refine ⟨2731818915911500342545293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29139401769722670320483125 2731818915911500342545293)
            ·
              refine ⟨1024432093466812628454485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2731818915911500342545293 1024432093466812628454485)
              ·
                refine ⟨12005063595314210489701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1024432093466812628454485 12005063595314210489701)
                ·
                  rfl

theorem cell22_315627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 8].length) (baseStart_315627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_315627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_315627 prefixEnd_315627 := by exact prefixLift 315627
  have htrace : WordTrace (prefixWord ++ tailWord_315627) baseStart_315627 baseEnd_315627 := by
    simpa [prefixWord, tailWord_315627, baseEnd_315627] using wordTrace_append hprefix tailTrace_315627
  have hstable : (prefixWord ++ tailWord_315627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315627).length < 2 ^ (prefixWord ++ tailWord_315627).sum := by decide
  have hdescent : baseEnd_315627 < baseStart_315627 := by decide
  rcases family_descends (prefixWord ++ tailWord_315627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315644 : List Nat := [2, 2, 2, 1, 4, 3, 8]
def baseStart_315644 : Nat := 118140960795 + 315644 * 2 ^ 59
def prefixEnd_315644 : Nat := 4983230072969 + 3 ^ 40 * 315644 * 2
def baseEnd_315644 : Nat := 4001903400194278397491

theorem tailTrace_315644 : CollatzResearch.WordTrace tailWord_315644 prefixEnd_315644 4001903400194278397491 := by
  unfold tailWord_315644
  simp only [CollatzResearch.WordTrace]
  refine ⟨5756241234241585274248993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7674988312322113698998657 5756241234241585274248993)
  ·
    refine ⟨4317180925681188955686745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5756241234241585274248993 4317180925681188955686745)
    ·
      refine ⟨3237885694260891716765059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4317180925681188955686745 3237885694260891716765059)
      ·
        refine ⟨4856828541391337575147589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3237885694260891716765059 4856828541391337575147589)
        ·
          refine ⟨910655351510875795340173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4856828541391337575147589 910655351510875795340173)
          ·
            refine ⟨341495756816578423252565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 910655351510875795340173 341495756816578423252565)
            ·
              refine ⟨4001903400194278397491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 341495756816578423252565 4001903400194278397491)
              ·
                rfl

theorem cell22_315644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 8].length) (baseStart_315644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_315644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_315644 prefixEnd_315644 := by exact prefixLift 315644
  have htrace : WordTrace (prefixWord ++ tailWord_315644) baseStart_315644 baseEnd_315644 := by
    simpa [prefixWord, tailWord_315644, baseEnd_315644] using wordTrace_append hprefix tailTrace_315644
  have hstable : (prefixWord ++ tailWord_315644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315644).length < 2 ^ (prefixWord ++ tailWord_315644).sum := by decide
  have hdescent : baseEnd_315644 < baseStart_315644 := by decide
  rcases family_descends (prefixWord ++ tailWord_315644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315646 : List Nat := [4, 2, 2, 1, 1, 1, 3, 2, 2, 4]
def baseStart_315646 : Nat := 118140960795 + 315646 * 2 ^ 59
def prefixEnd_315646 : Nat := 4983230072969 + 3 ^ 40 * 315646 * 2
def baseEnd_315646 : Nat := 108052076446118178182251

theorem tailTrace_315646 : CollatzResearch.WordTrace tailWord_315646 prefixEnd_315646 108052076446118178182251 := by
  unfold tailWord_315646
  simp only [CollatzResearch.WordTrace]
  refine ⟨1439069426809490611258849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7675036942983949926713861 1439069426809490611258849)
  ·
    refine ⟨1079302070107117958444137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1439069426809490611258849 1079302070107117958444137)
    ·
      refine ⟨809476552580338468833103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1079302070107117958444137 809476552580338468833103)
      ·
        refine ⟨1214214828870507703249655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 809476552580338468833103 1214214828870507703249655)
        ·
          refine ⟨1821322243305761554874483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1214214828870507703249655 1821322243305761554874483)
          ·
            refine ⟨2731983364958642332311725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1821322243305761554874483 2731983364958642332311725)
            ·
              refine ⟨1024493761859490874616897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2731983364958642332311725 1024493761859490874616897)
              ·
                refine ⟨768370321394618155962673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1024493761859490874616897 768370321394618155962673)
                ·
                  refine ⟨576277741045963616972005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 768370321394618155962673 576277741045963616972005)
                  ·
                    refine ⟨108052076446118178182251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 576277741045963616972005 108052076446118178182251)
                    ·
                      rfl

theorem cell22_315646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_315646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_315646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_315646 prefixEnd_315646 := by exact prefixLift 315646
  have htrace : WordTrace (prefixWord ++ tailWord_315646) baseStart_315646 baseEnd_315646 := by
    simpa [prefixWord, tailWord_315646, baseEnd_315646] using wordTrace_append hprefix tailTrace_315646
  have hstable : (prefixWord ++ tailWord_315646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315646).length < 2 ^ (prefixWord ++ tailWord_315646).sum := by decide
  have hdescent : baseEnd_315646 < baseStart_315646 := by decide
  rcases family_descends (prefixWord ++ tailWord_315646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315650 : List Nat := [3, 4, 1, 1, 2, 2, 3, 2, 4]
def baseStart_315650 : Nat := 118140960795 + 315650 * 2 ^ 59
def prefixEnd_315650 : Nat := 4983230072969 + 3 ^ 40 * 315650 * 2
def baseEnd_315650 : Nat := 36017815242621167027413

theorem tailTrace_315650 : CollatzResearch.WordTrace tailWord_315650 prefixEnd_315650 36017815242621167027413 := by
  unfold tailWord_315650
  simp only [CollatzResearch.WordTrace]
  refine ⟨2878175326615358393304101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7675134204307622382144269 2878175326615358393304101)
  ·
    refine ⟨539657873740379698744519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2878175326615358393304101 539657873740379698744519)
    ·
      refine ⟨809486810610569548116779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 539657873740379698744519 809486810610569548116779)
      ·
        refine ⟨1214230215915854322175169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 809486810610569548116779 1214230215915854322175169)
        ·
          refine ⟨910672661936890741631377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1214230215915854322175169 910672661936890741631377)
          ·
            refine ⟨683004496452668056223533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 910672661936890741631377 683004496452668056223533)
            ·
              refine ⟨256126686169750521083825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 683004496452668056223533 256126686169750521083825)
              ·
                refine ⟨192095014627312890812869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 256126686169750521083825 192095014627312890812869)
                ·
                  refine ⟨36017815242621167027413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 192095014627312890812869 36017815242621167027413)
                  ·
                    rfl

theorem cell22_315650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_315650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_315650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_315650 prefixEnd_315650 := by exact prefixLift 315650
  have htrace : WordTrace (prefixWord ++ tailWord_315650) baseStart_315650 baseEnd_315650 := by
    simpa [prefixWord, tailWord_315650, baseEnd_315650] using wordTrace_append hprefix tailTrace_315650
  have hstable : (prefixWord ++ tailWord_315650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315650).length < 2 ^ (prefixWord ++ tailWord_315650).sum := by decide
  have hdescent : baseEnd_315650 < baseStart_315650 := by decide
  rcases family_descends (prefixWord ++ tailWord_315650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315706 : List Nat := [3, 1, 1, 1, 4, 3, 2, 2, 5]
def baseStart_315706 : Nat := 118140960795 + 315706 * 2 ^ 59
def prefixEnd_315706 : Nat := 4983230072969 + 3 ^ 40 * 315706 * 2
def baseEnd_315706 : Nat := 36024205224099340560689

theorem tailTrace_315706 : CollatzResearch.WordTrace tailWord_315706 prefixEnd_315706 36024205224099340560689 := by
  unfold tailWord_315706
  simp only [CollatzResearch.WordTrace]
  refine ⟨2878685948564638784313743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7676495862839036758169981 2878685948564638784313743)
  ·
    refine ⟨4318028922846958176470615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2878685948564638784313743 4318028922846958176470615)
    ·
      refine ⟨6477043384270437264705923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4318028922846958176470615 6477043384270437264705923)
      ·
        refine ⟨9715565076405655897058885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6477043384270437264705923 9715565076405655897058885)
        ·
          refine ⟨1821668451826060480698541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9715565076405655897058885 1821668451826060480698541)
          ·
            refine ⟨683125669434772680261953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1821668451826060480698541 683125669434772680261953)
            ·
              refine ⟨512344252076079510196465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 683125669434772680261953 512344252076079510196465)
              ·
                refine ⟨384258189057059632647349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 512344252076079510196465 384258189057059632647349)
                ·
                  refine ⟨36024205224099340560689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 384258189057059632647349 36024205224099340560689)
                  ·
                    rfl

theorem cell22_315706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 2, 5].length) (baseStart_315706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_315706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_315706 prefixEnd_315706 := by exact prefixLift 315706
  have htrace : WordTrace (prefixWord ++ tailWord_315706) baseStart_315706 baseEnd_315706 := by
    simpa [prefixWord, tailWord_315706, baseEnd_315706] using wordTrace_append hprefix tailTrace_315706
  have hstable : (prefixWord ++ tailWord_315706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315706).length < 2 ^ (prefixWord ++ tailWord_315706).sum := by decide
  have hdescent : baseEnd_315706 < baseStart_315706 := by decide
  rcases family_descends (prefixWord ++ tailWord_315706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315710 : List Nat := [4, 2, 1, 2, 1, 3, 1, 4, 1, 3]
def baseStart_315710 : Nat := 118140960795 + 315710 * 2 ^ 59
def prefixEnd_315710 : Nat := 4983230072969 + 3 ^ 40 * 315710 * 2
def baseEnd_315710 : Nat := 108073984954043344582055

theorem tailTrace_315710 : CollatzResearch.WordTrace tailWord_315710 prefixEnd_315710 108073984954043344582055 := by
  unfold tailWord_315710
  simp only [CollatzResearch.WordTrace]
  refine ⟨1439361210780507977550073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7676593124162709213600389 1439361210780507977550073)
  ·
    refine ⟨1079520908085380983162555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1439361210780507977550073 1079520908085380983162555)
    ·
      refine ⟨1619281362128071474743833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1079520908085380983162555 1619281362128071474743833)
      ·
        refine ⟨1214461021596053606057875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1619281362128071474743833 1214461021596053606057875)
        ·
          refine ⟨1821691532394080409086813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1214461021596053606057875 1821691532394080409086813)
          ·
            refine ⟨683134324647780153407555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1821691532394080409086813 683134324647780153407555)
            ·
              refine ⟨1024701486971670230111333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 683134324647780153407555 1024701486971670230111333)
              ·
                refine ⟨192131528807188168145875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1024701486971670230111333 192131528807188168145875)
                ·
                  refine ⟨288197293210782252218813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 192131528807188168145875 288197293210782252218813)
                  ·
                    refine ⟨108073984954043344582055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 288197293210782252218813 108073984954043344582055)
                    ·
                      rfl

theorem cell22_315710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 4, 1, 3].length) (baseStart_315710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_315710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_315710 prefixEnd_315710 := by exact prefixLift 315710
  have htrace : WordTrace (prefixWord ++ tailWord_315710) baseStart_315710 baseEnd_315710 := by
    simpa [prefixWord, tailWord_315710, baseEnd_315710] using wordTrace_append hprefix tailTrace_315710
  have hstable : (prefixWord ++ tailWord_315710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315710).length < 2 ^ (prefixWord ++ tailWord_315710).sum := by decide
  have hdescent : baseEnd_315710 < baseStart_315710 := by decide
  rcases family_descends (prefixWord ++ tailWord_315710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315719 : List Nat := [1, 1, 4, 1, 2, 2, 1, 1, 5, 4]
def baseStart_315719 : Nat := 118140960795 + 315719 * 2 ^ 59
def prefixEnd_315719 : Nat := 4983230072969 + 3 ^ 40 * 315719 * 2
def baseEnd_315719 : Nat := 108077065837970321107027

theorem tailTrace_315719 : CollatzResearch.WordTrace tailWord_315719 prefixEnd_315719 108077065837970321107027 := by
  unfold tailWord_315719
  simp only [CollatzResearch.WordTrace]
  refine ⟨11515217943211458357478211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7676811962140972238318807 11515217943211458357478211)
  ·
    refine ⟨17272826914817187536217317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11515217943211458357478211 17272826914817187536217317)
    ·
      refine ⟨3238655046528222663040747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17272826914817187536217317 3238655046528222663040747)
      ·
        refine ⟨4857982569792333994561121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3238655046528222663040747 4857982569792333994561121)
        ·
          refine ⟨3643486927344250495920841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4857982569792333994561121 3643486927344250495920841)
          ·
            refine ⟨2732615195508187871940631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3643486927344250495920841 2732615195508187871940631)
            ·
              refine ⟨4098922793262281807910947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2732615195508187871940631 4098922793262281807910947)
              ·
                refine ⟨6148384189893422711866421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4098922793262281807910947 6148384189893422711866421)
                ·
                  refine ⟨576411017802508379237477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6148384189893422711866421 576411017802508379237477)
                  ·
                    refine ⟨108077065837970321107027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 576411017802508379237477 108077065837970321107027)
                    ·
                      rfl

theorem cell22_315719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_315719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_315719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_315719 prefixEnd_315719 := by exact prefixLift 315719
  have htrace : WordTrace (prefixWord ++ tailWord_315719) baseStart_315719 baseEnd_315719 := by
    simpa [prefixWord, tailWord_315719, baseEnd_315719] using wordTrace_append hprefix tailTrace_315719
  have hstable : (prefixWord ++ tailWord_315719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315719).length < 2 ^ (prefixWord ++ tailWord_315719).sum := by decide
  have hdescent : baseEnd_315719 < baseStart_315719 := by decide
  rcases family_descends (prefixWord ++ tailWord_315719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315862 : List Nat := [5, 2, 1, 1, 1, 1, 2, 5, 1, 3]
def baseStart_315862 : Nat := 118140960795 + 315862 * 2 ^ 59
def prefixEnd_315862 : Nat := 4983230072969 + 3 ^ 40 * 315862 * 2
def baseEnd_315862 : Nat := 108126017660365614781589

theorem tailTrace_315862 : CollatzResearch.WordTrace tailWord_315862 prefixEnd_315862 108126017660365614781589 := by
  unfold tailWord_315862
  simp only [CollatzResearch.WordTrace]
  refine ⟨720027098855837111245865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7680289054462262519955893 720027098855837111245865)
  ·
    refine ⟨540020324141877833434399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 720027098855837111245865 540020324141877833434399)
    ·
      refine ⟨810030486212816750151599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 540020324141877833434399 810030486212816750151599)
      ·
        refine ⟨1215045729319225125227399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 810030486212816750151599 1215045729319225125227399)
        ·
          refine ⟨1822568593978837687841099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1215045729319225125227399 1822568593978837687841099)
          ·
            refine ⟨2733852890968256531761649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1822568593978837687841099 2733852890968256531761649)
            ·
              refine ⟨2050389668226192398821237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2733852890968256531761649 2050389668226192398821237)
              ·
                refine ⟨192224031396205537389491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2050389668226192398821237 192224031396205537389491)
                ·
                  refine ⟨288336047094308306084237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 192224031396205537389491 288336047094308306084237)
                  ·
                    refine ⟨108126017660365614781589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 288336047094308306084237 108126017660365614781589)
                    ·
                      rfl

theorem cell22_315862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_315862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_315862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_315862 prefixEnd_315862 := by exact prefixLift 315862
  have htrace : WordTrace (prefixWord ++ tailWord_315862) baseStart_315862 baseEnd_315862 := by
    simpa [prefixWord, tailWord_315862, baseEnd_315862] using wordTrace_append hprefix tailTrace_315862
  have hstable : (prefixWord ++ tailWord_315862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315862).length < 2 ^ (prefixWord ++ tailWord_315862).sum := by decide
  have hdescent : baseEnd_315862 < baseStart_315862 := by decide
  rcases family_descends (prefixWord ++ tailWord_315862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315918 : List Nat := [4, 1, 1, 2, 3, 1, 2, 2, 1, 5]
def baseStart_315918 : Nat := 118140960795 + 315918 * 2 ^ 59
def prefixEnd_315918 : Nat := 4983230072969 + 3 ^ 40 * 315918 * 2
def baseEnd_315918 : Nat := 108145187604800135381417

theorem tailTrace_315918 : CollatzResearch.WordTrace tailWord_315918 prefixEnd_315918 108145187604800135381417 := by
  unfold tailWord_315918
  simp only [CollatzResearch.WordTrace]
  refine ⟨1440309508686314417996551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7681650712993676895981605 1440309508686314417996551)
  ·
    refine ⟨2160464263029471626994827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1440309508686314417996551 2160464263029471626994827)
    ·
      refine ⟨3240696394544207440492241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2160464263029471626994827 3240696394544207440492241)
      ·
        refine ⟨2430522295908155580369181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3240696394544207440492241 2430522295908155580369181)
        ·
          refine ⟨911445860965558342638443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2430522295908155580369181 911445860965558342638443)
          ·
            refine ⟨1367168791448337513957665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 911445860965558342638443 1367168791448337513957665)
            ·
              refine ⟨1025376593586253135468249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1367168791448337513957665 1025376593586253135468249)
              ·
                refine ⟨769032445189689851601187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1025376593586253135468249 769032445189689851601187)
                ·
                  refine ⟨1153548667784534777401781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 769032445189689851601187 1153548667784534777401781)
                  ·
                    refine ⟨108145187604800135381417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1153548667784534777401781 108145187604800135381417)
                    ·
                      rfl

theorem cell22_315918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 2, 1, 5].length) (baseStart_315918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_315918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_315918 prefixEnd_315918 := by exact prefixLift 315918
  have htrace : WordTrace (prefixWord ++ tailWord_315918) baseStart_315918 baseEnd_315918 := by
    simpa [prefixWord, tailWord_315918, baseEnd_315918] using wordTrace_append hprefix tailTrace_315918
  have hstable : (prefixWord ++ tailWord_315918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315918).length < 2 ^ (prefixWord ++ tailWord_315918).sum := by decide
  have hdescent : baseEnd_315918 < baseStart_315918 := by decide
  rcases family_descends (prefixWord ++ tailWord_315918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315965 : List Nat := [1, 4, 1, 3, 2, 3, 2, 6]
def baseStart_315965 : Nat := 118140960795 + 315965 * 2 ^ 59
def prefixEnd_315965 : Nat := 4983230072969 + 3 ^ 40 * 315965 * 2
def baseEnd_315965 : Nat := 12017919629478631050697

theorem tailTrace_315965 : CollatzResearch.WordTrace tailWord_315965 prefixEnd_315965 12017919629478631050697 := by
  unfold tailWord_315965
  simp only [CollatzResearch.WordTrace]
  refine ⟨11524190300320242370933349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7682793533546828247288899 11524190300320242370933349)
  ·
    refine ⟨2160785681310045444550003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11524190300320242370933349 2160785681310045444550003)
    ·
      refine ⟨3241178521965068166825005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2160785681310045444550003 3241178521965068166825005)
      ·
        refine ⟨1215441945736900562559377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3241178521965068166825005 1215441945736900562559377)
        ·
          refine ⟨911581459302675421919533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1215441945736900562559377 911581459302675421919533)
          ·
            refine ⟨341843047238503283219825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 911581459302675421919533 341843047238503283219825)
            ·
              refine ⟨256382285428877462414869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 341843047238503283219825 256382285428877462414869)
              ·
                refine ⟨12017919629478631050697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 256382285428877462414869 12017919629478631050697)
                ·
                  rfl

theorem cell22_315965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 2, 6].length) (baseStart_315965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_315965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_315965 prefixEnd_315965 := by exact prefixLift 315965
  have htrace : WordTrace (prefixWord ++ tailWord_315965) baseStart_315965 baseEnd_315965 := by
    simpa [prefixWord, tailWord_315965, baseEnd_315965] using wordTrace_append hprefix tailTrace_315965
  have hstable : (prefixWord ++ tailWord_315965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315965).length < 2 ^ (prefixWord ++ tailWord_315965).sum := by decide
  have hdescent : baseEnd_315965 < baseStart_315965 := by decide
  rcases family_descends (prefixWord ++ tailWord_315965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316055 : List Nat := [1, 1, 3, 3, 2, 1, 3, 4, 4]
def baseStart_316055 : Nat := 118140960795 + 316055 * 2 ^ 59
def prefixEnd_316055 : Nat := 4983230072969 + 3 ^ 40 * 316055 * 2
def baseEnd_316055 : Nat := 36064028501525814901999

theorem tailTrace_316055 : CollatzResearch.WordTrace tailWord_316055 prefixEnd_316055 36064028501525814901999 := by
  unfold tailWord_316055
  simp only [CollatzResearch.WordTrace]
  refine ⟨11527472869994187741709619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7684981913329458494473079 11527472869994187741709619)
  ·
    refine ⟨17291209304991281612564429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11527472869994187741709619 17291209304991281612564429)
    ·
      refine ⟨6484203489371730604711661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17291209304991281612564429 6484203489371730604711661)
      ·
        refine ⟨2431576308514398976766873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6484203489371730604711661 2431576308514398976766873)
        ·
          refine ⟨1823682231385799232575155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2431576308514398976766873 1823682231385799232575155)
          ·
            refine ⟨2735523347078698848862733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1823682231385799232575155 2735523347078698848862733)
            ·
              refine ⟨1025821255154512068323525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2735523347078698848862733 1025821255154512068323525)
              ·
                refine ⟨192341485341471012810661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1025821255154512068323525 192341485341471012810661)
                ·
                  refine ⟨36064028501525814901999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 192341485341471012810661 36064028501525814901999)
                  ·
                    rfl

theorem cell22_316055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 4, 4].length) (baseStart_316055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_316055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_316055 prefixEnd_316055 := by exact prefixLift 316055
  have htrace : WordTrace (prefixWord ++ tailWord_316055) baseStart_316055 baseEnd_316055 := by
    simpa [prefixWord, tailWord_316055, baseEnd_316055] using wordTrace_append hprefix tailTrace_316055
  have hstable : (prefixWord ++ tailWord_316055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316055).length < 2 ^ (prefixWord ++ tailWord_316055).sum := by decide
  have hdescent : baseEnd_316055 < baseStart_316055 := by decide
  rcases family_descends (prefixWord ++ tailWord_316055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316068 : List Nat := [2, 3, 1, 2, 2, 1, 2, 2, 1, 6]
def baseStart_316068 : Nat := 118140960795 + 316068 * 2 ^ 59
def prefixEnd_316068 : Nat := 4983230072969 + 3 ^ 40 * 316068 * 2
def baseEnd_316068 : Nat := 108196535670249744130957

theorem tailTrace_316068 : CollatzResearch.WordTrace tailWord_316068 prefixEnd_316068 108196535670249744130957 := by
  unfold tailWord_316068
  simp only [CollatzResearch.WordTrace]
  refine ⟨5763973509473545480966429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7685298012631393974621905 5763973509473545480966429)
  ·
    refine ⟨2161490066052579555362411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5763973509473545480966429 2161490066052579555362411)
    ·
      refine ⟨3242235099078869333043617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2161490066052579555362411 3242235099078869333043617)
      ·
        refine ⟨2431676324309151999782713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3242235099078869333043617 2431676324309151999782713)
        ·
          refine ⟨1823757243231863999837035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2431676324309151999782713 1823757243231863999837035)
          ·
            refine ⟨2735635864847795999755553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1823757243231863999837035 2735635864847795999755553)
            ·
              refine ⟨2051726898635846999816665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2735635864847795999755553 2051726898635846999816665)
              ·
                refine ⟨1538795173976885249862499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2051726898635846999816665 1538795173976885249862499)
                ·
                  refine ⟨2308192760965327874793749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1538795173976885249862499 2308192760965327874793749)
                  ·
                    refine ⟨108196535670249744130957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2308192760965327874793749 108196535670249744130957)
                    ·
                      rfl

theorem cell22_316068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 1, 6].length) (baseStart_316068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_316068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_316068 prefixEnd_316068 := by exact prefixLift 316068
  have htrace : WordTrace (prefixWord ++ tailWord_316068) baseStart_316068 baseEnd_316068 := by
    simpa [prefixWord, tailWord_316068, baseEnd_316068] using wordTrace_append hprefix tailTrace_316068
  have hstable : (prefixWord ++ tailWord_316068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316068).length < 2 ^ (prefixWord ++ tailWord_316068).sum := by decide
  have hdescent : baseEnd_316068 < baseStart_316068 := by decide
  rcases family_descends (prefixWord ++ tailWord_316068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316085 : List Nat := [1, 3, 3, 3, 1, 2, 1, 1, 1, 6]
def baseStart_316085 : Nat := 118140960795 + 316085 * 2 ^ 59
def prefixEnd_316085 : Nat := 4983230072969 + 3 ^ 40 * 316085 * 2
def baseEnd_316085 : Nat := 108202355117667366455905

theorem tailTrace_316085 : CollatzResearch.WordTrace tailWord_316085 prefixEnd_316085 108202355117667366455905 := by
  unfold tailWord_316085
  simp only [CollatzResearch.WordTrace]
  refine ⟨11528567059885502865301709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7685711373257001910201139 11528567059885502865301709)
  ·
    refine ⟨4323212647457063574488141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11528567059885502865301709 4323212647457063574488141)
    ·
      refine ⟨1621204742796398840433053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4323212647457063574488141 1621204742796398840433053)
      ·
        refine ⟨607951778548649565162395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1621204742796398840433053 607951778548649565162395)
        ·
          refine ⟨911927667822974347743593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 607951778548649565162395 911927667822974347743593)
          ·
            refine ⟨683945750867230760807695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 911927667822974347743593 683945750867230760807695)
            ·
              refine ⟨1025918626300846141211543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 683945750867230760807695 1025918626300846141211543)
              ·
                refine ⟨1538877939451269211817315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1025918626300846141211543 1538877939451269211817315)
                ·
                  refine ⟨2308316909176903817725973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1538877939451269211817315 2308316909176903817725973)
                  ·
                    refine ⟨108202355117667366455905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2308316909176903817725973 108202355117667366455905)
                    ·
                      rfl

theorem cell22_316085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_316085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_316085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_316085 prefixEnd_316085 := by exact prefixLift 316085
  have htrace : WordTrace (prefixWord ++ tailWord_316085) baseStart_316085 baseEnd_316085 := by
    simpa [prefixWord, tailWord_316085, baseEnd_316085] using wordTrace_append hprefix tailTrace_316085
  have hstable : (prefixWord ++ tailWord_316085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316085).length < 2 ^ (prefixWord ++ tailWord_316085).sum := by decide
  have hdescent : baseEnd_316085 < baseStart_316085 := by decide
  rcases family_descends (prefixWord ++ tailWord_316085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316192 : List Nat := [2, 1, 1, 5, 1, 2, 3, 2, 1, 4]
def baseStart_316192 : Nat := 118140960795 + 316192 * 2 ^ 59
def prefixEnd_316192 : Nat := 4983230072969 + 3 ^ 40 * 316192 * 2
def baseEnd_316192 : Nat := 108238983404354754030577

theorem tailTrace_316192 : CollatzResearch.WordTrace tailWord_316192 prefixEnd_316192 108238983404354754030577 := by
  unfold tailWord_316192
  simp only [CollatzResearch.WordTrace]
  refine ⟨5766234835248930069723415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7688313113665240092964553 5766234835248930069723415)
  ·
    refine ⟨8649352252873395104585123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5766234835248930069723415 8649352252873395104585123)
    ·
      refine ⟨12974028379310092656877685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8649352252873395104585123 12974028379310092656877685)
      ·
        refine ⟨1216315160560321186582283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12974028379310092656877685 1216315160560321186582283)
        ·
          refine ⟨1824472740840481779873425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1216315160560321186582283 1824472740840481779873425)
          ·
            refine ⟨1368354555630361334905069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1824472740840481779873425 1368354555630361334905069)
            ·
              refine ⟨513132958361385500589401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1368354555630361334905069 513132958361385500589401)
              ·
                refine ⟨384849718771039125442051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 513132958361385500589401 384849718771039125442051)
                ·
                  refine ⟨577274578156558688163077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 384849718771039125442051 577274578156558688163077)
                  ·
                    refine ⟨108238983404354754030577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 577274578156558688163077 108238983404354754030577)
                    ·
                      rfl

theorem cell22_316192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 2, 1, 4].length) (baseStart_316192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_316192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_316192 prefixEnd_316192 := by exact prefixLift 316192
  have htrace : WordTrace (prefixWord ++ tailWord_316192) baseStart_316192 baseEnd_316192 := by
    simpa [prefixWord, tailWord_316192, baseEnd_316192] using wordTrace_append hprefix tailTrace_316192
  have hstable : (prefixWord ++ tailWord_316192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316192).length < 2 ^ (prefixWord ++ tailWord_316192).sum := by decide
  have hdescent : baseEnd_316192 < baseStart_316192 := by decide
  rcases family_descends (prefixWord ++ tailWord_316192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316218 : List Nat := [3, 1, 1, 1, 16]
def baseStart_316218 : Nat := 118140960795 + 316218 * 2 ^ 59
def prefixEnd_316218 : Nat := 4983230072969 + 3 ^ 40 * 316218 * 2
def baseEnd_316218 : Nat := 445464542122219559179

theorem tailTrace_316218 : CollatzResearch.WordTrace tailWord_316218 prefixEnd_316218 445464542122219559179 := by
  unfold tailWord_316218
  simp only [CollatzResearch.WordTrace]
  refine ⟨2883354492100916644973327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7688945312269111053262205 2883354492100916644973327)
  ·
    refine ⟨4325031738151374967459991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2883354492100916644973327 4325031738151374967459991)
    ·
      refine ⟨6487547607227062451189987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4325031738151374967459991 6487547607227062451189987)
      ·
        refine ⟨9731321410840593676784981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6487547607227062451189987 9731321410840593676784981)
        ·
          refine ⟨445464542122219559179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 16 9731321410840593676784981 445464542122219559179)
          ·
            rfl

theorem cell22_316218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 16].length) (baseStart_316218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_316218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_316218 prefixEnd_316218 := by exact prefixLift 316218
  have htrace : WordTrace (prefixWord ++ tailWord_316218) baseStart_316218 baseEnd_316218 := by
    simpa [prefixWord, tailWord_316218, baseEnd_316218] using wordTrace_append hprefix tailTrace_316218
  have hstable : (prefixWord ++ tailWord_316218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316218).length < 2 ^ (prefixWord ++ tailWord_316218).sum := by decide
  have hdescent : baseEnd_316218 < baseStart_316218 := by decide
  rcases family_descends (prefixWord ++ tailWord_316218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316280 : List Nat := [2, 1, 2, 1, 1, 1, 1, 8, 5]
def baseStart_316280 : Nat := 118140960795 + 316280 * 2 ^ 59
def prefixEnd_316280 : Nat := 4983230072969 + 3 ^ 40 * 316280 * 2
def baseEnd_316280 : Nat := 36089702534250619276769

theorem tailTrace_316280 : CollatzResearch.WordTrace tailWord_316280 prefixEnd_316280 36089702534250619276769 := by
  unfold tailWord_316280
  simp only [CollatzResearch.WordTrace]
  refine ⟨5767839647089525584325147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7690452862786034112433529 5767839647089525584325147)
  ·
    refine ⟨8651759470634288376487721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5767839647089525584325147 8651759470634288376487721)
    ·
      refine ⟨6488819602975716282365791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8651759470634288376487721 6488819602975716282365791)
      ·
        refine ⟨9733229404463574423548687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6488819602975716282365791 9733229404463574423548687)
        ·
          refine ⟨14599844106695361635323031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9733229404463574423548687 14599844106695361635323031)
          ·
            refine ⟨21899766160043042452984547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14599844106695361635323031 21899766160043042452984547)
            ·
              refine ⟨32849649240064563679476821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21899766160043042452984547 32849649240064563679476821)
              ·
                refine ⟨384956827032006605618869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 32849649240064563679476821 384956827032006605618869)
                ·
                  refine ⟨36089702534250619276769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 384956827032006605618869 36089702534250619276769)
                  ·
                    rfl

theorem cell22_316280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 8, 5].length) (baseStart_316280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_316280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_316280 prefixEnd_316280 := by exact prefixLift 316280
  have htrace : WordTrace (prefixWord ++ tailWord_316280) baseStart_316280 baseEnd_316280 := by
    simpa [prefixWord, tailWord_316280, baseEnd_316280] using wordTrace_append hprefix tailTrace_316280
  have hstable : (prefixWord ++ tailWord_316280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316280).length < 2 ^ (prefixWord ++ tailWord_316280).sum := by decide
  have hdescent : baseEnd_316280 < baseStart_316280 := by decide
  rcases family_descends (prefixWord ++ tailWord_316280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316290 : List Nat := [3, 4, 2, 2, 1, 1, 3, 1, 2, 3]
def baseStart_316290 : Nat := 118140960795 + 316290 * 2 ^ 59
def prefixEnd_316290 : Nat := 4983230072969 + 3 ^ 40 * 316290 * 2
def baseEnd_316290 : Nat := 108272530807115165080277

theorem tailTrace_316290 : CollatzResearch.WordTrace tailWord_316290 prefixEnd_316290 108272530807115165080277 := by
  unfold tailWord_316290
  simp only [CollatzResearch.WordTrace]
  refine ⟨2884011006035705719128581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7690696016095215251009549 2884011006035705719128581)
  ·
    refine ⟨540752063631694822336609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2884011006035705719128581 540752063631694822336609)
    ·
      refine ⟨405564047723771116752457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 540752063631694822336609 405564047723771116752457)
      ·
        refine ⟨304173035792828337564343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 405564047723771116752457 304173035792828337564343)
        ·
          refine ⟨456259553689242506346515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 304173035792828337564343 456259553689242506346515)
          ·
            refine ⟨684389330533863759519773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 456259553689242506346515 684389330533863759519773)
            ·
              refine ⟨256645998950198909819915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 684389330533863759519773 256645998950198909819915)
              ·
                refine ⟨384968998425298364729873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 256645998950198909819915 384968998425298364729873)
                ·
                  refine ⟨288726748818973773547405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 384968998425298364729873 288726748818973773547405)
                  ·
                    refine ⟨108272530807115165080277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 288726748818973773547405 108272530807115165080277)
                    ·
                      rfl

theorem cell22_316290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_316290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_316290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_316290 prefixEnd_316290 := by exact prefixLift 316290
  have htrace : WordTrace (prefixWord ++ tailWord_316290) baseStart_316290 baseEnd_316290 := by
    simpa [prefixWord, tailWord_316290, baseEnd_316290] using wordTrace_append hprefix tailTrace_316290
  have hstable : (prefixWord ++ tailWord_316290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316290).length < 2 ^ (prefixWord ++ tailWord_316290).sum := by decide
  have hdescent : baseEnd_316290 < baseStart_316290 := by decide
  rcases family_descends (prefixWord ++ tailWord_316290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316374 : List Nat := [5, 2, 1, 1, 2, 1, 1, 1, 3, 5]
def baseStart_316374 : Nat := 118140960795 + 316374 * 2 ^ 59
def prefixEnd_316374 : Nat := 4983230072969 + 3 ^ 40 * 316374 * 2
def baseEnd_316374 : Nat := 108301285723766945980019

theorem tailTrace_316374 : CollatzResearch.WordTrace tailWord_316374 prefixEnd_316374 108301285723766945980019 := by
  unfold tailWord_316374
  simp only [CollatzResearch.WordTrace]
  refine ⟨721194234739906576410761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7692738503892336815048117 721194234739906576410761)
  ·
    refine ⟨540895676054929932308071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 721194234739906576410761 540895676054929932308071)
    ·
      refine ⟨811343514082394898462107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 540895676054929932308071 811343514082394898462107)
      ·
        refine ⟨1217015271123592347693161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 811343514082394898462107 1217015271123592347693161)
        ·
          refine ⟨912761453342694260769871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1217015271123592347693161 912761453342694260769871)
          ·
            refine ⟨1369142180014041391154807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 912761453342694260769871 1369142180014041391154807)
            ·
              refine ⟨2053713270021062086732211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1369142180014041391154807 2053713270021062086732211)
              ·
                refine ⟨3080569905031593130098317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2053713270021062086732211 3080569905031593130098317)
                ·
                  refine ⟨1155213714386847423786869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3080569905031593130098317 1155213714386847423786869)
                  ·
                    refine ⟨108301285723766945980019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1155213714386847423786869 108301285723766945980019)
                    ·
                      rfl

theorem cell22_316374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_316374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_316374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_316374 prefixEnd_316374 := by exact prefixLift 316374
  have htrace : WordTrace (prefixWord ++ tailWord_316374) baseStart_316374 baseEnd_316374 := by
    simpa [prefixWord, tailWord_316374, baseEnd_316374] using wordTrace_append hprefix tailTrace_316374
  have hstable : (prefixWord ++ tailWord_316374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316374).length < 2 ^ (prefixWord ++ tailWord_316374).sum := by decide
  have hdescent : baseEnd_316374 < baseStart_316374 := by decide
  rcases family_descends (prefixWord ++ tailWord_316374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316391 : List Nat := [1, 1, 5, 2, 2, 2, 2, 2, 2, 3]
def baseStart_316391 : Nat := 118140960795 + 316391 * 2 ^ 59
def prefixEnd_316391 : Nat := 4983230072969 + 3 ^ 40 * 316391 * 2
def baseEnd_316391 : Nat := 108307105171184568304967

theorem tailTrace_316391 : CollatzResearch.WordTrace tailWord_316391 prefixEnd_316391 108307105171184568304967 := by
  unfold tailWord_316391
  simp only [CollatzResearch.WordTrace]
  refine ⟨11539727796776917125941027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7693151864517944750627351 11539727796776917125941027)
  ·
    refine ⟨17309591695165375688911541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11539727796776917125941027 17309591695165375688911541)
    ·
      refine ⟨1622774221421753970835457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17309591695165375688911541 1622774221421753970835457)
      ·
        refine ⟨1217080666066315478126593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1622774221421753970835457 1217080666066315478126593)
        ·
          refine ⟨912810499549736608594945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1217080666066315478126593 912810499549736608594945)
          ·
            refine ⟨684607874662302456446209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 912810499549736608594945 684607874662302456446209)
            ·
              refine ⟨513455905996726842334657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 684607874662302456446209 513455905996726842334657)
              ·
                refine ⟨385091929497545131750993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 513455905996726842334657 385091929497545131750993)
                ·
                  refine ⟨288818947123158848813245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 385091929497545131750993 288818947123158848813245)
                  ·
                    refine ⟨108307105171184568304967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 288818947123158848813245 108307105171184568304967)
                    ·
                      rfl

theorem cell22_316391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 2, 2, 3].length) (baseStart_316391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_316391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_316391 prefixEnd_316391 := by exact prefixLift 316391
  have htrace : WordTrace (prefixWord ++ tailWord_316391) baseStart_316391 baseEnd_316391 := by
    simpa [prefixWord, tailWord_316391, baseEnd_316391] using wordTrace_append hprefix tailTrace_316391
  have hstable : (prefixWord ++ tailWord_316391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316391).length < 2 ^ (prefixWord ++ tailWord_316391).sum := by decide
  have hdescent : baseEnd_316391 < baseStart_316391 := by decide
  rcases family_descends (prefixWord ++ tailWord_316391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316415 : List Nat := [1, 1, 2, 2, 1, 2, 1, 1, 11]
def baseStart_316415 : Nat := 118140960795 + 316415 * 2 ^ 59
def prefixEnd_316415 : Nat := 4983230072969 + 3 ^ 40 * 316415 * 2
def baseEnd_316415 : Nat := 36105106953885501901631

theorem tailTrace_316415 : CollatzResearch.WordTrace tailWord_316415 prefixEnd_316415 36105106953885501901631 := by
  unfold tailWord_316415
  simp only [CollatzResearch.WordTrace]
  refine ⟨11540603148689969224814699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7693735432459979483209799 11540603148689969224814699)
  ·
    refine ⟨17310904723034953837222049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11540603148689969224814699 17310904723034953837222049)
    ·
      refine ⟨12983178542276215377916537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17310904723034953837222049 12983178542276215377916537)
      ·
        refine ⟨9737383906707161533437403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12983178542276215377916537 9737383906707161533437403)
        ·
          refine ⟨14606075860060742300156105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9737383906707161533437403 14606075860060742300156105)
          ·
            refine ⟨10954556895045556725117079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14606075860060742300156105 10954556895045556725117079)
            ·
              refine ⟨16431835342568335087675619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10954556895045556725117079 16431835342568335087675619)
              ·
                refine ⟨24647753013852502631513429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16431835342568335087675619 24647753013852502631513429)
                ·
                  refine ⟨36105106953885501901631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 24647753013852502631513429 36105106953885501901631)
                  ·
                    rfl

theorem cell22_316415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 11].length) (baseStart_316415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_316415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_316415 prefixEnd_316415 := by exact prefixLift 316415
  have htrace : WordTrace (prefixWord ++ tailWord_316415) baseStart_316415 baseEnd_316415 := by
    simpa [prefixWord, tailWord_316415, baseEnd_316415] using wordTrace_append hprefix tailTrace_316415
  have hstable : (prefixWord ++ tailWord_316415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316415).length < 2 ^ (prefixWord ++ tailWord_316415).sum := by decide
  have hdescent : baseEnd_316415 < baseStart_316415 := by decide
  rcases family_descends (prefixWord ++ tailWord_316415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316447 : List Nat := [1, 1, 2, 4, 1, 3, 1, 2, 2, 5]
def baseStart_316447 : Nat := 118140960795 + 316447 * 2 ^ 59
def prefixEnd_316447 : Nat := 4983230072969 + 3 ^ 40 * 316447 * 2
def baseEnd_316447 : Nat := 108326275115619088904795

theorem tailTrace_316447 : CollatzResearch.WordTrace tailWord_316447 prefixEnd_316447 108326275115619088904795 := by
  unfold tailWord_316447
  simp only [CollatzResearch.WordTrace]
  refine ⟨11541770284574038689979595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7694513523049359126653063 11541770284574038689979595)
  ·
    refine ⟨17312655426861058034969393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11541770284574038689979595 17312655426861058034969393)
    ·
      refine ⟨12984491570145793526227045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17312655426861058034969393 12984491570145793526227045)
      ·
        refine ⟨2434592169402336286167571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12984491570145793526227045 2434592169402336286167571)
        ·
          refine ⟨3651888254103504429251357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2434592169402336286167571 3651888254103504429251357)
          ·
            refine ⟨1369458095288814160969259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3651888254103504429251357 1369458095288814160969259)
            ·
              refine ⟨2054187142933221241453889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1369458095288814160969259 2054187142933221241453889)
              ·
                refine ⟨1540640357199915931090417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2054187142933221241453889 1540640357199915931090417)
                ·
                  refine ⟨1155480267899936948317813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1540640357199915931090417 1155480267899936948317813)
                  ·
                    refine ⟨108326275115619088904795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1155480267899936948317813 108326275115619088904795)
                    ·
                      rfl

theorem cell22_316447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 2, 5].length) (baseStart_316447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_316447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_316447 prefixEnd_316447 := by exact prefixLift 316447
  have htrace : WordTrace (prefixWord ++ tailWord_316447) baseStart_316447 baseEnd_316447 := by
    simpa [prefixWord, tailWord_316447, baseEnd_316447] using wordTrace_append hprefix tailTrace_316447
  have hstable : (prefixWord ++ tailWord_316447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316447).length < 2 ^ (prefixWord ++ tailWord_316447).sum := by decide
  have hdescent : baseEnd_316447 < baseStart_316447 := by decide
  rcases family_descends (prefixWord ++ tailWord_316447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316449 : List Nat := [1, 2, 3, 2, 3, 1, 3, 2, 5]
def baseStart_316449 : Nat := 118140960795 + 316449 * 2 ^ 59
def prefixEnd_316449 : Nat := 4983230072969 + 3 ^ 40 * 316449 * 2
def baseEnd_316449 : Nat := 36108986585497250118263

theorem tailTrace_316449 : CollatzResearch.WordTrace tailWord_316449 prefixEnd_316449 36108986585497250118263 := by
  unfold tailWord_316449
  simp only [CollatzResearch.WordTrace]
  refine ⟨11541843230566793031552401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7694562153711195354368267 11541843230566793031552401)
  ·
    refine ⟨8656382422925094773664301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11541843230566793031552401 8656382422925094773664301)
    ·
      refine ⟨3246143408596910540124113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8656382422925094773664301 3246143408596910540124113)
      ·
        refine ⟨2434607556447682905093085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3246143408596910540124113 2434607556447682905093085)
        ·
          refine ⟨912977833667881089409907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2434607556447682905093085 912977833667881089409907)
          ·
            refine ⟨1369466750501821634114861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 912977833667881089409907 1369466750501821634114861)
            ·
              refine ⟨513550031438183112793073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1369466750501821634114861 513550031438183112793073)
              ·
                refine ⟨385162523578637334594805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 513550031438183112793073 385162523578637334594805)
                ·
                  refine ⟨36108986585497250118263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 385162523578637334594805 36108986585497250118263)
                  ·
                    rfl

theorem cell22_316449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 2, 5].length) (baseStart_316449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_316449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_316449 prefixEnd_316449 := by exact prefixLift 316449
  have htrace : WordTrace (prefixWord ++ tailWord_316449) baseStart_316449 baseEnd_316449 := by
    simpa [prefixWord, tailWord_316449, baseEnd_316449] using wordTrace_append hprefix tailTrace_316449
  have hstable : (prefixWord ++ tailWord_316449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316449).length < 2 ^ (prefixWord ++ tailWord_316449).sum := by decide
  have hdescent : baseEnd_316449 < baseStart_316449 := by decide
  rcases family_descends (prefixWord ++ tailWord_316449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316492 : List Nat := [2, 2, 1, 3, 1, 1, 1, 3, 3, 5]
def baseStart_316492 : Nat := 118140960795 + 316492 * 2 ^ 59
def prefixEnd_316492 : Nat := 4983230072969 + 3 ^ 40 * 316492 * 2
def baseEnd_316492 : Nat := 108341679535253971529657

theorem tailTrace_316492 : CollatzResearch.WordTrace tailWord_316492 prefixEnd_316492 108341679535253971529657 := by
  unfold tailWord_316492
  simp only [CollatzResearch.WordTrace]
  refine ⟨5771705784705505687683865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7695607712940674250245153 5771705784705505687683865)
  ·
    refine ⟨4328779338529129265762899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5771705784705505687683865 4328779338529129265762899)
    ·
      refine ⟨6493169007793693898644349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4328779338529129265762899 6493169007793693898644349)
      ·
        refine ⟨2434938377922635211991631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6493169007793693898644349 2434938377922635211991631)
        ·
          refine ⟨3652407566883952817987447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2434938377922635211991631 3652407566883952817987447)
          ·
            refine ⟨5478611350325929226981171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3652407566883952817987447 5478611350325929226981171)
            ·
              refine ⟨8217917025488893840471757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5478611350325929226981171 8217917025488893840471757)
              ·
                refine ⟨3081718884558335190176909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8217917025488893840471757 3081718884558335190176909)
                ·
                  refine ⟨1155644581709375696316341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3081718884558335190176909 1155644581709375696316341)
                  ·
                    refine ⟨108341679535253971529657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1155644581709375696316341 108341679535253971529657)
                    ·
                      rfl

theorem cell22_316492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 3, 5].length) (baseStart_316492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_316492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_316492 prefixEnd_316492 := by exact prefixLift 316492
  have htrace : WordTrace (prefixWord ++ tailWord_316492) baseStart_316492 baseEnd_316492 := by
    simpa [prefixWord, tailWord_316492, baseEnd_316492] using wordTrace_append hprefix tailTrace_316492
  have hstable : (prefixWord ++ tailWord_316492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316492).length < 2 ^ (prefixWord ++ tailWord_316492).sum := by decide
  have hdescent : baseEnd_316492 < baseStart_316492 := by decide
  rcases family_descends (prefixWord ++ tailWord_316492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316511 : List Nat := [1, 1, 2, 3, 1, 1, 7, 2, 4]
def baseStart_316511 : Nat := 118140960795 + 316511 * 2 ^ 59
def prefixEnd_316511 : Nat := 4983230072969 + 3 ^ 40 * 316511 * 2
def baseEnd_316511 : Nat := 36116061207848085101533

theorem tailTrace_316511 : CollatzResearch.WordTrace tailWord_316511 prefixEnd_316511 36116061207848085101533 := by
  unfold tailWord_316511
  simp only [CollatzResearch.WordTrace]
  refine ⟨11544104556342177620309387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7696069704228118413539591 11544104556342177620309387)
  ·
    refine ⟨17316156834513266430464081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11544104556342177620309387 17316156834513266430464081)
    ·
      refine ⟨12987117625884949822848061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17316156834513266430464081 12987117625884949822848061)
      ·
        refine ⟨4870169109706856183568023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12987117625884949822848061 4870169109706856183568023)
        ·
          refine ⟨7305253664560284275352035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4870169109706856183568023 7305253664560284275352035)
          ·
            refine ⟨10957880496840426413028053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7305253664560284275352035 10957880496840426413028053)
            ·
              refine ⟨256825324144697494055345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 10957880496840426413028053 256825324144697494055345)
              ·
                refine ⟨192618993108523120541509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 256825324144697494055345 192618993108523120541509)
                ·
                  refine ⟨36116061207848085101533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 192618993108523120541509 36116061207848085101533)
                  ·
                    rfl

theorem cell22_316511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 7, 2, 4].length) (baseStart_316511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_316511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_316511 prefixEnd_316511 := by exact prefixLift 316511
  have htrace : WordTrace (prefixWord ++ tailWord_316511) baseStart_316511 baseEnd_316511 := by
    simpa [prefixWord, tailWord_316511, baseEnd_316511] using wordTrace_append hprefix tailTrace_316511
  have hstable : (prefixWord ++ tailWord_316511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316511).length < 2 ^ (prefixWord ++ tailWord_316511).sum := by decide
  have hdescent : baseEnd_316511 < baseStart_316511 := by decide
  rcases family_descends (prefixWord ++ tailWord_316511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316659 : List Nat := [1, 1, 1, 2, 2, 5, 2, 1, 1, 6]
def baseStart_316659 : Nat := 118140960795 + 316659 * 2 ^ 59
def prefixEnd_316659 : Nat := 4983230072969 + 3 ^ 40 * 316659 * 2
def baseEnd_316659 : Nat := 108398847048121202604145

theorem tailTrace_316659 : CollatzResearch.WordTrace tailWord_316659 prefixEnd_316659 108398847048121202604145 := by
  unfold tailWord_316659
  simp only [CollatzResearch.WordTrace]
  refine ⟨11549502559805998896697031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7699668373203999264464687 11549502559805998896697031)
  ·
    refine ⟨17324253839708998345045547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11549502559805998896697031 17324253839708998345045547)
    ·
      refine ⟨25986380759563497517568321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17324253839708998345045547 25986380759563497517568321)
      ·
        refine ⟨19489785569672623138176241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25986380759563497517568321 19489785569672623138176241)
        ·
          refine ⟨14617339177254467353632181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19489785569672623138176241 14617339177254467353632181)
          ·
            refine ⟨1370375547867606314403017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14617339177254467353632181 1370375547867606314403017)
            ·
              refine ⟨1027781660900704735802263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1370375547867606314403017 1027781660900704735802263)
              ·
                refine ⟨1541672491351057103703395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1027781660900704735802263 1541672491351057103703395)
                ·
                  refine ⟨2312508737026585655555093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1541672491351057103703395 2312508737026585655555093)
                  ·
                    refine ⟨108398847048121202604145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2312508737026585655555093 108398847048121202604145)
                    ·
                      rfl

theorem cell22_316659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 6].length) (baseStart_316659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_316659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_316659 prefixEnd_316659 := by exact prefixLift 316659
  have htrace : WordTrace (prefixWord ++ tailWord_316659) baseStart_316659 baseEnd_316659 := by
    simpa [prefixWord, tailWord_316659, baseEnd_316659] using wordTrace_append hprefix tailTrace_316659
  have hstable : (prefixWord ++ tailWord_316659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316659).length < 2 ^ (prefixWord ++ tailWord_316659).sum := by decide
  have hdescent : baseEnd_316659 < baseStart_316659 := by decide
  rcases family_descends (prefixWord ++ tailWord_316659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316676 : List Nat := [2, 3, 2, 2, 2, 1, 1, 1, 4, 4]
def baseStart_316676 : Nat := 118140960795 + 316676 * 2 ^ 59
def prefixEnd_316676 : Nat := 4983230072969 + 3 ^ 40 * 316676 * 2
def baseEnd_316676 : Nat := 108404666495538824929093

theorem tailTrace_316676 : CollatzResearch.WordTrace tailWord_316676 prefixEnd_316676 108404666495538824929093 := by
  unfold tailWord_316676
  simp only [CollatzResearch.WordTrace]
  refine ⟨5775061300372205400032941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7700081733829607200043921 5775061300372205400032941)
  ·
    refine ⟨2165647987639577025012353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5775061300372205400032941 2165647987639577025012353)
    ·
      refine ⟨1624235990729682768759265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2165647987639577025012353 1624235990729682768759265)
      ·
        refine ⟨1218176993047262076569449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1624235990729682768759265 1218176993047262076569449)
        ·
          refine ⟨913632744785446557427087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1218176993047262076569449 913632744785446557427087)
          ·
            refine ⟨1370449117178169836140631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 913632744785446557427087 1370449117178169836140631)
            ·
              refine ⟨2055673675767254754210947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1370449117178169836140631 2055673675767254754210947)
              ·
                refine ⟨3083510513650882131316421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2055673675767254754210947 3083510513650882131316421)
                ·
                  refine ⟨578158221309540399621829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3083510513650882131316421 578158221309540399621829)
                  ·
                    refine ⟨108404666495538824929093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 578158221309540399621829 108404666495538824929093)
                    ·
                      rfl

theorem cell22_316676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_316676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_316676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_316676 prefixEnd_316676 := by exact prefixLift 316676
  have htrace : WordTrace (prefixWord ++ tailWord_316676) baseStart_316676 baseEnd_316676 := by
    simpa [prefixWord, tailWord_316676, baseEnd_316676] using wordTrace_append hprefix tailTrace_316676
  have hstable : (prefixWord ++ tailWord_316676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316676).length < 2 ^ (prefixWord ++ tailWord_316676).sum := by decide
  have hdescent : baseEnd_316676 < baseStart_316676 := by decide
  rcases family_descends (prefixWord ++ tailWord_316676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316680 : List Nat := [2, 1, 3, 2, 4, 1, 3, 2, 4]
def baseStart_316680 : Nat := 118140960795 + 316680 * 2 ^ 59
def prefixEnd_316680 : Nat := 4983230072969 + 3 ^ 40 * 316680 * 2
def baseEnd_316680 : Nat := 36135345259094715943027

theorem tailTrace_316680 : CollatzResearch.WordTrace tailWord_316680 prefixEnd_316680 36135345259094715943027 := by
  unfold tailWord_316680
  simp only [CollatzResearch.WordTrace]
  refine ⟨5775134246364959741605747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7700178995153279655474329 5775134246364959741605747)
  ·
    refine ⟨8662701369547439612408621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5775134246364959741605747 8662701369547439612408621)
    ·
      refine ⟨3248513013580289854653233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8662701369547439612408621 3248513013580289854653233)
      ·
        refine ⟨2436384760185217390989925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3248513013580289854653233 2436384760185217390989925)
        ·
          refine ⟨456822142534728260810611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2436384760185217390989925 456822142534728260810611)
          ·
            refine ⟨685233213802092391215917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 456822142534728260810611 685233213802092391215917)
            ·
              refine ⟨256962455175784646705969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 685233213802092391215917 256962455175784646705969)
              ·
                refine ⟨192721841381838485029477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 256962455175784646705969 192721841381838485029477)
                ·
                  refine ⟨36135345259094715943027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 192721841381838485029477 36135345259094715943027)
                  ·
                    rfl

theorem cell22_316680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 3, 2, 4].length) (baseStart_316680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_316680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_316680 prefixEnd_316680 := by exact prefixLift 316680
  have htrace : WordTrace (prefixWord ++ tailWord_316680) baseStart_316680 baseEnd_316680 := by
    simpa [prefixWord, tailWord_316680, baseEnd_316680] using wordTrace_append hprefix tailTrace_316680
  have hstable : (prefixWord ++ tailWord_316680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316680).length < 2 ^ (prefixWord ++ tailWord_316680).sum := by decide
  have hdescent : baseEnd_316680 < baseStart_316680 := by decide
  rcases family_descends (prefixWord ++ tailWord_316680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316736 : List Nat := [2, 1, 1, 2, 2, 1, 6, 2, 5]
def baseStart_316736 : Nat := 118140960795 + 316736 * 2 ^ 59
def prefixEnd_316736 : Nat := 4983230072969 + 3 ^ 40 * 316736 * 2
def baseEnd_316736 : Nat := 36141735240572889476303

theorem tailTrace_316736 : CollatzResearch.WordTrace tailWord_316736 prefixEnd_316736 36141735240572889476303 := by
  unfold tailWord_316736
  simp only [CollatzResearch.WordTrace]
  refine ⟨5776155490263520523625031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7701540653684694031500041 5776155490263520523625031)
  ·
    refine ⟨8664233235395280785437547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5776155490263520523625031 8664233235395280785437547)
    ·
      refine ⟨12996349853092921178156321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8664233235395280785437547 12996349853092921178156321)
      ·
        refine ⟨9747262389819690883617241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12996349853092921178156321 9747262389819690883617241)
        ·
          refine ⟨7310446792364768162712931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9747262389819690883617241 7310446792364768162712931)
          ·
            refine ⟨10965670188547152244069397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7310446792364768162712931 10965670188547152244069397)
            ·
              refine ⟨514015790088147761440753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10965670188547152244069397 514015790088147761440753)
              ·
                refine ⟨385511842566110821080565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 514015790088147761440753 385511842566110821080565)
                ·
                  refine ⟨36141735240572889476303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 385511842566110821080565 36141735240572889476303)
                  ·
                    rfl

theorem cell22_316736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 2, 5].length) (baseStart_316736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_316736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_316736 prefixEnd_316736 := by exact prefixLift 316736
  have htrace : WordTrace (prefixWord ++ tailWord_316736) baseStart_316736 baseEnd_316736 := by
    simpa [prefixWord, tailWord_316736, baseEnd_316736] using wordTrace_append hprefix tailTrace_316736
  have hstable : (prefixWord ++ tailWord_316736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316736).length < 2 ^ (prefixWord ++ tailWord_316736).sum := by decide
  have hdescent : baseEnd_316736 < baseStart_316736 := by decide
  rcases family_descends (prefixWord ++ tailWord_316736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316742 : List Nat := [6, 1, 1, 3, 1, 2, 1, 7]
def baseStart_316742 : Nat := 118140960795 + 316742 * 2 ^ 59
def prefixEnd_316742 : Nat := 4983230072969 + 3 ^ 40 * 316742 * 2
def baseEnd_316742 : Nat := 12047473293815183642099

theorem tailTrace_316742 : CollatzResearch.WordTrace tailWord_316742 prefixEnd_316742 12047473293815183642099 := by
  unfold tailWord_316742
  simp only [CollatzResearch.WordTrace]
  refine ⟨361016556828290752249015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7701686545670202714645653 361016556828290752249015)
  ·
    refine ⟨541524835242436128373523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 361016556828290752249015 541524835242436128373523)
    ·
      refine ⟨812287252863654192560285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 541524835242436128373523 812287252863654192560285)
      ·
        refine ⟨304607719823870322210107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 812287252863654192560285 304607719823870322210107)
        ·
          refine ⟨456911579735805483315161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 304607719823870322210107 456911579735805483315161)
          ·
            refine ⟨342683684801854112486371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 456911579735805483315161 342683684801854112486371)
            ·
              refine ⟨514025527202781168729557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 342683684801854112486371 514025527202781168729557)
              ·
                refine ⟨12047473293815183642099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 514025527202781168729557 12047473293815183642099)
                ·
                  rfl

theorem cell22_316742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_316742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_316742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_316742 prefixEnd_316742 := by exact prefixLift 316742
  have htrace : WordTrace (prefixWord ++ tailWord_316742) baseStart_316742 baseEnd_316742 := by
    simpa [prefixWord, tailWord_316742, baseEnd_316742] using wordTrace_append hprefix tailTrace_316742
  have hstable : (prefixWord ++ tailWord_316742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316742).length < 2 ^ (prefixWord ++ tailWord_316742).sum := by decide
  have hdescent : baseEnd_316742 < baseStart_316742 := by decide
  rcases family_descends (prefixWord ++ tailWord_316742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316826 : List Nat := [3, 1, 1, 4, 1, 1, 3, 8]
def baseStart_316826 : Nat := 118140960795 + 316826 * 2 ^ 59
def prefixEnd_316826 : Nat := 4983230072969 + 3 ^ 40 * 316826 * 2
def baseEnd_316826 : Nat := 12050668284554270408737

theorem tailTrace_316826 : CollatzResearch.WordTrace tailWord_316826 prefixEnd_316826 12050668284554270408737 := by
  unfold tailWord_316826
  simp only [CollatzResearch.WordTrace]
  refine ⟨2888898387550246604506583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7703729033467324278684221 2888898387550246604506583)
  ·
    refine ⟨4333347581325369906759875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2888898387550246604506583 4333347581325369906759875)
    ·
      refine ⟨6500021371988054860139813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4333347581325369906759875 6500021371988054860139813)
      ·
        refine ⟨1218754007247760286276215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6500021371988054860139813 1218754007247760286276215)
        ·
          refine ⟨1828131010871640429414323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1218754007247760286276215 1828131010871640429414323)
          ·
            refine ⟨2742196516307460644121485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1828131010871640429414323 2742196516307460644121485)
            ·
              refine ⟨1028323693615297741545557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2742196516307460644121485 1028323693615297741545557)
              ·
                refine ⟨12050668284554270408737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1028323693615297741545557 12050668284554270408737)
                ·
                  rfl

theorem cell22_316826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 8].length) (baseStart_316826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_316826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_316826 prefixEnd_316826 := by exact prefixLift 316826
  have htrace : WordTrace (prefixWord ++ tailWord_316826) baseStart_316826 baseEnd_316826 := by
    simpa [prefixWord, tailWord_316826, baseEnd_316826] using wordTrace_append hprefix tailTrace_316826
  have hstable : (prefixWord ++ tailWord_316826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316826).length < 2 ^ (prefixWord ++ tailWord_316826).sum := by decide
  have hdescent : baseEnd_316826 < baseStart_316826 := by decide
  rcases family_descends (prefixWord ++ tailWord_316826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316845 : List Nat := [1, 5, 2, 2, 1, 2, 1, 2, 2, 4]
def baseStart_316845 : Nat := 118140960795 + 316845 * 2 ^ 59
def prefixEnd_316845 : Nat := 4983230072969 + 3 ^ 40 * 316845 * 2
def baseEnd_316845 : Nat := 108462518649278717453575

theorem tailTrace_316845 : CollatzResearch.WordTrace tailWord_316845 prefixEnd_316845 108462518649278717453575 := by
  unfold tailWord_316845
  simp only [CollatzResearch.WordTrace]
  refine ⟨11556286537132152662967989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7704191024754768441978659 11556286537132152662967989)
  ·
    refine ⟨1083401862856139312153249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11556286537132152662967989 1083401862856139312153249)
    ·
      refine ⟨812551397142104484114937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1083401862856139312153249 812551397142104484114937)
      ·
        refine ⟨609413547856578363086203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 812551397142104484114937 609413547856578363086203)
        ·
          refine ⟨914120321784867544629305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 609413547856578363086203 914120321784867544629305)
          ·
            refine ⟨685590241338650658471979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 914120321784867544629305 685590241338650658471979)
            ·
              refine ⟨1028385362007975987707969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 685590241338650658471979 1028385362007975987707969)
              ·
                refine ⟨771289021505981990780977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1028385362007975987707969 771289021505981990780977)
                ·
                  refine ⟨578466766129486493085733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 771289021505981990780977 578466766129486493085733)
                  ·
                    refine ⟨108462518649278717453575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 578466766129486493085733 108462518649278717453575)
                    ·
                      rfl

theorem cell22_316845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_316845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_316845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_316845 prefixEnd_316845 := by exact prefixLift 316845
  have htrace : WordTrace (prefixWord ++ tailWord_316845) baseStart_316845 baseEnd_316845 := by
    simpa [prefixWord, tailWord_316845, baseEnd_316845] using wordTrace_append hprefix tailTrace_316845
  have hstable : (prefixWord ++ tailWord_316845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316845).length < 2 ^ (prefixWord ++ tailWord_316845).sum := by decide
  have hdescent : baseEnd_316845 < baseStart_316845 := by decide
  rcases family_descends (prefixWord ++ tailWord_316845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316909 : List Nat := [1, 5, 1, 3, 2, 1, 1, 4, 1, 3]
def baseStart_316909 : Nat := 118140960795 + 316909 * 2 ^ 59
def prefixEnd_316909 : Nat := 4983230072969 + 3 ^ 40 * 316909 * 2
def baseEnd_316909 : Nat := 108484427157203883853379

theorem tailTrace_316909 : CollatzResearch.WordTrace tailWord_316909 prefixEnd_316909 108484427157203883853379 := by
  unfold tailWord_316909
  simp only [CollatzResearch.WordTrace]
  refine ⟨11558620808900291593297781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7705747205933527728865187 11558620808900291593297781)
  ·
    refine ⟨1083620700834402336871667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11558620808900291593297781 1083620700834402336871667)
    ·
      refine ⟨1625431051251603505307501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1083620700834402336871667 1625431051251603505307501)
      ·
        refine ⟨609536644219351314490313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1625431051251603505307501 609536644219351314490313)
        ·
          refine ⟨457152483164513485867735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 609536644219351314490313 457152483164513485867735)
          ·
            refine ⟨685728724746770228801603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 457152483164513485867735 685728724746770228801603)
            ·
              refine ⟨1028593087120155343202405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 685728724746770228801603 1028593087120155343202405)
              ·
                refine ⟨192861203835029126850451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1028593087120155343202405 192861203835029126850451)
                ·
                  refine ⟨289291805752543690275677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 192861203835029126850451 289291805752543690275677)
                  ·
                    refine ⟨108484427157203883853379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 289291805752543690275677 108484427157203883853379)
                    ·
                      rfl

theorem cell22_316909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 4, 1, 3].length) (baseStart_316909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_316909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_316909 prefixEnd_316909 := by exact prefixLift 316909
  have htrace : WordTrace (prefixWord ++ tailWord_316909) baseStart_316909 baseEnd_316909 := by
    simpa [prefixWord, tailWord_316909, baseEnd_316909] using wordTrace_append hprefix tailTrace_316909
  have hstable : (prefixWord ++ tailWord_316909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316909).length < 2 ^ (prefixWord ++ tailWord_316909).sum := by decide
  have hdescent : baseEnd_316909 < baseStart_316909 := by decide
  rcases family_descends (prefixWord ++ tailWord_316909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316993 : List Nat := [1, 2, 5, 1, 1, 1, 1, 1, 2, 7]
def baseStart_316993 : Nat := 118140960795 + 316993 * 2 ^ 59
def prefixEnd_316993 : Nat := 4983230072969 + 3 ^ 40 * 316993 * 2
def baseEnd_316993 : Nat := 108513182073855664753121

theorem tailTrace_316993 : CollatzResearch.WordTrace tailWord_316993 prefixEnd_316993 108513182073855664753121 := by
  unfold tailWord_316993
  simp only [CollatzResearch.WordTrace]
  refine ⟨11561684540595973939355633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7707789693730649292903755 11561684540595973939355633)
  ·
    refine ⟨8671263405446980454516725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11561684540595973939355633 8671263405446980454516725)
    ·
      refine ⟨812930944260654417610943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8671263405446980454516725 812930944260654417610943)
      ·
        refine ⟨1219396416390981626416415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 812930944260654417610943 1219396416390981626416415)
        ·
          refine ⟨1829094624586472439624623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1219396416390981626416415 1829094624586472439624623)
          ·
            refine ⟨2743641936879708659436935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1829094624586472439624623 2743641936879708659436935)
            ·
              refine ⟨4115462905319562989155403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2743641936879708659436935 4115462905319562989155403)
              ·
                refine ⟨6173194357979344483733105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4115462905319562989155403 6173194357979344483733105)
                ·
                  refine ⟨4629895768484508362799829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6173194357979344483733105 4629895768484508362799829)
                  ·
                    refine ⟨108513182073855664753121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4629895768484508362799829 108513182073855664753121)
                    ·
                      rfl

theorem cell22_316993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_316993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_316993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_316993 prefixEnd_316993 := by exact prefixLift 316993
  have htrace : WordTrace (prefixWord ++ tailWord_316993) baseStart_316993 baseEnd_316993 := by
    simpa [prefixWord, tailWord_316993, baseEnd_316993] using wordTrace_append hprefix tailTrace_316993
  have hstable : (prefixWord ++ tailWord_316993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316993).length < 2 ^ (prefixWord ++ tailWord_316993).sum := by decide
  have hdescent : baseEnd_316993 < baseStart_316993 := by decide
  rcases family_descends (prefixWord ++ tailWord_316993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317027 : List Nat := [1, 1, 1, 5, 1, 5, 1, 1, 3, 3]
def baseStart_317027 : Nat := 118140960795 + 317027 * 2 ^ 59
def prefixEnd_317027 : Nat := 4983230072969 + 3 ^ 40 * 317027 * 2
def baseEnd_317027 : Nat := 108524820968690909403017

theorem tailTrace_317027 : CollatzResearch.WordTrace tailWord_317027 prefixEnd_317027 108524820968690909403017 := by
  unfold tailWord_317027
  simp only [CollatzResearch.WordTrace]
  refine ⟨11562924622472797746093335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7708616414981865164062223 11562924622472797746093335)
  ·
    refine ⟨17344386933709196619140003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11562924622472797746093335 17344386933709196619140003)
    ·
      refine ⟨26016580400563794928710005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17344386933709196619140003 26016580400563794928710005)
      ·
        refine ⟨2439054412552855774566563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26016580400563794928710005 2439054412552855774566563)
        ·
          refine ⟨3658581618829283661849845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2439054412552855774566563 3658581618829283661849845)
          ·
            refine ⟨342992026765245343298423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3658581618829283661849845 342992026765245343298423)
            ·
              refine ⟨514488040147868014947635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 342992026765245343298423 514488040147868014947635)
              ·
                refine ⟨771732060221802022421453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 514488040147868014947635 771732060221802022421453)
                ·
                  refine ⟨289399522583175758408045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 771732060221802022421453 289399522583175758408045)
                  ·
                    refine ⟨108524820968690909403017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 289399522583175758408045 108524820968690909403017)
                    ·
                      rfl

theorem cell22_317027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 1, 3, 3].length) (baseStart_317027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_317027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_317027 prefixEnd_317027 := by exact prefixLift 317027
  have htrace : WordTrace (prefixWord ++ tailWord_317027) baseStart_317027 baseEnd_317027 := by
    simpa [prefixWord, tailWord_317027, baseEnd_317027] using wordTrace_append hprefix tailTrace_317027
  have hstable : (prefixWord ++ tailWord_317027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317027).length < 2 ^ (prefixWord ++ tailWord_317027).sum := by decide
  have hdescent : baseEnd_317027 < baseStart_317027 := by decide
  rcases family_descends (prefixWord ++ tailWord_317027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317040 : List Nat := [2, 1, 1, 1, 6, 2, 1, 3, 5]
def baseStart_317040 : Nat := 118140960795 + 317040 * 2 ^ 59
def prefixEnd_317040 : Nat := 4983230072969 + 3 ^ 40 * 317040 * 2
def baseEnd_317040 : Nat := 36176423711454402942659

theorem tailTrace_317040 : CollatzResearch.WordTrace tailWord_317040 prefixEnd_317040 36176423711454402942659 := by
  unfold tailWord_317040
  simp only [CollatzResearch.WordTrace]
  refine ⟨5781699385712850483158287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7708932514283800644211049 5781699385712850483158287)
  ·
    refine ⟨8672549078569275724737431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5781699385712850483158287 8672549078569275724737431)
    ·
      refine ⟨13008823617853913587106147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8672549078569275724737431 13008823617853913587106147)
      ·
        refine ⟨19513235426780870380659221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13008823617853913587106147 19513235426780870380659221)
        ·
          refine ⟨914682910630353299093401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 19513235426780870380659221 914682910630353299093401)
          ·
            refine ⟨686012182972764974320051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 914682910630353299093401 686012182972764974320051)
            ·
              refine ⟨1029018274459147461480077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 686012182972764974320051 1029018274459147461480077)
              ·
                refine ⟨385881852922180298055029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1029018274459147461480077 385881852922180298055029)
                ·
                  refine ⟨36176423711454402942659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 385881852922180298055029 36176423711454402942659)
                  ·
                    rfl

theorem cell22_317040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 3, 5].length) (baseStart_317040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_317040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_317040 prefixEnd_317040 := by exact prefixLift 317040
  have htrace : WordTrace (prefixWord ++ tailWord_317040) baseStart_317040 baseEnd_317040 := by
    simpa [prefixWord, tailWord_317040, baseEnd_317040] using wordTrace_append hprefix tailTrace_317040
  have hstable : (prefixWord ++ tailWord_317040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317040).length < 2 ^ (prefixWord ++ tailWord_317040).sum := by decide
  have hdescent : baseEnd_317040 < baseStart_317040 := by decide
  rcases family_descends (prefixWord ++ tailWord_317040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317113 : List Nat := [1, 2, 1, 4, 1, 1, 2, 10]
def baseStart_317113 : Nat := 118140960795 + 317113 * 2 ^ 59
def prefixEnd_317113 : Nat := 4983230072969 + 3 ^ 40 * 317113 * 2
def baseEnd_317113 : Nat := 12061584502912816861417

theorem tailTrace_317113 : CollatzResearch.WordTrace tailWord_317113 prefixEnd_317113 12061584502912816861417 := by
  unfold tailWord_317113
  simp only [CollatzResearch.WordTrace]
  refine ⟨11566061300161234433723993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7710707533440822955815995 11566061300161234433723993)
  ·
    refine ⟨8674545975120925825292995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11566061300161234433723993 8674545975120925825292995)
    ·
      refine ⟨13011818962681388737939493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8674545975120925825292995 13011818962681388737939493)
      ·
        refine ⟨2439716055502760388363655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13011818962681388737939493 2439716055502760388363655)
        ·
          refine ⟨3659574083254140582545483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2439716055502760388363655 3659574083254140582545483)
          ·
            refine ⟨5489361124881210873818225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3659574083254140582545483 5489361124881210873818225)
            ·
              refine ⟨4117020843660908155363669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5489361124881210873818225 4117020843660908155363669)
              ·
                refine ⟨12061584502912816861417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 4117020843660908155363669 12061584502912816861417)
                ·
                  rfl

theorem cell22_317113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 10].length) (baseStart_317113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_317113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_317113 prefixEnd_317113 := by exact prefixLift 317113
  have htrace : WordTrace (prefixWord ++ tailWord_317113) baseStart_317113 baseEnd_317113 := by
    simpa [prefixWord, tailWord_317113, baseEnd_317113] using wordTrace_append hprefix tailTrace_317113
  have hstable : (prefixWord ++ tailWord_317113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317113).length < 2 ^ (prefixWord ++ tailWord_317113).sum := by decide
  have hdescent : baseEnd_317113 < baseStart_317113 := by decide
  rcases family_descends (prefixWord ++ tailWord_317113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317130 : List Nat := [3, 1, 2, 1, 5, 1, 9]
def baseStart_317130 : Nat := 118140960795 + 317130 * 2 ^ 59
def prefixEnd_317130 : Nat := 4983230072969 + 3 ^ 40 * 317130 * 2
def baseEnd_317130 : Nat := 4020743702727147188063

theorem tailTrace_317130 : CollatzResearch.WordTrace tailWord_317130 prefixEnd_317130 4020743702727147188063 := by
  unfold tailWord_317130
  simp only [CollatzResearch.WordTrace]
  refine ⟨2891670335274911584273211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7711120894066430891395229 2891670335274911584273211)
  ·
    refine ⟨4337505502912367376409817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2891670335274911584273211 4337505502912367376409817)
    ·
      refine ⟨3253129127184275532307363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4337505502912367376409817 3253129127184275532307363)
      ·
        refine ⟨4879693690776413298461045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3253129127184275532307363 4879693690776413298461045)
        ·
          refine ⟨457471283510288746730723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4879693690776413298461045 457471283510288746730723)
          ·
            refine ⟨686206925265433120096085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 457471283510288746730723 686206925265433120096085)
            ·
              refine ⟨4020743702727147188063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 686206925265433120096085 4020743702727147188063)
              ·
                rfl

theorem cell22_317130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 9].length) (baseStart_317130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_317130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_317130 prefixEnd_317130 := by exact prefixLift 317130
  have htrace : WordTrace (prefixWord ++ tailWord_317130) baseStart_317130 baseEnd_317130 := by
    simpa [prefixWord, tailWord_317130, baseEnd_317130] using wordTrace_append hprefix tailTrace_317130
  have hstable : (prefixWord ++ tailWord_317130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317130).length < 2 ^ (prefixWord ++ tailWord_317130).sum := by decide
  have hdescent : baseEnd_317130 < baseStart_317130 := by decide
  rcases family_descends (prefixWord ++ tailWord_317130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317162 : List Nat := [3, 1, 3, 1, 1, 1, 4, 2, 3, 3]
def baseStart_317162 : Nat := 118140960795 + 317162 * 2 ^ 59
def prefixEnd_317162 : Nat := 4983230072969 + 3 ^ 40 * 317162 * 2
def baseEnd_317162 : Nat := 108571034227595557277603

theorem tailTrace_317162 : CollatzResearch.WordTrace tailWord_317162 prefixEnd_317162 108571034227595557277603 := by
  unfold tailWord_317162
  simp only [CollatzResearch.WordTrace]
  refine ⟨2891962119245928950564435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7711898984655810534838493 2891962119245928950564435)
  ·
    refine ⟨4337943178868893425846653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2891962119245928950564435 4337943178868893425846653)
    ·
      refine ⟨1626728692075835034692495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4337943178868893425846653 1626728692075835034692495)
      ·
        refine ⟨2440093038113752552038743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1626728692075835034692495 2440093038113752552038743)
        ·
          refine ⟨3660139557170628828058115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2440093038113752552038743 3660139557170628828058115)
          ·
            refine ⟨5490209335755943242087173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3660139557170628828058115 5490209335755943242087173)
            ·
              refine ⟨1029414250454239357891345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5490209335755943242087173 1029414250454239357891345)
              ·
                refine ⟨772060687840679518418509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1029414250454239357891345 772060687840679518418509)
                ·
                  refine ⟨289522757940254819406941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 772060687840679518418509 289522757940254819406941)
                  ·
                    refine ⟨108571034227595557277603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 289522757940254819406941 108571034227595557277603)
                    ·
                      rfl

theorem cell22_317162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 2, 3, 3].length) (baseStart_317162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_317162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_317162 prefixEnd_317162 := by exact prefixLift 317162
  have htrace : WordTrace (prefixWord ++ tailWord_317162) baseStart_317162 baseEnd_317162 := by
    simpa [prefixWord, tailWord_317162, baseEnd_317162] using wordTrace_append hprefix tailTrace_317162
  have hstable : (prefixWord ++ tailWord_317162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317162).length < 2 ^ (prefixWord ++ tailWord_317162).sum := by decide
  have hdescent : baseEnd_317162 < baseStart_317162 := by decide
  rcases family_descends (prefixWord ++ tailWord_317162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317269 : List Nat := [1, 3, 2, 2, 2, 2, 2, 3, 2, 3]
def baseStart_317269 : Nat := 118140960795 + 317269 * 2 ^ 59
def prefixEnd_317269 : Nat := 4983230072969 + 3 ^ 40 * 317269 * 2
def baseEnd_317269 : Nat := 108607662514282944852275

theorem tailTrace_317269 : CollatzResearch.WordTrace tailWord_317269 prefixEnd_317269 108607662514282944852275 := by
  unfold tailWord_317269
  simp only [CollatzResearch.WordTrace]
  refine ⟨11571751087596073076402861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7714500725064048717601907 11571751087596073076402861)
  ·
    refine ⟨4339406657848527403651073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11571751087596073076402861 4339406657848527403651073)
    ·
      refine ⟨3254554993386395552738305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4339406657848527403651073 3254554993386395552738305)
      ·
        refine ⟨2440916245039796664553729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3254554993386395552738305 2440916245039796664553729)
        ·
          refine ⟨1830687183779847498415297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2440916245039796664553729 1830687183779847498415297)
          ·
            refine ⟨1373015387834885623811473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1830687183779847498415297 1373015387834885623811473)
            ·
              refine ⟨1029761540876164217858605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1373015387834885623811473 1029761540876164217858605)
              ·
                refine ⟨386160577828561581696977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1029761540876164217858605 386160577828561581696977)
                ·
                  refine ⟨289620433371421186272733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 386160577828561581696977 289620433371421186272733)
                  ·
                    refine ⟨108607662514282944852275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 289620433371421186272733 108607662514282944852275)
                    ·
                      rfl

theorem cell22_317269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 3, 2, 3].length) (baseStart_317269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_317269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_317269 prefixEnd_317269 := by exact prefixLift 317269
  have htrace : WordTrace (prefixWord ++ tailWord_317269) baseStart_317269 baseEnd_317269 := by
    simpa [prefixWord, tailWord_317269, baseEnd_317269] using wordTrace_append hprefix tailTrace_317269
  have hstable : (prefixWord ++ tailWord_317269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317269).length < 2 ^ (prefixWord ++ tailWord_317269).sum := by decide
  have hdescent : baseEnd_317269 < baseStart_317269 := by decide
  rcases family_descends (prefixWord ++ tailWord_317269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317290 : List Nat := [3, 1, 3, 4, 2, 1, 2, 1, 1, 4]
def baseStart_317290 : Nat := 118140960795 + 317290 * 2 ^ 59
def prefixEnd_317290 : Nat := 4983230072969 + 3 ^ 40 * 317290 * 2
def baseEnd_317290 : Nat := 108614851243445890077211

theorem tailTrace_317290 : CollatzResearch.WordTrace tailWord_317290 prefixEnd_317290 108614851243445890077211 := by
  unfold tailWord_317290
  simp only [CollatzResearch.WordTrace]
  refine ⟨2893129255129998415729331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7715011347013329108611549 2893129255129998415729331)
  ·
    refine ⟨4339693882694997623593997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2893129255129998415729331 4339693882694997623593997)
    ·
      refine ⟨1627385206010624108847749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4339693882694997623593997 1627385206010624108847749)
      ·
        refine ⟨305134726126992020408953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1627385206010624108847749 305134726126992020408953)
        ·
          refine ⟨228851044595244015306715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 305134726126992020408953 228851044595244015306715)
          ·
            refine ⟨343276566892866022960073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228851044595244015306715 343276566892866022960073)
            ·
              refine ⟨257457425169649517220055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 343276566892866022960073 257457425169649517220055)
              ·
                refine ⟨386186137754474275830083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 257457425169649517220055 386186137754474275830083)
                ·
                  refine ⟨579279206631711413745125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 386186137754474275830083 579279206631711413745125)
                  ·
                    refine ⟨108614851243445890077211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 579279206631711413745125 108614851243445890077211)
                    ·
                      rfl

theorem cell22_317290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 2, 1, 1, 4].length) (baseStart_317290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_317290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_317290 prefixEnd_317290 := by exact prefixLift 317290
  have htrace : WordTrace (prefixWord ++ tailWord_317290) baseStart_317290 baseEnd_317290 := by
    simpa [prefixWord, tailWord_317290, baseEnd_317290] using wordTrace_append hprefix tailTrace_317290
  have hstable : (prefixWord ++ tailWord_317290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317290).length < 2 ^ (prefixWord ++ tailWord_317290).sum := by decide
  have hdescent : baseEnd_317290 < baseStart_317290 := by decide
  rcases family_descends (prefixWord ++ tailWord_317290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317297 : List Nat := [1, 2, 2, 2, 1, 3, 1, 2, 5, 3]
def baseStart_317297 : Nat := 118140960795 + 317297 * 2 ^ 59
def prefixEnd_317297 : Nat := 4983230072969 + 3 ^ 40 * 317297 * 2
def baseEnd_317297 : Nat := 108617247486500205152189

theorem tailTrace_317297 : CollatzResearch.WordTrace tailWord_317297 prefixEnd_317297 108617247486500205152189 := by
  unfold tailWord_317297
  simp only [CollatzResearch.WordTrace]
  refine ⟨11572772331494633858422145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7715181554329755905614763 11572772331494633858422145)
  ·
    refine ⟨8679579248620975393816609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11572772331494633858422145 8679579248620975393816609)
    ·
      refine ⟨6509684436465731545362457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8679579248620975393816609 6509684436465731545362457)
      ·
        refine ⟨4882263327349298659021843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6509684436465731545362457 4882263327349298659021843)
        ·
          refine ⟨7323394991023947988532765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4882263327349298659021843 7323394991023947988532765)
          ·
            refine ⟨2746273121633980495699787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7323394991023947988532765 2746273121633980495699787)
            ·
              refine ⟨4119409682450970743549681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2746273121633980495699787 4119409682450970743549681)
              ·
                refine ⟨3089557261838228057662261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4119409682450970743549681 3089557261838228057662261)
                ·
                  refine ⟨289645993297333880405837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3089557261838228057662261 289645993297333880405837)
                  ·
                    refine ⟨108617247486500205152189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 289645993297333880405837 108617247486500205152189)
                    ·
                      rfl

theorem cell22_317297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 5, 3].length) (baseStart_317297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_317297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_317297 prefixEnd_317297 := by exact prefixLift 317297
  have htrace : WordTrace (prefixWord ++ tailWord_317297) baseStart_317297 baseEnd_317297 := by
    simpa [prefixWord, tailWord_317297, baseEnd_317297] using wordTrace_append hprefix tailTrace_317297
  have hstable : (prefixWord ++ tailWord_317297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317297).length < 2 ^ (prefixWord ++ tailWord_317297).sum := by decide
  have hdescent : baseEnd_317297 < baseStart_317297 := by decide
  rcases family_descends (prefixWord ++ tailWord_317297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317348 : List Nat := [2, 3, 1, 2, 1, 5, 1, 3, 1, 3]
def baseStart_317348 : Nat := 118140960795 + 317348 * 2 ^ 59
def prefixEnd_317348 : Nat := 4983230072969 + 3 ^ 40 * 317348 * 2
def baseEnd_317348 : Nat := 108634705828753072127033

theorem tailTrace_317348 : CollatzResearch.WordTrace tailWord_317348 prefixEnd_317348 108634705828753072127033 := by
  unfold tailWord_317348
  simp only [CollatzResearch.WordTrace]
  refine ⟨5787316227154934784264349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7716421636206579712352465 5787316227154934784264349)
  ·
    refine ⟨2170243585183100544099131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5787316227154934784264349 2170243585183100544099131)
    ·
      refine ⟨3255365377774650816148697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2170243585183100544099131 3255365377774650816148697)
      ·
        refine ⟨2441524033330988112111523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3255365377774650816148697 2441524033330988112111523)
        ·
          refine ⟨3662286049996482168167285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2441524033330988112111523 3662286049996482168167285)
          ·
            refine ⟨343339317187170203265683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3662286049996482168167285 343339317187170203265683)
            ·
              refine ⟨515008975780755304898525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 343339317187170203265683 515008975780755304898525)
              ·
                refine ⟨193128365917783239336947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 515008975780755304898525 193128365917783239336947)
                ·
                  refine ⟨289692548876674859005421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 193128365917783239336947 289692548876674859005421)
                  ·
                    refine ⟨108634705828753072127033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 289692548876674859005421 108634705828753072127033)
                    ·
                      rfl

theorem cell22_317348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 3, 1, 3].length) (baseStart_317348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_317348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_317348 prefixEnd_317348 := by exact prefixLift 317348
  have htrace : WordTrace (prefixWord ++ tailWord_317348) baseStart_317348 baseEnd_317348 := by
    simpa [prefixWord, tailWord_317348, baseEnd_317348] using wordTrace_append hprefix tailTrace_317348
  have hstable : (prefixWord ++ tailWord_317348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317348).length < 2 ^ (prefixWord ++ tailWord_317348).sum := by decide
  have hdescent : baseEnd_317348 < baseStart_317348 := by decide
  rcases family_descends (prefixWord ++ tailWord_317348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317387 : List Nat := [1, 1, 1, 1, 3, 4, 2, 3, 1, 5]
def baseStart_317387 : Nat := 118140960795 + 317387 * 2 ^ 59
def prefixEnd_317387 : Nat := 4983230072969 + 3 ^ 40 * 317387 * 2
def baseEnd_317387 : Nat := 108648056325769970401913

theorem tailTrace_317387 : CollatzResearch.WordTrace tailWord_317387 prefixEnd_317387 108648056325769970401913 := by
  unfold tailWord_317387
  simp only [CollatzResearch.WordTrace]
  refine ⟨11576054901168579229198415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7717369934112386152798943 11576054901168579229198415)
  ·
    refine ⟨17364082351752868843797623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11576054901168579229198415 17364082351752868843797623)
    ·
      refine ⟨26046123527629303265696435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17364082351752868843797623 26046123527629303265696435)
      ·
        refine ⟨39069185291443954898544653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26046123527629303265696435 39069185291443954898544653)
        ·
          refine ⟨14650944484291483086954245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39069185291443954898544653 14650944484291483086954245)
          ·
            refine ⟨2747052090804653078803921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14650944484291483086954245 2747052090804653078803921)
            ·
              refine ⟨2060289068103489809102941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2747052090804653078803921 2060289068103489809102941)
              ·
                refine ⟨772608400538808678413603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2060289068103489809102941 772608400538808678413603)
                ·
                  refine ⟨1158912600808213017620405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 772608400538808678413603 1158912600808213017620405)
                  ·
                    refine ⟨108648056325769970401913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1158912600808213017620405 108648056325769970401913)
                    ·
                      rfl

theorem cell22_317387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 3, 1, 5].length) (baseStart_317387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_317387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_317387 prefixEnd_317387 := by exact prefixLift 317387
  have htrace : WordTrace (prefixWord ++ tailWord_317387) baseStart_317387 baseEnd_317387 := by
    simpa [prefixWord, tailWord_317387, baseEnd_317387] using wordTrace_append hprefix tailTrace_317387
  have hstable : (prefixWord ++ tailWord_317387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317387).length < 2 ^ (prefixWord ++ tailWord_317387).sum := by decide
  have hdescent : baseEnd_317387 < baseStart_317387 := by decide
  rcases family_descends (prefixWord ++ tailWord_317387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317438 : List Nat := [4, 2, 2, 2, 1, 1, 2, 3, 2, 3]
def baseStart_317438 : Nat := 118140960795 + 317438 * 2 ^ 59
def prefixEnd_317438 : Nat := 4983230072969 + 3 ^ 40 * 317438 * 2
def baseEnd_317438 : Nat := 108665514668022837376757

theorem tailTrace_317438 : CollatzResearch.WordTrace tailWord_317438 prefixEnd_317438 108665514668022837376757 := by
  unfold tailWord_317438
  simp only [CollatzResearch.WordTrace]
  refine ⟨1447239377997976867413121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7718610015989209959536645 1447239377997976867413121)
  ·
    refine ⟨1085429533498482650559841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1447239377997976867413121 1085429533498482650559841)
    ·
      refine ⟨814072150123861987919881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1085429533498482650559841 814072150123861987919881)
      ·
        refine ⟨610554112592896490939911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 814072150123861987919881 610554112592896490939911)
        ·
          refine ⟨915831168889344736409867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 610554112592896490939911 915831168889344736409867)
          ·
            refine ⟨1373746753334017104614801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 915831168889344736409867 1373746753334017104614801)
            ·
              refine ⟨1030310065000512828461101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1373746753334017104614801 1030310065000512828461101)
              ·
                refine ⟨386366274375192310672913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1030310065000512828461101 386366274375192310672913)
                ·
                  refine ⟨289774705781394233004685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 386366274375192310672913 289774705781394233004685)
                  ·
                    refine ⟨108665514668022837376757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 289774705781394233004685 108665514668022837376757)
                    ·
                      rfl

theorem cell22_317438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_317438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_317438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_317438 prefixEnd_317438 := by exact prefixLift 317438
  have htrace : WordTrace (prefixWord ++ tailWord_317438) baseStart_317438 baseEnd_317438 := by
    simpa [prefixWord, tailWord_317438, baseEnd_317438] using wordTrace_append hprefix tailTrace_317438
  have hstable : (prefixWord ++ tailWord_317438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317438).length < 2 ^ (prefixWord ++ tailWord_317438).sum := by decide
  have hdescent : baseEnd_317438 < baseStart_317438 := by decide
  rcases family_descends (prefixWord ++ tailWord_317438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317507 : List Nat := [1, 1, 1, 3, 1, 2, 2, 3, 8]
def baseStart_317507 : Nat := 118140960795 + 317507 * 2 ^ 59
def prefixEnd_317507 : Nat := 4983230072969 + 3 ^ 40 * 317507 * 2
def baseEnd_317507 : Nat := 36229711592709885800515

theorem tailTrace_317507 : CollatzResearch.WordTrace tailWord_317507 prefixEnd_317507 36229711592709885800515 := by
  unfold tailWord_317507
  simp only [CollatzResearch.WordTrace]
  refine ⟨11580431660733839723566775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7720287773822559815711183 11580431660733839723566775)
  ·
    refine ⟨17370647491100759585350163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11580431660733839723566775 17370647491100759585350163)
    ·
      refine ⟨26055971236651139378025245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17370647491100759585350163 26055971236651139378025245)
      ·
        refine ⟨9770989213744177266759467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26055971236651139378025245 9770989213744177266759467)
        ·
          refine ⟨14656483820616265900139201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9770989213744177266759467 14656483820616265900139201)
          ·
            refine ⟨10992362865462199425104401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14656483820616265900139201 10992362865462199425104401)
            ·
              refine ⟨8244272149096649568828301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10992362865462199425104401 8244272149096649568828301)
              ·
                refine ⟨3091602055911243588310613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8244272149096649568828301 3091602055911243588310613)
                ·
                  refine ⟨36229711592709885800515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3091602055911243588310613 36229711592709885800515)
                  ·
                    rfl

theorem cell22_317507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 8].length) (baseStart_317507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_317507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_317507 prefixEnd_317507 := by exact prefixLift 317507
  have htrace : WordTrace (prefixWord ++ tailWord_317507) baseStart_317507 baseEnd_317507 := by
    simpa [prefixWord, tailWord_317507, baseEnd_317507] using wordTrace_append hprefix tailTrace_317507
  have hstable : (prefixWord ++ tailWord_317507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317507).length < 2 ^ (prefixWord ++ tailWord_317507).sum := by decide
  have hdescent : baseEnd_317507 < baseStart_317507 := by decide
  rcases family_descends (prefixWord ++ tailWord_317507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317534 : List Nat := [4, 4, 1, 1, 3, 1, 1, 1, 3, 3]
def baseStart_317534 : Nat := 118140960795 + 317534 * 2 ^ 59
def prefixEnd_317534 : Nat := 4983230072969 + 3 ^ 40 * 317534 * 2
def baseEnd_317534 : Nat := 108698377429910586976463

theorem tailTrace_317534 : CollatzResearch.WordTrace tailWord_317534 prefixEnd_317534 108698377429910586976463 := by
  unfold tailWord_317534
  simp only [CollatzResearch.WordTrace]
  refine ⟨1447677053954502916849957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7720944287757348889866437 1447677053954502916849957)
  ·
    refine ⟨271439447616469296909367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1447677053954502916849957 271439447616469296909367)
    ·
      refine ⟨407159171424703945364051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271439447616469296909367 407159171424703945364051)
      ·
        refine ⟨610738757137055918046077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 407159171424703945364051 610738757137055918046077)
        ·
          refine ⟨229027033926395969267279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 610738757137055918046077 229027033926395969267279)
          ·
            refine ⟨343540550889593953900919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229027033926395969267279 343540550889593953900919)
            ·
              refine ⟨515310826334390930851379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 343540550889593953900919 515310826334390930851379)
              ·
                refine ⟨772966239501586396277069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 515310826334390930851379 772966239501586396277069)
                ·
                  refine ⟨289862339813094898603901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 772966239501586396277069 289862339813094898603901)
                  ·
                    refine ⟨108698377429910586976463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 289862339813094898603901 108698377429910586976463)
                    ·
                      rfl

theorem cell22_317534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_317534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_317534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_317534 prefixEnd_317534 := by exact prefixLift 317534
  have htrace : WordTrace (prefixWord ++ tailWord_317534) baseStart_317534 baseEnd_317534 := by
    simpa [prefixWord, tailWord_317534, baseEnd_317534] using wordTrace_append hprefix tailTrace_317534
  have hstable : (prefixWord ++ tailWord_317534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317534).length < 2 ^ (prefixWord ++ tailWord_317534).sum := by decide
  have hdescent : baseEnd_317534 < baseStart_317534 := by decide
  rcases family_descends (prefixWord ++ tailWord_317534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317541 : List Nat := [1, 3, 1, 3, 2, 4, 1, 1, 6]
def baseStart_317541 : Nat := 118140960795 + 317541 * 2 ^ 59
def prefixEnd_317541 : Nat := 4983230072969 + 3 ^ 40 * 317541 * 2
def baseEnd_317541 : Nat := 36233591224321634017147

theorem tailTrace_317541 : CollatzResearch.WordTrace tailWord_317541 prefixEnd_317541 36233591224321634017147 := by
  unfold tailWord_317541
  simp only [CollatzResearch.WordTrace]
  refine ⟨11581671742610663530304477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7721114495073775686869651 11581671742610663530304477)
  ·
    refine ⟨4343126903478998823864179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11581671742610663530304477 4343126903478998823864179)
    ·
      refine ⟨6514690355218498235796269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4343126903478998823864179 6514690355218498235796269)
      ·
        refine ⟨2443008883206936838423601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6514690355218498235796269 2443008883206936838423601)
        ·
          refine ⟨1832256662405202628817701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2443008883206936838423601 1832256662405202628817701)
          ·
            refine ⟨343548124200975492903319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1832256662405202628817701 343548124200975492903319)
            ·
              refine ⟨515322186301463239354979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 343548124200975492903319 515322186301463239354979)
              ·
                refine ⟨772983279452194859032469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 515322186301463239354979 772983279452194859032469)
                ·
                  refine ⟨36233591224321634017147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 772983279452194859032469 36233591224321634017147)
                  ·
                    rfl

theorem cell22_317541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 1, 6].length) (baseStart_317541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_317541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_317541 prefixEnd_317541 := by exact prefixLift 317541
  have htrace : WordTrace (prefixWord ++ tailWord_317541) baseStart_317541 baseEnd_317541 := by
    simpa [prefixWord, tailWord_317541, baseEnd_317541] using wordTrace_append hprefix tailTrace_317541
  have hstable : (prefixWord ++ tailWord_317541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317541).length < 2 ^ (prefixWord ++ tailWord_317541).sum := by decide
  have hdescent : baseEnd_317541 < baseStart_317541 := by decide
  rcases family_descends (prefixWord ++ tailWord_317541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317571 : List Nat := [1, 1, 1, 3, 3, 4, 2, 1, 2, 4]
def baseStart_317571 : Nat := 118140960795 + 317571 * 2 ^ 59
def prefixEnd_317571 : Nat := 4983230072969 + 3 ^ 40 * 317571 * 2
def baseEnd_317571 : Nat := 108711043286054823801349

theorem tailTrace_317571 : CollatzResearch.WordTrace tailWord_317571 prefixEnd_317571 108711043286054823801349 := by
  unfold tailWord_317571
  simp only [CollatzResearch.WordTrace]
  refine ⟨11582765932501978653896567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7721843955001319102597711 11582765932501978653896567)
  ·
    refine ⟨17374148898752967980844851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11582765932501978653896567 17374148898752967980844851)
    ·
      refine ⟨26061223348129451971267277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17374148898752967980844851 26061223348129451971267277)
      ·
        refine ⟨9772958755548544489225229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26061223348129451971267277 9772958755548544489225229)
        ·
          refine ⟨3664859533330704183459461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9772958755548544489225229 3664859533330704183459461)
          ·
            refine ⟨687161162499507034398649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3664859533330704183459461 687161162499507034398649)
            ·
              refine ⟨515370871874630275798987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 687161162499507034398649 515370871874630275798987)
              ·
                refine ⟨773056307811945413698481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 515370871874630275798987 773056307811945413698481)
                ·
                  refine ⟨579792230858959060273861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 773056307811945413698481 579792230858959060273861)
                  ·
                    refine ⟨108711043286054823801349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 579792230858959060273861 108711043286054823801349)
                    ·
                      rfl

theorem cell22_317571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 1, 2, 4].length) (baseStart_317571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_317571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_317571 prefixEnd_317571 := by exact prefixLift 317571
  have htrace : WordTrace (prefixWord ++ tailWord_317571) baseStart_317571 baseEnd_317571 := by
    simpa [prefixWord, tailWord_317571, baseEnd_317571] using wordTrace_append hprefix tailTrace_317571
  have hstable : (prefixWord ++ tailWord_317571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317571).length < 2 ^ (prefixWord ++ tailWord_317571).sum := by decide
  have hdescent : baseEnd_317571 < baseStart_317571 := by decide
  rcases family_descends (prefixWord ++ tailWord_317571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317592 : List Nat := [2, 1, 2, 4, 4, 1, 2, 2, 4]
def baseStart_317592 : Nat := 118140960795 + 317592 * 2 ^ 59
def prefixEnd_317592 : Nat := 4983230072969 + 3 ^ 40 * 317592 * 2
def baseEnd_317592 : Nat := 36239410671739256342095

theorem tailTrace_317592 : CollatzResearch.WordTrace tailWord_317592 prefixEnd_317592 36239410671739256342095 := by
  unfold tailWord_317592
  simp only [CollatzResearch.WordTrace]
  refine ⟨5791765932712949620205515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7722354576950599493607353 5791765932712949620205515)
  ·
    refine ⟨8687648899069424430308273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5791765932712949620205515 8687648899069424430308273)
    ·
      refine ⟨6515736674302068322731205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8687648899069424430308273 6515736674302068322731205)
      ·
        refine ⟨1221700626431637810512101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6515736674302068322731205 1221700626431637810512101)
        ·
          refine ⟨229068867455932089471019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1221700626431637810512101 229068867455932089471019)
          ·
            refine ⟨343603301183898134206529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229068867455932089471019 343603301183898134206529)
            ·
              refine ⟨257702475887923600654897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 343603301183898134206529 257702475887923600654897)
              ·
                refine ⟨193276856915942700491173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 257702475887923600654897 193276856915942700491173)
                ·
                  refine ⟨36239410671739256342095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 193276856915942700491173 36239410671739256342095)
                  ·
                    rfl

theorem cell22_317592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 2, 2, 4].length) (baseStart_317592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_317592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_317592 prefixEnd_317592 := by exact prefixLift 317592
  have htrace : WordTrace (prefixWord ++ tailWord_317592) baseStart_317592 baseEnd_317592 := by
    simpa [prefixWord, tailWord_317592, baseEnd_317592] using wordTrace_append hprefix tailTrace_317592
  have hstable : (prefixWord ++ tailWord_317592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317592).length < 2 ^ (prefixWord ++ tailWord_317592).sum := by decide
  have hdescent : baseEnd_317592 < baseStart_317592 := by decide
  rcases family_descends (prefixWord ++ tailWord_317592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317629 : List Nat := [1, 4, 1, 2, 1, 1, 1, 1, 3, 7]
def baseStart_317629 : Nat := 118140960795 + 317629 * 2 ^ 59
def prefixEnd_317629 : Nat := 4983230072969 + 3 ^ 40 * 317629 * 2
def baseEnd_317629 : Nat := 108730897871362005851171

theorem tailTrace_317629 : CollatzResearch.WordTrace tailWord_317629 prefixEnd_317629 108730897871362005851171 := by
  unfold tailWord_317629
  simp only [CollatzResearch.WordTrace]
  refine ⟨11584881366291854559507941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7723254244194569706338627 11584881366291854559507941)
  ·
    refine ⟨2172165256179722729907739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11584881366291854559507941 2172165256179722729907739)
    ·
      refine ⟨3258247884269584094861609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2172165256179722729907739 3258247884269584094861609)
      ·
        refine ⟨2443685913202188071146207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3258247884269584094861609 2443685913202188071146207)
        ·
          refine ⟨3665528869803282106719311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2443685913202188071146207 3665528869803282106719311)
          ·
            refine ⟨5498293304704923160078967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3665528869803282106719311 5498293304704923160078967)
            ·
              refine ⟨8247439957057384740118451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5498293304704923160078967 8247439957057384740118451)
              ·
                refine ⟨12371159935586077110177677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8247439957057384740118451 12371159935586077110177677)
                ·
                  refine ⟨4639184975844778916316629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12371159935586077110177677 4639184975844778916316629)
                  ·
                    refine ⟨108730897871362005851171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4639184975844778916316629 108730897871362005851171)
                    ·
                      rfl

theorem cell22_317629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_317629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_317629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_317629 prefixEnd_317629 := by exact prefixLift 317629
  have htrace : WordTrace (prefixWord ++ tailWord_317629) baseStart_317629 baseEnd_317629 := by
    simpa [prefixWord, tailWord_317629, baseEnd_317629] using wordTrace_append hprefix tailTrace_317629
  have hstable : (prefixWord ++ tailWord_317629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317629).length < 2 ^ (prefixWord ++ tailWord_317629).sum := by decide
  have hdescent : baseEnd_317629 < baseStart_317629 := by decide
  rcases family_descends (prefixWord ++ tailWord_317629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317646 : List Nat := [4, 1, 1, 1, 4, 1, 1, 2, 2, 5]
def baseStart_317646 : Nat := 118140960795 + 317646 * 2 ^ 59
def prefixEnd_317646 : Nat := 4983230072969 + 3 ^ 40 * 317646 * 2
def baseEnd_317646 : Nat := 108736717318779628176119

theorem tailTrace_317646 : CollatzResearch.WordTrace tailWord_317646 prefixEnd_317646 108736717318779628176119 := by
  unfold tailWord_317646
  simp only [CollatzResearch.WordTrace]
  refine ⟨1448187675903783307859599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7723667604820177641917861 1448187675903783307859599)
  ·
    refine ⟨2172281513855674961789399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1448187675903783307859599 2172281513855674961789399)
    ·
      refine ⟨3258422270783512442684099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2172281513855674961789399 3258422270783512442684099)
      ·
        refine ⟨4887633406175268664026149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3258422270783512442684099 4887633406175268664026149)
        ·
          refine ⟨916431263657862874504903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4887633406175268664026149 916431263657862874504903)
          ·
            refine ⟨1374646895486794311757355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 916431263657862874504903 1374646895486794311757355)
            ·
              refine ⟨2061970343230191467636033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1374646895486794311757355 2061970343230191467636033)
              ·
                refine ⟨1546477757422643600727025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2061970343230191467636033 1546477757422643600727025)
                ·
                  refine ⟨1159858318066982700545269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1546477757422643600727025 1159858318066982700545269)
                  ·
                    refine ⟨108736717318779628176119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1159858318066982700545269 108736717318779628176119)
                    ·
                      rfl

theorem cell22_317646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 2, 5].length) (baseStart_317646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_317646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_317646 prefixEnd_317646 := by exact prefixLift 317646
  have htrace : WordTrace (prefixWord ++ tailWord_317646) baseStart_317646 baseEnd_317646 := by
    simpa [prefixWord, tailWord_317646, baseEnd_317646] using wordTrace_append hprefix tailTrace_317646
  have hstable : (prefixWord ++ tailWord_317646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317646).length < 2 ^ (prefixWord ++ tailWord_317646).sum := by decide
  have hdescent : baseEnd_317646 < baseStart_317646 := by decide
  rcases family_descends (prefixWord ++ tailWord_317646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317659 : List Nat := [1, 1, 1, 1, 1, 1, 1, 9, 6]
def baseStart_317659 : Nat := 118140960795 + 317659 * 2 ^ 59
def prefixEnd_317659 : Nat := 4983230072969 + 3 ^ 40 * 317659 * 2
def baseEnd_317659 : Nat := 36247055828150642533693

theorem tailTrace_317659 : CollatzResearch.WordTrace tailWord_317659 prefixEnd_317659 36247055828150642533693 := by
  unfold tailWord_317659
  simp only [CollatzResearch.WordTrace]
  refine ⟨11585975556183169683100031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7723983704122113122066687 11585975556183169683100031)
  ·
    refine ⟨17378963334274754524650047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11585975556183169683100031 17378963334274754524650047)
    ·
      refine ⟨26068445001412131786975071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17378963334274754524650047 26068445001412131786975071)
      ·
        refine ⟨39102667502118197680462607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26068445001412131786975071 39102667502118197680462607)
        ·
          refine ⟨58654001253177296520693911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39102667502118197680462607 58654001253177296520693911)
          ·
            refine ⟨87981001879765944781040867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58654001253177296520693911 87981001879765944781040867)
            ·
              refine ⟨131971502819648917171561301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87981001879765944781040867 131971502819648917171561301)
              ·
                refine ⟨773270524333880374052117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 131971502819648917171561301 773270524333880374052117)
                ·
                  refine ⟨36247055828150642533693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 773270524333880374052117 36247055828150642533693)
                  ·
                    rfl

theorem cell22_317659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 6].length) (baseStart_317659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_317659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_317659 prefixEnd_317659 := by exact prefixLift 317659
  have htrace : WordTrace (prefixWord ++ tailWord_317659) baseStart_317659 baseEnd_317659 := by
    simpa [prefixWord, tailWord_317659, baseEnd_317659] using wordTrace_append hprefix tailTrace_317659
  have hstable : (prefixWord ++ tailWord_317659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317659).length < 2 ^ (prefixWord ++ tailWord_317659).sum := by decide
  have hdescent : baseEnd_317659 < baseStart_317659 := by decide
  rcases family_descends (prefixWord ++ tailWord_317659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317706 : List Nat := [3, 1, 2, 2, 1, 1, 3, 1, 4, 4]
def baseStart_317706 : Nat := 118140960795 + 317706 * 2 ^ 59
def prefixEnd_317706 : Nat := 4983230072969 + 3 ^ 40 * 317706 * 2
def baseEnd_317706 : Nat := 108757256544959471675935

theorem tailTrace_317706 : CollatzResearch.WordTrace tailWord_317706 prefixEnd_317706 108757256544959471675935 := by
  unfold tailWord_317706
  simp only [CollatzResearch.WordTrace]
  refine ⟨2896922446753224177515243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7725126524675264473373981 2896922446753224177515243)
  ·
    refine ⟨4345383670129836266272865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2896922446753224177515243 4345383670129836266272865)
    ·
      refine ⟨3259037752597377199704649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4345383670129836266272865 3259037752597377199704649)
      ·
        refine ⟨2444278314448032899778487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3259037752597377199704649 2444278314448032899778487)
        ·
          refine ⟨3666417471672049349667731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2444278314448032899778487 3666417471672049349667731)
          ·
            refine ⟨5499626207508074024501597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3666417471672049349667731 5499626207508074024501597)
            ·
              refine ⟨2062359827815527759188099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5499626207508074024501597 2062359827815527759188099)
              ·
                refine ⟨3093539741723291638782149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2062359827815527759188099 3093539741723291638782149)
                ·
                  refine ⟨580038701573117182271653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3093539741723291638782149 580038701573117182271653)
                  ·
                    refine ⟨108757256544959471675935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 580038701573117182271653 108757256544959471675935)
                    ·
                      rfl

theorem cell22_317706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 4, 4].length) (baseStart_317706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_317706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_317706 prefixEnd_317706 := by exact prefixLift 317706
  have htrace : WordTrace (prefixWord ++ tailWord_317706) baseStart_317706 baseEnd_317706 := by
    simpa [prefixWord, tailWord_317706, baseEnd_317706] using wordTrace_append hprefix tailTrace_317706
  have hstable : (prefixWord ++ tailWord_317706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317706).length < 2 ^ (prefixWord ++ tailWord_317706).sum := by decide
  have hdescent : baseEnd_317706 < baseStart_317706 := by decide
  rcases family_descends (prefixWord ++ tailWord_317706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317708 : List Nat := [2, 2, 1, 2, 2, 2, 2, 4, 2, 3]
def baseStart_317708 : Nat := 118140960795 + 317708 * 2 ^ 59
def prefixEnd_317708 : Nat := 4983230072969 + 3 ^ 40 * 317708 * 2
def baseEnd_317708 : Nat := 108757941185832133125929

theorem tailTrace_317708 : CollatzResearch.WordTrace tailWord_317708 prefixEnd_317708 108757941185832133125929 := by
  unfold tailWord_317708
  simp only [CollatzResearch.WordTrace]
  refine ⟨5793881366502825525816889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7725175155337100701089185 5793881366502825525816889)
  ·
    refine ⟨4345411024877119144362667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5793881366502825525816889 4345411024877119144362667)
    ·
      refine ⟨6518116537315678716544001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4345411024877119144362667 6518116537315678716544001)
      ·
        refine ⟨4888587402986759037408001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6518116537315678716544001 4888587402986759037408001)
        ·
          refine ⟨3666440552240069278056001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4888587402986759037408001 3666440552240069278056001)
          ·
            refine ⟨2749830414180051958542001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3666440552240069278056001 2749830414180051958542001)
            ·
              refine ⟨2062372810635038968906501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2749830414180051958542001 2062372810635038968906501)
              ·
                refine ⟨386694901994069806669969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2062372810635038968906501 386694901994069806669969)
                ·
                  refine ⟨290021176495552355002477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 386694901994069806669969 290021176495552355002477)
                  ·
                    refine ⟨108757941185832133125929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 290021176495552355002477 108757941185832133125929)
                    ·
                      rfl

theorem cell22_317708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 4, 2, 3].length) (baseStart_317708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_317708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_317708 prefixEnd_317708 := by exact prefixLift 317708
  have htrace : WordTrace (prefixWord ++ tailWord_317708) baseStart_317708 baseEnd_317708 := by
    simpa [prefixWord, tailWord_317708, baseEnd_317708] using wordTrace_append hprefix tailTrace_317708
  have hstable : (prefixWord ++ tailWord_317708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317708).length < 2 ^ (prefixWord ++ tailWord_317708).sum := by decide
  have hdescent : baseEnd_317708 < baseStart_317708 := by decide
  rcases family_descends (prefixWord ++ tailWord_317708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317710 : List Nat := [4, 1, 1, 2, 1, 2, 5, 2, 4]
def baseStart_317710 : Nat := 118140960795 + 317710 * 2 ^ 59
def prefixEnd_317710 : Nat := 4983230072969 + 3 ^ 40 * 317710 * 2
def baseEnd_317710 : Nat := 36252875275568264858641

theorem tailTrace_317710 : CollatzResearch.WordTrace tailWord_317710 prefixEnd_317710 36252875275568264858641 := by
  unfold tailWord_317710
  simp only [CollatzResearch.WordTrace]
  refine ⟨1448479459874800674150823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7725223785998936928804389 1448479459874800674150823)
  ·
    refine ⟨2172719189812201011226235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1448479459874800674150823 2172719189812201011226235)
    ·
      refine ⟨3259078784718301516839353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2172719189812201011226235 3259078784718301516839353)
      ·
        refine ⟨2444309088538726137629515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3259078784718301516839353 2444309088538726137629515)
        ·
          refine ⟨3666463632808089206444273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2444309088538726137629515 3666463632808089206444273)
          ·
            refine ⟨2749847724606066904833205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3666463632808089206444273 2749847724606066904833205)
            ·
              refine ⟨257798224181818772328113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2749847724606066904833205 257798224181818772328113)
              ·
                refine ⟨193348668136364079246085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 257798224181818772328113 193348668136364079246085)
                ·
                  refine ⟨36252875275568264858641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 193348668136364079246085 36252875275568264858641)
                  ·
                    rfl

theorem cell22_317710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 5, 2, 4].length) (baseStart_317710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_317710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_317710 prefixEnd_317710 := by exact prefixLift 317710
  have htrace : WordTrace (prefixWord ++ tailWord_317710) baseStart_317710 baseEnd_317710 := by
    simpa [prefixWord, tailWord_317710, baseEnd_317710] using wordTrace_append hprefix tailTrace_317710
  have hstable : (prefixWord ++ tailWord_317710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317710).length < 2 ^ (prefixWord ++ tailWord_317710).sum := by decide
  have hdescent : baseEnd_317710 < baseStart_317710 := by decide
  rcases family_descends (prefixWord ++ tailWord_317710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317828 : List Nat := [2, 3, 2, 1, 1, 2, 4, 1, 6]
def baseStart_317828 : Nat := 118140960795 + 317828 * 2 ^ 59
def prefixEnd_317828 : Nat := 4983230072969 + 3 ^ 40 * 317828 * 2
def baseEnd_317828 : Nat := 36266339879397273375187

theorem tailTrace_317828 : CollatzResearch.WordTrace tailWord_317828 prefixEnd_317828 36266339879397273375187 := by
  unfold tailWord_317828
  simp only [CollatzResearch.WordTrace]
  refine ⟨5796069746285455773001069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7728092995047274364001425 5796069746285455773001069)
  ·
    refine ⟨2173526154857045914875401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5796069746285455773001069 2173526154857045914875401)
    ·
      refine ⟨1630144616142784436156551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2173526154857045914875401 1630144616142784436156551)
      ·
        refine ⟨2445216924214176654234827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1630144616142784436156551 2445216924214176654234827)
        ·
          refine ⟨3667825386321264981352241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2445216924214176654234827 3667825386321264981352241)
          ·
            refine ⟨2750869039740948736014181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3667825386321264981352241 2750869039740948736014181)
            ·
              refine ⟨515787944951427888002659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2750869039740948736014181 515787944951427888002659)
              ·
                refine ⟨773681917427141832003989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 515787944951427888002659 773681917427141832003989)
                ·
                  refine ⟨36266339879397273375187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 773681917427141832003989 36266339879397273375187)
                  ·
                    rfl

theorem cell22_317828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 1, 6].length) (baseStart_317828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_317828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_317828 prefixEnd_317828 := by exact prefixLift 317828
  have htrace : WordTrace (prefixWord ++ tailWord_317828) baseStart_317828 baseEnd_317828 := by
    simpa [prefixWord, tailWord_317828, baseEnd_317828] using wordTrace_append hprefix tailTrace_317828
  have hstable : (prefixWord ++ tailWord_317828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317828).length < 2 ^ (prefixWord ++ tailWord_317828).sum := by decide
  have hdescent : baseEnd_317828 < baseStart_317828 := by decide
  rcases family_descends (prefixWord ++ tailWord_317828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317858 : List Nat := [3, 3, 1, 2, 1, 1, 1, 3, 1, 6]
def baseStart_317858 : Nat := 118140960795 + 317858 * 2 ^ 59
def prefixEnd_317858 : Nat := 4983230072969 + 3 ^ 40 * 317858 * 2
def baseEnd_317858 : Nat := 108809289251281741875469

theorem tailTrace_317858 : CollatzResearch.WordTrace tailWord_317858 prefixEnd_317858 108809289251281741875469 := by
  unfold tailWord_317858
  simp only [CollatzResearch.WordTrace]
  refine ⟨2898308420615556667398557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7728822454974817779729485 2898308420615556667398557)
  ·
    refine ⟨1086865657730833750274459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2898308420615556667398557 1086865657730833750274459)
    ·
      refine ⟨1630298486596250625411689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1086865657730833750274459 1630298486596250625411689)
      ·
        refine ⟨1222723864947187969058767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1630298486596250625411689 1222723864947187969058767)
        ·
          refine ⟨1834085797420781953588151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1222723864947187969058767 1834085797420781953588151)
          ·
            refine ⟨2751128696131172930382227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1834085797420781953588151 2751128696131172930382227)
            ·
              refine ⟨4126693044196759395573341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2751128696131172930382227 4126693044196759395573341)
              ·
                refine ⟨1547509891573784773340003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4126693044196759395573341 1547509891573784773340003)
                ·
                  refine ⟨2321264837360677160010005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1547509891573784773340003 2321264837360677160010005)
                  ·
                    refine ⟨108809289251281741875469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2321264837360677160010005 108809289251281741875469)
                    ·
                      rfl

theorem cell22_317858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_317858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_317858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_317858 prefixEnd_317858 := by exact prefixLift 317858
  have htrace : WordTrace (prefixWord ++ tailWord_317858) baseStart_317858 baseEnd_317858 := by
    simpa [prefixWord, tailWord_317858, baseEnd_317858] using wordTrace_append hprefix tailTrace_317858
  have hstable : (prefixWord ++ tailWord_317858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317858).length < 2 ^ (prefixWord ++ tailWord_317858).sum := by decide
  have hdescent : baseEnd_317858 < baseStart_317858 := by decide
  rcases family_descends (prefixWord ++ tailWord_317858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317873 : List Nat := [1, 2, 2, 4, 1, 4, 8]
def baseStart_317873 : Nat := 118140960795 + 317873 * 2 ^ 59
def prefixEnd_317873 : Nat := 4983230072969 + 3 ^ 40 * 317873 * 2
def baseEnd_317873 : Nat := 4030163853993581583349

theorem tailTrace_317873 : CollatzResearch.WordTrace tailWord_317873 prefixEnd_317873 4030163853993581583349 := by
  unfold tailWord_317873
  simp only [CollatzResearch.WordTrace]
  refine ⟨11593780777407884231390273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7729187184938589487593515 11593780777407884231390273)
  ·
    refine ⟨8695335583055913173542705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11593780777407884231390273 8695335583055913173542705)
    ·
      refine ⟨6521501687291934880157029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8695335583055913173542705 6521501687291934880157029)
      ·
        refine ⟨1222781566367237790029443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6521501687291934880157029 1222781566367237790029443)
        ·
          refine ⟨1834172349550856685044165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1222781566367237790029443 1834172349550856685044165)
          ·
            refine ⟨343907315540785628445781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1834172349550856685044165 343907315540785628445781)
            ·
              refine ⟨4030163853993581583349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 343907315540785628445781 4030163853993581583349)
              ·
                rfl

theorem cell22_317873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 8].length) (baseStart_317873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_317873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_317873 prefixEnd_317873 := by exact prefixLift 317873
  have htrace : WordTrace (prefixWord ++ tailWord_317873) baseStart_317873 baseEnd_317873 := by
    simpa [prefixWord, tailWord_317873, baseEnd_317873] using wordTrace_append hprefix tailTrace_317873
  have hstable : (prefixWord ++ tailWord_317873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317873).length < 2 ^ (prefixWord ++ tailWord_317873).sum := by decide
  have hdescent : baseEnd_317873 < baseStart_317873 := by decide
  rcases family_descends (prefixWord ++ tailWord_317873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317963 : List Nat := [1, 1, 1, 1, 7, 1, 1, 1, 8]
def baseStart_317963 : Nat := 118140960795 + 317963 * 2 ^ 59
def prefixEnd_317963 : Nat := 4983230072969 + 3 ^ 40 * 317963 * 2
def baseEnd_317963 : Nat := 36281744299032156000049

theorem tailTrace_317963 : CollatzResearch.WordTrace tailWord_317963 prefixEnd_317963 36281744299032156000049 := by
  unfold tailWord_317963
  simp only [CollatzResearch.WordTrace]
  refine ⟨11597063347081829602166543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7731375564721219734777695 11597063347081829602166543)
  ·
    refine ⟨17395595020622744403249815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11597063347081829602166543 17395595020622744403249815)
    ·
      refine ⟨26093392530934116604874723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17395595020622744403249815 26093392530934116604874723)
      ·
        refine ⟨39140088796401174907312085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26093392530934116604874723 39140088796401174907312085)
        ·
          refine ⟨917345831165652536890127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 39140088796401174907312085 917345831165652536890127)
          ·
            refine ⟨1376018746748478805335191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 917345831165652536890127 1376018746748478805335191)
            ·
              refine ⟨2064028120122718208002787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1376018746748478805335191 2064028120122718208002787)
              ·
                refine ⟨3096042180184077312004181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2064028120122718208002787 3096042180184077312004181)
                ·
                  refine ⟨36281744299032156000049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3096042180184077312004181 36281744299032156000049)
                  ·
                    rfl

theorem cell22_317963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 8].length) (baseStart_317963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_317963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_317963 prefixEnd_317963 := by exact prefixLift 317963
  have htrace : WordTrace (prefixWord ++ tailWord_317963) baseStart_317963 baseEnd_317963 := by
    simpa [prefixWord, tailWord_317963, baseEnd_317963] using wordTrace_append hprefix tailTrace_317963
  have hstable : (prefixWord ++ tailWord_317963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317963).length < 2 ^ (prefixWord ++ tailWord_317963).sum := by decide
  have hdescent : baseEnd_317963 < baseStart_317963 := by decide
  rcases family_descends (prefixWord ++ tailWord_317963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318008 : List Nat := [2, 1, 2, 1, 4, 1, 2, 9]
def baseStart_318008 : Nat := 118140960795 + 318008 * 2 ^ 59
def prefixEnd_318008 : Nat := 4983230072969 + 3 ^ 40 * 318008 * 2
def baseEnd_318008 : Nat := 12095626368525705625001

theorem tailTrace_318008 : CollatzResearch.WordTrace tailWord_318008 prefixEnd_318008 12095626368525705625001 := by
  unfold tailWord_318008
  simp only [CollatzResearch.WordTrace]
  refine ⟨5799352315959401143777339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7732469754612534858369785 5799352315959401143777339)
  ·
    refine ⟨8699028473939101715666009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5799352315959401143777339 8699028473939101715666009)
    ·
      refine ⟨6524271355454326286749507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8699028473939101715666009 6524271355454326286749507)
      ·
        refine ⟨9786407033181489430124261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6524271355454326286749507 9786407033181489430124261)
        ·
          refine ⟨1834951318721529268148299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9786407033181489430124261 1834951318721529268148299)
          ·
            refine ⟨2752426978082293902222449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1834951318721529268148299 2752426978082293902222449)
            ·
              refine ⟨2064320233561720426666837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2752426978082293902222449 2064320233561720426666837)
              ·
                refine ⟨12095626368525705625001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2064320233561720426666837 12095626368525705625001)
                ·
                  rfl

theorem cell22_318008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 9].length) (baseStart_318008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_318008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_318008 prefixEnd_318008 := by exact prefixLift 318008
  have htrace : WordTrace (prefixWord ++ tailWord_318008) baseStart_318008 baseEnd_318008 := by
    simpa [prefixWord, tailWord_318008, baseEnd_318008] using wordTrace_append hprefix tailTrace_318008
  have hstable : (prefixWord ++ tailWord_318008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318008).length < 2 ^ (prefixWord ++ tailWord_318008).sum := by decide
  have hdescent : baseEnd_318008 < baseStart_318008 := by decide
  rcases family_descends (prefixWord ++ tailWord_318008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318012 : List Nat := [2, 2, 2, 2, 3, 3, 1, 1, 1, 5]
def baseStart_318012 : Nat := 118140960795 + 318012 * 2 ^ 59
def prefixEnd_318012 : Nat := 4983230072969 + 3 ^ 40 * 318012 * 2
def baseEnd_318012 : Nat := 108862006598476673524997

theorem tailTrace_318012 : CollatzResearch.WordTrace tailWord_318012 prefixEnd_318012 108862006598476673524997 := by
  unfold tailWord_318012
  simp only [CollatzResearch.WordTrace]
  refine ⟨5799425261952155485350145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7732567015936207313800193 5799425261952155485350145)
  ·
    refine ⟨4349568946464116614012609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5799425261952155485350145 4349568946464116614012609)
    ·
      refine ⟨3262176709848087460509457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4349568946464116614012609 3262176709848087460509457)
      ·
        refine ⟨2446632532386065595382093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3262176709848087460509457 2446632532386065595382093)
        ·
          refine ⟨917487199644774598268285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2446632532386065595382093 917487199644774598268285)
          ·
            refine ⟨344057699866790474350607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 917487199644774598268285 344057699866790474350607)
            ·
              refine ⟨516086549800185711525911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 344057699866790474350607 516086549800185711525911)
              ·
                refine ⟨774129824700278567288867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 516086549800185711525911 774129824700278567288867)
                ·
                  refine ⟨1161194737050417850933301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 774129824700278567288867 1161194737050417850933301)
                  ·
                    refine ⟨108862006598476673524997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1161194737050417850933301 108862006598476673524997)
                    ·
                      rfl

theorem cell22_318012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 1, 1, 5].length) (baseStart_318012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_318012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_318012 prefixEnd_318012 := by exact prefixLift 318012
  have htrace : WordTrace (prefixWord ++ tailWord_318012) baseStart_318012 baseEnd_318012 := by
    simpa [prefixWord, tailWord_318012, baseEnd_318012] using wordTrace_append hprefix tailTrace_318012
  have hstable : (prefixWord ++ tailWord_318012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318012).length < 2 ^ (prefixWord ++ tailWord_318012).sum := by decide
  have hdescent : baseEnd_318012 < baseStart_318012 := by decide
  rcases family_descends (prefixWord ++ tailWord_318012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318040 : List Nat := [2, 1, 2, 2, 1, 2, 2, 2, 5, 3]
def baseStart_318040 : Nat := 118140960795 + 318040 * 2 ^ 59
def prefixEnd_318040 : Nat := 4983230072969 + 3 ^ 40 * 318040 * 2
def baseEnd_318040 : Nat := 108871591570693933824911

theorem tailTrace_318040 : CollatzResearch.WordTrace tailWord_318040 prefixEnd_318040 108871591570693933824911 := by
  unfold tailWord_318040
  simp only [CollatzResearch.WordTrace]
  refine ⟨5799935883901435876359787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7733247845201914501813049 5799935883901435876359787)
  ·
    refine ⟨8699903825852153814539681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5799935883901435876359787 8699903825852153814539681)
    ·
      refine ⟨6524927869389115360904761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8699903825852153814539681 6524927869389115360904761)
      ·
        refine ⟨4893695902041836520678571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6524927869389115360904761 4893695902041836520678571)
        ·
          refine ⟨7340543853062754781017857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4893695902041836520678571 7340543853062754781017857)
          ·
            refine ⟨5505407889797066085763393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7340543853062754781017857 5505407889797066085763393)
            ·
              refine ⟨4129055917347799564322545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5505407889797066085763393 4129055917347799564322545)
              ·
                refine ⟨3096791938010849673241909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4129055917347799564322545 3096791938010849673241909)
                ·
                  refine ⟨290324244188517156866429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3096791938010849673241909 290324244188517156866429)
                  ·
                    refine ⟨108871591570693933824911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 290324244188517156866429 108871591570693933824911)
                    ·
                      rfl

theorem cell22_318040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 5, 3].length) (baseStart_318040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_318040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_318040 prefixEnd_318040 := by exact prefixLift 318040
  have htrace : WordTrace (prefixWord ++ tailWord_318040) baseStart_318040 baseEnd_318040 := by
    simpa [prefixWord, tailWord_318040, baseEnd_318040] using wordTrace_append hprefix tailTrace_318040
  have hstable : (prefixWord ++ tailWord_318040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318040).length < 2 ^ (prefixWord ++ tailWord_318040).sum := by decide
  have hdescent : baseEnd_318040 < baseStart_318040 := by decide
  rcases family_descends (prefixWord ++ tailWord_318040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318108 : List Nat := [2, 2, 3, 2, 2, 3, 2, 2, 1, 3]
def baseStart_318108 : Nat := 118140960795 + 318108 * 2 ^ 59
def prefixEnd_318108 : Nat := 4983230072969 + 3 ^ 40 * 318108 * 2
def baseEnd_318108 : Nat := 108894869360364423124703

theorem tailTrace_318108 : CollatzResearch.WordTrace tailWord_318108 prefixEnd_318108 108894869360364423124703 := by
  unfold tailWord_318108
  simp only [CollatzResearch.WordTrace]
  refine ⟨5801175965778259683097489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7734901287704346244129985 5801175965778259683097489)
  ·
    refine ⟨4350881974333694762323117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5801175965778259683097489 4350881974333694762323117)
    ·
      refine ⟨1631580740375135535871169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4350881974333694762323117 1631580740375135535871169)
      ·
        refine ⟨1223685555281351651903377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1631580740375135535871169 1223685555281351651903377)
        ·
          refine ⟨917764166461013738927533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1223685555281351651903377 917764166461013738927533)
          ·
            refine ⟨344161562422880152097825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 917764166461013738927533 344161562422880152097825)
            ·
              refine ⟨258121171817160114073369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 344161562422880152097825 258121171817160114073369)
              ·
                refine ⟨193590878862870085555027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 258121171817160114073369 193590878862870085555027)
                ·
                  refine ⟨290386318294305128332541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 193590878862870085555027 290386318294305128332541)
                  ·
                    refine ⟨108894869360364423124703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 290386318294305128332541 108894869360364423124703)
                    ·
                      rfl

theorem cell22_318108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 2, 2, 1, 3].length) (baseStart_318108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_318108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_318108 prefixEnd_318108 := by exact prefixLift 318108
  have htrace : WordTrace (prefixWord ++ tailWord_318108) baseStart_318108 baseEnd_318108 := by
    simpa [prefixWord, tailWord_318108, baseEnd_318108] using wordTrace_append hprefix tailTrace_318108
  have hstable : (prefixWord ++ tailWord_318108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318108).length < 2 ^ (prefixWord ++ tailWord_318108).sum := by decide
  have hdescent : baseEnd_318108 < baseStart_318108 := by decide
  rcases family_descends (prefixWord ++ tailWord_318108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318119 : List Nat := [1, 1, 6, 3, 1, 1, 1, 1, 2, 5]
def baseStart_318119 : Nat := 118140960795 + 318119 * 2 ^ 59
def prefixEnd_318119 : Nat := 4983230072969 + 3 ^ 40 * 318119 * 2
def baseEnd_318119 : Nat := 108898634885164061099669

theorem tailTrace_318119 : CollatzResearch.WordTrace tailWord_318119 prefixEnd_318119 108898634885164061099669 := by
  unfold tailWord_318119
  simp only [CollatzResearch.WordTrace]
  refine ⟨11602753134516668244845411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7735168756344445496563607 11602753134516668244845411)
  ·
    refine ⟨17404129701775002367268117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11602753134516668244845411 17404129701775002367268117)
    ·
      refine ⟨815818579770703235965693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 17404129701775002367268117 815818579770703235965693)
      ·
        refine ⟨305931967414013713487135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 815818579770703235965693 305931967414013713487135)
        ·
          refine ⟨458897951121020570230703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 305931967414013713487135 458897951121020570230703)
          ·
            refine ⟨688346926681530855346055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 458897951121020570230703 688346926681530855346055)
            ·
              refine ⟨1032520390022296283019083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 688346926681530855346055 1032520390022296283019083)
              ·
                refine ⟨1548780585033444424528625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1032520390022296283019083 1548780585033444424528625)
                ·
                  refine ⟨1161585438775083318396469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1548780585033444424528625 1161585438775083318396469)
                  ·
                    refine ⟨108898634885164061099669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1161585438775083318396469 108898634885164061099669)
                    ·
                      rfl

theorem cell22_318119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_318119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_318119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_318119 prefixEnd_318119 := by exact prefixLift 318119
  have htrace : WordTrace (prefixWord ++ tailWord_318119) baseStart_318119 baseEnd_318119 := by
    simpa [prefixWord, tailWord_318119, baseEnd_318119] using wordTrace_append hprefix tailTrace_318119
  have hstable : (prefixWord ++ tailWord_318119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318119).length < 2 ^ (prefixWord ++ tailWord_318119).sum := by decide
  have hdescent : baseEnd_318119 < baseStart_318119 := by decide
  rcases family_descends (prefixWord ++ tailWord_318119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318181 : List Nat := [1, 3, 1, 4, 1, 3, 3, 1, 2, 3]
def baseStart_318181 : Nat := 118140960795 + 318181 * 2 ^ 59
def prefixEnd_318181 : Nat := 4983230072969 + 3 ^ 40 * 318181 * 2
def baseEnd_318181 : Nat := 108919858752216566049479

theorem tailTrace_318181 : CollatzResearch.WordTrace tailWord_318181 prefixEnd_318181 108919858752216566049479 := by
  unfold tailWord_318181
  simp only [CollatzResearch.WordTrace]
  refine ⟨11605014460292052833602397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7736676306861368555734931 11605014460292052833602397)
  ·
    refine ⟨4351880422609519812600899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11605014460292052833602397 4351880422609519812600899)
    ·
      refine ⟨6527820633914279718901349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4351880422609519812600899 6527820633914279718901349)
      ·
        refine ⟨1223966368858927447294003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6527820633914279718901349 1223966368858927447294003)
        ·
          refine ⟨1835949553288391170941005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1223966368858927447294003 1835949553288391170941005)
          ·
            refine ⟨688481082483146689102877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1835949553288391170941005 688481082483146689102877)
            ·
              refine ⟨258180405931180008413579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 688481082483146689102877 258180405931180008413579)
              ·
                refine ⟨387270608896770012620369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 258180405931180008413579 387270608896770012620369)
                ·
                  refine ⟨290452956672577509465277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 387270608896770012620369 290452956672577509465277)
                  ·
                    refine ⟨108919858752216566049479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 290452956672577509465277 108919858752216566049479)
                    ·
                      rfl

theorem cell22_318181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 3, 1, 2, 3].length) (baseStart_318181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_318181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_318181 prefixEnd_318181 := by exact prefixLift 318181
  have htrace : WordTrace (prefixWord ++ tailWord_318181) baseStart_318181 baseEnd_318181 := by
    simpa [prefixWord, tailWord_318181, baseEnd_318181] using wordTrace_append hprefix tailTrace_318181
  have hstable : (prefixWord ++ tailWord_318181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318181).length < 2 ^ (prefixWord ++ tailWord_318181).sum := by decide
  have hdescent : baseEnd_318181 < baseStart_318181 := by decide
  rcases family_descends (prefixWord ++ tailWord_318181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318192 : List Nat := [2, 1, 1, 1, 3, 1, 3, 4, 3, 3]
def baseStart_318192 : Nat := 118140960795 + 318192 * 2 ^ 59
def prefixEnd_318192 : Nat := 4983230072969 + 3 ^ 40 * 318192 * 2
def baseEnd_318192 : Nat := 108923624277016204024445

theorem tailTrace_318192 : CollatzResearch.WordTrace tailWord_318192 prefixEnd_318192 108923624277016204024445 := by
  unfold tailWord_318192
  simp only [CollatzResearch.WordTrace]
  refine ⟨5802707831626100856126415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7736943775501467808168553 5802707831626100856126415)
  ·
    refine ⟨8704061747439151284189623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5802707831626100856126415 8704061747439151284189623)
    ·
      refine ⟨13056092621158726926284435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8704061747439151284189623 13056092621158726926284435)
      ·
        refine ⟨19584138931738090389426653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13056092621158726926284435 19584138931738090389426653)
        ·
          refine ⟨7344052099401783896034995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19584138931738090389426653 7344052099401783896034995)
          ·
            refine ⟨11016078149102675844052493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7344052099401783896034995 11016078149102675844052493)
            ·
              refine ⟨4131029305913503441519685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11016078149102675844052493 4131029305913503441519685)
              ·
                refine ⟨774567994858781895284941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4131029305913503441519685 774567994858781895284941)
                ·
                  refine ⟨290462998072043210731853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 774567994858781895284941 290462998072043210731853)
                  ·
                    refine ⟨108923624277016204024445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 290462998072043210731853 108923624277016204024445)
                    ·
                      rfl

theorem cell22_318192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 4, 3, 3].length) (baseStart_318192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_318192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_318192 prefixEnd_318192 := by exact prefixLift 318192
  have htrace : WordTrace (prefixWord ++ tailWord_318192) baseStart_318192 baseEnd_318192 := by
    simpa [prefixWord, tailWord_318192, baseEnd_318192] using wordTrace_append hprefix tailTrace_318192
  have hstable : (prefixWord ++ tailWord_318192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318192).length < 2 ^ (prefixWord ++ tailWord_318192).sum := by decide
  have hdescent : baseEnd_318192 < baseStart_318192 := by decide
  rcases family_descends (prefixWord ++ tailWord_318192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318194 : List Nat := [3, 2, 1, 3, 1, 4, 2, 6]
def baseStart_318194 : Nat := 118140960795 + 318194 * 2 ^ 59
def prefixEnd_318194 : Nat := 4983230072969 + 3 ^ 40 * 318194 * 2
def baseEnd_318194 : Nat := 12102700990876540608271

theorem tailTrace_318194 : CollatzResearch.WordTrace tailWord_318194 prefixEnd_318194 12102700990876540608271 := by
  unfold tailWord_318194
  simp only [CollatzResearch.WordTrace]
  refine ⟨2901372152311239013456409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7736992406163304035883757 2901372152311239013456409)
  ·
    refine ⟨2176029114233429260092307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2901372152311239013456409 2176029114233429260092307)
    ·
      refine ⟨3264043671350143890138461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2176029114233429260092307 3264043671350143890138461)
      ·
        refine ⟨1224016376756303958801923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3264043671350143890138461 1224016376756303958801923)
        ·
          refine ⟨1836024565134455938202885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1224016376756303958801923 1836024565134455938202885)
          ·
            refine ⟨344254605962710488413041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1836024565134455938202885 344254605962710488413041)
            ·
              refine ⟨258190954472032866309781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 344254605962710488413041 258190954472032866309781)
              ·
                refine ⟨12102700990876540608271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 258190954472032866309781 12102700990876540608271)
                ·
                  rfl

theorem cell22_318194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 2, 6].length) (baseStart_318194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_318194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_318194 prefixEnd_318194 := by exact prefixLift 318194
  have htrace : WordTrace (prefixWord ++ tailWord_318194) baseStart_318194 baseEnd_318194 := by
    simpa [prefixWord, tailWord_318194, baseEnd_318194] using wordTrace_append hprefix tailTrace_318194
  have hstable : (prefixWord ++ tailWord_318194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318194).length < 2 ^ (prefixWord ++ tailWord_318194).sum := by decide
  have hdescent : baseEnd_318194 < baseStart_318194 := by decide
  rcases family_descends (prefixWord ++ tailWord_318194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318205 : List Nat := [1, 4, 1, 1, 1, 1, 3, 1, 9]
def baseStart_318205 : Nat := 118140960795 + 318205 * 2 ^ 59
def prefixEnd_318205 : Nat := 4983230072969 + 3 ^ 40 * 318205 * 2
def baseEnd_318205 : Nat := 36309358147562834483135

theorem tailTrace_318205 : CollatzResearch.WordTrace tailWord_318205 prefixEnd_318205 36309358147562834483135 := by
  unfold tailWord_318205
  simp only [CollatzResearch.WordTrace]
  refine ⟨11605889812205104932476069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7737259874803403288317379 11605889812205104932476069)
  ·
    refine ⟨2176104339788457174839263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11605889812205104932476069 2176104339788457174839263)
    ·
      refine ⟨3264156509682685762258895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2176104339788457174839263 3264156509682685762258895)
      ·
        refine ⟨4896234764524028643388343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3264156509682685762258895 4896234764524028643388343)
        ·
          refine ⟨7344352146786042965082515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4896234764524028643388343 7344352146786042965082515)
          ·
            refine ⟨11016528220179064447623773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7344352146786042965082515 11016528220179064447623773)
            ·
              refine ⟨4131198082567149167858915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11016528220179064447623773 4131198082567149167858915)
              ·
                refine ⟨6196797123850723751788373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4131198082567149167858915 6196797123850723751788373)
                ·
                  refine ⟨36309358147562834483135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 6196797123850723751788373 36309358147562834483135)
                  ·
                    rfl

theorem cell22_318205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 9].length) (baseStart_318205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_318205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_318205 prefixEnd_318205 := by exact prefixLift 318205
  have htrace : WordTrace (prefixWord ++ tailWord_318205) baseStart_318205 baseEnd_318205 := by
    simpa [prefixWord, tailWord_318205, baseEnd_318205] using wordTrace_append hprefix tailTrace_318205
  have hstable : (prefixWord ++ tailWord_318205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318205).length < 2 ^ (prefixWord ++ tailWord_318205).sum := by decide
  have hdescent : baseEnd_318205 < baseStart_318205 := by decide
  rcases family_descends (prefixWord ++ tailWord_318205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318222 : List Nat := [4, 1, 1, 2, 1, 1, 1, 6, 5]
def baseStart_318222 : Nat := 118140960795 + 318222 * 2 ^ 59
def prefixEnd_318222 : Nat := 4983230072969 + 3 ^ 40 * 318222 * 2
def baseEnd_318222 : Nat := 36311297963368708591451

theorem tailTrace_318222 : CollatzResearch.WordTrace tailWord_318222 prefixEnd_318222 36311297963368708591451 := by
  unfold tailWord_318222
  simp only [CollatzResearch.WordTrace]
  refine ⟨1450813731642939604480615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7737673235429011223896613 1450813731642939604480615)
  ·
    refine ⟨2176220597464409406720923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1450813731642939604480615 2176220597464409406720923)
    ·
      refine ⟨3264330896196614110081385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2176220597464409406720923 3264330896196614110081385)
      ·
        refine ⟨2448248172147460582561039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3264330896196614110081385 2448248172147460582561039)
        ·
          refine ⟨3672372258221190873841559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2448248172147460582561039 3672372258221190873841559)
          ·
            refine ⟨5508558387331786310762339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3672372258221190873841559 5508558387331786310762339)
            ·
              refine ⟨8262837580997679466143509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5508558387331786310762339 8262837580997679466143509)
              ·
                refine ⟨387320511609266224975477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8262837580997679466143509 387320511609266224975477)
                ·
                  refine ⟨36311297963368708591451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 387320511609266224975477 36311297963368708591451)
                  ·
                    rfl

theorem cell22_318222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 6, 5].length) (baseStart_318222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_318222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_318222 prefixEnd_318222 := by exact prefixLift 318222
  have htrace : WordTrace (prefixWord ++ tailWord_318222) baseStart_318222 baseEnd_318222 := by
    simpa [prefixWord, tailWord_318222, baseEnd_318222] using wordTrace_append hprefix tailTrace_318222
  have hstable : (prefixWord ++ tailWord_318222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318222).length < 2 ^ (prefixWord ++ tailWord_318222).sum := by decide
  have hdescent : baseEnd_318222 < baseStart_318222 := by decide
  rcases family_descends (prefixWord ++ tailWord_318222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318239 : List Nat := [1, 1, 2, 4, 2, 2, 4, 1, 5]
def baseStart_318239 : Nat := 118140960795 + 318239 * 2 ^ 59
def prefixEnd_318239 : Nat := 4983230072969 + 3 ^ 40 * 318239 * 2
def baseEnd_318239 : Nat := 36313237779174582699767

theorem tailTrace_318239 : CollatzResearch.WordTrace tailWord_318239 prefixEnd_318239 36313237779174582699767 := by
  unfold tailWord_318239
  simp only [CollatzResearch.WordTrace]
  refine ⟨11607129894081928739213771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7738086596054619159475847 11607129894081928739213771)
  ·
    refine ⟨17410694841122893108820657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11607129894081928739213771 17410694841122893108820657)
    ·
      refine ⟨13058021130842169831615493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17410694841122893108820657 13058021130842169831615493)
      ·
        refine ⟨2448378962032906843427905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13058021130842169831615493 2448378962032906843427905)
        ·
          refine ⟨1836284221524680132570929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2448378962032906843427905 1836284221524680132570929)
          ·
            refine ⟨1377213166143510099428197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1836284221524680132570929 1377213166143510099428197)
            ·
              refine ⟨258227468651908143642787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1377213166143510099428197 258227468651908143642787)
              ·
                refine ⟨387341202977862215464181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 258227468651908143642787 387341202977862215464181)
                ·
                  refine ⟨36313237779174582699767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 387341202977862215464181 36313237779174582699767)
                  ·
                    rfl

theorem cell22_318239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 4, 1, 5].length) (baseStart_318239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_318239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_318239 prefixEnd_318239 := by exact prefixLift 318239
  have htrace : WordTrace (prefixWord ++ tailWord_318239) baseStart_318239 baseEnd_318239 := by
    simpa [prefixWord, tailWord_318239, baseEnd_318239] using wordTrace_append hprefix tailTrace_318239
  have hstable : (prefixWord ++ tailWord_318239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318239).length < 2 ^ (prefixWord ++ tailWord_318239).sum := by decide
  have hdescent : baseEnd_318239 < baseStart_318239 := by decide
  rcases family_descends (prefixWord ++ tailWord_318239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318252 : List Nat := [2, 2, 1, 1, 1, 4, 3, 1, 3, 4]
def baseStart_318252 : Nat := 118140960795 + 318252 * 2 ^ 59
def prefixEnd_318252 : Nat := 4983230072969 + 3 ^ 40 * 318252 * 2
def baseEnd_318252 : Nat := 108944163503196047524261

theorem tailTrace_318252 : CollatzResearch.WordTrace tailWord_318252 prefixEnd_318252 108944163503196047524261 := by
  unfold tailWord_318252
  simp only [CollatzResearch.WordTrace]
  refine ⟨5803802021517415979718505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7738402695356554639624673 5803802021517415979718505)
  ·
    refine ⟨4352851516138061984788879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5803802021517415979718505 4352851516138061984788879)
    ·
      refine ⟨6529277274207092977183319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4352851516138061984788879 6529277274207092977183319)
      ·
        refine ⟨9793915911310639465774979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6529277274207092977183319 9793915911310639465774979)
        ·
          refine ⟨14690873866965959198662469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9793915911310639465774979 14690873866965959198662469)
          ·
            refine ⟨2754538850056117349749213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14690873866965959198662469 2754538850056117349749213)
            ·
              refine ⟨1032952068771044006155955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2754538850056117349749213 1032952068771044006155955)
              ·
                refine ⟨1549428103156566009233933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1032952068771044006155955 1549428103156566009233933)
                ·
                  refine ⟨581035538683712253462725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1549428103156566009233933 581035538683712253462725)
                  ·
                    refine ⟨108944163503196047524261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 581035538683712253462725 108944163503196047524261)
                    ·
                      rfl

theorem cell22_318252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 4].length) (baseStart_318252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_318252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_318252 prefixEnd_318252 := by exact prefixLift 318252
  have htrace : WordTrace (prefixWord ++ tailWord_318252) baseStart_318252 baseEnd_318252 := by
    simpa [prefixWord, tailWord_318252, baseEnd_318252] using wordTrace_append hprefix tailTrace_318252
  have hstable : (prefixWord ++ tailWord_318252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318252).length < 2 ^ (prefixWord ++ tailWord_318252).sum := by decide
  have hdescent : baseEnd_318252 < baseStart_318252 := by decide
  rcases family_descends (prefixWord ++ tailWord_318252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318318 : List Nat := [4, 1, 2, 3, 2, 1, 2, 3, 4]
def baseStart_318318 : Nat := 118140960795 + 318318 * 2 ^ 59
def prefixEnd_318318 : Nat := 4983230072969 + 3 ^ 40 * 318318 * 2
def baseEnd_318318 : Nat := 36322252217331291791353

theorem tailTrace_318318 : CollatzResearch.WordTrace tailWord_318318 prefixEnd_318318 36322252217331291791353 := by
  unfold tailWord_318318
  simp only [CollatzResearch.WordTrace]
  refine ⟨1451251407599465653917451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7740007507197150154226405 1451251407599465653917451)
  ·
    refine ⟨2176877111399198480876177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1451251407599465653917451 2176877111399198480876177)
    ·
      refine ⟨1632657833549398860657133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2176877111399198480876177 1632657833549398860657133)
      ·
        refine ⟨612246687581024572746425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1632657833549398860657133 612246687581024572746425)
        ·
          refine ⟨459185015685768429559819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 612246687581024572746425 459185015685768429559819)
          ·
            refine ⟨688777523528652644339729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 459185015685768429559819 688777523528652644339729)
            ·
              refine ⟨516583142646489483254797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 688777523528652644339729 516583142646489483254797)
              ·
                refine ⟨193718678492433556220549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 516583142646489483254797 193718678492433556220549)
                ·
                  refine ⟨36322252217331291791353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 193718678492433556220549 36322252217331291791353)
                  ·
                    rfl

theorem cell22_318318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 3, 4].length) (baseStart_318318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_318318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_318318 prefixEnd_318318 := by exact prefixLift 318318
  have htrace : WordTrace (prefixWord ++ tailWord_318318) baseStart_318318 baseEnd_318318 := by
    simpa [prefixWord, tailWord_318318, baseEnd_318318] using wordTrace_append hprefix tailTrace_318318
  have hstable : (prefixWord ++ tailWord_318318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318318).length < 2 ^ (prefixWord ++ tailWord_318318).sum := by decide
  have hdescent : baseEnd_318318 < baseStart_318318 := by decide
  rcases family_descends (prefixWord ++ tailWord_318318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318408 : List Nat := [2, 1, 3, 1, 5, 2, 2, 1, 5]
def baseStart_318408 : Nat := 118140960795 + 318408 * 2 ^ 59
def prefixEnd_318408 : Nat := 4983230072969 + 3 ^ 40 * 318408 * 2
def baseEnd_318408 : Nat := 36332521830421213541261

theorem tailTrace_318408 : CollatzResearch.WordTrace tailWord_318408 prefixEnd_318408 36332521830421213541261 := by
  unfold tailWord_318408
  simp only [CollatzResearch.WordTrace]
  refine ⟨5806646915234835301057939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7742195886979780401410585 5806646915234835301057939)
  ·
    refine ⟨8709970372852252951586909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5806646915234835301057939 8709970372852252951586909)
    ·
      refine ⟨3266238889819594856845091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8709970372852252951586909 3266238889819594856845091)
      ·
        refine ⟨4899358334729392285267637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3266238889819594856845091 4899358334729392285267637)
        ·
          refine ⟨459314843880880526743841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4899358334729392285267637 459314843880880526743841)
          ·
            refine ⟨344486132910660395057881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 459314843880880526743841 344486132910660395057881)
            ·
              refine ⟨258364599682995296293411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 344486132910660395057881 258364599682995296293411)
              ·
                refine ⟨387546899524492944440117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 258364599682995296293411 387546899524492944440117)
                ·
                  refine ⟨36332521830421213541261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 387546899524492944440117 36332521830421213541261)
                  ·
                    rfl

theorem cell22_318408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 2, 1, 5].length) (baseStart_318408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_318408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_318408 prefixEnd_318408 := by exact prefixLift 318408
  have htrace : WordTrace (prefixWord ++ tailWord_318408) baseStart_318408 baseEnd_318408 := by
    simpa [prefixWord, tailWord_318408, baseEnd_318408] using wordTrace_append hprefix tailTrace_318408
  have hstable : (prefixWord ++ tailWord_318408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318408).length < 2 ^ (prefixWord ++ tailWord_318408).sum := by decide
  have hdescent : baseEnd_318408 < baseStart_318408 := by decide
  rcases family_descends (prefixWord ++ tailWord_318408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318421 : List Nat := [1, 3, 2, 3, 3, 1, 1, 1, 3, 4]
def baseStart_318421 : Nat := 118140960795 + 318421 * 2 ^ 59
def prefixEnd_318421 : Nat := 4983230072969 + 3 ^ 40 * 318421 * 2
def baseEnd_318421 : Nat := 109002015656935940048743

theorem tailTrace_318421 : CollatzResearch.WordTrace tailWord_318421 prefixEnd_318421 109002015656935940048743 := by
  unfold tailWord_318421
  simp only [CollatzResearch.WordTrace]
  refine ⟨11613767979422573822339117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7742511986281715881559411 11613767979422573822339117)
  ·
    refine ⟨4355162992283465183377169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11613767979422573822339117 4355162992283465183377169)
    ·
      refine ⟨3266372244212598887532877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4355162992283465183377169 3266372244212598887532877)
      ·
        refine ⟨1224889591579724582824829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3266372244212598887532877 1224889591579724582824829)
        ·
          refine ⟨459333596842396718559311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1224889591579724582824829 459333596842396718559311)
          ·
            refine ⟨689000395263595077838967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 459333596842396718559311 689000395263595077838967)
            ·
              refine ⟨1033500592895392616758451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 689000395263595077838967 1033500592895392616758451)
              ·
                refine ⟨1550250889343088925137677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1033500592895392616758451 1550250889343088925137677)
                ·
                  refine ⟨581344083503658346926629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1550250889343088925137677 581344083503658346926629)
                  ·
                    refine ⟨109002015656935940048743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 581344083503658346926629 109002015656935940048743)
                    ·
                      rfl

theorem cell22_318421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 3, 4].length) (baseStart_318421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_318421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_318421 prefixEnd_318421 := by exact prefixLift 318421
  have htrace : WordTrace (prefixWord ++ tailWord_318421) baseStart_318421 baseEnd_318421 := by
    simpa [prefixWord, tailWord_318421, baseEnd_318421] using wordTrace_append hprefix tailTrace_318421
  have hstable : (prefixWord ++ tailWord_318421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318421).length < 2 ^ (prefixWord ++ tailWord_318421).sum := by decide
  have hdescent : baseEnd_318421 < baseStart_318421 := by decide
  rcases family_descends (prefixWord ++ tailWord_318421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318447 : List Nat := [1, 1, 2, 1, 4, 13]
def baseStart_318447 : Nat := 118140960795 + 318447 * 2 ^ 59
def prefixEnd_318447 : Nat := 4983230072969 + 3 ^ 40 * 318447 * 2
def baseEnd_318447 : Nat := 1345813777633093072823

theorem tailTrace_318447 : CollatzResearch.WordTrace tailWord_318447 prefixEnd_318447 1345813777633093072823 := by
  unfold tailWord_318447
  simp only [CollatzResearch.WordTrace]
  refine ⟨11614716277328380262785595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7743144184885586841857063 11614716277328380262785595)
  ·
    refine ⟨17422074415992570394178393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11614716277328380262785595 17422074415992570394178393)
    ·
      refine ⟨13066555811994427795633795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17422074415992570394178393 13066555811994427795633795)
      ·
        refine ⟨19599833717991641693450693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13066555811994427795633795 19599833717991641693450693)
        ·
          refine ⟨3674968822123432817522005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19599833717991641693450693 3674968822123432817522005)
          ·
            refine ⟨1345813777633093072823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 3674968822123432817522005 1345813777633093072823)
            ·
              rfl

theorem cell22_318447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 13].length) (baseStart_318447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_318447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_318447 prefixEnd_318447 := by exact prefixLift 318447
  have htrace : WordTrace (prefixWord ++ tailWord_318447) baseStart_318447 baseEnd_318447 := by
    simpa [prefixWord, tailWord_318447, baseEnd_318447] using wordTrace_append hprefix tailTrace_318447
  have hstable : (prefixWord ++ tailWord_318447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318447).length < 2 ^ (prefixWord ++ tailWord_318447).sum := by decide
  have hdescent : baseEnd_318447 < baseStart_318447 := by decide
  rcases family_descends (prefixWord ++ tailWord_318447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318513 : List Nat := [1, 2, 2, 3, 1, 2, 1, 6, 1, 3]
def baseStart_318513 : Nat := 118140960795 + 318513 * 2 ^ 59
def prefixEnd_318513 : Nat := 4983230072969 + 3 ^ 40 * 318513 * 2
def baseEnd_318513 : Nat := 109033509137078366748461

theorem tailTrace_318513 : CollatzResearch.WordTrace tailWord_318513 prefixEnd_318513 109033509137078366748461 := by
  unfold tailWord_318513
  simp only [CollatzResearch.WordTrace]
  refine ⟨11617123495089273534688193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7744748996726182356458795 11617123495089273534688193)
  ·
    refine ⟨8712842621316955151016145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11617123495089273534688193 8712842621316955151016145)
    ·
      refine ⟨6534631965987716363262109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8712842621316955151016145 6534631965987716363262109)
      ·
        refine ⟨2450486987245393636223291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6534631965987716363262109 2450486987245393636223291)
        ·
          refine ⟨3675730480868090454334937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2450486987245393636223291 3675730480868090454334937)
          ·
            refine ⟨2756797860651067840751203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3675730480868090454334937 2756797860651067840751203)
            ·
              refine ⟨4135196790976601761126805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2756797860651067840751203 4135196790976601761126805)
              ·
                refine ⟨193837349577028207552819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4135196790976601761126805 193837349577028207552819)
                ·
                  refine ⟨290756024365542311329229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 193837349577028207552819 290756024365542311329229)
                  ·
                    refine ⟨109033509137078366748461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 290756024365542311329229 109033509137078366748461)
                    ·
                      rfl

theorem cell22_318513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 6, 1, 3].length) (baseStart_318513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_318513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_318513 prefixEnd_318513 := by exact prefixLift 318513
  have htrace : WordTrace (prefixWord ++ tailWord_318513) baseStart_318513 baseEnd_318513 := by
    simpa [prefixWord, tailWord_318513, baseEnd_318513] using wordTrace_append hprefix tailTrace_318513
  have hstable : (prefixWord ++ tailWord_318513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318513).length < 2 ^ (prefixWord ++ tailWord_318513).sum := by decide
  have hdescent : baseEnd_318513 < baseStart_318513 := by decide
  rcases family_descends (prefixWord ++ tailWord_318513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318584 : List Nat := [2, 1, 2, 1, 1, 1, 4, 1, 3, 6]
def baseStart_318584 : Nat := 118140960795 + 318584 * 2 ^ 59
def prefixEnd_318584 : Nat := 4983230072969 + 3 ^ 40 * 318584 * 2
def baseEnd_318584 : Nat := 109057813888057848223243

theorem tailTrace_318584 : CollatzResearch.WordTrace tailWord_318584 prefixEnd_318584 109057813888057848223243 := by
  unfold tailWord_318584
  simp only [CollatzResearch.WordTrace]
  refine ⟨5809856538916026330261403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7746475385221368440348537 5809856538916026330261403)
  ·
    refine ⟨8714784808374039495392105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5809856538916026330261403 8714784808374039495392105)
    ·
      refine ⟨6536088606280529621544079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8714784808374039495392105 6536088606280529621544079)
      ·
        refine ⟨9804132909420794432316119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6536088606280529621544079 9804132909420794432316119)
        ·
          refine ⟨14706199364131191648474179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9804132909420794432316119 14706199364131191648474179)
          ·
            refine ⟨22059299046196787472711269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14706199364131191648474179 22059299046196787472711269)
            ·
              refine ⟨4136118571161897651133363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22059299046196787472711269 4136118571161897651133363)
              ·
                refine ⟨6204177856742846476700045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4136118571161897651133363 6204177856742846476700045)
                ·
                  refine ⟨2326566696278567428762517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6204177856742846476700045 2326566696278567428762517)
                  ·
                    refine ⟨109057813888057848223243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2326566696278567428762517 109057813888057848223243)
                    ·
                      rfl

theorem cell22_318584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 3, 6].length) (baseStart_318584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_318584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_318584 prefixEnd_318584 := by exact prefixLift 318584
  have htrace : WordTrace (prefixWord ++ tailWord_318584) baseStart_318584 baseEnd_318584 := by
    simpa [prefixWord, tailWord_318584, baseEnd_318584] using wordTrace_append hprefix tailTrace_318584
  have hstable : (prefixWord ++ tailWord_318584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318584).length < 2 ^ (prefixWord ++ tailWord_318584).sum := by decide
  have hdescent : baseEnd_318584 < baseStart_318584 := by decide
  rcases family_descends (prefixWord ++ tailWord_318584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318601 : List Nat := [1, 2, 1, 1, 4, 3, 1, 3, 2, 4]
def baseStart_318601 : Nat := 118140960795 + 318601 * 2 ^ 59
def prefixEnd_318601 : Nat := 4983230072969 + 3 ^ 40 * 318601 * 2
def baseEnd_318601 : Nat := 109063633335475470548191

theorem tailTrace_318601 : CollatzResearch.WordTrace tailWord_318601 prefixEnd_318601 109063633335475470548191 := by
  unfold tailWord_318601
  simp only [CollatzResearch.WordTrace]
  refine ⟨11620333118770464563891657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7746888745846976375927771 11620333118770464563891657)
  ·
    refine ⟨8715249839077848422918743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11620333118770464563891657 8715249839077848422918743)
    ·
      refine ⟨13072874758616772634378115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8715249839077848422918743 13072874758616772634378115)
      ·
        refine ⟨19609312137925158951567173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13072874758616772634378115 19609312137925158951567173)
        ·
          refine ⟨3676746025860967303418845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19609312137925158951567173 3676746025860967303418845)
          ·
            refine ⟨1378779759697862738782067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3676746025860967303418845 1378779759697862738782067)
            ·
              refine ⟨2068169639546794108173101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1378779759697862738782067 2068169639546794108173101)
              ·
                refine ⟨775563614830047790564913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2068169639546794108173101 775563614830047790564913)
                ·
                  refine ⟨581672711122535842923685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 775563614830047790564913 581672711122535842923685)
                  ·
                    refine ⟨109063633335475470548191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 581672711122535842923685 109063633335475470548191)
                    ·
                      rfl

theorem cell22_318601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 3, 2, 4].length) (baseStart_318601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_318601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_318601 prefixEnd_318601 := by exact prefixLift 318601
  have htrace : WordTrace (prefixWord ++ tailWord_318601) baseStart_318601 baseEnd_318601 := by
    simpa [prefixWord, tailWord_318601, baseEnd_318601] using wordTrace_append hprefix tailTrace_318601
  have hstable : (prefixWord ++ tailWord_318601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318601).length < 2 ^ (prefixWord ++ tailWord_318601).sum := by decide
  have hdescent : baseEnd_318601 < baseStart_318601 := by decide
  rcases family_descends (prefixWord ++ tailWord_318601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318618 : List Nat := [3, 1, 1, 5, 1, 1, 2, 2, 2, 4]
def baseStart_318618 : Nat := 118140960795 + 318618 * 2 ^ 59
def prefixEnd_318618 : Nat := 4983230072969 + 3 ^ 40 * 318618 * 2
def baseEnd_318618 : Nat := 109069452782893092873139

theorem tailTrace_318618 : CollatzResearch.WordTrace tailWord_318618 prefixEnd_318618 109069452782893092873139 := by
  unfold tailWord_318618
  simp only [CollatzResearch.WordTrace]
  refine ⟨2905238289927219116815127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7747302106472584311507005 2905238289927219116815127)
  ·
    refine ⟨4357857434890828675222691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2905238289927219116815127 4357857434890828675222691)
    ·
      refine ⟨6536786152336243012834037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4357857434890828675222691 6536786152336243012834037)
      ·
        refine ⟨612823701781522782453191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6536786152336243012834037 612823701781522782453191)
        ·
          refine ⟨919235552672284173679787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 612823701781522782453191 919235552672284173679787)
          ·
            refine ⟨1378853329008426260519681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 919235552672284173679787 1378853329008426260519681)
            ·
              refine ⟨1034139996756319695389761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1378853329008426260519681 1034139996756319695389761)
              ·
                refine ⟨775604997567239771542321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1034139996756319695389761 775604997567239771542321)
                ·
                  refine ⟨581703748175429828656741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 775604997567239771542321 581703748175429828656741)
                  ·
                    refine ⟨109069452782893092873139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 581703748175429828656741 109069452782893092873139)
                    ·
                      rfl

theorem cell22_318618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 2, 2, 4].length) (baseStart_318618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_318618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_318618 prefixEnd_318618 := by exact prefixLift 318618
  have htrace : WordTrace (prefixWord ++ tailWord_318618) baseStart_318618 baseEnd_318618 := by
    simpa [prefixWord, tailWord_318618, baseEnd_318618] using wordTrace_append hprefix tailTrace_318618
  have hstable : (prefixWord ++ tailWord_318618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318618).length < 2 ^ (prefixWord ++ tailWord_318618).sum := by decide
  have hdescent : baseEnd_318618 < baseStart_318618 := by decide
  rcases family_descends (prefixWord ++ tailWord_318618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318620 : List Nat := [2, 2, 3, 2, 1, 3, 2, 2, 2, 3]
def baseStart_318620 : Nat := 118140960795 + 318620 * 2 ^ 59
def prefixEnd_318620 : Nat := 4983230072969 + 3 ^ 40 * 318620 * 2
def baseEnd_318620 : Nat := 109070137423765754323133

theorem tailTrace_318620 : CollatzResearch.WordTrace tailWord_318620 prefixEnd_318620 109070137423765754323133 := by
  unfold tailWord_318620
  simp only [CollatzResearch.WordTrace]
  refine ⟨5810513052850815404416657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7747350737134420539222209 5810513052850815404416657)
  ·
    refine ⟨4357884789638111553312493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5810513052850815404416657 4357884789638111553312493)
    ·
      refine ⟨1634206796114291832492185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4357884789638111553312493 1634206796114291832492185)
      ·
        refine ⟨1225655097085718874369139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1634206796114291832492185 1225655097085718874369139)
        ·
          refine ⟨1838482645628578311553709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1225655097085718874369139 1838482645628578311553709)
          ·
            refine ⟨689430992110716866832641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1838482645628578311553709 689430992110716866832641)
            ·
              refine ⟨517073244083037650124481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 689430992110716866832641 517073244083037650124481)
              ·
                refine ⟨387804933062278237593361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 517073244083037650124481 387804933062278237593361)
                ·
                  refine ⟨290853699796708678195021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 387804933062278237593361 290853699796708678195021)
                  ·
                    refine ⟨109070137423765754323133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 290853699796708678195021 109070137423765754323133)
                    ·
                      rfl

theorem cell22_318620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 2, 2, 3].length) (baseStart_318620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_318620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_318620 prefixEnd_318620 := by exact prefixLift 318620
  have htrace : WordTrace (prefixWord ++ tailWord_318620) baseStart_318620 baseEnd_318620 := by
    simpa [prefixWord, tailWord_318620, baseEnd_318620] using wordTrace_append hprefix tailTrace_318620
  have hstable : (prefixWord ++ tailWord_318620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318620).length < 2 ^ (prefixWord ++ tailWord_318620).sum := by decide
  have hdescent : baseEnd_318620 < baseStart_318620 := by decide
  rcases family_descends (prefixWord ++ tailWord_318620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318622 : List Nat := [4, 3, 1, 1, 2, 1, 4, 2, 4]
def baseStart_318622 : Nat := 118140960795 + 318622 * 2 ^ 59
def prefixEnd_318622 : Nat := 4983230072969 + 3 ^ 40 * 318622 * 2
def baseEnd_318622 : Nat := 36356940688212805257709

theorem tailTrace_318622 : CollatzResearch.WordTrace tailWord_318622 prefixEnd_318622 36356940688212805257709 := by
  unfold tailWord_318622
  simp only [CollatzResearch.WordTrace]
  refine ⟨1452637381461798143800765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7747399367796256766937413 1452637381461798143800765)
  ·
    refine ⟨544739018048174303925287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1452637381461798143800765 544739018048174303925287)
    ·
      refine ⟨817108527072261455887931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 544739018048174303925287 817108527072261455887931)
      ·
        refine ⟨1225662790608392183831897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 817108527072261455887931 1225662790608392183831897)
        ·
          refine ⟨919247092956294137873923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1225662790608392183831897 919247092956294137873923)
          ·
            refine ⟨1378870639434441206810885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 919247092956294137873923 1378870639434441206810885)
            ·
              refine ⟨258538244893957726277041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1378870639434441206810885 258538244893957726277041)
              ·
                refine ⟨193903683670468294707781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 258538244893957726277041 193903683670468294707781)
                ·
                  refine ⟨36356940688212805257709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 193903683670468294707781 36356940688212805257709)
                  ·
                    rfl

theorem cell22_318622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_318622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_318622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_318622 prefixEnd_318622 := by exact prefixLift 318622
  have htrace : WordTrace (prefixWord ++ tailWord_318622) baseStart_318622 baseEnd_318622 := by
    simpa [prefixWord, tailWord_318622, baseEnd_318622] using wordTrace_append hprefix tailTrace_318622
  have hstable : (prefixWord ++ tailWord_318622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318622).length < 2 ^ (prefixWord ++ tailWord_318622).sum := by decide
  have hdescent : baseEnd_318622 < baseStart_318622 := by decide
  rcases family_descends (prefixWord ++ tailWord_318622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318755 : List Nat := [1, 1, 1, 4, 2, 4, 1, 3, 2, 3]
def baseStart_318755 : Nat := 118140960795 + 318755 * 2 ^ 59
def prefixEnd_318755 : Nat := 4983230072969 + 3 ^ 40 * 318755 * 2
def baseEnd_318755 : Nat := 109116350682670402197719

theorem tailTrace_318755 : CollatzResearch.WordTrace tailWord_318755 prefixEnd_318755 109116350682670402197719 := by
  unfold tailWord_318755
  simp only [CollatzResearch.WordTrace]
  refine ⟨11625949960212548864997719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7750633306808365909998479 11625949960212548864997719)
  ·
    refine ⟨17438924940318823297496579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11625949960212548864997719 17438924940318823297496579)
    ·
      refine ⟨26158387410478234946244869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17438924940318823297496579 26158387410478234946244869)
      ·
        refine ⟨4904697639464669052420913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26158387410478234946244869 4904697639464669052420913)
        ·
          refine ⟨3678523229598501789315685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4904697639464669052420913 3678523229598501789315685)
          ·
            refine ⟨689723105549719085496691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3678523229598501789315685 689723105549719085496691)
            ·
              refine ⟨1034584658324578628245037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 689723105549719085496691 1034584658324578628245037)
              ·
                refine ⟨387969246871716985591889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1034584658324578628245037 387969246871716985591889)
                ·
                  refine ⟨290976935153787739193917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 387969246871716985591889 290976935153787739193917)
                  ·
                    refine ⟨109116350682670402197719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 290976935153787739193917 109116350682670402197719)
                    ·
                      rfl

theorem cell22_318755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 3, 2, 3].length) (baseStart_318755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_318755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_318755 prefixEnd_318755 := by exact prefixLift 318755
  have htrace : WordTrace (prefixWord ++ tailWord_318755) baseStart_318755 baseEnd_318755 := by
    simpa [prefixWord, tailWord_318755, baseEnd_318755] using wordTrace_append hprefix tailTrace_318755
  have hstable : (prefixWord ++ tailWord_318755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318755).length < 2 ^ (prefixWord ++ tailWord_318755).sum := by decide
  have hdescent : baseEnd_318755 < baseStart_318755 := by decide
  rcases family_descends (prefixWord ++ tailWord_318755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318770 : List Nat := [3, 2, 1, 1, 4, 2, 2, 1, 2, 4]
def baseStart_318770 : Nat := 118140960795 + 318770 * 2 ^ 59
def prefixEnd_318770 : Nat := 4983230072969 + 3 ^ 40 * 318770 * 2
def baseEnd_318770 : Nat := 109121485489215363072673

theorem tailTrace_318770 : CollatzResearch.WordTrace tailWord_318770 prefixEnd_318770 109121485489215363072673 := by
  unfold tailWord_318770
  simp only [CollatzResearch.WordTrace]
  refine ⟨2906624263789551606698441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7750998036772137617862509 2906624263789551606698441)
  ·
    refine ⟨2179968197842163705023831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2906624263789551606698441 2179968197842163705023831)
    ·
      refine ⟨3269952296763245557535747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2179968197842163705023831 3269952296763245557535747)
      ·
        refine ⟨4904928445144868336303621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3269952296763245557535747 4904928445144868336303621)
        ·
          refine ⟨919674083464662813056929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4904928445144868336303621 919674083464662813056929)
          ·
            refine ⟨689755562598497109792697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 919674083464662813056929 689755562598497109792697)
            ·
              refine ⟨517316671948872832344523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 689755562598497109792697 517316671948872832344523)
              ·
                refine ⟨775975007923309248516785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 517316671948872832344523 775975007923309248516785)
                ·
                  refine ⟨581981255942481936387589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 775975007923309248516785 581981255942481936387589)
                  ·
                    refine ⟨109121485489215363072673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 581981255942481936387589 109121485489215363072673)
                    ·
                      rfl

theorem cell22_318770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 1, 2, 4].length) (baseStart_318770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_318770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_318770 prefixEnd_318770 := by exact prefixLift 318770
  have htrace : WordTrace (prefixWord ++ tailWord_318770) baseStart_318770 baseEnd_318770 := by
    simpa [prefixWord, tailWord_318770, baseEnd_318770] using wordTrace_append hprefix tailTrace_318770
  have hstable : (prefixWord ++ tailWord_318770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318770).length < 2 ^ (prefixWord ++ tailWord_318770).sum := by decide
  have hdescent : baseEnd_318770 < baseStart_318770 := by decide
  rcases family_descends (prefixWord ++ tailWord_318770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318806 : List Nat := [5, 2, 3, 1, 1, 1, 2, 1, 1, 5]
def baseStart_318806 : Nat := 118140960795 + 318806 * 2 ^ 59
def prefixEnd_318806 : Nat := 4983230072969 + 3 ^ 40 * 318806 * 2
def baseEnd_318806 : Nat := 109133809024923269172563

theorem tailTrace_318806 : CollatzResearch.WordTrace tailWord_318806 prefixEnd_318806 109133809024923269172563 := by
  unfold tailWord_318806
  simp only [CollatzResearch.WordTrace]
  refine ⟨726738130189236535944017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7751873388685189716736181 726738130189236535944017)
  ·
    refine ⟨545053597641927401958013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 726738130189236535944017 545053597641927401958013)
    ·
      refine ⟨204395099115722775734255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 545053597641927401958013 204395099115722775734255)
      ·
        refine ⟨306592648673584163601383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204395099115722775734255 306592648673584163601383)
        ·
          refine ⟨459888973010376245402075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 306592648673584163601383 459888973010376245402075)
          ·
            refine ⟨689833459515564368103113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 459888973010376245402075 689833459515564368103113)
            ·
              refine ⟨517375094636673276077335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 689833459515564368103113 517375094636673276077335)
              ·
                refine ⟨776062641955009914116003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 517375094636673276077335 776062641955009914116003)
                ·
                  refine ⟨1164093962932514871174005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 776062641955009914116003 1164093962932514871174005)
                  ·
                    refine ⟨109133809024923269172563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1164093962932514871174005 109133809024923269172563)
                    ·
                      rfl

theorem cell22_318806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_318806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_318806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_318806 prefixEnd_318806 := by exact prefixLift 318806
  have htrace : WordTrace (prefixWord ++ tailWord_318806) baseStart_318806 baseEnd_318806 := by
    simpa [prefixWord, tailWord_318806, baseEnd_318806] using wordTrace_append hprefix tailTrace_318806
  have hstable : (prefixWord ++ tailWord_318806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318806).length < 2 ^ (prefixWord ++ tailWord_318806).sum := by decide
  have hdescent : baseEnd_318806 < baseStart_318806 := by decide
  rcases family_descends (prefixWord ++ tailWord_318806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318877 : List Nat := [1, 4, 2, 1, 3, 2, 2, 2, 1, 4]
def baseStart_318877 : Nat := 118140960795 + 318877 * 2 ^ 59
def prefixEnd_318877 : Nat := 4983230072969 + 3 ^ 40 * 318877 * 2
def baseEnd_318877 : Nat := 109158113775902750647345

theorem tailTrace_318877 : CollatzResearch.WordTrace tailWord_318877 prefixEnd_318877 109158113775902750647345 := by
  unfold tailWord_318877
  simp only [CollatzResearch.WordTrace]
  refine ⟨11630399665770563700938885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7753599777180375800625923 11630399665770563700938885)
  ·
    refine ⟨2180699937331980693926041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11630399665770563700938885 2180699937331980693926041)
    ·
      refine ⟨1635524952998985520444531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2180699937331980693926041 1635524952998985520444531)
      ·
        refine ⟨2453287429498478280666797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1635524952998985520444531 2453287429498478280666797)
        ·
          refine ⟨919982786061929355250049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2453287429498478280666797 919982786061929355250049)
          ·
            refine ⟨689987089546447016437537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 919982786061929355250049 689987089546447016437537)
            ·
              refine ⟨517490317159835262328153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 689987089546447016437537 517490317159835262328153)
              ·
                refine ⟨388117737869876446746115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 517490317159835262328153 388117737869876446746115)
                ·
                  refine ⟨582176606804814670119173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 388117737869876446746115 582176606804814670119173)
                  ·
                    refine ⟨109158113775902750647345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 582176606804814670119173 109158113775902750647345)
                    ·
                      rfl

theorem cell22_318877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_318877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_318877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_318877 prefixEnd_318877 := by exact prefixLift 318877
  have htrace : WordTrace (prefixWord ++ tailWord_318877) baseStart_318877 baseEnd_318877 := by
    simpa [prefixWord, tailWord_318877, baseEnd_318877] using wordTrace_append hprefix tailTrace_318877
  have hstable : (prefixWord ++ tailWord_318877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318877).length < 2 ^ (prefixWord ++ tailWord_318877).sum := by decide
  have hdescent : baseEnd_318877 < baseStart_318877 := by decide
  rcases family_descends (prefixWord ++ tailWord_318877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318924 : List Nat := [2, 2, 1, 4, 2, 1, 4, 1, 2, 3]
def baseStart_318924 : Nat := 118140960795 + 318924 * 2 ^ 59
def prefixEnd_318924 : Nat := 4983230072969 + 3 ^ 40 * 318924 * 2
def baseEnd_318924 : Nat := 109174202836410294722201

theorem tailTrace_318924 : CollatzResearch.WordTrace tailWord_318924 prefixEnd_318924 109174202836410294722201 := by
  unfold tailWord_318924
  simp only [CollatzResearch.WordTrace]
  refine ⟨5816056948300145363949913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7754742597733527151933217 5816056948300145363949913)
  ·
    refine ⟨4362042711225109022962435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5816056948300145363949913 4362042711225109022962435)
    ·
      refine ⟨6543064066837663534443653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4362042711225109022962435 6543064066837663534443653)
      ·
        refine ⟨1226824512532061912708185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6543064066837663534443653 1226824512532061912708185)
        ·
          refine ⟨920118384399046434531139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1226824512532061912708185 920118384399046434531139)
          ·
            refine ⟨1380177576598569651796709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 920118384399046434531139 1380177576598569651796709)
            ·
              refine ⟨258783295612231809711883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1380177576598569651796709 258783295612231809711883)
              ·
                refine ⟨388174943418347714567825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 258783295612231809711883 388174943418347714567825)
                ·
                  refine ⟨291131207563760785925869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 388174943418347714567825 291131207563760785925869)
                  ·
                    refine ⟨109174202836410294722201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 291131207563760785925869 109174202836410294722201)
                    ·
                      rfl

theorem cell22_318924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 4, 1, 2, 3].length) (baseStart_318924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_318924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_318924 prefixEnd_318924 := by exact prefixLift 318924
  have htrace : WordTrace (prefixWord ++ tailWord_318924) baseStart_318924 baseEnd_318924 := by
    simpa [prefixWord, tailWord_318924, baseEnd_318924] using wordTrace_append hprefix tailTrace_318924
  have hstable : (prefixWord ++ tailWord_318924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318924).length < 2 ^ (prefixWord ++ tailWord_318924).sum := by decide
  have hdescent : baseEnd_318924 < baseStart_318924 := by decide
  rcases family_descends (prefixWord ++ tailWord_318924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318935 : List Nat := [1, 1, 3, 2, 1, 1, 1, 6, 3, 3]
def baseStart_318935 : Nat := 118140960795 + 318935 * 2 ^ 59
def prefixEnd_318935 : Nat := 4983230072969 + 3 ^ 40 * 318935 * 2
def baseEnd_318935 : Nat := 109177968361209932697167

theorem tailTrace_318935 : CollatzResearch.WordTrace tailWord_318935 prefixEnd_318935 109177968361209932697167 := by
  unfold tailWord_318935
  simp only [CollatzResearch.WordTrace]
  refine ⟨11632515099560439606550259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7755010066373626404366839 11632515099560439606550259)
  ·
    refine ⟨17448772649340659409825389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11632515099560439606550259 17448772649340659409825389)
    ·
      refine ⟨6543289743502747278684521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17448772649340659409825389 6543289743502747278684521)
      ·
        refine ⟨4907467307627060459013391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6543289743502747278684521 4907467307627060459013391)
        ·
          refine ⟨7361200961440590688520087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4907467307627060459013391 7361200961440590688520087)
          ·
            refine ⟨11041801442160886032780131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7361200961440590688520087 11041801442160886032780131)
            ·
              refine ⟨16562702163241329049170197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11041801442160886032780131 16562702163241329049170197)
              ·
                refine ⟨776376663901937299179853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16562702163241329049170197 776376663901937299179853)
                ·
                  refine ⟨291141248963226487192445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 776376663901937299179853 291141248963226487192445)
                  ·
                    refine ⟨109177968361209932697167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 291141248963226487192445 109177968361209932697167)
                    ·
                      rfl

theorem cell22_318935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 6, 3, 3].length) (baseStart_318935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_318935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_318935 prefixEnd_318935 := by exact prefixLift 318935
  have htrace : WordTrace (prefixWord ++ tailWord_318935) baseStart_318935 baseEnd_318935 := by
    simpa [prefixWord, tailWord_318935, baseEnd_318935] using wordTrace_append hprefix tailTrace_318935
  have hstable : (prefixWord ++ tailWord_318935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318935).length < 2 ^ (prefixWord ++ tailWord_318935).sum := by decide
  have hdescent : baseEnd_318935 < baseStart_318935 := by decide
  rcases family_descends (prefixWord ++ tailWord_318935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318948 : List Nat := [2, 3, 1, 1, 1, 1, 1, 3, 9]
def baseStart_318948 : Nat := 118140960795 + 318948 * 2 ^ 59
def prefixEnd_318948 : Nat := 4983230072969 + 3 ^ 40 * 318948 * 2
def baseEnd_318948 : Nat := 36394139508960744040709

theorem tailTrace_318948 : CollatzResearch.WordTrace tailWord_318948 prefixEnd_318948 36394139508960744040709 := by
  unfold tailWord_318948
  simp only [CollatzResearch.WordTrace]
  refine ⟨5816494624256671413386749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7755326165675561884515665 5816494624256671413386749)
  ·
    refine ⟨2181185484096251780020031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5816494624256671413386749 2181185484096251780020031)
    ·
      refine ⟨3271778226144377670030047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2181185484096251780020031 3271778226144377670030047)
      ·
        refine ⟨4907667339216566505045071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3271778226144377670030047 4907667339216566505045071)
        ·
          refine ⟨7361501008824849757567607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4907667339216566505045071 7361501008824849757567607)
          ·
            refine ⟨11042251513237274636351411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7361501008824849757567607 11042251513237274636351411)
            ·
              refine ⟨16563377269855911954527117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11042251513237274636351411 16563377269855911954527117)
              ·
                refine ⟨6211266476195966982947669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16563377269855911954527117 6211266476195966982947669)
                ·
                  refine ⟨36394139508960744040709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 6211266476195966982947669 36394139508960744040709)
                  ·
                    rfl

theorem cell22_318948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 9].length) (baseStart_318948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_318948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_318948 prefixEnd_318948 := by exact prefixLift 318948
  have htrace : WordTrace (prefixWord ++ tailWord_318948) baseStart_318948 baseEnd_318948 := by
    simpa [prefixWord, tailWord_318948, baseEnd_318948] using wordTrace_append hprefix tailTrace_318948
  have hstable : (prefixWord ++ tailWord_318948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318948).length < 2 ^ (prefixWord ++ tailWord_318948).sum := by decide
  have hdescent : baseEnd_318948 < baseStart_318948 := by decide
  rcases family_descends (prefixWord ++ tailWord_318948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318995 : List Nat := [1, 1, 1, 2, 1, 6, 2, 1, 3, 4]
def baseStart_318995 : Nat := 118140960795 + 318995 * 2 ^ 59
def prefixEnd_318995 : Nat := 4983230072969 + 3 ^ 40 * 318995 * 2
def baseEnd_318995 : Nat := 109198507587389776196983

theorem tailTrace_318995 : CollatzResearch.WordTrace tailWord_318995 prefixEnd_318995 109198507587389776196983 := by
  unfold tailWord_318995
  simp only [CollatzResearch.WordTrace]
  refine ⟨11634703479343069853734439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7756468986228713235822959 11634703479343069853734439)
  ·
    refine ⟨17452055219014604780601659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11634703479343069853734439 17452055219014604780601659)
    ·
      refine ⟨26178082828521907170902489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17452055219014604780601659 26178082828521907170902489)
      ·
        refine ⟨19633562121391430378176867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26178082828521907170902489 19633562121391430378176867)
        ·
          refine ⟨29450343182087145567265301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19633562121391430378176867 29450343182087145567265301)
          ·
            refine ⟨1380484836660334948465561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 29450343182087145567265301 1380484836660334948465561)
            ·
              refine ⟨1035363627495251211349171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1380484836660334948465561 1035363627495251211349171)
              ·
                refine ⟨1553045441242876817023757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1035363627495251211349171 1553045441242876817023757)
                ·
                  refine ⟨582392040466078806383909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1553045441242876817023757 582392040466078806383909)
                  ·
                    refine ⟨109198507587389776196983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 582392040466078806383909 109198507587389776196983)
                    ·
                      rfl

theorem cell22_318995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 3, 4].length) (baseStart_318995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_318995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_318995 prefixEnd_318995 := by exact prefixLift 318995
  have htrace : WordTrace (prefixWord ++ tailWord_318995) baseStart_318995 baseEnd_318995 := by
    simpa [prefixWord, tailWord_318995, baseEnd_318995] using wordTrace_append hprefix tailTrace_318995
  have hstable : (prefixWord ++ tailWord_318995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318995).length < 2 ^ (prefixWord ++ tailWord_318995).sum := by decide
  have hdescent : baseEnd_318995 < baseStart_318995 := by decide
  rcases family_descends (prefixWord ++ tailWord_318995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319016 : List Nat := [2, 1, 5, 2, 3, 1, 1, 2, 5]
def baseStart_319016 : Nat := 118140960795 + 319016 * 2 ^ 59
def prefixEnd_319016 : Nat := 4983230072969 + 3 ^ 40 * 319016 * 2
def baseEnd_319016 : Nat := 36401898772184240473973

theorem tailTrace_319016 : CollatzResearch.WordTrace tailWord_319016 prefixEnd_319016 36401898772184240473973 := by
  unfold tailWord_319016
  simp only [CollatzResearch.WordTrace]
  refine ⟨5817734706133495220124451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7756979608177993626832601 5817734706133495220124451)
  ·
    refine ⟨8726602059200242830186677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5817734706133495220124451 8726602059200242830186677)
    ·
      refine ⟨818118943050022765330001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8726602059200242830186677 818118943050022765330001)
      ·
        refine ⟨613589207287517073997501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 818118943050022765330001 613589207287517073997501)
        ·
          refine ⟨230095952732818902749063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 613589207287517073997501 230095952732818902749063)
          ·
            refine ⟨345143929099228354123595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230095952732818902749063 345143929099228354123595)
            ·
              refine ⟨517715893648842531185393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 345143929099228354123595 517715893648842531185393)
              ·
                refine ⟨388286920236631898389045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 517715893648842531185393 388286920236631898389045)
                ·
                  refine ⟨36401898772184240473973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 388286920236631898389045 36401898772184240473973)
                  ·
                    rfl

theorem cell22_319016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 2, 5].length) (baseStart_319016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_319016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_319016 prefixEnd_319016 := by exact prefixLift 319016
  have htrace : WordTrace (prefixWord ++ tailWord_319016) baseStart_319016 baseEnd_319016 := by
    simpa [prefixWord, tailWord_319016, baseEnd_319016] using wordTrace_append hprefix tailTrace_319016
  have hstable : (prefixWord ++ tailWord_319016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319016).length < 2 ^ (prefixWord ++ tailWord_319016).sum := by decide
  have hdescent : baseEnd_319016 < baseStart_319016 := by decide
  rcases family_descends (prefixWord ++ tailWord_319016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319027 : List Nat := [1, 1, 1, 2, 4, 3, 2, 4, 4]
def baseStart_319027 : Nat := 118140960795 + 319027 * 2 ^ 59
def prefixEnd_319027 : Nat := 4983230072969 + 3 ^ 40 * 319027 * 2
def baseEnd_319027 : Nat := 36403153947117453132295

theorem tailTrace_319027 : CollatzResearch.WordTrace tailWord_319027 prefixEnd_319027 36403153947117453132295 := by
  unfold tailWord_319027
  simp only [CollatzResearch.WordTrace]
  refine ⟨11635870615227139318899335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7757247076818092879266223 11635870615227139318899335)
  ·
    refine ⟨17453805922840708978349003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11635870615227139318899335 17453805922840708978349003)
    ·
      refine ⟨26180708884261063467523505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17453805922840708978349003 26180708884261063467523505)
      ·
        refine ⟨19635531663195797600642629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26180708884261063467523505 19635531663195797600642629)
        ·
          refine ⟨3681662186849212050120493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19635531663195797600642629 3681662186849212050120493)
          ·
            refine ⟨1380623320068454518795185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3681662186849212050120493 1380623320068454518795185)
            ·
              refine ⟨1035467490051340889096389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1380623320068454518795185 1035467490051340889096389)
              ·
                refine ⟨194150154384626416705573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1035467490051340889096389 194150154384626416705573)
                ·
                  refine ⟨36403153947117453132295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 194150154384626416705573 36403153947117453132295)
                  ·
                    rfl

theorem cell22_319027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 4, 4].length) (baseStart_319027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_319027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_319027 prefixEnd_319027 := by exact prefixLift 319027
  have htrace : WordTrace (prefixWord ++ tailWord_319027) baseStart_319027 baseEnd_319027 := by
    simpa [prefixWord, tailWord_319027, baseEnd_319027] using wordTrace_append hprefix tailTrace_319027
  have hstable : (prefixWord ++ tailWord_319027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319027).length < 2 ^ (prefixWord ++ tailWord_319027).sum := by decide
  have hdescent : baseEnd_319027 < baseStart_319027 := by decide
  rcases family_descends (prefixWord ++ tailWord_319027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319093 : List Nat := [1, 3, 4, 2, 1, 3, 2, 1, 2, 3]
def baseStart_319093 : Nat := 118140960795 + 319093 * 2 ^ 59
def prefixEnd_319093 : Nat := 4983230072969 + 3 ^ 40 * 319093 * 2
def baseEnd_319093 : Nat := 109232054990150187246683

theorem tailTrace_319093 : CollatzResearch.WordTrace tailWord_319093 prefixEnd_319093 109232054990150187246683 := by
  unfold tailWord_319093
  simp only [CollatzResearch.WordTrace]
  refine ⟨11638277832988032590801933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7758851888658688393867955 11638277832988032590801933)
  ·
    refine ⟨4364354187370512221550725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11638277832988032590801933 4364354187370512221550725)
    ·
      refine ⟨818316410131971041540761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4364354187370512221550725 818316410131971041540761)
      ·
        refine ⟨613737307598978281155571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 818316410131971041540761 613737307598978281155571)
        ·
          refine ⟨920605961398467421733357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 613737307598978281155571 920605961398467421733357)
          ·
            refine ⟨345227235524425283150009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 920605961398467421733357 345227235524425283150009)
            ·
              refine ⟨258920426643318962362507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 345227235524425283150009 258920426643318962362507)
              ·
                refine ⟨388380639964978443543761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 258920426643318962362507 388380639964978443543761)
                ·
                  refine ⟨291285479973733832657821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 388380639964978443543761 291285479973733832657821)
                  ·
                    refine ⟨109232054990150187246683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 291285479973733832657821 109232054990150187246683)
                    ·
                      rfl

theorem cell22_319093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_319093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_319093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_319093 prefixEnd_319093 := by exact prefixLift 319093
  have htrace : WordTrace (prefixWord ++ tailWord_319093) baseStart_319093 baseEnd_319093 := by
    simpa [prefixWord, tailWord_319093, baseEnd_319093] using wordTrace_append hprefix tailTrace_319093
  have hstable : (prefixWord ++ tailWord_319093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319093).length < 2 ^ (prefixWord ++ tailWord_319093).sum := by decide
  have hdescent : baseEnd_319093 < baseStart_319093 := by decide
  rcases family_descends (prefixWord ++ tailWord_319093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319134 : List Nat := [4, 3, 1, 1, 1, 2, 1, 4, 5]
def baseStart_319134 : Nat := 118140960795 + 319134 * 2 ^ 59
def prefixEnd_319134 : Nat := 4983230072969 + 3 ^ 40 * 319134 * 2
def baseEnd_319134 : Nat := 36415363376013248990519

theorem tailTrace_319134 : CollatzResearch.WordTrace tailWord_319134 prefixEnd_319134 36415363376013248990519 := by
  unfold tailWord_319134
  simp only [CollatzResearch.WordTrace]
  refine ⟨1454971653229937074130557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7759848817226331062029637 1454971653229937074130557)
  ·
    refine ⟨545614369961226402798959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1454971653229937074130557 545614369961226402798959)
    ·
      refine ⟨818421554941839604198439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 545614369961226402798959 818421554941839604198439)
      ·
        refine ⟨1227632332412759406297659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 818421554941839604198439 1227632332412759406297659)
        ·
          refine ⟨1841448498619139109446489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1227632332412759406297659 1841448498619139109446489)
          ·
            refine ⟨1381086373964354332084867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1841448498619139109446489 1381086373964354332084867)
            ·
              refine ⟨2071629560946531498127301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1381086373964354332084867 2071629560946531498127301)
              ·
                refine ⟨388430542677474655898869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2071629560946531498127301 388430542677474655898869)
                ·
                  refine ⟨36415363376013248990519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 388430542677474655898869 36415363376013248990519)
                  ·
                    rfl

theorem cell22_319134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_319134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_319134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_319134 prefixEnd_319134 := by exact prefixLift 319134
  have htrace : WordTrace (prefixWord ++ tailWord_319134) baseStart_319134 baseEnd_319134 := by
    simpa [prefixWord, tailWord_319134, baseEnd_319134] using wordTrace_append hprefix tailTrace_319134
  have hstable : (prefixWord ++ tailWord_319134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319134).length < 2 ^ (prefixWord ++ tailWord_319134).sum := by decide
  have hdescent : baseEnd_319134 < baseStart_319134 := by decide
  rcases family_descends (prefixWord ++ tailWord_319134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319162 : List Nat := [3, 1, 1, 1, 2, 5, 1, 2, 6]
def baseStart_319162 : Nat := 118140960795 + 319162 * 2 ^ 59
def prefixEnd_319162 : Nat := 4983230072969 + 3 ^ 40 * 319162 * 2
def baseEnd_319162 : Nat := 36418558366752335757157

theorem tailTrace_319162 : CollatzResearch.WordTrace tailWord_319162 prefixEnd_319162 36418558366752335757157 := by
  unfold tailWord_319162
  simp only [CollatzResearch.WordTrace]
  refine ⟨2910198617434514343765935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7760529646492038250042493 2910198617434514343765935)
  ·
    refine ⟨4365297926151771515648903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2910198617434514343765935 4365297926151771515648903)
    ·
      refine ⟨6547946889227657273473355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4365297926151771515648903 6547946889227657273473355)
      ·
        refine ⟨9821920333841485910210033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6547946889227657273473355 9821920333841485910210033)
        ·
          refine ⟨7366440250381114432657525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9821920333841485910210033 7366440250381114432657525)
          ·
            refine ⟨690603773473229478061643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7366440250381114432657525 690603773473229478061643)
            ·
              refine ⟨1035905660209844217092465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 690603773473229478061643 1035905660209844217092465)
              ·
                refine ⟨776929245157383162819349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1035905660209844217092465 776929245157383162819349)
                ·
                  refine ⟨36418558366752335757157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 776929245157383162819349 36418558366752335757157)
                  ·
                    rfl

theorem cell22_319162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 2, 6].length) (baseStart_319162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_319162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_319162 prefixEnd_319162 := by exact prefixLift 319162
  have htrace : WordTrace (prefixWord ++ tailWord_319162) baseStart_319162 baseEnd_319162 := by
    simpa [prefixWord, tailWord_319162, baseEnd_319162] using wordTrace_append hprefix tailTrace_319162
  have hstable : (prefixWord ++ tailWord_319162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319162).length < 2 ^ (prefixWord ++ tailWord_319162).sum := by decide
  have hdescent : baseEnd_319162 < baseStart_319162 := by decide
  rcases family_descends (prefixWord ++ tailWord_319162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319192 : List Nat := [2, 1, 2, 2, 3, 1, 2, 1, 4, 4]
def baseStart_319192 : Nat := 118140960795 + 319192 * 2 ^ 59
def prefixEnd_319192 : Nat := 4983230072969 + 3 ^ 40 * 319192 * 2
def baseEnd_319192 : Nat := 109265944713346929021379

theorem tailTrace_319192 : CollatzResearch.WordTrace tailWord_319192 prefixEnd_319192 109265944713346929021379 := by
  unfold tailWord_319192
  simp only [CollatzResearch.WordTrace]
  refine ⟨5820944329814686249327915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7761259106419581665770553 5820944329814686249327915)
  ·
    refine ⟨8731416494722029373991873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5820944329814686249327915 8731416494722029373991873)
    ·
      refine ⟨6548562371041522030493905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8731416494722029373991873 6548562371041522030493905)
      ·
        refine ⟨4911421778281141522870429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6548562371041522030493905 4911421778281141522870429)
        ·
          refine ⟨1841783166855428071076411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4911421778281141522870429 1841783166855428071076411)
          ·
            refine ⟨2762674750283142106614617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1841783166855428071076411 2762674750283142106614617)
            ·
              refine ⟨2072006062712356579960963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2762674750283142106614617 2072006062712356579960963)
              ·
                refine ⟨3108009094068534869941445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2072006062712356579960963 3108009094068534869941445)
                ·
                  refine ⟨582751705137850288114021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3108009094068534869941445 582751705137850288114021)
                  ·
                    refine ⟨109265944713346929021379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 582751705137850288114021 109265944713346929021379)
                    ·
                      rfl

theorem cell22_319192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 4, 4].length) (baseStart_319192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_319192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_319192 prefixEnd_319192 := by exact prefixLift 319192
  have htrace : WordTrace (prefixWord ++ tailWord_319192) baseStart_319192 baseEnd_319192 := by
    simpa [prefixWord, tailWord_319192, baseEnd_319192] using wordTrace_append hprefix tailTrace_319192
  have hstable : (prefixWord ++ tailWord_319192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319192).length < 2 ^ (prefixWord ++ tailWord_319192).sum := by decide
  have hdescent : baseEnd_319192 < baseStart_319192 := by decide
  rcases family_descends (prefixWord ++ tailWord_319192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319194 : List Nat := [3, 1, 1, 2, 2, 4, 1, 1, 4, 3]
def baseStart_319194 : Nat := 118140960795 + 319194 * 2 ^ 59
def prefixEnd_319194 : Nat := 4983230072969 + 3 ^ 40 * 319194 * 2
def baseEnd_319194 : Nat := 109266629354219590471373

theorem tailTrace_319194 : CollatzResearch.WordTrace tailWord_319194 prefixEnd_319194 109266629354219590471373 := by
  unfold tailWord_319194
  simp only [CollatzResearch.WordTrace]
  refine ⟨2910490401405531710057159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7761307737081417893485757 2910490401405531710057159)
  ·
    refine ⟨4365735602108297565085739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2910490401405531710057159 4365735602108297565085739)
    ·
      refine ⟨6548603403162446347628609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4365735602108297565085739 6548603403162446347628609)
      ·
        refine ⟨4911452552371834760721457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6548603403162446347628609 4911452552371834760721457)
        ·
          refine ⟨3683589414278876070541093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4911452552371834760721457 3683589414278876070541093)
          ·
            refine ⟨690673015177289263226455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3683589414278876070541093 690673015177289263226455)
            ·
              refine ⟨1036009522765933894839683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 690673015177289263226455 1036009522765933894839683)
              ·
                refine ⟨1554014284148900842259525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1036009522765933894839683 1554014284148900842259525)
                ·
                  refine ⟨291377678277918907923661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1554014284148900842259525 291377678277918907923661)
                  ·
                    refine ⟨109266629354219590471373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 291377678277918907923661 109266629354219590471373)
                    ·
                      rfl

theorem cell22_319194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 4, 3].length) (baseStart_319194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_319194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_319194 prefixEnd_319194 := by exact prefixLift 319194
  have htrace : WordTrace (prefixWord ++ tailWord_319194) baseStart_319194 baseEnd_319194 := by
    simpa [prefixWord, tailWord_319194, baseEnd_319194] using wordTrace_append hprefix tailTrace_319194
  have hstable : (prefixWord ++ tailWord_319194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319194).length < 2 ^ (prefixWord ++ tailWord_319194).sum := by decide
  have hdescent : baseEnd_319194 < baseStart_319194 := by decide
  rcases family_descends (prefixWord ++ tailWord_319194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319196 : List Nat := [2, 2, 5, 1, 2, 1, 2, 1, 6]
def baseStart_319196 : Nat := 118140960795 + 319196 * 2 ^ 59
def prefixEnd_319196 : Nat := 4983230072969 + 3 ^ 40 * 319196 * 2
def baseEnd_319196 : Nat := 36422437998364083973789

theorem tailTrace_319196 : CollatzResearch.WordTrace tailWord_319196 prefixEnd_319196 36422437998364083973789 := by
  unfold tailWord_319196
  simp only [CollatzResearch.WordTrace]
  refine ⟨5821017275807440590900721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7761356367743254121200961 5821017275807440590900721)
  ·
    refine ⟨4365762956855580443175541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5821017275807440590900721 4365762956855580443175541)
    ·
      refine ⟨409290277205210666547707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4365762956855580443175541 409290277205210666547707)
      ·
        refine ⟨613935415807815999821561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 409290277205210666547707 613935415807815999821561)
        ·
          refine ⟨460451561855861999866171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 613935415807815999821561 460451561855861999866171)
          ·
            refine ⟨690677342783792999799257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 460451561855861999866171 690677342783792999799257)
            ·
              refine ⟨518008007087844749849443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 690677342783792999799257 518008007087844749849443)
              ·
                refine ⟨777012010631767124774165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 518008007087844749849443 777012010631767124774165)
                ·
                  refine ⟨36422437998364083973789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 777012010631767124774165 36422437998364083973789)
                  ·
                    rfl

theorem cell22_319196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 1, 6].length) (baseStart_319196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_319196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_319196 prefixEnd_319196 := by exact prefixLift 319196
  have htrace : WordTrace (prefixWord ++ tailWord_319196) baseStart_319196 baseEnd_319196 := by
    simpa [prefixWord, tailWord_319196, baseEnd_319196] using wordTrace_append hprefix tailTrace_319196
  have hstable : (prefixWord ++ tailWord_319196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319196).length < 2 ^ (prefixWord ++ tailWord_319196).sum := by decide
  have hdescent : baseEnd_319196 < baseStart_319196 := by decide
  rcases family_descends (prefixWord ++ tailWord_319196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319230 : List Nat := [4, 2, 2, 1, 4, 1, 1, 3, 4]
def baseStart_319230 : Nat := 118140960795 + 319230 * 2 ^ 59
def prefixEnd_319230 : Nat := 4983230072969 + 3 ^ 40 * 319230 * 2
def baseEnd_319230 : Nat := 36426317629975832190421

theorem tailTrace_319230 : CollatzResearch.WordTrace tailWord_319230 prefixEnd_319230 36426317629975832190421 := by
  unfold tailWord_319230
  simp only [CollatzResearch.WordTrace]
  refine ⟨1455409329186463123567393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7762183088994469992359429 1455409329186463123567393)
  ·
    refine ⟨1091556996889847342675545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1455409329186463123567393 1091556996889847342675545)
    ·
      refine ⟨818667747667385507006659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1091556996889847342675545 818667747667385507006659)
      ·
        refine ⟨1228001621501078260509989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 818667747667385507006659 1228001621501078260509989)
        ·
          refine ⟨230250304031452173845623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1228001621501078260509989 230250304031452173845623)
          ·
            refine ⟨345375456047178260768435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230250304031452173845623 345375456047178260768435)
            ·
              refine ⟨518063184070767391152653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 345375456047178260768435 518063184070767391152653)
              ·
                refine ⟨194273694026537771682245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 518063184070767391152653 194273694026537771682245)
                ·
                  refine ⟨36426317629975832190421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 194273694026537771682245 36426317629975832190421)
                  ·
                    rfl

theorem cell22_319230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 3, 4].length) (baseStart_319230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_319230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_319230 prefixEnd_319230 := by exact prefixLift 319230
  have htrace : WordTrace (prefixWord ++ tailWord_319230) baseStart_319230 baseEnd_319230 := by
    simpa [prefixWord, tailWord_319230, baseEnd_319230] using wordTrace_append hprefix tailTrace_319230
  have hstable : (prefixWord ++ tailWord_319230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319230).length < 2 ^ (prefixWord ++ tailWord_319230).sum := by decide
  have hdescent : baseEnd_319230 < baseStart_319230 := by decide
  rcases family_descends (prefixWord ++ tailWord_319230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319256 : List Nat := [2, 1, 2, 3, 1, 1, 2, 6, 1, 3]
def baseStart_319256 : Nat := 118140960795 + 319256 * 2 ^ 59
def prefixEnd_319256 : Nat := 4983230072969 + 3 ^ 40 * 319256 * 2
def baseEnd_319256 : Nat := 109287853221272095421183

theorem tailTrace_319256 : CollatzResearch.WordTrace tailWord_319256 prefixEnd_319256 109287853221272095421183 := by
  unfold tailWord_319256
  simp only [CollatzResearch.WordTrace]
  refine ⟨5822111465698755714492811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7762815287598340952657081 5822111465698755714492811)
  ·
    refine ⟨8733167198548133571739217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5822111465698755714492811 8733167198548133571739217)
    ·
      refine ⟨6549875398911100178804413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8733167198548133571739217 6549875398911100178804413)
      ·
        refine ⟨2456203274591662567051655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6549875398911100178804413 2456203274591662567051655)
        ·
          refine ⟨3684304911887493850577483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2456203274591662567051655 3684304911887493850577483)
          ·
            refine ⟨5526457367831240775866225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3684304911887493850577483 5526457367831240775866225)
            ·
              refine ⟨4144843025873430581899669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5526457367831240775866225 4144843025873430581899669)
              ·
                refine ⟨194289516837817058526547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4144843025873430581899669 194289516837817058526547)
                ·
                  refine ⟨291434275256725587789821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 194289516837817058526547 291434275256725587789821)
                  ·
                    refine ⟨109287853221272095421183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 291434275256725587789821 109287853221272095421183)
                    ·
                      rfl

theorem cell22_319256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 6, 1, 3].length) (baseStart_319256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_319256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_319256 prefixEnd_319256 := by exact prefixLift 319256
  have htrace : WordTrace (prefixWord ++ tailWord_319256) baseStart_319256 baseEnd_319256 := by
    simpa [prefixWord, tailWord_319256, baseEnd_319256] using wordTrace_append hprefix tailTrace_319256
  have hstable : (prefixWord ++ tailWord_319256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319256).length < 2 ^ (prefixWord ++ tailWord_319256).sum := by decide
  have hdescent : baseEnd_319256 < baseStart_319256 := by decide
  rcases family_descends (prefixWord ++ tailWord_319256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319267 : List Nat := [1, 1, 1, 4, 2, 1, 2, 3, 2, 5]
def baseStart_319267 : Nat := 118140960795 + 319267 * 2 ^ 59
def prefixEnd_319267 : Nat := 4983230072969 + 3 ^ 40 * 319267 * 2
def baseEnd_319267 : Nat := 109291618746071733396149

theorem tailTrace_319267 : CollatzResearch.WordTrace tailWord_319267 prefixEnd_319267 109291618746071733396149 := by
  unfold tailWord_319267
  simp only [CollatzResearch.WordTrace]
  refine ⟨11644624134357660307636055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7763082756238440205090703 11644624134357660307636055)
  ·
    refine ⟨17466936201536490461454083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11644624134357660307636055 17466936201536490461454083)
    ·
      refine ⟨26200404302304735692181125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17466936201536490461454083 26200404302304735692181125)
      ·
        refine ⟨4912575806682137942283961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26200404302304735692181125 4912575806682137942283961)
        ·
          refine ⟨3684431855011603456712971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4912575806682137942283961 3684431855011603456712971)
          ·
            refine ⟨5526647782517405185069457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3684431855011603456712971 5526647782517405185069457)
            ·
              refine ⟨4144985836888053888802093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5526647782517405185069457 4144985836888053888802093)
              ·
                refine ⟨1554369688833020208300785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4144985836888053888802093 1554369688833020208300785)
                ·
                  refine ⟨1165777266624765156225589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1554369688833020208300785 1165777266624765156225589)
                  ·
                    refine ⟨109291618746071733396149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1165777266624765156225589 109291618746071733396149)
                    ·
                      rfl

theorem cell22_319267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 2, 5].length) (baseStart_319267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_319267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_319267 prefixEnd_319267 := by exact prefixLift 319267
  have htrace : WordTrace (prefixWord ++ tailWord_319267) baseStart_319267 baseEnd_319267 := by
    simpa [prefixWord, tailWord_319267, baseEnd_319267] using wordTrace_append hprefix tailTrace_319267
  have hstable : (prefixWord ++ tailWord_319267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319267).length < 2 ^ (prefixWord ++ tailWord_319267).sum := by decide
  have hdescent : baseEnd_319267 < baseStart_319267 := by decide
  rcases family_descends (prefixWord ++ tailWord_319267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319269 : List Nat := [1, 3, 1, 2, 3, 3, 1, 3, 5]
def baseStart_319269 : Nat := 118140960795 + 319269 * 2 ^ 59
def prefixEnd_319269 : Nat := 4983230072969 + 3 ^ 40 * 319269 * 2
def baseEnd_319269 : Nat := 36430767795648131615381

theorem tailTrace_319269 : CollatzResearch.WordTrace tailWord_319269 prefixEnd_319269 36430767795648131615381 := by
  unfold tailWord_319269
  simp only [CollatzResearch.WordTrace]
  refine ⟨11644697080350414649208861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7763131386900276432805907 11644697080350414649208861)
  ·
    refine ⟨4366761405131405493453323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11644697080350414649208861 4366761405131405493453323)
    ·
      refine ⟨6550142107697108240179985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4366761405131405493453323 6550142107697108240179985)
      ·
        refine ⟨4912606580772831180134989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6550142107697108240179985 4912606580772831180134989)
        ·
          refine ⟨1842227467789811692550621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4912606580772831180134989 1842227467789811692550621)
          ·
            refine ⟨690835300421179384706483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1842227467789811692550621 690835300421179384706483)
            ·
              refine ⟨1036252950631769077059725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 690835300421179384706483 1036252950631769077059725)
              ·
                refine ⟨388594856486913403897397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1036252950631769077059725 388594856486913403897397)
                ·
                  refine ⟨36430767795648131615381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 388594856486913403897397 36430767795648131615381)
                  ·
                    rfl

theorem cell22_319269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 3, 5].length) (baseStart_319269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_319269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_319269 prefixEnd_319269 := by exact prefixLift 319269
  have htrace : WordTrace (prefixWord ++ tailWord_319269) baseStart_319269 baseEnd_319269 := by
    simpa [prefixWord, tailWord_319269, baseEnd_319269] using wordTrace_append hprefix tailTrace_319269
  have hstable : (prefixWord ++ tailWord_319269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319269).length < 2 ^ (prefixWord ++ tailWord_319269).sum := by decide
  have hdescent : baseEnd_319269 < baseStart_319269 := by decide
  rcases family_descends (prefixWord ++ tailWord_319269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319312 : List Nat := [2, 1, 1, 1, 1, 4, 1, 1, 5, 5]
def baseStart_319312 : Nat := 118140960795 + 319312 * 2 ^ 59
def prefixEnd_319312 : Nat := 4983230072969 + 3 ^ 40 * 319312 * 2
def baseEnd_319312 : Nat := 109307023165706616021011

theorem tailTrace_319312 : CollatzResearch.WordTrace tailWord_319312 prefixEnd_319312 109307023165706616021011 := by
  unfold tailWord_319312
  simp only [CollatzResearch.WordTrace]
  refine ⟨5823132709597316496512095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7764176946129755328682793 5823132709597316496512095)
  ·
    refine ⟨8734699064395974744768143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5823132709597316496512095 8734699064395974744768143)
    ·
      refine ⟨13102048596593962117152215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8734699064395974744768143 13102048596593962117152215)
      ·
        refine ⟨19653072894890943175728323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13102048596593962117152215 19653072894890943175728323)
        ·
          refine ⟨29479609342336414763592485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19653072894890943175728323 29479609342336414763592485)
          ·
            refine ⟨5527426751688077768173591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29479609342336414763592485 5527426751688077768173591)
            ·
              refine ⟨8291140127532116652260387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5527426751688077768173591 8291140127532116652260387)
              ·
                refine ⟨12436710191298174978390581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8291140127532116652260387 12436710191298174978390581)
                ·
                  refine ⟨1165941580434203904224117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12436710191298174978390581 1165941580434203904224117)
                  ·
                    refine ⟨109307023165706616021011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1165941580434203904224117 109307023165706616021011)
                    ·
                      rfl

theorem cell22_319312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 5, 5].length) (baseStart_319312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_319312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_319312 prefixEnd_319312 := by exact prefixLift 319312
  have htrace : WordTrace (prefixWord ++ tailWord_319312) baseStart_319312 baseEnd_319312 := by
    simpa [prefixWord, tailWord_319312, baseEnd_319312] using wordTrace_append hprefix tailTrace_319312
  have hstable : (prefixWord ++ tailWord_319312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319312).length < 2 ^ (prefixWord ++ tailWord_319312).sum := by decide
  have hdescent : baseEnd_319312 < baseStart_319312 := by decide
  rcases family_descends (prefixWord ++ tailWord_319312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319329 : List Nat := [1, 2, 3, 1, 1, 1, 6, 1, 1, 5]
def baseStart_319329 : Nat := 118140960795 + 319329 * 2 ^ 59
def prefixEnd_319329 : Nat := 4983230072969 + 3 ^ 40 * 319329 * 2
def baseEnd_319329 : Nat := 109312842613124238345959

theorem tailTrace_319329 : CollatzResearch.WordTrace tailWord_319329 prefixEnd_319329 109312842613124238345959 := by
  unfold tailWord_319329
  simp only [CollatzResearch.WordTrace]
  refine ⟨11646885460133044896393041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7764590306755363264262027 11646885460133044896393041)
  ·
    refine ⟨8735164095099783672294781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11646885460133044896393041 8735164095099783672294781)
    ·
      refine ⟨3275686535662418877110543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8735164095099783672294781 3275686535662418877110543)
      ·
        refine ⟨4913529803493628315665815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3275686535662418877110543 4913529803493628315665815)
        ·
          refine ⟨7370294705240442473498723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4913529803493628315665815 7370294705240442473498723)
          ·
            refine ⟨11055442057860663710248085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7370294705240442473498723 11055442057860663710248085)
            ·
              refine ⟨518223846462218611417879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11055442057860663710248085 518223846462218611417879)
              ·
                refine ⟨777335769693327917126819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 518223846462218611417879 777335769693327917126819)
                ·
                  refine ⟨1166003654539991875690229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 777335769693327917126819 1166003654539991875690229)
                  ·
                    refine ⟨109312842613124238345959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1166003654539991875690229 109312842613124238345959)
                    ·
                      rfl

theorem cell22_319329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 1, 1, 5].length) (baseStart_319329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_319329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_319329 prefixEnd_319329 := by exact prefixLift 319329
  have htrace : WordTrace (prefixWord ++ tailWord_319329) baseStart_319329 baseEnd_319329 := by
    simpa [prefixWord, tailWord_319329, baseEnd_319329] using wordTrace_append hprefix tailTrace_319329
  have hstable : (prefixWord ++ tailWord_319329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319329).length < 2 ^ (prefixWord ++ tailWord_319329).sum := by decide
  have hdescent : baseEnd_319329 < baseStart_319329 := by decide
  rcases family_descends (prefixWord ++ tailWord_319329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319363 : List Nat := [1, 1, 1, 3, 4, 4, 1, 2, 2, 3]
def baseStart_319363 : Nat := 118140960795 + 319363 * 2 ^ 59
def prefixEnd_319363 : Nat := 4983230072969 + 3 ^ 40 * 319363 * 2
def baseEnd_319363 : Nat := 109324481507959482995855

theorem tailTrace_319363 : CollatzResearch.WordTrace tailWord_319363 prefixEnd_319363 109324481507959482995855 := by
  unfold tailWord_319363
  simp only [CollatzResearch.WordTrace]
  refine ⟨11648125542009868703130743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7765417028006579135420495 11648125542009868703130743)
  ·
    refine ⟨17472188313014803054696115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11648125542009868703130743 17472188313014803054696115)
    ·
      refine ⟨26208282469522204582044173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17472188313014803054696115 26208282469522204582044173)
      ·
        refine ⟨9828105926070826718266565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26208282469522204582044173 9828105926070826718266565)
        ·
          refine ⟨1842769861138280009674981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9828105926070826718266565 1842769861138280009674981)
          ·
            refine ⟨345519348963427501814059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1842769861138280009674981 345519348963427501814059)
            ·
              refine ⟨518279023445141252721089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 345519348963427501814059 518279023445141252721089)
              ·
                refine ⟨388709267583855939540817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 518279023445141252721089 388709267583855939540817)
                ·
                  refine ⟨291531950687891954655613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 388709267583855939540817 291531950687891954655613)
                  ·
                    refine ⟨109324481507959482995855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 291531950687891954655613 109324481507959482995855)
                    ·
                      rfl

theorem cell22_319363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 2, 2, 3].length) (baseStart_319363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_319363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_319363 prefixEnd_319363 := by exact prefixLift 319363
  have htrace : WordTrace (prefixWord ++ tailWord_319363) baseStart_319363 baseEnd_319363 := by
    simpa [prefixWord, tailWord_319363, baseEnd_319363] using wordTrace_append hprefix tailTrace_319363
  have hstable : (prefixWord ++ tailWord_319363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319363).length < 2 ^ (prefixWord ++ tailWord_319363).sum := by decide
  have hdescent : baseEnd_319363 < baseStart_319363 := by decide
  rcases family_descends (prefixWord ++ tailWord_319363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319380 : List Nat := [2, 4, 2, 1, 1, 3, 3, 1, 2, 3]
def baseStart_319380 : Nat := 118140960795 + 319380 * 2 ^ 59
def prefixEnd_319380 : Nat := 4983230072969 + 3 ^ 40 * 319380 * 2
def baseEnd_319380 : Nat := 109330300955377105320803

theorem tailTrace_319380 : CollatzResearch.WordTrace tailWord_319380 prefixEnd_319380 109330300955377105320803 := by
  unfold tailWord_319380
  simp only [CollatzResearch.WordTrace]
  refine ⟨5824372791474140303249797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7765830388632187070999729 5824372791474140303249797)
  ·
    refine ⟨1092069898401401306859337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5824372791474140303249797 1092069898401401306859337)
    ·
      refine ⟨819052423801050980144503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1092069898401401306859337 819052423801050980144503)
      ·
        refine ⟨1228578635701576470216755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 819052423801050980144503 1228578635701576470216755)
        ·
          refine ⟨1842867953552364705325133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1228578635701576470216755 1842867953552364705325133)
          ·
            refine ⟨691075482582136764496925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1842867953552364705325133 691075482582136764496925)
            ·
              refine ⟨259153305968301286686347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 691075482582136764496925 259153305968301286686347)
              ·
                refine ⟨388729958952451930029521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 259153305968301286686347 388729958952451930029521)
                ·
                  refine ⟨291547469214338947522141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 388729958952451930029521 291547469214338947522141)
                  ·
                    refine ⟨109330300955377105320803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 291547469214338947522141 109330300955377105320803)
                    ·
                      rfl

theorem cell22_319380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_319380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_319380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_319380 prefixEnd_319380 := by exact prefixLift 319380
  have htrace : WordTrace (prefixWord ++ tailWord_319380) baseStart_319380 baseEnd_319380 := by
    simpa [prefixWord, tailWord_319380, baseEnd_319380] using wordTrace_append hprefix tailTrace_319380
  have hstable : (prefixWord ++ tailWord_319380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319380).length < 2 ^ (prefixWord ++ tailWord_319380).sum := by decide
  have hdescent : baseEnd_319380 < baseStart_319380 := by decide
  rcases family_descends (prefixWord ++ tailWord_319380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319393 : List Nat := [1, 2, 3, 4, 2, 2, 2, 6]
def baseStart_319393 : Nat := 118140960795 + 319393 * 2 ^ 59
def prefixEnd_319393 : Nat := 4983230072969 + 3 ^ 40 * 319393 * 2
def baseEnd_319393 : Nat := 12148305680116600527307

theorem tailTrace_319393 : CollatzResearch.WordTrace tailWord_319393 prefixEnd_319393 12148305680116600527307 := by
  unfold tailWord_319393
  simp only [CollatzResearch.WordTrace]
  refine ⟨11649219731901183826722833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7766146487934122551148555 11649219731901183826722833)
  ·
    refine ⟨8736914798925887870042125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11649219731901183826722833 8736914798925887870042125)
    ·
      refine ⟨3276343049597207951265797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8736914798925887870042125 3276343049597207951265797)
      ·
        refine ⟨614314321799476490862337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3276343049597207951265797 614314321799476490862337)
        ·
          refine ⟨460735741349607368146753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 614314321799476490862337 460735741349607368146753)
          ·
            refine ⟨345551806012205526110065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 460735741349607368146753 345551806012205526110065)
            ·
              refine ⟨259163854509154144582549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 345551806012205526110065 259163854509154144582549)
              ·
                refine ⟨12148305680116600527307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 259163854509154144582549 12148305680116600527307)
                ·
                  rfl

theorem cell22_319393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 2, 6].length) (baseStart_319393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_319393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_319393 prefixEnd_319393 := by exact prefixLift 319393
  have htrace : WordTrace (prefixWord ++ tailWord_319393) baseStart_319393 baseEnd_319393 := by
    simpa [prefixWord, tailWord_319393, baseEnd_319393] using wordTrace_append hprefix tailTrace_319393
  have hstable : (prefixWord ++ tailWord_319393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319393).length < 2 ^ (prefixWord ++ tailWord_319393).sum := by decide
  have hdescent : baseEnd_319393 < baseStart_319393 := by decide
  rcases family_descends (prefixWord ++ tailWord_319393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319483 : List Nat := [1, 1, 1, 1, 1, 3, 8, 2, 4]
def baseStart_319483 : Nat := 118140960795 + 319483 * 2 ^ 59
def prefixEnd_319483 : Nat := 4983230072969 + 3 ^ 40 * 319483 * 2
def baseEnd_319483 : Nat := 36455186653439723331829

theorem tailTrace_319483 : CollatzResearch.WordTrace tailWord_319483 prefixEnd_319483 36455186653439723331829 := by
  unfold tailWord_319483
  simp only [CollatzResearch.WordTrace]
  refine ⟨11652502301575129197499103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7768334867716752798332735 11652502301575129197499103)
  ·
    refine ⟨17478753452362693796248655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11652502301575129197499103 17478753452362693796248655)
    ·
      refine ⟨26218130178544040694372983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17478753452362693796248655 26218130178544040694372983)
      ·
        refine ⟨39327195267816061041559475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26218130178544040694372983 39327195267816061041559475)
        ·
          refine ⟨58990792901724091562339213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39327195267816061041559475 58990792901724091562339213)
          ·
            refine ⟨22121547338146534335877205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58990792901724091562339213 22121547338146534335877205)
            ·
              refine ⟨259236882868904699248561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 22121547338146534335877205 259236882868904699248561)
              ·
                refine ⟨194427662151678524436421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 259236882868904699248561 194427662151678524436421)
                ·
                  refine ⟨36455186653439723331829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 194427662151678524436421 36455186653439723331829)
                  ·
                    rfl

theorem cell22_319483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 8, 2, 4].length) (baseStart_319483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_319483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_319483 prefixEnd_319483 := by exact prefixLift 319483
  have htrace : WordTrace (prefixWord ++ tailWord_319483) baseStart_319483 baseEnd_319483 := by
    simpa [prefixWord, tailWord_319483, baseEnd_319483] using wordTrace_append hprefix tailTrace_319483
  have hstable : (prefixWord ++ tailWord_319483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319483).length < 2 ^ (prefixWord ++ tailWord_319483).sum := by decide
  have hdescent : baseEnd_319483 < baseStart_319483 := by decide
  rcases family_descends (prefixWord ++ tailWord_319483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319498 : List Nat := [3, 1, 2, 2, 4, 1, 2, 1, 1, 5]
def baseStart_319498 : Nat := 118140960795 + 319498 * 2 ^ 59
def prefixEnd_319498 : Nat := 4983230072969 + 3 ^ 40 * 319498 * 2
def baseEnd_319498 : Nat := 109370694766864130870441

theorem tailTrace_319498 : CollatzResearch.WordTrace tailWord_319498 prefixEnd_319498 109370694766864130870441 := by
  unfold tailWord_319498
  simp only [CollatzResearch.WordTrace]
  refine ⟨2913262349130196689823787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7768699597680524506196765 2913262349130196689823787)
  ·
    refine ⟨4369893523695295034735681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2913262349130196689823787 4369893523695295034735681)
    ·
      refine ⟨3277420142771471276051761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4369893523695295034735681 3277420142771471276051761)
      ·
        refine ⟨2458065107078603457038821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3277420142771471276051761 2458065107078603457038821)
        ·
          refine ⟨460887207577238148194779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2458065107078603457038821 460887207577238148194779)
          ·
            refine ⟨691330811365857222292169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 460887207577238148194779 691330811365857222292169)
            ·
              refine ⟨518498108524392916719127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 691330811365857222292169 518498108524392916719127)
              ·
                refine ⟨777747162786589375078691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 518498108524392916719127 777747162786589375078691)
                ·
                  refine ⟨1166620744179884062618037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 777747162786589375078691 1166620744179884062618037)
                  ·
                    refine ⟨109370694766864130870441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1166620744179884062618037 109370694766864130870441)
                    ·
                      rfl

theorem cell22_319498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 1, 1, 5].length) (baseStart_319498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_319498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_319498 prefixEnd_319498 := by exact prefixLift 319498
  have htrace : WordTrace (prefixWord ++ tailWord_319498) baseStart_319498 baseEnd_319498 := by
    simpa [prefixWord, tailWord_319498, baseEnd_319498] using wordTrace_append hprefix tailTrace_319498
  have hstable : (prefixWord ++ tailWord_319498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319498).length < 2 ^ (prefixWord ++ tailWord_319498).sum := by decide
  have hdescent : baseEnd_319498 < baseStart_319498 := by decide
  rcases family_descends (prefixWord ++ tailWord_319498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319528 : List Nat := [2, 1, 5, 3, 1, 1, 9]
def baseStart_319528 : Nat := 118140960795 + 319528 * 2 ^ 59
def prefixEnd_319528 : Nat := 4983230072969 + 3 ^ 40 * 319528 * 2
def baseEnd_319528 : Nat := 4051146828887187134087

theorem tailTrace_319528 : CollatzResearch.WordTrace tailWord_319528 prefixEnd_319528 4051146828887187134087 := by
  unfold tailWord_319528
  simp only [CollatzResearch.WordTrace]
  refine ⟨5827071793206050941443619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7769429057608067921924825 5827071793206050941443619)
  ·
    refine ⟨8740607689809076412165429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5827071793206050941443619 8740607689809076412165429)
    ·
      refine ⟨819431970919600913640509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8740607689809076412165429 819431970919600913640509)
      ·
        refine ⟨307286989094850342615191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 819431970919600913640509 307286989094850342615191)
        ·
          refine ⟨460930483642275513922787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 307286989094850342615191 460930483642275513922787)
          ·
            refine ⟨691395725463413270884181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 460930483642275513922787 691395725463413270884181)
            ·
              refine ⟨4051146828887187134087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 691395725463413270884181 4051146828887187134087)
              ·
                rfl

theorem cell22_319528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 9].length) (baseStart_319528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_319528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_319528 prefixEnd_319528 := by exact prefixLift 319528
  have htrace : WordTrace (prefixWord ++ tailWord_319528) baseStart_319528 baseEnd_319528 := by
    simpa [prefixWord, tailWord_319528, baseEnd_319528] using wordTrace_append hprefix tailTrace_319528
  have hstable : (prefixWord ++ tailWord_319528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319528).length < 2 ^ (prefixWord ++ tailWord_319528).sum := by decide
  have hdescent : baseEnd_319528 < baseStart_319528 := by decide
  rcases family_descends (prefixWord ++ tailWord_319528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319594 : List Nat := [3, 1, 3, 2, 3, 1, 3, 2, 1, 3]
def baseStart_319594 : Nat := 118140960795 + 319594 * 2 ^ 59
def prefixEnd_319594 : Nat := 4983230072969 + 3 ^ 40 * 319594 * 2
def baseEnd_319594 : Nat := 109403557528751880470147

theorem tailTrace_319594 : CollatzResearch.WordTrace tailWord_319594 prefixEnd_319594 109403557528751880470147 := by
  unfold tailWord_319594
  simp only [CollatzResearch.WordTrace]
  refine ⟨2914137701043248788697459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7771033869448663436526557 2914137701043248788697459)
  ·
    refine ⟨4371206551564873183046189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2914137701043248788697459 4371206551564873183046189)
    ·
      refine ⟨1639202456836827443642321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4371206551564873183046189 1639202456836827443642321)
      ·
        refine ⟨1229401842627620582731741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1639202456836827443642321 1229401842627620582731741)
        ·
          refine ⟨461025690985357718524403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1229401842627620582731741 461025690985357718524403)
          ·
            refine ⟨691538536478036577786605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 461025690985357718524403 691538536478036577786605)
            ·
              refine ⟨259326951179263716669977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 691538536478036577786605 259326951179263716669977)
              ·
                refine ⟨194495213384447787502483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 259326951179263716669977 194495213384447787502483)
                ·
                  refine ⟨291742820076671681253725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 194495213384447787502483 291742820076671681253725)
                  ·
                    refine ⟨109403557528751880470147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 291742820076671681253725 109403557528751880470147)
                    ·
                      rfl

theorem cell22_319594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 3, 2, 1, 3].length) (baseStart_319594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_319594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_319594 prefixEnd_319594 := by exact prefixLift 319594
  have htrace : WordTrace (prefixWord ++ tailWord_319594) baseStart_319594 baseEnd_319594 := by
    simpa [prefixWord, tailWord_319594, baseEnd_319594] using wordTrace_append hprefix tailTrace_319594
  have hstable : (prefixWord ++ tailWord_319594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319594).length < 2 ^ (prefixWord ++ tailWord_319594).sum := by decide
  have hdescent : baseEnd_319594 < baseStart_319594 := by decide
  rcases family_descends (prefixWord ++ tailWord_319594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319616 : List Nat := [2, 1, 1, 2, 1, 3, 1, 5, 1, 5]
def baseStart_319616 : Nat := 118140960795 + 319616 * 2 ^ 59
def prefixEnd_319616 : Nat := 4983230072969 + 3 ^ 40 * 319616 * 2
def baseEnd_319616 : Nat := 109411088578351156420079

theorem tailTrace_319616 : CollatzResearch.WordTrace tailWord_319616 prefixEnd_319616 109411088578351156420079 := by
  unfold tailWord_319616
  simp only [CollatzResearch.WordTrace]
  refine ⟨5828676605046646456045351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7771568806728861941393801 5828676605046646456045351)
  ·
    refine ⟨8743014907569969684068027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5828676605046646456045351 8743014907569969684068027)
    ·
      refine ⟨13114522361354954526102041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8743014907569969684068027 13114522361354954526102041)
      ·
        refine ⟨9835891771016215894576531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13114522361354954526102041 9835891771016215894576531)
        ·
          refine ⟨14753837656524323841864797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9835891771016215894576531 14753837656524323841864797)
          ·
            refine ⟨5532689121196621440699299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14753837656524323841864797 5532689121196621440699299)
            ·
              refine ⟨8299033681794932161048949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5532689121196621440699299 8299033681794932161048949)
              ·
                refine ⟨778034407668274890098339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8299033681794932161048949 778034407668274890098339)
                ·
                  refine ⟨1167051611502412335147509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 778034407668274890098339 1167051611502412335147509)
                  ·
                    refine ⟨109411088578351156420079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1167051611502412335147509 109411088578351156420079)
                    ·
                      rfl

theorem cell22_319616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 5, 1, 5].length) (baseStart_319616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_319616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_319616 prefixEnd_319616 := by exact prefixLift 319616
  have htrace : WordTrace (prefixWord ++ tailWord_319616) baseStart_319616 baseEnd_319616 := by
    simpa [prefixWord, tailWord_319616, baseEnd_319616] using wordTrace_append hprefix tailTrace_319616
  have hstable : (prefixWord ++ tailWord_319616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319616).length < 2 ^ (prefixWord ++ tailWord_319616).sum := by decide
  have hdescent : baseEnd_319616 < baseStart_319616 := by decide
  rcases family_descends (prefixWord ++ tailWord_319616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319648 : List Nat := [2, 1, 1, 4, 2, 2, 2, 2, 2, 4]
def baseStart_319648 : Nat := 118140960795 + 319648 * 2 ^ 59
def prefixEnd_319648 : Nat := 4983230072969 + 3 ^ 40 * 319648 * 2
def baseEnd_319648 : Nat := 109422042832313739619981

theorem tailTrace_319648 : CollatzResearch.WordTrace tailWord_319648 prefixEnd_319648 109422042832313739619981 := by
  unfold tailWord_319648
  simp only [CollatzResearch.WordTrace]
  refine ⟨5829260172988681188627799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7772346897318241584837065 5829260172988681188627799)
  ·
    refine ⟨8743890259483021782941699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5829260172988681188627799 8743890259483021782941699)
    ·
      refine ⟨13115835389224532674412549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8743890259483021782941699 13115835389224532674412549)
      ·
        refine ⟨2459219135479599876452353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13115835389224532674412549 2459219135479599876452353)
        ·
          refine ⟨1844414351609699907339265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2459219135479599876452353 1844414351609699907339265)
          ·
            refine ⟨1383310763707274930504449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1844414351609699907339265 1383310763707274930504449)
            ·
              refine ⟨1037483072780456197878337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1383310763707274930504449 1037483072780456197878337)
              ·
                refine ⟨778112304585342148408753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1037483072780456197878337 778112304585342148408753)
                ·
                  refine ⟨583584228439006611306565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 778112304585342148408753 583584228439006611306565)
                  ·
                    refine ⟨109422042832313739619981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 583584228439006611306565 109422042832313739619981)
                    ·
                      rfl

theorem cell22_319648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 2, 2, 4].length) (baseStart_319648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_319648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_319648 prefixEnd_319648 := by exact prefixLift 319648
  have htrace : WordTrace (prefixWord ++ tailWord_319648) baseStart_319648 baseEnd_319648 := by
    simpa [prefixWord, tailWord_319648, baseEnd_319648] using wordTrace_append hprefix tailTrace_319648
  have hstable : (prefixWord ++ tailWord_319648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319648).length < 2 ^ (prefixWord ++ tailWord_319648).sum := by decide
  have hdescent : baseEnd_319648 < baseStart_319648 := by decide
  rcases family_descends (prefixWord ++ tailWord_319648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319682 : List Nat := [3, 5, 1, 1, 1, 2, 1, 1, 1, 6]
def baseStart_319682 : Nat := 118140960795 + 319682 * 2 ^ 59
def prefixEnd_319682 : Nat := 4983230072969 + 3 ^ 40 * 319682 * 2
def baseEnd_319682 : Nat := 109433681727148984269877

theorem tailTrace_319682 : CollatzResearch.WordTrace tailWord_319682 prefixEnd_319682 109433681727148984269877 := by
  unfold tailWord_319682
  simp only [CollatzResearch.WordTrace]
  refine ⟨2914940106963546545998325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7773173618569457455995533 2914940106963546545998325)
  ·
    refine ⟨273275635027832488687343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2914940106963546545998325 273275635027832488687343)
    ·
      refine ⟨409913452541748733031015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273275635027832488687343 409913452541748733031015)
      ·
        refine ⟨614870178812623099546523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 409913452541748733031015 614870178812623099546523)
        ·
          refine ⟨922305268218934649319785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 614870178812623099546523 922305268218934649319785)
          ·
            refine ⟨691728951164200986989839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 922305268218934649319785 691728951164200986989839)
            ·
              refine ⟨1037593426746301480484759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 691728951164200986989839 1037593426746301480484759)
              ·
                refine ⟨1556390140119452220727139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1037593426746301480484759 1556390140119452220727139)
                ·
                  refine ⟨2334585210179178331090709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1556390140119452220727139 2334585210179178331090709)
                  ·
                    refine ⟨109433681727148984269877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2334585210179178331090709 109433681727148984269877)
                    ·
                      rfl

theorem cell22_319682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_319682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_319682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_319682 prefixEnd_319682 := by exact prefixLift 319682
  have htrace : WordTrace (prefixWord ++ tailWord_319682) baseStart_319682 baseEnd_319682 := by
    simpa [prefixWord, tailWord_319682, baseEnd_319682] using wordTrace_append hprefix tailTrace_319682
  have hstable : (prefixWord ++ tailWord_319682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319682).length < 2 ^ (prefixWord ++ tailWord_319682).sum := by decide
  have hdescent : baseEnd_319682 < baseStart_319682 := by decide
  rcases family_descends (prefixWord ++ tailWord_319682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319691 : List Nat := [1, 1, 1, 1, 3, 2, 4, 2, 7]
def baseStart_319691 : Nat := 118140960795 + 319691 * 2 ^ 59
def prefixEnd_319691 : Nat := 4983230072969 + 3 ^ 40 * 319691 * 2
def baseEnd_319691 : Nat := 36478920870358653598283

theorem tailTrace_319691 : CollatzResearch.WordTrace tailWord_319691 prefixEnd_319691 36478920870358653598283 := by
  unfold tailWord_319691
  simp only [CollatzResearch.WordTrace]
  refine ⟨11660088684821580721070927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7773392456547720480713951 11660088684821580721070927)
  ·
    refine ⟨17490133027232371081606391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11660088684821580721070927 17490133027232371081606391)
    ·
      refine ⟨26235199540848556622409587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17490133027232371081606391 26235199540848556622409587)
      ·
        refine ⟨39352799311272834933614381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26235199540848556622409587 39352799311272834933614381)
        ·
          refine ⟨14757299741727313100105393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39352799311272834933614381 14757299741727313100105393)
          ·
            refine ⟨11067974806295484825079045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14757299741727313100105393 11067974806295484825079045)
            ·
              refine ⟨2075245276180403404702321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11067974806295484825079045 2075245276180403404702321)
              ·
                refine ⟨1556433957135302553526741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2075245276180403404702321 1556433957135302553526741)
                ·
                  refine ⟨36478920870358653598283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1556433957135302553526741 36478920870358653598283)
                  ·
                    rfl

theorem cell22_319691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 7].length) (baseStart_319691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_319691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_319691 prefixEnd_319691 := by exact prefixLift 319691
  have htrace : WordTrace (prefixWord ++ tailWord_319691) baseStart_319691 baseEnd_319691 := by
    simpa [prefixWord, tailWord_319691, baseEnd_319691] using wordTrace_append hprefix tailTrace_319691
  have hstable : (prefixWord ++ tailWord_319691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319691).length < 2 ^ (prefixWord ++ tailWord_319691).sum := by decide
  have hdescent : baseEnd_319691 < baseStart_319691 := by decide
  rcases family_descends (prefixWord ++ tailWord_319691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319746 : List Nat := [3, 4, 1, 1, 2, 3, 1, 3, 1, 3]
def baseStart_319746 : Nat := 118140960795 + 319746 * 2 ^ 59
def prefixEnd_319746 : Nat := 4983230072969 + 3 ^ 40 * 319746 * 2
def baseEnd_319746 : Nat := 109455590235074150669681

theorem tailTrace_319746 : CollatzResearch.WordTrace tailWord_319746 prefixEnd_319746 109455590235074150669681 := by
  unfold tailWord_319746
  simp only [CollatzResearch.WordTrace]
  refine ⟨2915523674905581278580773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7774729799748216742882061 2915523674905581278580773)
  ·
    refine ⟨546660689044796489733895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2915523674905581278580773 546660689044796489733895)
    ·
      refine ⟨819991033567194734600843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 546660689044796489733895 819991033567194734600843)
      ·
        refine ⟨1229986550350792101901265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 819991033567194734600843 1229986550350792101901265)
        ·
          refine ⟨922489912763094076425949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1229986550350792101901265 922489912763094076425949)
          ·
            refine ⟨345933717286160278659731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 922489912763094076425949 345933717286160278659731)
            ·
              refine ⟨518900575929240417989597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 345933717286160278659731 518900575929240417989597)
              ·
                refine ⟨194587715973465156746099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 518900575929240417989597 194587715973465156746099)
                ·
                  refine ⟨291881573960197735119149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 194587715973465156746099 291881573960197735119149)
                  ·
                    refine ⟨109455590235074150669681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 291881573960197735119149 109455590235074150669681)
                    ·
                      rfl

theorem cell22_319746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_319746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_319746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_319746 prefixEnd_319746 := by exact prefixLift 319746
  have htrace : WordTrace (prefixWord ++ tailWord_319746) baseStart_319746 baseEnd_319746 := by
    simpa [prefixWord, tailWord_319746, baseEnd_319746] using wordTrace_append hprefix tailTrace_319746
  have hstable : (prefixWord ++ tailWord_319746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319746).length < 2 ^ (prefixWord ++ tailWord_319746).sum := by decide
  have hdescent : baseEnd_319746 < baseStart_319746 := by decide
  rcases family_descends (prefixWord ++ tailWord_319746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319847 : List Nat := [1, 1, 5, 1, 3, 2, 1, 2, 3, 3]
def baseStart_319847 : Nat := 118140960795 + 319847 * 2 ^ 59
def prefixEnd_319847 : Nat := 4983230072969 + 3 ^ 40 * 319847 * 2
def baseEnd_319847 : Nat := 109490164599143553894371

theorem tailTrace_319847 : CollatzResearch.WordTrace tailWord_319847 prefixEnd_319847 109490164599143553894371 := by
  unfold tailWord_319847
  simp only [CollatzResearch.WordTrace]
  refine ⟨11665778472256419363749795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7777185648170946242499863 11665778472256419363749795)
  ·
    refine ⟨17498667708384629045624693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11665778472256419363749795 17498667708384629045624693)
    ·
      refine ⟨1640500097661058973027315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17498667708384629045624693 1640500097661058973027315)
      ·
        refine ⟨2460750146491588459540973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1640500097661058973027315 2460750146491588459540973)
        ·
          refine ⟨922781304934345672327865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2460750146491588459540973 922781304934345672327865)
          ·
            refine ⟨692085978700759254245899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 922781304934345672327865 692085978700759254245899)
            ·
              refine ⟨1038128968051138881368849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 692085978700759254245899 1038128968051138881368849)
              ·
                refine ⟨778596726038354161026637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1038128968051138881368849 778596726038354161026637)
                ·
                  refine ⟨291973772264382810384989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 778596726038354161026637 291973772264382810384989)
                  ·
                    refine ⟨109490164599143553894371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 291973772264382810384989 109490164599143553894371)
                    ·
                      rfl

theorem cell22_319847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 2, 3, 3].length) (baseStart_319847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_319847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_319847 prefixEnd_319847 := by exact prefixLift 319847
  have htrace : WordTrace (prefixWord ++ tailWord_319847) baseStart_319847 baseEnd_319847 := by
    simpa [prefixWord, tailWord_319847, baseEnd_319847] using wordTrace_append hprefix tailTrace_319847
  have hstable : (prefixWord ++ tailWord_319847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319847).length < 2 ^ (prefixWord ++ tailWord_319847).sum := by decide
  have hdescent : baseEnd_319847 < baseStart_319847 := by decide
  rcases family_descends (prefixWord ++ tailWord_319847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319907 : List Nat := [1, 1, 1, 4, 1, 5, 2, 2, 1, 4]
def baseStart_319907 : Nat := 118140960795 + 319907 * 2 ^ 59
def prefixEnd_319907 : Nat := 4983230072969 + 3 ^ 40 * 319907 * 2
def baseEnd_319907 : Nat := 109510703825323397394187

theorem tailTrace_319907 : CollatzResearch.WordTrace tailWord_319907 prefixEnd_319907 109510703825323397394187 := by
  unfold tailWord_319907
  simp only [CollatzResearch.WordTrace]
  refine ⟨11667966852039049610933975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7778644568026033073955983 11667966852039049610933975)
  ·
    refine ⟨17501950278058574416400963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11667966852039049610933975 17501950278058574416400963)
    ·
      refine ⟨26252925417087861624601445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17501950278058574416400963 26252925417087861624601445)
      ·
        refine ⟨4922423515703974054612771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26252925417087861624601445 4922423515703974054612771)
        ·
          refine ⟨7383635273555961081919157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4922423515703974054612771 7383635273555961081919157)
          ·
            refine ⟨692215806895871351429921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7383635273555961081919157 692215806895871351429921)
            ·
              refine ⟨519161855171903513572441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 692215806895871351429921 519161855171903513572441)
              ·
                refine ⟨389371391378927635179331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 519161855171903513572441 389371391378927635179331)
                ·
                  refine ⟨584057087068391452768997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 389371391378927635179331 584057087068391452768997)
                  ·
                    refine ⟨109510703825323397394187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 584057087068391452768997 109510703825323397394187)
                    ·
                      rfl

theorem cell22_319907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 2, 1, 4].length) (baseStart_319907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_319907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_319907 prefixEnd_319907 := by exact prefixLift 319907
  have htrace : WordTrace (prefixWord ++ tailWord_319907) baseStart_319907 baseEnd_319907 := by
    simpa [prefixWord, tailWord_319907, baseEnd_319907] using wordTrace_append hprefix tailTrace_319907
  have hstable : (prefixWord ++ tailWord_319907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319907).length < 2 ^ (prefixWord ++ tailWord_319907).sum := by decide
  have hdescent : baseEnd_319907 < baseStart_319907 := by decide
  rcases family_descends (prefixWord ++ tailWord_319907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319999 : List Nat := [1, 1, 2, 2, 1, 2, 5, 4, 1, 3]
def baseStart_319999 : Nat := 118140960795 + 319999 * 2 ^ 59
def prefixEnd_319999 : Nat := 4983230072969 + 3 ^ 40 * 319999 * 2
def baseEnd_319999 : Nat := 109542197305465824093905

theorem tailTrace_319999 : CollatzResearch.WordTrace tailWord_319999 prefixEnd_319999 109542197305465824093905 := by
  unfold tailWord_319999
  simp only [CollatzResearch.WordTrace]
  refine ⟨11671322367705749323283051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7780881578470499548855367 11671322367705749323283051)
  ·
    refine ⟨17506983551558623984924577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11671322367705749323283051 17506983551558623984924577)
    ·
      refine ⟨13130237663668967988693433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17506983551558623984924577 13130237663668967988693433)
      ·
        refine ⟨9847678247751725991520075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13130237663668967988693433 9847678247751725991520075)
        ·
          refine ⟨14771517371627588987280113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9847678247751725991520075 14771517371627588987280113)
          ·
            refine ⟨11078638028720691740460085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14771517371627588987280113 11078638028720691740460085)
            ·
              refine ⟨1038622315192564850668133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11078638028720691740460085 1038622315192564850668133)
              ·
                refine ⟨194741684098605909500275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1038622315192564850668133 194741684098605909500275)
                ·
                  refine ⟨292112526147908864250413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 194741684098605909500275 292112526147908864250413)
                  ·
                    refine ⟨109542197305465824093905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 292112526147908864250413 109542197305465824093905)
                    ·
                      rfl

theorem cell22_319999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 4, 1, 3].length) (baseStart_319999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_319999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_319999 prefixEnd_319999 := by exact prefixLift 319999
  have htrace : WordTrace (prefixWord ++ tailWord_319999) baseStart_319999 baseEnd_319999 := by
    simpa [prefixWord, tailWord_319999, baseEnd_319999] using wordTrace_append hprefix tailTrace_319999
  have hstable : (prefixWord ++ tailWord_319999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319999).length < 2 ^ (prefixWord ++ tailWord_319999).sum := by decide
  have hdescent : baseEnd_319999 < baseStart_319999 := by decide
  rcases family_descends (prefixWord ++ tailWord_319999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320012 : List Nat := [2, 2, 1, 2, 4, 1, 2, 3, 5]
def baseStart_320012 : Nat := 118140960795 + 320012 * 2 ^ 59
def prefixEnd_320012 : Nat := 4983230072969 + 3 ^ 40 * 320012 * 2
def baseEnd_320012 : Nat := 36515549157046041172955

theorem tailTrace_320012 : CollatzResearch.WordTrace tailWord_320012 prefixEnd_320012 36515549157046041172955 := by
  unfold tailWord_320012
  simp only [CollatzResearch.WordTrace]
  refine ⟨5835898258329326271753145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7781197677772435029004193 5835898258329326271753145)
  ·
    refine ⟨4376923693746994703814859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5835898258329326271753145 4376923693746994703814859)
    ·
      refine ⟨6565385540620492055722289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4376923693746994703814859 6565385540620492055722289)
      ·
        refine ⟨4924039155465369041791717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6565385540620492055722289 4924039155465369041791717)
        ·
          refine ⟨923257341649756695335947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4924039155465369041791717 923257341649756695335947)
          ·
            refine ⟨1384886012474635043003921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 923257341649756695335947 1384886012474635043003921)
            ·
              refine ⟨1038664509355976282252941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1384886012474635043003921 1038664509355976282252941)
              ·
                refine ⟨389499191008491105844853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1038664509355976282252941 389499191008491105844853)
                ·
                  refine ⟨36515549157046041172955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 389499191008491105844853 36515549157046041172955)
                  ·
                    rfl

theorem cell22_320012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 3, 5].length) (baseStart_320012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_320012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_320012 prefixEnd_320012 := by exact prefixLift 320012
  have htrace : WordTrace (prefixWord ++ tailWord_320012) baseStart_320012 baseEnd_320012 := by
    simpa [prefixWord, tailWord_320012, baseEnd_320012] using wordTrace_append hprefix tailTrace_320012
  have hstable : (prefixWord ++ tailWord_320012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320012).length < 2 ^ (prefixWord ++ tailWord_320012).sum := by decide
  have hdescent : baseEnd_320012 < baseStart_320012 := by decide
  rcases family_descends (prefixWord ++ tailWord_320012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320046 : List Nat := [4, 1, 3, 1, 3, 2, 1, 2, 5]
def baseStart_320046 : Nat := 118140960795 + 320046 * 2 ^ 59
def prefixEnd_320046 : Nat := 4983230072969 + 3 ^ 40 * 320046 * 2
def baseEnd_320046 : Nat := 36519428788657789389587

theorem tailTrace_320046 : CollatzResearch.WordTrace tailWord_320046 prefixEnd_320046 36519428788657789389587 := by
  unfold tailWord_320046
  simp only [CollatzResearch.WordTrace]
  refine ⟨1459129574816934543780499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7782024399023650900162661 1459129574816934543780499)
  ·
    refine ⟨2188694362225401815670749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1459129574816934543780499 2188694362225401815670749)
    ·
      refine ⟨820760385834525680876531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2188694362225401815670749 820760385834525680876531)
      ·
        refine ⟨1231140578751788521314797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 820760385834525680876531 1231140578751788521314797)
        ·
          refine ⟨461677717031920695493049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1231140578751788521314797 461677717031920695493049)
          ·
            refine ⟨346258287773940521619787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 461677717031920695493049 346258287773940521619787)
            ·
              refine ⟨519387431660910782429681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 346258287773940521619787 519387431660910782429681)
              ·
                refine ⟨389540573745683086822261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 519387431660910782429681 389540573745683086822261)
                ·
                  refine ⟨36519428788657789389587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 389540573745683086822261 36519428788657789389587)
                  ·
                    rfl

theorem cell22_320046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 2, 5].length) (baseStart_320046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_320046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_320046 prefixEnd_320046 := by exact prefixLift 320046
  have htrace : WordTrace (prefixWord ++ tailWord_320046) baseStart_320046 baseEnd_320046 := by
    simpa [prefixWord, tailWord_320046, baseEnd_320046] using wordTrace_append hprefix tailTrace_320046
  have hstable : (prefixWord ++ tailWord_320046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320046).length < 2 ^ (prefixWord ++ tailWord_320046).sum := by decide
  have hdescent : baseEnd_320046 < baseStart_320046 := by decide
  rcases family_descends (prefixWord ++ tailWord_320046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320057 : List Nat := [1, 2, 1, 5, 1, 1, 4, 1, 6]
def baseStart_320057 : Nat := 118140960795 + 320057 * 2 ^ 59
def prefixEnd_320057 : Nat := 4983230072969 + 3 ^ 40 * 320057 * 2
def baseEnd_320057 : Nat := 36520683963591002047909

theorem tailTrace_320057 : CollatzResearch.WordTrace tailWord_320057 prefixEnd_320057 36520683963591002047909 := by
  unfold tailWord_320057
  simp only [CollatzResearch.WordTrace]
  refine ⟨11673437801495625228894425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7782291867663750152596283 11673437801495625228894425)
  ·
    refine ⟨8755078351121718921670819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11673437801495625228894425 8755078351121718921670819)
    ·
      refine ⟨13132617526682578382506229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8755078351121718921670819 13132617526682578382506229)
      ·
        refine ⟨1231182893126491723359959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13132617526682578382506229 1231182893126491723359959)
        ·
          refine ⟨1846774339689737585039939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1231182893126491723359959 1846774339689737585039939)
          ·
            refine ⟨2770161509534606377559909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1846774339689737585039939 2770161509534606377559909)
            ·
              refine ⟨519405283037738695792483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2770161509534606377559909 519405283037738695792483)
              ·
                refine ⟨779107924556608043688725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 519405283037738695792483 779107924556608043688725)
                ·
                  refine ⟨36520683963591002047909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 779107924556608043688725 36520683963591002047909)
                  ·
                    rfl

theorem cell22_320057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 1, 6].length) (baseStart_320057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_320057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_320057 prefixEnd_320057 := by exact prefixLift 320057
  have htrace : WordTrace (prefixWord ++ tailWord_320057) baseStart_320057 baseEnd_320057 := by
    simpa [prefixWord, tailWord_320057, baseEnd_320057] using wordTrace_append hprefix tailTrace_320057
  have hstable : (prefixWord ++ tailWord_320057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320057).length < 2 ^ (prefixWord ++ tailWord_320057).sum := by decide
  have hdescent : baseEnd_320057 < baseStart_320057 := by decide
  rcases family_descends (prefixWord ++ tailWord_320057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320087 : List Nat := [1, 1, 3, 2, 2, 2, 2, 3, 2, 4]
def baseStart_320087 : Nat := 118140960795 + 320087 * 2 ^ 59
def prefixEnd_320087 : Nat := 4983230072969 + 3 ^ 40 * 320087 * 2
def baseEnd_320087 : Nat := 109572321503862927893635

theorem tailTrace_320087 : CollatzResearch.WordTrace tailWord_320087 prefixEnd_320087 109572321503862927893635 := by
  unfold tailWord_320087
  simp only [CollatzResearch.WordTrace]
  refine ⟨11674531991386940352486515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7783021327591293568324343 11674531991386940352486515)
  ·
    refine ⟨17511797987080410528729773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11674531991386940352486515 17511797987080410528729773)
    ·
      refine ⟨6566924245155153948273665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17511797987080410528729773 6566924245155153948273665)
      ·
        refine ⟨4925193183866365461205249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6566924245155153948273665 4925193183866365461205249)
        ·
          refine ⟨3693894887899774095903937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4925193183866365461205249 3693894887899774095903937)
          ·
            refine ⟨2770421165924830571927953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3693894887899774095903937 2770421165924830571927953)
            ·
              refine ⟨2077815874443622928945965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2770421165924830571927953 2077815874443622928945965)
              ·
                refine ⟨779180952916358598354737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2077815874443622928945965 779180952916358598354737)
                ·
                  refine ⟨584385714687268948766053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 779180952916358598354737 584385714687268948766053)
                  ·
                    refine ⟨109572321503862927893635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 584385714687268948766053 109572321503862927893635)
                    ·
                      rfl

theorem cell22_320087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 3, 2, 4].length) (baseStart_320087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_320087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_320087 prefixEnd_320087 := by exact prefixLift 320087
  have htrace : WordTrace (prefixWord ++ tailWord_320087) baseStart_320087 baseEnd_320087 := by
    simpa [prefixWord, tailWord_320087, baseEnd_320087] using wordTrace_append hprefix tailTrace_320087
  have hstable : (prefixWord ++ tailWord_320087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320087).length < 2 ^ (prefixWord ++ tailWord_320087).sum := by decide
  have hdescent : baseEnd_320087 < baseStart_320087 := by decide
  rcases family_descends (prefixWord ++ tailWord_320087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320151 : List Nat := [1, 1, 3, 3, 2, 1, 2, 5, 1, 3]
def baseStart_320151 : Nat := 118140960795 + 320151 * 2 ^ 59
def prefixEnd_320151 : Nat := 4983230072969 + 3 ^ 40 * 320151 * 2
def baseEnd_320151 : Nat := 109594230011788094293439

theorem tailTrace_320151 : CollatzResearch.WordTrace tailWord_320151 prefixEnd_320151 109594230011788094293439 := by
  unfold tailWord_320151
  simp only [CollatzResearch.WordTrace]
  refine ⟨11676866263155079282816307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7784577508770052855210871 11676866263155079282816307)
  ·
    refine ⟨17515299394732618924224461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11676866263155079282816307 17515299394732618924224461)
    ·
      refine ⟨6568237273024732096584173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17515299394732618924224461 6568237273024732096584173)
      ·
        refine ⟨2463088977384274536219065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6568237273024732096584173 2463088977384274536219065)
        ·
          refine ⟨1847316733038205902164299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2463088977384274536219065 1847316733038205902164299)
          ·
            refine ⟨2770975099557308853246449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1847316733038205902164299 2770975099557308853246449)
            ·
              refine ⟨2078231324667981639934837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2770975099557308853246449 2078231324667981639934837)
              ·
                refine ⟨194834186687623278743891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2078231324667981639934837 194834186687623278743891)
                ·
                  refine ⟨292251280031434918115837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 194834186687623278743891 292251280031434918115837)
                  ·
                    refine ⟨109594230011788094293439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 292251280031434918115837 109594230011788094293439)
                    ·
                      rfl

theorem cell22_320151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 5, 1, 3].length) (baseStart_320151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_320151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_320151 prefixEnd_320151 := by exact prefixLift 320151
  have htrace : WordTrace (prefixWord ++ tailWord_320151) baseStart_320151 baseEnd_320151 := by
    simpa [prefixWord, tailWord_320151, baseEnd_320151] using wordTrace_append hprefix tailTrace_320151
  have hstable : (prefixWord ++ tailWord_320151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320151).length < 2 ^ (prefixWord ++ tailWord_320151).sum := by decide
  have hdescent : baseEnd_320151 < baseStart_320151 := by decide
  rcases family_descends (prefixWord ++ tailWord_320151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320164 : List Nat := [2, 3, 1, 2, 2, 1, 4, 2, 5]
def baseStart_320164 : Nat := 118140960795 + 320164 * 2 ^ 59
def prefixEnd_320164 : Nat := 4983230072969 + 3 ^ 40 * 320164 * 2
def baseEnd_320164 : Nat := 36532893392486797906133

theorem tailTrace_320164 : CollatzResearch.WordTrace tailWord_320164 prefixEnd_320164 36532893392486797906133 := by
  unfold tailWord_320164
  simp only [CollatzResearch.WordTrace]
  refine ⟨5838670206053991251519773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7784893608071988335359697 5838670206053991251519773)
  ·
    refine ⟨2189501327270246719319915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5838670206053991251519773 2189501327270246719319915)
    ·
      refine ⟨3284251990905370078979873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2189501327270246719319915 3284251990905370078979873)
      ·
        refine ⟨2463188993179027559234905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3284251990905370078979873 2463188993179027559234905)
        ·
          refine ⟨1847391744884270669426179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2463188993179027559234905 1847391744884270669426179)
          ·
            refine ⟨2771087617326406004139269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1847391744884270669426179 2771087617326406004139269)
            ·
              refine ⟨519578928248701125776113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2771087617326406004139269 519578928248701125776113)
              ·
                refine ⟨389684196186525844332085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 519578928248701125776113 389684196186525844332085)
                ·
                  refine ⟨36532893392486797906133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 389684196186525844332085 36532893392486797906133)
                  ·
                    rfl

theorem cell22_320164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 2, 5].length) (baseStart_320164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_320164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_320164 prefixEnd_320164 := by exact prefixLift 320164
  have htrace : WordTrace (prefixWord ++ tailWord_320164) baseStart_320164 baseEnd_320164 := by
    simpa [prefixWord, tailWord_320164, baseEnd_320164] using wordTrace_append hprefix tailTrace_320164
  have hstable : (prefixWord ++ tailWord_320164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320164).length < 2 ^ (prefixWord ++ tailWord_320164).sum := by decide
  have hdescent : baseEnd_320164 < baseStart_320164 := by decide
  rcases family_descends (prefixWord ++ tailWord_320164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320192 : List Nat := [2, 1, 1, 2, 4, 2, 1, 1, 8]
def baseStart_320192 : Nat := 118140960795 + 320192 * 2 ^ 59
def prefixEnd_320192 : Nat := 4983230072969 + 3 ^ 40 * 320192 * 2
def baseEnd_320192 : Nat := 36536088383225884672771

theorem tailTrace_320192 : CollatzResearch.WordTrace tailWord_320192 prefixEnd_320192 36536088383225884672771 := by
  unfold tailWord_320192
  simp only [CollatzResearch.WordTrace]
  refine ⟨5839180828003271642529415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7785574437337695523372553 5839180828003271642529415)
  ·
    refine ⟨8758771242004907463794123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5839180828003271642529415 8758771242004907463794123)
    ·
      refine ⟨13138156863007361195691185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8758771242004907463794123 13138156863007361195691185)
      ·
        refine ⟨9853617647255520896768389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13138156863007361195691185 9853617647255520896768389)
        ·
          refine ⟨1847553308860410168144073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9853617647255520896768389 1847553308860410168144073)
          ·
            refine ⟨1385664981645307626108055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1847553308860410168144073 1385664981645307626108055)
            ·
              refine ⟨2078497472467961439162083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1385664981645307626108055 2078497472467961439162083)
              ·
                refine ⟨3117746208701942158743125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2078497472467961439162083 3117746208701942158743125)
                ·
                  refine ⟨36536088383225884672771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3117746208701942158743125 36536088383225884672771)
                  ·
                    rfl

theorem cell22_320192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 8].length) (baseStart_320192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_320192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_320192 prefixEnd_320192 := by exact prefixLift 320192
  have htrace : WordTrace (prefixWord ++ tailWord_320192) baseStart_320192 baseEnd_320192 := by
    simpa [prefixWord, tailWord_320192, baseEnd_320192] using wordTrace_append hprefix tailTrace_320192
  have hstable : (prefixWord ++ tailWord_320192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320192).length < 2 ^ (prefixWord ++ tailWord_320192).sum := by decide
  have hdescent : baseEnd_320192 < baseStart_320192 := by decide
  rcases family_descends (prefixWord ++ tailWord_320192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320267 : List Nat := [1, 1, 1, 1, 5, 1, 1, 2, 1, 8]
def baseStart_320267 : Nat := 118140960795 + 320267 * 2 ^ 59
def prefixEnd_320267 : Nat := 4983230072969 + 3 ^ 40 * 320267 * 2
def baseEnd_320267 : Nat := 109633939182402458393083

theorem tailTrace_320267 : CollatzResearch.WordTrace tailWord_320267 prefixEnd_320267 109633939182402458393083 := by
  unfold tailWord_320267
  simp only [CollatzResearch.WordTrace]
  refine ⟨11681097130734831094039055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7787398087156554062692703 11681097130734831094039055)
  ·
    refine ⟨17521645696102246641058583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11681097130734831094039055 17521645696102246641058583)
    ·
      refine ⟨26282468544153369961587875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17521645696102246641058583 26282468544153369961587875)
      ·
        refine ⟨39423702816230054942381813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26282468544153369961587875 39423702816230054942381813)
        ·
          refine ⟨3695972139021567650848295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39423702816230054942381813 3695972139021567650848295)
          ·
            refine ⟨5543958208532351476272443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3695972139021567650848295 5543958208532351476272443)
            ·
              refine ⟨8315937312798527214408665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5543958208532351476272443 8315937312798527214408665)
              ·
                refine ⟨6236952984598895410806499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8315937312798527214408665 6236952984598895410806499)
                ·
                  refine ⟨9355429476898343116209749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6236952984598895410806499 9355429476898343116209749)
                  ·
                    refine ⟨109633939182402458393083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 9355429476898343116209749 109633939182402458393083)
                    ·
                      rfl

theorem cell22_320267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 8].length) (baseStart_320267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_320267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_320267 prefixEnd_320267 := by exact prefixLift 320267
  have htrace : WordTrace (prefixWord ++ tailWord_320267) baseStart_320267 baseEnd_320267 := by
    simpa [prefixWord, tailWord_320267, baseEnd_320267] using wordTrace_append hprefix tailTrace_320267
  have hstable : (prefixWord ++ tailWord_320267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320267).length < 2 ^ (prefixWord ++ tailWord_320267).sum := by decide
  have hdescent : baseEnd_320267 < baseStart_320267 := by decide
  rcases family_descends (prefixWord ++ tailWord_320267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320292 : List Nat := [2, 3, 1, 3, 4, 1, 2, 1, 2, 3]
def baseStart_320292 : Nat := 118140960795 + 320292 * 2 ^ 59
def prefixEnd_320292 : Nat := 4983230072969 + 3 ^ 40 * 320292 * 2
def baseEnd_320292 : Nat := 109642497193310726518007

theorem tailTrace_320292 : CollatzResearch.WordTrace tailWord_320292 prefixEnd_320292 109642497193310726518007 := by
  unfold tailWord_320292
  simp only [CollatzResearch.WordTrace]
  refine ⟨5841004477822130181849565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7788005970429506909132753 5841004477822130181849565)
  ·
    refine ⟨2190376679183298818193587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5841004477822130181849565 2190376679183298818193587)
    ·
      refine ⟨3285565018774948227290381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2190376679183298818193587 3285565018774948227290381)
      ·
        refine ⟨1232086882040605585233893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3285565018774948227290381 1232086882040605585233893)
        ·
          refine ⟨231016290382613547231355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1232086882040605585233893 231016290382613547231355)
          ·
            refine ⟨346524435573920320847033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231016290382613547231355 346524435573920320847033)
            ·
              refine ⟨259893326680440240635275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 346524435573920320847033 259893326680440240635275)
              ·
                refine ⟨389839990020660360952913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 259893326680440240635275 389839990020660360952913)
                ·
                  refine ⟨292379992515495270714685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 389839990020660360952913 292379992515495270714685)
                  ·
                    refine ⟨109642497193310726518007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 292379992515495270714685 109642497193310726518007)
                    ·
                      rfl

theorem cell22_320292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 2, 1, 2, 3].length) (baseStart_320292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_320292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_320292 prefixEnd_320292 := by exact prefixLift 320292
  have htrace : WordTrace (prefixWord ++ tailWord_320292) baseStart_320292 baseEnd_320292 := by
    simpa [prefixWord, tailWord_320292, baseEnd_320292] using wordTrace_append hprefix tailTrace_320292
  have hstable : (prefixWord ++ tailWord_320292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320292).length < 2 ^ (prefixWord ++ tailWord_320292).sum := by decide
  have hdescent : baseEnd_320292 < baseStart_320292 := by decide
  rcases family_descends (prefixWord ++ tailWord_320292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320337 : List Nat := [1, 2, 2, 1, 6, 2, 2, 2, 1, 3]
def baseStart_320337 : Nat := 118140960795 + 320337 * 2 ^ 59
def prefixEnd_320337 : Nat := 4983230072969 + 3 ^ 40 * 320337 * 2
def baseEnd_320337 : Nat := 109657901612945609142869

theorem tailTrace_320337 : CollatzResearch.WordTrace tailWord_320337 prefixEnd_320337 109657901612945609142869 := by
  unfold tailWord_320337
  simp only [CollatzResearch.WordTrace]
  refine ⟨11683650240481233049087265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7789100160320822032724843 11683650240481233049087265)
  ·
    refine ⟨8762737680360924786815449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11683650240481233049087265 8762737680360924786815449)
    ·
      refine ⟨6572053260270693590111587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8762737680360924786815449 6572053260270693590111587)
      ·
        refine ⟨9858079890406040385167381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6572053260270693590111587 9858079890406040385167381)
        ·
          refine ⟨462097494862783143054721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 9858079890406040385167381 462097494862783143054721)
          ·
            refine ⟨346573121147087357291041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 462097494862783143054721 346573121147087357291041)
            ·
              refine ⟨259929840860315517968281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 346573121147087357291041 259929840860315517968281)
              ·
                refine ⟨194947380645236638476211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 259929840860315517968281 194947380645236638476211)
                ·
                  refine ⟨292421070967854957714317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 194947380645236638476211 292421070967854957714317)
                  ·
                    refine ⟨109657901612945609142869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 292421070967854957714317 109657901612945609142869)
                    ·
                      rfl

theorem cell22_320337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 2, 2, 1, 3].length) (baseStart_320337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_320337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_320337 prefixEnd_320337 := by exact prefixLift 320337
  have htrace : WordTrace (prefixWord ++ tailWord_320337) baseStart_320337 baseEnd_320337 := by
    simpa [prefixWord, tailWord_320337, baseEnd_320337] using wordTrace_append hprefix tailTrace_320337
  have hstable : (prefixWord ++ tailWord_320337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320337).length < 2 ^ (prefixWord ++ tailWord_320337).sum := by decide
  have hdescent : baseEnd_320337 < baseStart_320337 := by decide
  rcases family_descends (prefixWord ++ tailWord_320337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320389 : List Nat := [1, 3, 1, 1, 3, 4, 9]
def baseStart_320389 : Nat := 118140960795 + 320389 * 2 ^ 59
def prefixEnd_320389 : Nat := 4983230072969 + 3 ^ 40 * 320389 * 2
def baseEnd_320389 : Nat := 4062063047245733586767

theorem tailTrace_320389 : CollatzResearch.WordTrace tailWord_320389 prefixEnd_320389 4062063047245733586767 := by
  unfold tailWord_320389
  simp only [CollatzResearch.WordTrace]
  refine ⟨11685546836292845929980221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7790364557528563953320147 11685546836292845929980221)
  ·
    refine ⟨4382080063609817223742583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11685546836292845929980221 4382080063609817223742583)
    ·
      refine ⟨6573120095414725835613875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4382080063609817223742583 6573120095414725835613875)
      ·
        refine ⟨9859680143122088753420813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6573120095414725835613875 9859680143122088753420813)
        ·
          refine ⟨3697380053670783282532805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9859680143122088753420813 3697380053670783282532805)
          ·
            refine ⟨693258760063271865474901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3697380053670783282532805 693258760063271865474901)
            ·
              refine ⟨4062063047245733586767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 693258760063271865474901 4062063047245733586767)
              ·
                rfl

theorem cell22_320389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 9].length) (baseStart_320389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_320389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_320389 prefixEnd_320389 := by exact prefixLift 320389
  have htrace : WordTrace (prefixWord ++ tailWord_320389) baseStart_320389 baseEnd_320389 := by
    simpa [prefixWord, tailWord_320389, baseEnd_320389] using wordTrace_append hprefix tailTrace_320389
  have hstable : (prefixWord ++ tailWord_320389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320389).length < 2 ^ (prefixWord ++ tailWord_320389).sum := by decide
  have hdescent : baseEnd_320389 < baseStart_320389 := by decide
  rcases family_descends (prefixWord ++ tailWord_320389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320393 : List Nat := [1, 2, 1, 1, 5, 2, 3, 2, 2, 3]
def baseStart_320393 : Nat := 118140960795 + 320393 * 2 ^ 59
def prefixEnd_320393 : Nat := 4983230072969 + 3 ^ 40 * 320393 * 2
def baseEnd_320393 : Nat := 109677071557380129742697

theorem tailTrace_320393 : CollatzResearch.WordTrace tailWord_320393 prefixEnd_320393 109677071557380129742697 := by
  unfold tailWord_320393
  simp only [CollatzResearch.WordTrace]
  refine ⟨11685692728278354613125833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7790461818852236408750555 11685692728278354613125833)
  ·
    refine ⟨8764269546208765959844375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11685692728278354613125833 8764269546208765959844375)
    ·
      refine ⟨13146404319313148939766563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8764269546208765959844375 13146404319313148939766563)
      ·
        refine ⟨19719606478969723409649845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13146404319313148939766563 19719606478969723409649845)
        ·
          refine ⟨1848713107403411569654673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19719606478969723409649845 1848713107403411569654673)
          ·
            refine ⟨1386534830552558677241005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1848713107403411569654673 1386534830552558677241005)
            ·
              refine ⟨519950561457209503965377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1386534830552558677241005 519950561457209503965377)
              ·
                refine ⟨389962921092907127974033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 519950561457209503965377 389962921092907127974033)
                ·
                  refine ⟨292472190819680345980525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 389962921092907127974033 292472190819680345980525)
                  ·
                    refine ⟨109677071557380129742697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 292472190819680345980525 109677071557380129742697)
                    ·
                      rfl

theorem cell22_320393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 2, 2, 3].length) (baseStart_320393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_320393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_320393 prefixEnd_320393 := by exact prefixLift 320393
  have htrace : WordTrace (prefixWord ++ tailWord_320393) baseStart_320393 baseEnd_320393 := by
    simpa [prefixWord, tailWord_320393, baseEnd_320393] using wordTrace_append hprefix tailTrace_320393
  have hstable : (prefixWord ++ tailWord_320393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320393).length < 2 ^ (prefixWord ++ tailWord_320393).sum := by decide
  have hdescent : baseEnd_320393 < baseStart_320393 := by decide
  rcases family_descends (prefixWord ++ tailWord_320393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320410 : List Nat := [3, 1, 1, 4, 4, 1, 1, 1, 1, 5]
def baseStart_320410 : Nat := 118140960795 + 320410 * 2 ^ 59
def prefixEnd_320410 : Nat := 4983230072969 + 3 ^ 40 * 320410 * 2
def baseEnd_320410 : Nat := 109682891004797752067645

theorem tailTrace_320410 : CollatzResearch.WordTrace tailWord_320410 prefixEnd_320410 109682891004797752067645 := by
  unfold tailWord_320410
  simp only [CollatzResearch.WordTrace]
  refine ⟨2921578192304191629123671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7790875179477844344329789 2921578192304191629123671)
  ·
    refine ⟨4382367288456287443685507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2921578192304191629123671 4382367288456287443685507)
    ·
      refine ⟨6573550932684431165528261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4382367288456287443685507 6573550932684431165528261)
      ·
        refine ⟨1232540799878330843536549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6573550932684431165528261 1232540799878330843536549)
        ·
          refine ⟨231101399977187033163103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1232540799878330843536549 231101399977187033163103)
          ·
            refine ⟨346652099965780549744655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231101399977187033163103 346652099965780549744655)
            ·
              refine ⟨519978149948670824616983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 346652099965780549744655 519978149948670824616983)
              ·
                refine ⟨779967224923006236925475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 519978149948670824616983 779967224923006236925475)
                ·
                  refine ⟨1169950837384509355388213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 779967224923006236925475 1169950837384509355388213)
                  ·
                    refine ⟨109682891004797752067645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1169950837384509355388213 109682891004797752067645)
                    ·
                      rfl

theorem cell22_320410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 1, 1, 5].length) (baseStart_320410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_320410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_320410 prefixEnd_320410 := by exact prefixLift 320410
  have htrace : WordTrace (prefixWord ++ tailWord_320410) baseStart_320410 baseEnd_320410 := by
    simpa [prefixWord, tailWord_320410, baseEnd_320410] using wordTrace_append hprefix tailTrace_320410
  have hstable : (prefixWord ++ tailWord_320410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320410).length < 2 ^ (prefixWord ++ tailWord_320410).sum := by decide
  have hdescent : baseEnd_320410 < baseStart_320410 := by decide
  rcases family_descends (prefixWord ++ tailWord_320410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320419 : List Nat := [1, 1, 1, 4, 1, 2, 2, 2, 2, 6]
def baseStart_320419 : Nat := 118140960795 + 320419 * 2 ^ 59
def prefixEnd_320419 : Nat := 4983230072969 + 3 ^ 40 * 320419 * 2
def baseEnd_320419 : Nat := 109685971888724728592617

theorem tailTrace_320419 : CollatzResearch.WordTrace tailWord_320419 prefixEnd_320419 109685971888724728592617 := by
  unfold tailWord_320419
  simp only [CollatzResearch.WordTrace]
  refine ⟨11686641026184161053572311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7791094017456107369048207 11686641026184161053572311)
  ·
    refine ⟨17529961539276241580358467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11686641026184161053572311 17529961539276241580358467)
    ·
      refine ⟨26294942308914362370537701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17529961539276241580358467 26294942308914362370537701)
      ·
        refine ⟨4930301682921442944475819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26294942308914362370537701 4930301682921442944475819)
        ·
          refine ⟨7395452524382164416713729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4930301682921442944475819 7395452524382164416713729)
          ·
            refine ⟨5546589393286623312535297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7395452524382164416713729 5546589393286623312535297)
            ·
              refine ⟨4159942044964967484401473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5546589393286623312535297 4159942044964967484401473)
              ·
                refine ⟨3119956533723725613301105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4159942044964967484401473 3119956533723725613301105)
                ·
                  refine ⟨2339967400292794209975829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3119956533723725613301105 2339967400292794209975829)
                  ·
                    refine ⟨109685971888724728592617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2339967400292794209975829 109685971888724728592617)
                    ·
                      rfl

theorem cell22_320419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 6].length) (baseStart_320419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_320419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_320419 prefixEnd_320419 := by exact prefixLift 320419
  have htrace : WordTrace (prefixWord ++ tailWord_320419) baseStart_320419 baseEnd_320419 := by
    simpa [prefixWord, tailWord_320419, baseEnd_320419] using wordTrace_append hprefix tailTrace_320419
  have hstable : (prefixWord ++ tailWord_320419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320419).length < 2 ^ (prefixWord ++ tailWord_320419).sum := by decide
  have hdescent : baseEnd_320419 < baseStart_320419 := by decide
  rcases family_descends (prefixWord ++ tailWord_320419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320429 : List Nat := [1, 5, 2, 3, 2, 1, 1, 3, 4]
def baseStart_320429 : Nat := 118140960795 + 320429 * 2 ^ 59
def prefixEnd_320429 : Nat := 4983230072969 + 3 ^ 40 * 320429 * 2
def baseEnd_320429 : Nat := 36563131697696011947529

theorem tailTrace_320429 : CollatzResearch.WordTrace tailWord_320429 prefixEnd_320429 36563131697696011947529 := by
  unfold tailWord_320429
  simp only [CollatzResearch.WordTrace]
  refine ⟨11687005756147932761436341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7791337170765288507624227 11687005756147932761436341)
  ·
    refine ⟨1095656789638868696384657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11687005756147932761436341 1095656789638868696384657)
    ·
      refine ⟨821742592229151522288493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1095656789638868696384657 821742592229151522288493)
      ·
        refine ⟨308153472085931820858185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 821742592229151522288493 308153472085931820858185)
        ·
          refine ⟨231115104064448865643639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 308153472085931820858185 231115104064448865643639)
          ·
            refine ⟨346672656096673298465459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231115104064448865643639 346672656096673298465459)
            ·
              refine ⟨520008984145009947698189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 346672656096673298465459 520008984145009947698189)
              ·
                refine ⟨195003369054378730386821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 520008984145009947698189 195003369054378730386821)
                ·
                  refine ⟨36563131697696011947529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 195003369054378730386821 36563131697696011947529)
                  ·
                    rfl

theorem cell22_320429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 3, 4].length) (baseStart_320429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_320429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_320429 prefixEnd_320429 := by exact prefixLift 320429
  have htrace : WordTrace (prefixWord ++ tailWord_320429) baseStart_320429 baseEnd_320429 := by
    simpa [prefixWord, tailWord_320429, baseEnd_320429] using wordTrace_append hprefix tailTrace_320429
  have hstable : (prefixWord ++ tailWord_320429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320429).length < 2 ^ (prefixWord ++ tailWord_320429).sum := by decide
  have hdescent : baseEnd_320429 < baseStart_320429 := by decide
  rcases family_descends (prefixWord ++ tailWord_320429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320464 : List Nat := [2, 1, 1, 1, 1, 2, 3, 1, 2, 8]
def baseStart_320464 : Nat := 118140960795 + 320464 * 2 ^ 59
def prefixEnd_320464 : Nat := 4983230072969 + 3 ^ 40 * 320464 * 2
def baseEnd_320464 : Nat := 109701376308359611217479

theorem tailTrace_320464 : CollatzResearch.WordTrace tailWord_320464 prefixEnd_320464 109701376308359611217479 := by
  unfold tailWord_320464
  simp only [CollatzResearch.WordTrace]
  refine ⟨5844141155510566869480223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7792188207347422492640297 5844141155510566869480223)
  ·
    refine ⟨8766211733265850304220335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5844141155510566869480223 8766211733265850304220335)
    ·
      refine ⟨13149317599898775456330503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8766211733265850304220335 13149317599898775456330503)
      ·
        refine ⟨19723976399848163184495755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13149317599898775456330503 19723976399848163184495755)
        ·
          refine ⟨29585964599772244776743633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19723976399848163184495755 29585964599772244776743633)
          ·
            refine ⟨22189473449829183582557725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29585964599772244776743633 22189473449829183582557725)
            ·
              refine ⟨8321052543685943843459147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22189473449829183582557725 8321052543685943843459147)
              ·
                refine ⟨12481578815528915765188721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8321052543685943843459147 12481578815528915765188721)
                ·
                  refine ⟨9361184111646686823891541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12481578815528915765188721 9361184111646686823891541)
                  ·
                    refine ⟨109701376308359611217479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 9361184111646686823891541 109701376308359611217479)
                    ·
                      rfl

theorem cell22_320464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 2, 8].length) (baseStart_320464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_320464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_320464 prefixEnd_320464 := by exact prefixLift 320464
  have htrace : WordTrace (prefixWord ++ tailWord_320464) baseStart_320464 baseEnd_320464 := by
    simpa [prefixWord, tailWord_320464, baseEnd_320464] using wordTrace_append hprefix tailTrace_320464
  have hstable : (prefixWord ++ tailWord_320464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320464).length < 2 ^ (prefixWord ++ tailWord_320464).sum := by decide
  have hdescent : baseEnd_320464 < baseStart_320464 := by decide
  rcases family_descends (prefixWord ++ tailWord_320464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320468 : List Nat := [2, 4, 1, 2, 1, 3, 1, 3, 5]
def baseStart_320468 : Nat := 118140960795 + 320468 * 2 ^ 59
def prefixEnd_320468 : Nat := 4983230072969 + 3 ^ 40 * 320468 * 2
def baseEnd_320468 : Nat := 36567581863368311372489

theorem tailTrace_320468 : CollatzResearch.WordTrace tailWord_320468 prefixEnd_320468 36567581863368311372489 := by
  unfold tailWord_320468
  simp only [CollatzResearch.WordTrace]
  refine ⟨5844214101503321211053029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7792285468671094948070705 5844214101503321211053029)
  ·
    refine ⟨1095790144031872727072443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5844214101503321211053029 1095790144031872727072443)
    ·
      refine ⟨1643685216047809090608665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1095790144031872727072443 1643685216047809090608665)
      ·
        refine ⟨1232763912035856817956499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1643685216047809090608665 1232763912035856817956499)
        ·
          refine ⟨1849145868053785226934749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1232763912035856817956499 1849145868053785226934749)
          ·
            refine ⟨693429700520169460100531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1849145868053785226934749 693429700520169460100531)
            ·
              refine ⟨1040144550780254190150797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 693429700520169460100531 1040144550780254190150797)
              ·
                refine ⟨390054206542595321306549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1040144550780254190150797 390054206542595321306549)
                ·
                  refine ⟨36567581863368311372489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 390054206542595321306549 36567581863368311372489)
                  ·
                    rfl

theorem cell22_320468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 3, 5].length) (baseStart_320468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_320468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_320468 prefixEnd_320468 := by exact prefixLift 320468
  have htrace : WordTrace (prefixWord ++ tailWord_320468) baseStart_320468 baseEnd_320468 := by
    simpa [prefixWord, tailWord_320468, baseEnd_320468] using wordTrace_append hprefix tailTrace_320468
  have hstable : (prefixWord ++ tailWord_320468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320468).length < 2 ^ (prefixWord ++ tailWord_320468).sum := by decide
  have hdescent : baseEnd_320468 < baseStart_320468 := by decide
  rcases family_descends (prefixWord ++ tailWord_320468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320543 : List Nat := [1, 1, 2, 4, 1, 3, 3, 1, 2, 4]
def baseStart_320543 : Nat := 118140960795 + 320543 * 2 ^ 59
def prefixEnd_320543 : Nat := 4983230072969 + 3 ^ 40 * 320543 * 2
def baseEnd_320543 : Nat := 109728419622829738492237

theorem tailTrace_320543 : CollatzResearch.WordTrace tailWord_320543 prefixEnd_320543 109728419622829738492237 := by
  unfold tailWord_320543
  simp only [CollatzResearch.WordTrace]
  refine ⟨11691163677734930231086283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7794109118489953487390855 11691163677734930231086283)
  ·
    refine ⟨17536745516602395346629425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11691163677734930231086283 17536745516602395346629425)
    ·
      refine ⟨13152559137451796509972069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17536745516602395346629425 13152559137451796509972069)
      ·
        refine ⟨2466104838272211845619763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13152559137451796509972069 2466104838272211845619763)
        ·
          refine ⟨3699157257408317768429645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2466104838272211845619763 3699157257408317768429645)
          ·
            refine ⟨1387183971528119163161117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3699157257408317768429645 1387183971528119163161117)
            ·
              refine ⟨520193989323044686185419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1387183971528119163161117 520193989323044686185419)
              ·
                refine ⟨780290983984567029278129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 520193989323044686185419 780290983984567029278129)
                ·
                  refine ⟨585218237988425271958597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 780290983984567029278129 585218237988425271958597)
                  ·
                    refine ⟨109728419622829738492237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 585218237988425271958597 109728419622829738492237)
                    ·
                      rfl

theorem cell22_320543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 1, 2, 4].length) (baseStart_320543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_320543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_320543 prefixEnd_320543 := by exact prefixLift 320543
  have htrace : WordTrace (prefixWord ++ tailWord_320543) baseStart_320543 baseEnd_320543 := by
    simpa [prefixWord, tailWord_320543, baseEnd_320543] using wordTrace_append hprefix tailTrace_320543
  have hstable : (prefixWord ++ tailWord_320543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320543).length < 2 ^ (prefixWord ++ tailWord_320543).sum := by decide
  have hdescent : baseEnd_320543 < baseStart_320543 := by decide
  rcases family_descends (prefixWord ++ tailWord_320543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320601 : List Nat := [1, 2, 1, 2, 2, 1, 2, 2, 4, 5]
def baseStart_320601 : Nat := 118140960795 + 320601 * 2 ^ 59
def prefixEnd_320601 : Nat := 4983230072969 + 3 ^ 40 * 320601 * 2
def baseEnd_320601 : Nat := 109748274208136920542059

theorem tailTrace_320601 : CollatzResearch.WordTrace tailWord_320601 prefixEnd_320601 109748274208136920542059 := by
  unfold tailWord_320601
  simp only [CollatzResearch.WordTrace]
  refine ⟨11693279111524806136697657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7795519407683204091131771 11693279111524806136697657)
  ·
    refine ⟨8769959333643604602523243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11693279111524806136697657 8769959333643604602523243)
    ·
      refine ⟨13154939000465406903784865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8769959333643604602523243 13154939000465406903784865)
      ·
        refine ⟨9866204250349055177838649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13154939000465406903784865 9866204250349055177838649)
        ·
          refine ⟨7399653187761791383378987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9866204250349055177838649 7399653187761791383378987)
          ·
            refine ⟨11099479781642687075068481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7399653187761791383378987 11099479781642687075068481)
            ·
              refine ⟨8324609836232015306301361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11099479781642687075068481 8324609836232015306301361)
              ·
                refine ⟨6243457377174011479726021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8324609836232015306301361 6243457377174011479726021)
                ·
                  refine ⟨1170648258220127152448629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6243457377174011479726021 1170648258220127152448629)
                  ·
                    refine ⟨109748274208136920542059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1170648258220127152448629 109748274208136920542059)
                    ·
                      rfl

theorem cell22_320601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 4, 5].length) (baseStart_320601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_320601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_320601 prefixEnd_320601 := by exact prefixLift 320601
  have htrace : WordTrace (prefixWord ++ tailWord_320601) baseStart_320601 baseEnd_320601 := by
    simpa [prefixWord, tailWord_320601, baseEnd_320601] using wordTrace_append hprefix tailTrace_320601
  have hstable : (prefixWord ++ tailWord_320601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320601).length < 2 ^ (prefixWord ++ tailWord_320601).sum := by decide
  have hdescent : baseEnd_320601 < baseStart_320601 := by decide
  rcases family_descends (prefixWord ++ tailWord_320601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320663 : List Nat := [1, 1, 3, 3, 3, 1, 1, 1, 3, 5]
def baseStart_320663 : Nat := 118140960795 + 320663 * 2 ^ 59
def prefixEnd_320663 : Nat := 4983230072969 + 3 ^ 40 * 320663 * 2
def baseEnd_320663 : Nat := 109769498075189425491869

theorem tailTrace_320663 : CollatzResearch.WordTrace tailWord_320663 prefixEnd_320663 109769498075189425491869 := by
  unfold tailWord_320663
  simp only [CollatzResearch.WordTrace]
  refine ⟨11695540437300190725454643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7797026958200127150303095 11695540437300190725454643)
  ·
    refine ⟨17543310655950286088181965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11695540437300190725454643 17543310655950286088181965)
    ·
      refine ⟨6578741495981357283068237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17543310655950286088181965 6578741495981357283068237)
      ·
        refine ⟨2467028060993008981150589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6578741495981357283068237 2467028060993008981150589)
        ·
          refine ⟨925135522872378367931471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2467028060993008981150589 925135522872378367931471)
          ·
            refine ⟨1387703284308567551897207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 925135522872378367931471 1387703284308567551897207)
            ·
              refine ⟨2081554926462851327845811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1387703284308567551897207 2081554926462851327845811)
              ·
                refine ⟨3122332389694276991768717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2081554926462851327845811 3122332389694276991768717)
                ·
                  refine ⟨1170874646135353871913269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3122332389694276991768717 1170874646135353871913269)
                  ·
                    refine ⟨109769498075189425491869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1170874646135353871913269 109769498075189425491869)
                    ·
                      rfl

theorem cell22_320663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 3, 5].length) (baseStart_320663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_320663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_320663 prefixEnd_320663 := by exact prefixLift 320663
  have htrace : WordTrace (prefixWord ++ tailWord_320663) baseStart_320663 baseEnd_320663 := by
    simpa [prefixWord, tailWord_320663, baseEnd_320663] using wordTrace_append hprefix tailTrace_320663
  have hstable : (prefixWord ++ tailWord_320663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320663).length < 2 ^ (prefixWord ++ tailWord_320663).sum := by decide
  have hdescent : baseEnd_320663 < baseStart_320663 := by decide
  rcases family_descends (prefixWord ++ tailWord_320663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320776 : List Nat := [2, 1, 3, 2, 4, 2, 1, 3, 1, 3]
def baseStart_320776 : Nat := 118140960795 + 320776 * 2 ^ 59
def prefixEnd_320776 : Nat := 4983230072969 + 3 ^ 40 * 320776 * 2
def baseEnd_320776 : Nat := 109808180284494797416523

theorem tailTrace_320776 : CollatzResearch.WordTrace tailWord_320776 prefixEnd_320776 109808180284494797416523 := by
  unfold tailWord_320776
  simp only [CollatzResearch.WordTrace]
  refine ⟨5849830942945405512159091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7799774590593874016212121 5849830942945405512159091)
  ·
    refine ⟨8774746414418108268238637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5849830942945405512159091 8774746414418108268238637)
    ·
      refine ⟨3290529905406790600589489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8774746414418108268238637 3290529905406790600589489)
      ·
        refine ⟨2467897429055092950442117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3290529905406790600589489 2467897429055092950442117)
        ·
          refine ⟨462730767947829928207897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2467897429055092950442117 462730767947829928207897)
          ·
            refine ⟨347048075960872446155923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 462730767947829928207897 347048075960872446155923)
            ·
              refine ⟨520572113941308669233885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 347048075960872446155923 520572113941308669233885)
              ·
                refine ⟨195214542727990750962707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 520572113941308669233885 195214542727990750962707)
                ·
                  refine ⟨292821814091986126444061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 195214542727990750962707 292821814091986126444061)
                  ·
                    refine ⟨109808180284494797416523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 292821814091986126444061 109808180284494797416523)
                    ·
                      rfl

theorem cell22_320776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 3, 1, 3].length) (baseStart_320776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_320776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_320776 prefixEnd_320776 := by exact prefixLift 320776
  have htrace : WordTrace (prefixWord ++ tailWord_320776) baseStart_320776 baseEnd_320776 := by
    simpa [prefixWord, tailWord_320776, baseEnd_320776] using wordTrace_append hprefix tailTrace_320776
  have hstable : (prefixWord ++ tailWord_320776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320776).length < 2 ^ (prefixWord ++ tailWord_320776).sum := by decide
  have hdescent : baseEnd_320776 < baseStart_320776 := by decide
  rcases family_descends (prefixWord ++ tailWord_320776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320785 : List Nat := [1, 2, 2, 1, 1, 4, 1, 5, 1, 4]
def baseStart_320785 : Nat := 118140960795 + 320785 * 2 ^ 59
def prefixEnd_320785 : Nat := 4983230072969 + 3 ^ 40 * 320785 * 2
def baseEnd_320785 : Nat := 109811261168421773941495

theorem tailTrace_320785 : CollatzResearch.WordTrace tailWord_320785 prefixEnd_320785 109811261168421773941495 := by
  unfold tailWord_320785
  simp only [CollatzResearch.WordTrace]
  refine ⟨11699990142858205561395809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7799993428572137040930539 11699990142858205561395809)
  ·
    refine ⟨8774992607143654171046857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11699990142858205561395809 8774992607143654171046857)
    ·
      refine ⟨6581244455357740628285143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8774992607143654171046857 6581244455357740628285143)
      ·
        refine ⟨9871866683036610942427715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6581244455357740628285143 9871866683036610942427715)
        ·
          refine ⟨14807800024554916413641573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9871866683036610942427715 14807800024554916413641573)
          ·
            refine ⟨2776462504604046827557795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14807800024554916413641573 2776462504604046827557795)
            ·
              refine ⟨4164693756906070241336693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2776462504604046827557795 4164693756906070241336693)
              ·
                refine ⟨390440039709944085125315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4164693756906070241336693 390440039709944085125315)
                ·
                  refine ⟨585660059564916127687973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 390440039709944085125315 585660059564916127687973)
                  ·
                    refine ⟨109811261168421773941495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 585660059564916127687973 109811261168421773941495)
                    ·
                      rfl

theorem cell22_320785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 4].length) (baseStart_320785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_320785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_320785 prefixEnd_320785 := by exact prefixLift 320785
  have htrace : WordTrace (prefixWord ++ tailWord_320785) baseStart_320785 baseEnd_320785 := by
    simpa [prefixWord, tailWord_320785, baseEnd_320785] using wordTrace_append hprefix tailTrace_320785
  have hstable : (prefixWord ++ tailWord_320785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320785).length < 2 ^ (prefixWord ++ tailWord_320785).sum := by decide
  have hdescent : baseEnd_320785 < baseStart_320785 := by decide
  rcases family_descends (prefixWord ++ tailWord_320785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320836 : List Nat := [2, 3, 4, 1, 1, 2, 3, 1, 1, 4]
def baseStart_320836 : Nat := 118140960795 + 320836 * 2 ^ 59
def prefixEnd_320836 : Nat := 4983230072969 + 3 ^ 40 * 320836 * 2
def baseEnd_320836 : Nat := 109828719510674640916339

theorem tailTrace_320836 : CollatzResearch.WordTrace tailWord_320836 prefixEnd_320836 109828719510674640916339 := by
  unfold tailWord_320836
  simp only [CollatzResearch.WordTrace]
  refine ⟨5850925132836720635751181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7801233510448960847668241 5850925132836720635751181)
  ·
    refine ⟨2194096924813770238406693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5850925132836720635751181 2194096924813770238406693)
    ·
      refine ⟨411393173402581919701255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2194096924813770238406693 411393173402581919701255)
      ·
        refine ⟨617089760103872879551883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 411393173402581919701255 617089760103872879551883)
        ·
          refine ⟨925634640155809319327825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 617089760103872879551883 925634640155809319327825)
          ·
            refine ⟨694225980116856989495869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 925634640155809319327825 694225980116856989495869)
            ·
              refine ⟨260334742543821371060951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 694225980116856989495869 260334742543821371060951)
              ·
                refine ⟨390502113815732056591427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 260334742543821371060951 390502113815732056591427)
                ·
                  refine ⟨585753170723598084887141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 390502113815732056591427 585753170723598084887141)
                  ·
                    refine ⟨109828719510674640916339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 585753170723598084887141 109828719510674640916339)
                    ·
                      rfl

theorem cell22_320836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_320836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_320836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_320836 prefixEnd_320836 := by exact prefixLift 320836
  have htrace : WordTrace (prefixWord ++ tailWord_320836) baseStart_320836 baseEnd_320836 := by
    simpa [prefixWord, tailWord_320836, baseEnd_320836] using wordTrace_append hprefix tailTrace_320836
  have hstable : (prefixWord ++ tailWord_320836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320836).length < 2 ^ (prefixWord ++ tailWord_320836).sum := by decide
  have hdescent : baseEnd_320836 < baseStart_320836 := by decide
  rcases family_descends (prefixWord ++ tailWord_320836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320843 : List Nat := [1, 1, 1, 1, 3, 1, 1, 2, 4, 7]
def baseStart_320843 : Nat := 118140960795 + 320843 * 2 ^ 59
def prefixEnd_320843 : Nat := 4983230072969 + 3 ^ 40 * 320843 * 2
def baseEnd_320843 : Nat := 109831115753728955991317

theorem tailTrace_320843 : CollatzResearch.WordTrace tailWord_320843 prefixEnd_320843 109831115753728955991317 := by
  unfold tailWord_320843
  simp only [CollatzResearch.WordTrace]
  refine ⟨11702105576648081467007183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7801403717765387644671455 11702105576648081467007183)
  ·
    refine ⟨17553158364972122200510775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11702105576648081467007183 17553158364972122200510775)
    ·
      refine ⟨26329737547458183300766163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17553158364972122200510775 26329737547458183300766163)
      ·
        refine ⟨39494606321187274951149245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26329737547458183300766163 39494606321187274951149245)
        ·
          refine ⟨14810477370445228106680967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39494606321187274951149245 14810477370445228106680967)
          ·
            refine ⟨22215716055667842160021451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14810477370445228106680967 22215716055667842160021451)
            ·
              refine ⟨33323574083501763240032177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22215716055667842160021451 33323574083501763240032177)
              ·
                refine ⟨24992680562626322430024133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33323574083501763240032177 24992680562626322430024133)
                ·
                  refine ⟨4686127605492435455629525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24992680562626322430024133 4686127605492435455629525)
                  ·
                    refine ⟨109831115753728955991317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4686127605492435455629525 109831115753728955991317)
                    ·
                      rfl

theorem cell22_320843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 7].length) (baseStart_320843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_320843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_320843 prefixEnd_320843 := by exact prefixLift 320843
  have htrace : WordTrace (prefixWord ++ tailWord_320843) baseStart_320843 baseEnd_320843 := by
    simpa [prefixWord, tailWord_320843, baseEnd_320843] using wordTrace_append hprefix tailTrace_320843
  have hstable : (prefixWord ++ tailWord_320843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320843).length < 2 ^ (prefixWord ++ tailWord_320843).sum := by decide
  have hdescent : baseEnd_320843 < baseStart_320843 := by decide
  rcases family_descends (prefixWord ++ tailWord_320843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320877 : List Nat := [1, 5, 1, 1, 1, 3, 1, 1, 5, 3]
def baseStart_320877 : Nat := 118140960795 + 320877 * 2 ^ 59
def prefixEnd_320877 : Nat := 4983230072969 + 3 ^ 40 * 320877 * 2
def baseEnd_320877 : Nat := 109842754648564200641213

theorem tailTrace_320877 : CollatzResearch.WordTrace tailWord_320877 prefixEnd_320877 109842754648564200641213 := by
  unfold tailWord_320877
  simp only [CollatzResearch.WordTrace]
  refine ⟨11703345658524905273744885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7802230439016603515829923 11703345658524905273744885)
  ·
    refine ⟨1097188655486709869413583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11703345658524905273744885 1097188655486709869413583)
    ·
      refine ⟨1645782983230064804120375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1097188655486709869413583 1645782983230064804120375)
      ·
        refine ⟨2468674474845097206180563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1645782983230064804120375 2468674474845097206180563)
        ·
          refine ⟨3703011712267645809270845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2468674474845097206180563 3703011712267645809270845)
          ·
            refine ⟨1388629392100367178476567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3703011712267645809270845 1388629392100367178476567)
            ·
              refine ⟨2082944088150550767714851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1388629392100367178476567 2082944088150550767714851)
              ·
                refine ⟨3124416132225826151572277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2082944088150550767714851 3124416132225826151572277)
                ·
                  refine ⟨292914012396171201709901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3124416132225826151572277 292914012396171201709901)
                  ·
                    refine ⟨109842754648564200641213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 292914012396171201709901 109842754648564200641213)
                    ·
                      rfl

theorem cell22_320877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 5, 3].length) (baseStart_320877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_320877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_320877 prefixEnd_320877 := by exact prefixLift 320877
  have htrace : WordTrace (prefixWord ++ tailWord_320877) baseStart_320877 baseEnd_320877 := by
    simpa [prefixWord, tailWord_320877, baseEnd_320877] using wordTrace_append hprefix tailTrace_320877
  have hstable : (prefixWord ++ tailWord_320877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320877).length < 2 ^ (prefixWord ++ tailWord_320877).sum := by decide
  have hdescent : baseEnd_320877 < baseStart_320877 := by decide
  rcases family_descends (prefixWord ++ tailWord_320877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320962 : List Nat := [3, 5, 2, 1, 1, 2, 1, 1, 3, 3]
def baseStart_320962 : Nat := 118140960795 + 320962 * 2 ^ 59
def prefixEnd_320962 : Nat := 4983230072969 + 3 ^ 40 * 320962 * 2
def baseEnd_320962 : Nat := 109871851885652312265953

theorem tailTrace_320962 : CollatzResearch.WordTrace tailWord_320962 prefixEnd_320962 109871851885652312265953 := by
  unfold tailWord_320962
  simp only [CollatzResearch.WordTrace]
  refine ⟨2926611465804241197647285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7804297242144643193726093 2926611465804241197647285)
  ·
    refine ⟨274369824919147612279433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2926611465804241197647285 274369824919147612279433)
    ·
      refine ⟨205777368689360709209575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 274369824919147612279433 205777368689360709209575)
      ·
        refine ⟨308666053034041063814363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205777368689360709209575 308666053034041063814363)
        ·
          refine ⟨462999079551061595721545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 308666053034041063814363 462999079551061595721545)
          ·
            refine ⟨347249309663296196791159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 462999079551061595721545 347249309663296196791159)
            ·
              refine ⟨520873964494944295186739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 347249309663296196791159 520873964494944295186739)
              ·
                refine ⟨781310946742416442780109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 520873964494944295186739 781310946742416442780109)
                ·
                  refine ⟨292991605028406166042541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 781310946742416442780109 292991605028406166042541)
                  ·
                    refine ⟨109871851885652312265953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 292991605028406166042541 109871851885652312265953)
                    ·
                      rfl

theorem cell22_320962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_320962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_320962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_320962 prefixEnd_320962 := by exact prefixLift 320962
  have htrace : WordTrace (prefixWord ++ tailWord_320962) baseStart_320962 baseEnd_320962 := by
    simpa [prefixWord, tailWord_320962, baseEnd_320962] using wordTrace_append hprefix tailTrace_320962
  have hstable : (prefixWord ++ tailWord_320962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320962).length < 2 ^ (prefixWord ++ tailWord_320962).sum := by decide
  have hdescent : baseEnd_320962 < baseStart_320962 := by decide
  rcases family_descends (prefixWord ++ tailWord_320962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320967 : List Nat := [1, 1, 4, 1, 1, 3, 1, 3, 4, 3]
def baseStart_320967 : Nat := 118140960795 + 320967 * 2 ^ 59
def prefixEnd_320967 : Nat := 4983230072969 + 3 ^ 40 * 320967 * 2
def baseEnd_320967 : Nat := 109873563487833965890937

theorem tailTrace_320967 : CollatzResearch.WordTrace tailWord_320967 prefixEnd_320967 109873563487833965890937 := by
  unfold tailWord_320967
  simp only [CollatzResearch.WordTrace]
  refine ⟨11706628228198850644521155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7804418818799233763014103 11706628228198850644521155)
  ·
    refine ⟨17559942342298275966781733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11706628228198850644521155 17559942342298275966781733)
    ·
      refine ⟨3292489189180926743771575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17559942342298275966781733 3292489189180926743771575)
      ·
        refine ⟨4938733783771390115657363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3292489189180926743771575 4938733783771390115657363)
        ·
          refine ⟨7408100675657085173486045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4938733783771390115657363 7408100675657085173486045)
          ·
            refine ⟨2778037753371406940057267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7408100675657085173486045 2778037753371406940057267)
            ·
              refine ⟨4167056630057110410085901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2778037753371406940057267 4167056630057110410085901)
              ·
                refine ⟨1562646236271416403782213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4167056630057110410085901 1562646236271416403782213)
                ·
                  refine ⟨292996169300890575709165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1562646236271416403782213 292996169300890575709165)
                  ·
                    refine ⟨109873563487833965890937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 292996169300890575709165 109873563487833965890937)
                    ·
                      rfl

theorem cell22_320967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 4, 3].length) (baseStart_320967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_320967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_320967 prefixEnd_320967 := by exact prefixLift 320967
  have htrace : WordTrace (prefixWord ++ tailWord_320967) baseStart_320967 baseEnd_320967 := by
    simpa [prefixWord, tailWord_320967, baseEnd_320967] using wordTrace_append hprefix tailTrace_320967
  have hstable : (prefixWord ++ tailWord_320967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320967).length < 2 ^ (prefixWord ++ tailWord_320967).sum := by decide
  have hdescent : baseEnd_320967 < baseStart_320967 := by decide
  rcases family_descends (prefixWord ++ tailWord_320967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320997 : List Nat := [1, 3, 1, 5, 1, 1, 2, 8]
def baseStart_320997 : Nat := 118140960795 + 320997 * 2 ^ 59
def prefixEnd_320997 : Nat := 4983230072969 + 3 ^ 40 * 320997 * 2
def baseEnd_320997 : Nat := 12209314788991543071205

theorem tailTrace_320997 : CollatzResearch.WordTrace tailWord_320997 prefixEnd_320997 12209314788991543071205 := by
  unfold tailWord_320997
  simp only [CollatzResearch.WordTrace]
  refine ⟨11707722418090165768113245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7805148278726777178742163 11707722418090165768113245)
  ·
    refine ⟨4390395906783812163042467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11707722418090165768113245 4390395906783812163042467)
    ·
      refine ⟨6585593860175718244563701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4390395906783812163042467 6585593860175718244563701)
      ·
        refine ⟨617399424391473585427847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6585593860175718244563701 617399424391473585427847)
        ·
          refine ⟨926099136587210378141771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 617399424391473585427847 926099136587210378141771)
          ·
            refine ⟨1389148704880815567212657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 926099136587210378141771 1389148704880815567212657)
            ·
              refine ⟨1041861528660611675409493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1389148704880815567212657 1041861528660611675409493)
              ·
                refine ⟨12209314788991543071205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1041861528660611675409493 12209314788991543071205)
                ·
                  rfl

theorem cell22_320997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 8].length) (baseStart_320997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_320997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_320997 prefixEnd_320997 := by exact prefixLift 320997
  have htrace : WordTrace (prefixWord ++ tailWord_320997) baseStart_320997 baseEnd_320997 := by
    simpa [prefixWord, tailWord_320997, baseEnd_320997] using wordTrace_append hprefix tailTrace_320997
  have hstable : (prefixWord ++ tailWord_320997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320997).length < 2 ^ (prefixWord ++ tailWord_320997).sum := by decide
  have hdescent : baseEnd_320997 < baseStart_320997 := by decide
  rcases family_descends (prefixWord ++ tailWord_320997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320999 : List Nat := [1, 1, 5, 2, 1, 3, 2, 1, 2, 4]
def baseStart_320999 : Nat := 118140960795 + 320999 * 2 ^ 59
def prefixEnd_320999 : Nat := 4983230072969 + 3 ^ 40 * 320999 * 2
def baseEnd_320999 : Nat := 109884517741796549090839

theorem tailTrace_320999 : CollatzResearch.WordTrace tailWord_320999 prefixEnd_320999 109884517741796549090839 := by
  unfold tailWord_320999
  simp only [CollatzResearch.WordTrace]
  refine ⟨11707795364082920109686051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7805196909388613406457367 11707795364082920109686051)
  ·
    refine ⟨17561693046124380164529077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11707795364082920109686051 17561693046124380164529077)
    ·
      refine ⟨1646408723074160640424601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17561693046124380164529077 1646408723074160640424601)
      ·
        refine ⟨1234806542305620480318451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1646408723074160640424601 1234806542305620480318451)
        ·
          refine ⟨1852209813458430720477677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1234806542305620480318451 1852209813458430720477677)
          ·
            refine ⟨694578680046911520179129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1852209813458430720477677 694578680046911520179129)
            ·
              refine ⟨520934010035183640134347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 694578680046911520179129 520934010035183640134347)
              ·
                refine ⟨781401015052775460201521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 520934010035183640134347 781401015052775460201521)
                ·
                  refine ⟨586050761289581595151141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 781401015052775460201521 586050761289581595151141)
                  ·
                    refine ⟨109884517741796549090839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 586050761289581595151141 109884517741796549090839)
                    ·
                      rfl

theorem cell22_320999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_320999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_320999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_320999 prefixEnd_320999 := by exact prefixLift 320999
  have htrace : WordTrace (prefixWord ++ tailWord_320999) baseStart_320999 baseEnd_320999 := by
    simpa [prefixWord, tailWord_320999, baseEnd_320999] using wordTrace_append hprefix tailTrace_320999
  have hstable : (prefixWord ++ tailWord_320999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320999).length < 2 ^ (prefixWord ++ tailWord_320999).sum := by decide
  have hdescent : baseEnd_320999 < baseStart_320999 := by decide
  rcases family_descends (prefixWord ++ tailWord_320999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321087 : List Nat := [1, 1, 2, 2, 3, 3, 1, 3, 6]
def baseStart_321087 : Nat := 118140960795 + 321087 * 2 ^ 59
def prefixEnd_321087 : Nat := 4983230072969 + 3 ^ 40 * 321087 * 2
def baseEnd_321087 : Nat := 36638213980064550963523

theorem tailTrace_321087 : CollatzResearch.WordTrace tailWord_321087 prefixEnd_321087 36638213980064550963523 := by
  unfold tailWord_321087
  simp only [CollatzResearch.WordTrace]
  refine ⟨11711004987764111138889515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7807336658509407425926343 11711004987764111138889515)
  ·
    refine ⟨17566507481646166708334273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11711004987764111138889515 17566507481646166708334273)
    ·
      refine ⟨13174880611234625031250705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17566507481646166708334273 13174880611234625031250705)
      ·
        refine ⟨9881160458425968773438029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13174880611234625031250705 9881160458425968773438029)
        ·
          refine ⟨3705435171909738290039261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9881160458425968773438029 3705435171909738290039261)
          ·
            refine ⟨1389538189466151858764723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3705435171909738290039261 1389538189466151858764723)
            ·
              refine ⟨2084307284199227788147085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1389538189466151858764723 2084307284199227788147085)
              ·
                refine ⟨781615231574710420555157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2084307284199227788147085 781615231574710420555157)
                ·
                  refine ⟨36638213980064550963523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 781615231574710420555157 36638213980064550963523)
                  ·
                    rfl

theorem cell22_321087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 3, 6].length) (baseStart_321087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_321087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_321087 prefixEnd_321087 := by exact prefixLift 321087
  have htrace : WordTrace (prefixWord ++ tailWord_321087) baseStart_321087 baseEnd_321087 := by
    simpa [prefixWord, tailWord_321087, baseEnd_321087] using wordTrace_append hprefix tailTrace_321087
  have hstable : (prefixWord ++ tailWord_321087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321087).length < 2 ^ (prefixWord ++ tailWord_321087).sum := by decide
  have hdescent : baseEnd_321087 < baseStart_321087 := by decide
  rcases family_descends (prefixWord ++ tailWord_321087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321106 : List Nat := [3, 2, 2, 1, 2, 3, 2, 2, 1, 4]
def baseStart_321106 : Nat := 118140960795 + 321106 * 2 ^ 59
def prefixEnd_321106 : Nat := 4983230072969 + 3 ^ 40 * 321106 * 2
def baseEnd_321106 : Nat := 109921146028483936665511

theorem tailTrace_321106 : CollatzResearch.WordTrace tailWord_321106 prefixEnd_321106 109921146028483936665511 := by
  unfold tailWord_321106
  simp only [CollatzResearch.WordTrace]
  refine ⟨2927924493673819345957793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7807798649796851589220781 2927924493673819345957793)
  ·
    refine ⟨2195943370255364509468345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2927924493673819345957793 2195943370255364509468345)
    ·
      refine ⟨1646957527691523382101259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2195943370255364509468345 1646957527691523382101259)
      ·
        refine ⟨2470436291537285073151889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1646957527691523382101259 2470436291537285073151889)
        ·
          refine ⟨1852827218652963804863917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2470436291537285073151889 1852827218652963804863917)
          ·
            refine ⟨694810206994861426823969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1852827218652963804863917 694810206994861426823969)
            ·
              refine ⟨521107655246146070117977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 694810206994861426823969 521107655246146070117977)
              ·
                refine ⟨390830741434609552588483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 521107655246146070117977 390830741434609552588483)
                ·
                  refine ⟨586246112151914328882725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 390830741434609552588483 586246112151914328882725)
                  ·
                    refine ⟨109921146028483936665511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 586246112151914328882725 109921146028483936665511)
                    ·
                      rfl

theorem cell22_321106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_321106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_321106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_321106 prefixEnd_321106 := by exact prefixLift 321106
  have htrace : WordTrace (prefixWord ++ tailWord_321106) baseStart_321106 baseEnd_321106 := by
    simpa [prefixWord, tailWord_321106, baseEnd_321106] using wordTrace_append hprefix tailTrace_321106
  have hstable : (prefixWord ++ tailWord_321106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321106).length < 2 ^ (prefixWord ++ tailWord_321106).sum := by decide
  have hdescent : baseEnd_321106 < baseStart_321106 := by decide
  rcases family_descends (prefixWord ++ tailWord_321106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321138 : List Nat := [3, 2, 1, 2, 3, 2, 3, 2, 4]
def baseStart_321138 : Nat := 118140960795 + 321138 * 2 ^ 59
def prefixEnd_321138 : Nat := 4983230072969 + 3 ^ 40 * 321138 * 2
def baseEnd_321138 : Nat := 36644033427482173288471

theorem tailTrace_321138 : CollatzResearch.WordTrace tailWord_321138 prefixEnd_321138 36644033427482173288471 := by
  unfold tailWord_321138
  simp only [CollatzResearch.WordTrace]
  refine ⟨2928216277644836712249017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7808576740386231232664045 2928216277644836712249017)
  ·
    refine ⟨2196162208233627534186763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2928216277644836712249017 2196162208233627534186763)
    ·
      refine ⟨3294243312350441301280145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2196162208233627534186763 3294243312350441301280145)
      ·
        refine ⟨2470682484262830975960109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3294243312350441301280145 2470682484262830975960109)
        ·
          refine ⟨926505931598561615985041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2470682484262830975960109 926505931598561615985041)
          ·
            refine ⟨694879448698921211988781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 926505931598561615985041 694879448698921211988781)
            ·
              refine ⟨260579793262095454495793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 694879448698921211988781 260579793262095454495793)
              ·
                refine ⟨195434844946571590871845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 260579793262095454495793 195434844946571590871845)
                ·
                  refine ⟨36644033427482173288471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 195434844946571590871845 36644033427482173288471)
                  ·
                    rfl

theorem cell22_321138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 3, 2, 4].length) (baseStart_321138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_321138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_321138 prefixEnd_321138 := by exact prefixLift 321138
  have htrace : WordTrace (prefixWord ++ tailWord_321138) baseStart_321138 baseEnd_321138 := by
    simpa [prefixWord, tailWord_321138, baseEnd_321138] using wordTrace_append hprefix tailTrace_321138
  have hstable : (prefixWord ++ tailWord_321138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321138).length < 2 ^ (prefixWord ++ tailWord_321138).sum := by decide
  have hdescent : baseEnd_321138 < baseStart_321138 := by decide
  rcases family_descends (prefixWord ++ tailWord_321138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321149 : List Nat := [1, 4, 1, 1, 4, 2, 2, 7]
def baseStart_321149 : Nat := 118140960795 + 321149 * 2 ^ 59
def prefixEnd_321149 : Nat := 4983230072969 + 3 ^ 40 * 321149 * 2
def baseEnd_321149 : Nat := 12215096200805128648931

theorem tailTrace_321149 : CollatzResearch.WordTrace tailWord_321149 prefixEnd_321149 12215096200805128648931 := by
  unfold tailWord_321149
  simp only [CollatzResearch.WordTrace]
  refine ⟨11713266313539495727646501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7808844209026330485097667 11713266313539495727646501)
  ·
    refine ⟨2196237433788655448933719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11713266313539495727646501 2196237433788655448933719)
    ·
      refine ⟨3294356150682983173400579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2196237433788655448933719 3294356150682983173400579)
      ·
        refine ⟨4941534226024474760100869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3294356150682983173400579 4941534226024474760100869)
        ·
          refine ⟨926537667379589017518913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4941534226024474760100869 926537667379589017518913)
          ·
            refine ⟨694903250534691763139185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 926537667379589017518913 694903250534691763139185)
            ·
              refine ⟨521177437901018822354389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 694903250534691763139185 521177437901018822354389)
              ·
                refine ⟨12215096200805128648931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 521177437901018822354389 12215096200805128648931)
                ·
                  rfl

theorem cell22_321149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 7].length) (baseStart_321149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_321149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_321149 prefixEnd_321149 := by exact prefixLift 321149
  have htrace : WordTrace (prefixWord ++ tailWord_321149) baseStart_321149 baseEnd_321149 := by
    simpa [prefixWord, tailWord_321149, baseEnd_321149] using wordTrace_append hprefix tailTrace_321149
  have hstable : (prefixWord ++ tailWord_321149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321149).length < 2 ^ (prefixWord ++ tailWord_321149).sum := by decide
  have hdescent : baseEnd_321149 < baseStart_321149 := by decide
  rcases family_descends (prefixWord ++ tailWord_321149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321153 : List Nat := [1, 2, 4, 2, 1, 2, 4, 1, 2, 3]
def baseStart_321153 : Nat := 118140960795 + 321153 * 2 ^ 59
def prefixEnd_321153 : Nat := 4983230072969 + 3 ^ 40 * 321153 * 2
def baseEnd_321153 : Nat := 109937235088991480740367

theorem tailTrace_321153 : CollatzResearch.WordTrace tailWord_321153 prefixEnd_321153 109937235088991480740367 := by
  unfold tailWord_321153
  simp only [CollatzResearch.WordTrace]
  refine ⟨11713412205525004410792113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7808941470350002940528075 11713412205525004410792113)
  ·
    refine ⟨8785059154143753308094085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11713412205525004410792113 8785059154143753308094085)
    ·
      refine ⟨1647198591401953745267641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8785059154143753308094085 1647198591401953745267641)
      ·
        refine ⟨1235398943551465308950731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1647198591401953745267641 1235398943551465308950731)
        ·
          refine ⟨1853098415327197963426097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1235398943551465308950731 1853098415327197963426097)
          ·
            refine ⟨1389823811495398472569573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1853098415327197963426097 1389823811495398472569573)
            ·
              refine ⟨260591964655387213606795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1389823811495398472569573 260591964655387213606795)
              ·
                refine ⟨390887946983080820410193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 260591964655387213606795 390887946983080820410193)
                ·
                  refine ⟨293165960237310615307645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 390887946983080820410193 293165960237310615307645)
                  ·
                    refine ⟨109937235088991480740367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 293165960237310615307645 109937235088991480740367)
                    ·
                      rfl

theorem cell22_321153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 4, 1, 2, 3].length) (baseStart_321153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_321153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_321153 prefixEnd_321153 := by exact prefixLift 321153
  have htrace : WordTrace (prefixWord ++ tailWord_321153) baseStart_321153 baseEnd_321153 := by
    simpa [prefixWord, tailWord_321153, baseEnd_321153] using wordTrace_append hprefix tailTrace_321153
  have hstable : (prefixWord ++ tailWord_321153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321153).length < 2 ^ (prefixWord ++ tailWord_321153).sum := by decide
  have hdescent : baseEnd_321153 < baseStart_321153 := by decide
  rcases family_descends (prefixWord ++ tailWord_321153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321164 : List Nat := [2, 2, 1, 2, 1, 1, 4, 1, 5, 3]
def baseStart_321164 : Nat := 118140960795 + 321164 * 2 ^ 59
def prefixEnd_321164 : Nat := 4983230072969 + 3 ^ 40 * 321164 * 2
def baseEnd_321164 : Nat := 109941000613791118715333

theorem tailTrace_321164 : CollatzResearch.WordTrace tailWord_321164 prefixEnd_321164 109941000613791118715333 := by
  unfold tailWord_321164
  simp only [CollatzResearch.WordTrace]
  refine ⟨5856906704242576644721273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7809208938990102192961697 5856906704242576644721273)
  ·
    refine ⟨4392680028181932483540955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5856906704242576644721273 4392680028181932483540955)
    ·
      refine ⟨6589020042272898725311433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4392680028181932483540955 6589020042272898725311433)
      ·
        refine ⟨4941765031704674043983575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6589020042272898725311433 4941765031704674043983575)
        ·
          refine ⟨7412647547557011065975363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4941765031704674043983575 7412647547557011065975363)
          ·
            refine ⟨11118971321335516598963045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7412647547557011065975363 11118971321335516598963045)
            ·
              refine ⟨2084807122750409362305571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11118971321335516598963045 2084807122750409362305571)
              ·
                refine ⟨3127210684125614043458357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2084807122750409362305571 3127210684125614043458357)
                ·
                  refine ⟨293176001636776316574221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3127210684125614043458357 293176001636776316574221)
                  ·
                    refine ⟨109941000613791118715333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 293176001636776316574221 109941000613791118715333)
                    ·
                      rfl

theorem cell22_321164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 5, 3].length) (baseStart_321164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_321164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_321164 prefixEnd_321164 := by exact prefixLift 321164
  have htrace : WordTrace (prefixWord ++ tailWord_321164) baseStart_321164 baseEnd_321164 := by
    simpa [prefixWord, tailWord_321164, baseEnd_321164] using wordTrace_append hprefix tailTrace_321164
  have hstable : (prefixWord ++ tailWord_321164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321164).length < 2 ^ (prefixWord ++ tailWord_321164).sum := by decide
  have hdescent : baseEnd_321164 < baseStart_321164 := by decide
  rcases family_descends (prefixWord ++ tailWord_321164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321177 : List Nat := [1, 2, 1, 2, 1, 2, 2, 4, 7]
def baseStart_321177 : Nat := 118140960795 + 321177 * 2 ^ 59
def prefixEnd_321177 : Nat := 4983230072969 + 3 ^ 40 * 321177 * 2
def baseEnd_321177 : Nat := 36648483593154472713431

theorem tailTrace_321177 : CollatzResearch.WordTrace tailWord_321177 prefixEnd_321177 36648483593154472713431 := by
  unfold tailWord_321177
  simp only [CollatzResearch.WordTrace]
  refine ⟨11714287557438056509665785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7809525038292037673110523 11714287557438056509665785)
  ·
    refine ⟨8785715668078542382249339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11714287557438056509665785 8785715668078542382249339)
    ·
      refine ⟨13178573502117813573374009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8785715668078542382249339 13178573502117813573374009)
      ·
        refine ⟨9883930126588360180030507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13178573502117813573374009 9883930126588360180030507)
        ·
          refine ⟨14825895189882540270045761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9883930126588360180030507 14825895189882540270045761)
          ·
            refine ⟨11119421392411905202534321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14825895189882540270045761 11119421392411905202534321)
            ·
              refine ⟨8339566044308928901900741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11119421392411905202534321 8339566044308928901900741)
              ·
                refine ⟨1563668633307924169106389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8339566044308928901900741 1563668633307924169106389)
                ·
                  refine ⟨36648483593154472713431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1563668633307924169106389 36648483593154472713431)
                  ·
                    rfl

theorem cell22_321177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 7].length) (baseStart_321177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_321177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_321177 prefixEnd_321177 := by exact prefixLift 321177
  have htrace : WordTrace (prefixWord ++ tailWord_321177) baseStart_321177 baseEnd_321177 := by
    simpa [prefixWord, tailWord_321177, baseEnd_321177] using wordTrace_append hprefix tailTrace_321177
  have hstable : (prefixWord ++ tailWord_321177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321177).length < 2 ^ (prefixWord ++ tailWord_321177).sum := by decide
  have hdescent : baseEnd_321177 < baseStart_321177 := by decide
  rcases family_descends (prefixWord ++ tailWord_321177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321224 : List Nat := [2, 1, 3, 1, 2, 2, 1, 3, 3, 4]
def baseStart_321224 : Nat := 118140960795 + 321224 * 2 ^ 59
def prefixEnd_321224 : Nat := 4983230072969 + 3 ^ 40 * 321224 * 2
def baseEnd_321224 : Nat := 109961539839970962215149

theorem tailTrace_321224 : CollatzResearch.WordTrace tailWord_321224 prefixEnd_321224 109961539839970962215149 := by
  unfold tailWord_321224
  simp only [CollatzResearch.WordTrace]
  refine ⟨5858000894133891768313363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7810667858845189024417817 5858000894133891768313363)
  ·
    refine ⟨8787001341200837652470045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5858000894133891768313363 8787001341200837652470045)
    ·
      refine ⟨3295125502950314119676267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8787001341200837652470045 3295125502950314119676267)
      ·
        refine ⟨4942688254425471179514401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3295125502950314119676267 4942688254425471179514401)
        ·
          refine ⟨3707016190819103384635801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4942688254425471179514401 3707016190819103384635801)
          ·
            refine ⟨2780262143114327538476851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3707016190819103384635801 2780262143114327538476851)
            ·
              refine ⟨4170393214671491307715277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2780262143114327538476851 4170393214671491307715277)
              ·
                refine ⟨1563897455501809240393229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4170393214671491307715277 1563897455501809240393229)
                ·
                  refine ⟨586461545813178465147461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1563897455501809240393229 586461545813178465147461)
                  ·
                    refine ⟨109961539839970962215149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 586461545813178465147461 109961539839970962215149)
                    ·
                      rfl

theorem cell22_321224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 3, 4].length) (baseStart_321224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_321224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_321224 prefixEnd_321224 := by exact prefixLift 321224
  have htrace : WordTrace (prefixWord ++ tailWord_321224) baseStart_321224 baseEnd_321224 := by
    simpa [prefixWord, tailWord_321224, baseEnd_321224] using wordTrace_append hprefix tailTrace_321224
  have hstable : (prefixWord ++ tailWord_321224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321224).length < 2 ^ (prefixWord ++ tailWord_321224).sum := by decide
  have hdescent : baseEnd_321224 < baseStart_321224 := by decide
  rcases family_descends (prefixWord ++ tailWord_321224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321241 : List Nat := [1, 2, 1, 2, 3, 4, 1, 3, 1, 4]
def baseStart_321241 : Nat := 118140960795 + 321241 * 2 ^ 59
def prefixEnd_321241 : Nat := 4983230072969 + 3 ^ 40 * 321241 * 2
def baseEnd_321241 : Nat := 109967359287388584540097

theorem tailTrace_321241 : CollatzResearch.WordTrace tailWord_321241 prefixEnd_321241 109967359287388584540097 := by
  unfold tailWord_321241
  simp only [CollatzResearch.WordTrace]
  refine ⟨11716621829206195439995577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7811081219470796959997051 11716621829206195439995577)
  ·
    refine ⟨8787466371904646579996683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11716621829206195439995577 8787466371904646579996683)
    ·
      refine ⟨13181199557856969869995025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8787466371904646579996683 13181199557856969869995025)
      ·
        refine ⟨9885899668392727402496269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13181199557856969869995025 9885899668392727402496269)
        ·
          refine ⟨3707212375647272775936101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9885899668392727402496269 3707212375647272775936101)
          ·
            refine ⟨695102320433863645488019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3707212375647272775936101 695102320433863645488019)
            ·
              refine ⟨1042653480650795468232029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 695102320433863645488019 1042653480650795468232029)
              ·
                refine ⟨390995055244048300587011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1042653480650795468232029 390995055244048300587011)
                ·
                  refine ⟨586492582866072450880517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 390995055244048300587011 586492582866072450880517)
                  ·
                    refine ⟨109967359287388584540097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 586492582866072450880517 109967359287388584540097)
                    ·
                      rfl

theorem cell22_321241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 3, 1, 4].length) (baseStart_321241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_321241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_321241 prefixEnd_321241 := by exact prefixLift 321241
  have htrace : WordTrace (prefixWord ++ tailWord_321241) baseStart_321241 baseEnd_321241 := by
    simpa [prefixWord, tailWord_321241, baseEnd_321241] using wordTrace_append hprefix tailTrace_321241
  have hstable : (prefixWord ++ tailWord_321241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321241).length < 2 ^ (prefixWord ++ tailWord_321241).sum := by decide
  have hdescent : baseEnd_321241 < baseStart_321241 := by decide
  rcases family_descends (prefixWord ++ tailWord_321241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321245 : List Nat := [1, 4, 3, 3, 1, 2, 1, 2, 5]
def baseStart_321245 : Nat := 118140960795 + 321245 * 2 ^ 59
def prefixEnd_321245 : Nat := 4983230072969 + 3 ^ 40 * 321245 * 2
def baseEnd_321245 : Nat := 36656242856377969146695

theorem tailTrace_321245 : CollatzResearch.WordTrace tailWord_321245 prefixEnd_321245 36656242856377969146695 := by
  unfold tailWord_321245
  simp only [CollatzResearch.WordTrace]
  refine ⟨11716767721191704123141189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7811178480794469415427459 11716767721191704123141189)
  ·
    refine ⟨2196893947723444523088973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11716767721191704123141189 2196893947723444523088973)
    ·
      refine ⟨823835230396291696158365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2196893947723444523088973 823835230396291696158365)
      ·
        refine ⟨308938211398609386059387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 823835230396291696158365 308938211398609386059387)
        ·
          refine ⟨463407317097914079089081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 308938211398609386059387 463407317097914079089081)
          ·
            refine ⟨347555487823435559316811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 463407317097914079089081 347555487823435559316811)
            ·
              refine ⟨521333231735153338975217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 347555487823435559316811 521333231735153338975217)
              ·
                refine ⟨390999923801365004231413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 521333231735153338975217 390999923801365004231413)
                ·
                  refine ⟨36656242856377969146695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 390999923801365004231413 36656242856377969146695)
                  ·
                    rfl

theorem cell22_321245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 2, 5].length) (baseStart_321245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_321245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_321245 prefixEnd_321245 := by exact prefixLift 321245
  have htrace : WordTrace (prefixWord ++ tailWord_321245) baseStart_321245 baseEnd_321245 := by
    simpa [prefixWord, tailWord_321245, baseEnd_321245] using wordTrace_append hprefix tailTrace_321245
  have hstable : (prefixWord ++ tailWord_321245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321245).length < 2 ^ (prefixWord ++ tailWord_321245).sum := by decide
  have hdescent : baseEnd_321245 < baseStart_321245 := by decide
  rcases family_descends (prefixWord ++ tailWord_321245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321256 : List Nat := [2, 1, 4, 1, 3, 2, 2, 1, 6]
def baseStart_321256 : Nat := 118140960795 + 321256 * 2 ^ 59
def prefixEnd_321256 : Nat := 4983230072969 + 3 ^ 40 * 321256 * 2
def baseEnd_321256 : Nat := 36657498031311181805017

theorem tailTrace_321256 : CollatzResearch.WordTrace tailWord_321256 prefixEnd_321256 36657498031311181805017 := by
  unfold tailWord_321256
  simp only [CollatzResearch.WordTrace]
  refine ⟨5858584462075926500895811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7811445949434568667861081 5858584462075926500895811)
  ·
    refine ⟨8787876693113889751343717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5858584462075926500895811 8787876693113889751343717)
    ·
      refine ⟨1647726879958854328376947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8787876693113889751343717 1647726879958854328376947)
      ·
        refine ⟨2471590319938281492565421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1647726879958854328376947 2471590319938281492565421)
        ·
          refine ⟨926846369976855559712033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2471590319938281492565421 926846369976855559712033)
          ·
            refine ⟨695134777482641669784025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 926846369976855559712033 695134777482641669784025)
            ·
              refine ⟨521351083111981252338019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 695134777482641669784025 521351083111981252338019)
              ·
                refine ⟨782026624667971878507029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 521351083111981252338019 782026624667971878507029)
                ·
                  refine ⟨36657498031311181805017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 782026624667971878507029 36657498031311181805017)
                  ·
                    rfl

theorem cell22_321256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 1, 6].length) (baseStart_321256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_321256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_321256 prefixEnd_321256 := by exact prefixLift 321256
  have htrace : WordTrace (prefixWord ++ tailWord_321256) baseStart_321256 baseEnd_321256 := by
    simpa [prefixWord, tailWord_321256, baseEnd_321256] using wordTrace_append hprefix tailTrace_321256
  have hstable : (prefixWord ++ tailWord_321256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321256).length < 2 ^ (prefixWord ++ tailWord_321256).sum := by decide
  have hdescent : baseEnd_321256 < baseStart_321256 := by decide
  rcases family_descends (prefixWord ++ tailWord_321256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321271 : List Nat := [1, 1, 3, 1, 1, 1, 4, 5, 2, 3]
def baseStart_321271 : Nat := 118140960795 + 321271 * 2 ^ 59
def prefixEnd_321271 : Nat := 4983230072969 + 3 ^ 40 * 321271 * 2
def baseEnd_321271 : Nat := 109977628900478506290005

theorem tailTrace_321271 : CollatzResearch.WordTrace tailWord_321271 prefixEnd_321271 109977628900478506290005 := by
  unfold tailWord_321271
  simp only [CollatzResearch.WordTrace]
  refine ⟨11717716019097510563587667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7811810679398340375725111 11717716019097510563587667)
  ·
    refine ⟨17576574028646265845381501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11717716019097510563587667 17576574028646265845381501)
    ·
      refine ⟨6591215260742349692018063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17576574028646265845381501 6591215260742349692018063)
      ·
        refine ⟨9886822891113524538027095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6591215260742349692018063 9886822891113524538027095)
        ·
          refine ⟨14830234336670286807040643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9886822891113524538027095 14830234336670286807040643)
          ·
            refine ⟨22245351505005430210560965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14830234336670286807040643 22245351505005430210560965)
            ·
              refine ⟨4171003407188518164480181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22245351505005430210560965 4171003407188518164480181)
              ·
                refine ⟨391031569423923577920017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4171003407188518164480181 391031569423923577920017)
                ·
                  refine ⟨293273677067942683440013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 391031569423923577920017 293273677067942683440013)
                  ·
                    refine ⟨109977628900478506290005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 293273677067942683440013 109977628900478506290005)
                    ·
                      rfl

theorem cell22_321271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 5, 2, 3].length) (baseStart_321271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_321271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_321271 prefixEnd_321271 := by exact prefixLift 321271
  have htrace : WordTrace (prefixWord ++ tailWord_321271) baseStart_321271 baseEnd_321271 := by
    simpa [prefixWord, tailWord_321271, baseEnd_321271] using wordTrace_append hprefix tailTrace_321271
  have hstable : (prefixWord ++ tailWord_321271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321271).length < 2 ^ (prefixWord ++ tailWord_321271).sum := by decide
  have hdescent : baseEnd_321271 < baseStart_321271 := by decide
  rcases family_descends (prefixWord ++ tailWord_321271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321344 : List Nat := [2, 1, 1, 2, 2, 1, 1, 1, 6, 5]
def baseStart_321344 : Nat := 118140960795 + 321344 * 2 ^ 59
def prefixEnd_321344 : Nat := 4983230072969 + 3 ^ 40 * 321344 * 2
def baseEnd_321344 : Nat := 110002618292330649214781

theorem tailTrace_321344 : CollatzResearch.WordTrace tailWord_321344 prefixEnd_321344 110002618292330649214781 := by
  unfold tailWord_321344
  simp only [CollatzResearch.WordTrace]
  refine ⟨5860189273916522015497543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7813585698555362687330057 5860189273916522015497543)
  ·
    refine ⟨8790283910874783023246315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5860189273916522015497543 8790283910874783023246315)
    ·
      refine ⟨13185425866312174534869473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8790283910874783023246315 13185425866312174534869473)
      ·
        refine ⟨9889069399734130901152105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13185425866312174534869473 9889069399734130901152105)
        ·
          refine ⟨7416802049800598175864079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9889069399734130901152105 7416802049800598175864079)
          ·
            refine ⟨11125203074700897263796119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7416802049800598175864079 11125203074700897263796119)
            ·
              refine ⟨16687804612051345895694179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11125203074700897263796119 16687804612051345895694179)
              ·
                refine ⟨25031706918077018843541269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16687804612051345895694179 25031706918077018843541269)
                ·
                  refine ⟨1173361261784860258290997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 25031706918077018843541269 1173361261784860258290997)
                  ·
                    refine ⟨110002618292330649214781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1173361261784860258290997 110002618292330649214781)
                    ·
                      rfl

theorem cell22_321344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 6, 5].length) (baseStart_321344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_321344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_321344 prefixEnd_321344 := by exact prefixLift 321344
  have htrace : WordTrace (prefixWord ++ tailWord_321344) baseStart_321344 baseEnd_321344 := by
    simpa [prefixWord, tailWord_321344, baseEnd_321344] using wordTrace_append hprefix tailTrace_321344
  have hstable : (prefixWord ++ tailWord_321344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321344).length < 2 ^ (prefixWord ++ tailWord_321344).sum := by decide
  have hdescent : baseEnd_321344 < baseStart_321344 := by decide
  rcases family_descends (prefixWord ++ tailWord_321344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321376 : List Nat := [2, 1, 1, 3, 3, 2, 1, 2, 3, 4]
def baseStart_321376 : Nat := 118140960795 + 321376 * 2 ^ 59
def prefixEnd_321376 : Nat := 4983230072969 + 3 ^ 40 * 321376 * 2
def baseEnd_321376 : Nat := 110013572546293232414683

theorem tailTrace_321376 : CollatzResearch.WordTrace tailWord_321376 prefixEnd_321376 110013572546293232414683 := by
  unfold tailWord_321376
  simp only [CollatzResearch.WordTrace]
  refine ⟨5860772841858556748079991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7814363789144742330773321 5860772841858556748079991)
  ·
    refine ⟨8791159262787835122119987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5860772841858556748079991 8791159262787835122119987)
    ·
      refine ⟨13186738894181752683179981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8791159262787835122119987 13186738894181752683179981)
      ·
        refine ⟨4945027085318157256192493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13186738894181752683179981 4945027085318157256192493)
        ·
          refine ⟨1854385156994308971072185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4945027085318157256192493 1854385156994308971072185)
          ·
            refine ⟨1390788867745731728304139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1854385156994308971072185 1390788867745731728304139)
            ·
              refine ⟨2086183301618597592456209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1390788867745731728304139 2086183301618597592456209)
              ·
                refine ⟨1564637476213948194342157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2086183301618597592456209 1564637476213948194342157)
                ·
                  refine ⟨586739053580230572878309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1564637476213948194342157 586739053580230572878309)
                  ·
                    refine ⟨110013572546293232414683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 586739053580230572878309 110013572546293232414683)
                    ·
                      rfl

theorem cell22_321376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 3, 4].length) (baseStart_321376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_321376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_321376 prefixEnd_321376 := by exact prefixLift 321376
  have htrace : WordTrace (prefixWord ++ tailWord_321376) baseStart_321376 baseEnd_321376 := by
    simpa [prefixWord, tailWord_321376, baseEnd_321376] using wordTrace_append hprefix tailTrace_321376
  have hstable : (prefixWord ++ tailWord_321376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321376).length < 2 ^ (prefixWord ++ tailWord_321376).sum := by decide
  have hdescent : baseEnd_321376 < baseStart_321376 := by decide
  rcases family_descends (prefixWord ++ tailWord_321376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321378 : List Nat := [3, 3, 2, 1, 2, 2, 1, 1, 2, 5]
def baseStart_321378 : Nat := 118140960795 + 321378 * 2 ^ 59
def prefixEnd_321378 : Nat := 4983230072969 + 3 ^ 40 * 321378 * 2
def baseEnd_321378 : Nat := 110014257187165893864677

theorem tailTrace_321378 : CollatzResearch.WordTrace tailWord_321378 prefixEnd_321378 110014257187165893864677 := by
  unfold tailWord_321378
  simp only [CollatzResearch.WordTrace]
  refine ⟨2930404657427466959433197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7814412419806578558488525 2930404657427466959433197)
  ·
    refine ⟨1098901746535300109787449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2930404657427466959433197 1098901746535300109787449)
    ·
      refine ⟨824176309901475082340587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1098901746535300109787449 824176309901475082340587)
      ·
        refine ⟨1236264464852212623510881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 824176309901475082340587 1236264464852212623510881)
        ·
          refine ⟨927198348639159467633161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1236264464852212623510881 927198348639159467633161)
          ·
            refine ⟨695398761479369600724871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 927198348639159467633161 695398761479369600724871)
            ·
              refine ⟨1043098142219054401087307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 695398761479369600724871 1043098142219054401087307)
              ·
                refine ⟨1564647213328581601630961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1043098142219054401087307 1564647213328581601630961)
                ·
                  refine ⟨1173485409996436201223221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1564647213328581601630961 1173485409996436201223221)
                  ·
                    refine ⟨110014257187165893864677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1173485409996436201223221 110014257187165893864677)
                    ·
                      rfl

theorem cell22_321378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_321378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_321378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_321378 prefixEnd_321378 := by exact prefixLift 321378
  have htrace : WordTrace (prefixWord ++ tailWord_321378) baseStart_321378 baseEnd_321378 := by
    simpa [prefixWord, tailWord_321378, baseEnd_321378] using wordTrace_append hprefix tailTrace_321378
  have hstable : (prefixWord ++ tailWord_321378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321378).length < 2 ^ (prefixWord ++ tailWord_321378).sum := by decide
  have hdescent : baseEnd_321378 < baseStart_321378 := by decide
  rcases family_descends (prefixWord ++ tailWord_321378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321408 : List Nat := [2, 1, 1, 2, 1, 2, 6, 3, 4]
def baseStart_321408 : Nat := 118140960795 + 321408 * 2 ^ 59
def prefixEnd_321408 : Nat := 4983230072969 + 3 ^ 40 * 321408 * 2
def baseEnd_321408 : Nat := 36674842266751938538195

theorem tailTrace_321408 : CollatzResearch.WordTrace tailWord_321408 prefixEnd_321408 36674842266751938538195 := by
  unfold tailWord_321408
  simp only [CollatzResearch.WordTrace]
  refine ⟨5861356409800591480662439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7815141879734121974216585 5861356409800591480662439)
  ·
    refine ⟨8792034614700887220993659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5861356409800591480662439 8792034614700887220993659)
    ·
      refine ⟨13188051922051330831490489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8792034614700887220993659 13188051922051330831490489)
      ·
        refine ⟨9891038941538498123617867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13188051922051330831490489 9891038941538498123617867)
        ·
          refine ⟨14836558412307747185426801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9891038941538498123617867 14836558412307747185426801)
          ·
            refine ⟨11127418809230810389070101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14836558412307747185426801 11127418809230810389070101)
            ·
              refine ⟨521597756682694236987661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11127418809230810389070101 521597756682694236987661)
              ·
                refine ⟨195599158756010338870373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 521597756682694236987661 195599158756010338870373)
                ·
                  refine ⟨36674842266751938538195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 195599158756010338870373 36674842266751938538195)
                  ·
                    rfl

theorem cell22_321408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 3, 4].length) (baseStart_321408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_321408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_321408 prefixEnd_321408 := by exact prefixLift 321408
  have htrace : WordTrace (prefixWord ++ tailWord_321408) baseStart_321408 baseEnd_321408 := by
    simpa [prefixWord, tailWord_321408, baseEnd_321408] using wordTrace_append hprefix tailTrace_321408
  have hstable : (prefixWord ++ tailWord_321408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321408).length < 2 ^ (prefixWord ++ tailWord_321408).sum := by decide
  have hdescent : baseEnd_321408 < baseStart_321408 := by decide
  rcases family_descends (prefixWord ++ tailWord_321408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321496 : List Nat := [2, 1, 2, 2, 2, 2, 2, 1, 1, 7]
def baseStart_321496 : Nat := 118140960795 + 321496 * 2 ^ 59
def prefixEnd_321496 : Nat := 4983230072969 + 3 ^ 40 * 321496 * 2
def baseEnd_321496 : Nat := 110054650998652919414315

theorem tailTrace_321496 : CollatzResearch.WordTrace tailWord_321496 prefixEnd_321496 110054650998652919414315 := by
  unfold tailWord_321496
  simp only [CollatzResearch.WordTrace]
  refine ⟨5862961221641186995264171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7817281628854915993685561 5862961221641186995264171)
  ·
    refine ⟨8794441832461780492896257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5862961221641186995264171 8794441832461780492896257)
    ·
      refine ⟨6595831374346335369672193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8794441832461780492896257 6595831374346335369672193)
      ·
        refine ⟨4946873530759751527254145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6595831374346335369672193 4946873530759751527254145)
        ·
          refine ⟨3710155148069813645440609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4946873530759751527254145 3710155148069813645440609)
          ·
            refine ⟨2782616361052360234080457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3710155148069813645440609 2782616361052360234080457)
            ·
              refine ⟨2086962270789270175560343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2782616361052360234080457 2086962270789270175560343)
              ·
                refine ⟨3130443406183905263340515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2086962270789270175560343 3130443406183905263340515)
                ·
                  refine ⟨4695665109275857895010773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3130443406183905263340515 4695665109275857895010773)
                  ·
                    refine ⟨110054650998652919414315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4695665109275857895010773 110054650998652919414315)
                    ·
                      rfl

theorem cell22_321496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 1, 7].length) (baseStart_321496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_321496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_321496 prefixEnd_321496 := by exact prefixLift 321496
  have htrace : WordTrace (prefixWord ++ tailWord_321496) baseStart_321496 baseEnd_321496 := by
    simpa [prefixWord, tailWord_321496, baseEnd_321496] using wordTrace_append hprefix tailTrace_321496
  have hstable : (prefixWord ++ tailWord_321496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321496).length < 2 ^ (prefixWord ++ tailWord_321496).sum := by decide
  have hdescent : baseEnd_321496 < baseStart_321496 := by decide
  rcases family_descends (prefixWord ++ tailWord_321496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321528 : List Nat := [2, 1, 2, 1, 1, 3, 2, 5, 1, 4]
def baseStart_321528 : Nat := 118140960795 + 321528 * 2 ^ 59
def prefixEnd_321528 : Nat := 4983230072969 + 3 ^ 40 * 321528 * 2
def baseEnd_321528 : Nat := 110065605252615502614217

theorem tailTrace_321528 : CollatzResearch.WordTrace tailWord_321528 prefixEnd_321528 110065605252615502614217 := by
  unfold tailWord_321528
  simp only [CollatzResearch.WordTrace]
  refine ⟨5863544789583221727846619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7818059719444295637128825 5863544789583221727846619)
  ·
    refine ⟨8795317184374832591769929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5863544789583221727846619 8795317184374832591769929)
    ·
      refine ⟨6596487888281124443827447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8795317184374832591769929 6596487888281124443827447)
      ·
        refine ⟨9894731832421686665741171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6596487888281124443827447 9894731832421686665741171)
        ·
          refine ⟨14842097748632529998611757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9894731832421686665741171 14842097748632529998611757)
          ·
            refine ⟨5565786655737198749479409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14842097748632529998611757 5565786655737198749479409)
            ·
              refine ⟨4174339991802899062109557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5565786655737198749479409 4174339991802899062109557)
              ·
                refine ⟨391344374231521787072771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4174339991802899062109557 391344374231521787072771)
                ·
                  refine ⟨587016561347282680609157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 391344374231521787072771 587016561347282680609157)
                  ·
                    refine ⟨110065605252615502614217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 587016561347282680609157 110065605252615502614217)
                    ·
                      rfl

theorem cell22_321528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 5, 1, 4].length) (baseStart_321528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_321528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_321528 prefixEnd_321528 := by exact prefixLift 321528
  have htrace : WordTrace (prefixWord ++ tailWord_321528) baseStart_321528 baseEnd_321528 := by
    simpa [prefixWord, tailWord_321528, baseEnd_321528] using wordTrace_append hprefix tailTrace_321528
  have hstable : (prefixWord ++ tailWord_321528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321528).length < 2 ^ (prefixWord ++ tailWord_321528).sum := by decide
  have hdescent : baseEnd_321528 < baseStart_321528 := by decide
  rcases family_descends (prefixWord ++ tailWord_321528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321573 : List Nat := [1, 3, 1, 2, 2, 4, 1, 1, 1, 6]
def baseStart_321573 : Nat := 118140960795 + 321573 * 2 ^ 59
def prefixEnd_321573 : Nat := 4983230072969 + 3 ^ 40 * 321573 * 2
def baseEnd_321573 : Nat := 110081009672250385239079

theorem tailTrace_321573 : CollatzResearch.WordTrace tailWord_321573 prefixEnd_321573 110081009672250385239079 := by
  unfold tailWord_321573
  simp only [CollatzResearch.WordTrace]
  refine ⟨11728730864003416141081373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7819153909335610760720915 11728730864003416141081373)
  ·
    refine ⟨4398274074001281052905515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11728730864003416141081373 4398274074001281052905515)
    ·
      refine ⟨6597411111001921579358273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4398274074001281052905515 6597411111001921579358273)
      ·
        refine ⟨4948058333251441184518705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6597411111001921579358273 4948058333251441184518705)
        ·
          refine ⟨3711043749938580888389029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4948058333251441184518705 3711043749938580888389029)
          ·
            refine ⟨695820703113483916572943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3711043749938580888389029 695820703113483916572943)
            ·
              refine ⟨1043731054670225874859415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 695820703113483916572943 1043731054670225874859415)
              ·
                refine ⟨1565596582005338812289123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1043731054670225874859415 1565596582005338812289123)
                ·
                  refine ⟨2348394873008008218433685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1565596582005338812289123 2348394873008008218433685)
                  ·
                    refine ⟨110081009672250385239079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2348394873008008218433685 110081009672250385239079)
                    ·
                      rfl

theorem cell22_321573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 6].length) (baseStart_321573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_321573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_321573 prefixEnd_321573 := by exact prefixLift 321573
  have htrace : WordTrace (prefixWord ++ tailWord_321573) baseStart_321573 baseEnd_321573 := by
    simpa [prefixWord, tailWord_321573, baseEnd_321573] using wordTrace_append hprefix tailTrace_321573
  have hstable : (prefixWord ++ tailWord_321573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321573).length < 2 ^ (prefixWord ++ tailWord_321573).sum := by decide
  have hdescent : baseEnd_321573 < baseStart_321573 := by decide
  rcases family_descends (prefixWord ++ tailWord_321573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321590 : List Nat := [5, 1, 2, 1, 1, 1, 2, 1, 4, 4]
def baseStart_321590 : Nat := 118140960795 + 321590 * 2 ^ 59
def prefixEnd_321590 : Nat := 4983230072969 + 3 ^ 40 * 321590 * 2
def baseEnd_321590 : Nat := 110086829119668007564027

theorem tailTrace_321590 : CollatzResearch.WordTrace tailWord_321590 prefixEnd_321590 110086829119668007564027 := by
  unfold tailWord_321590
  simp only [CollatzResearch.WordTrace]
  refine ⟨733084431558864252778139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7819567269961218696300149 733084431558864252778139)
  ·
    refine ⟨1099626647338296379167209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 733084431558864252778139 1099626647338296379167209)
    ·
      refine ⟨824719985503722284375407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1099626647338296379167209 824719985503722284375407)
      ·
        refine ⟨1237079978255583426563111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 824719985503722284375407 1237079978255583426563111)
        ·
          refine ⟨1855619967383375139844667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1237079978255583426563111 1855619967383375139844667)
          ·
            refine ⟨2783429951075062709767001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1855619967383375139844667 2783429951075062709767001)
            ·
              refine ⟨2087572463306297032325251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2783429951075062709767001 2087572463306297032325251)
              ·
                refine ⟨3131358694959445548487877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2087572463306297032325251 3131358694959445548487877)
                ·
                  refine ⟨587129755304896040341477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3131358694959445548487877 587129755304896040341477)
                  ·
                    refine ⟨110086829119668007564027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 587129755304896040341477 110086829119668007564027)
                    ·
                      rfl

theorem cell22_321590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_321590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_321590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_321590 prefixEnd_321590 := by exact prefixLift 321590
  have htrace : WordTrace (prefixWord ++ tailWord_321590) baseStart_321590 baseEnd_321590 := by
    simpa [prefixWord, tailWord_321590, baseEnd_321590] using wordTrace_append hprefix tailTrace_321590
  have hstable : (prefixWord ++ tailWord_321590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321590).length < 2 ^ (prefixWord ++ tailWord_321590).sum := by decide
  have hdescent : baseEnd_321590 < baseStart_321590 := by decide
  rcases family_descends (prefixWord ++ tailWord_321590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321622 : List Nat := [5, 2, 2, 1, 1, 2, 1, 8]
def baseStart_321622 : Nat := 118140960795 + 321622 * 2 ^ 59
def prefixEnd_321622 : Nat := 4983230072969 + 3 ^ 40 * 321622 * 2
def baseEnd_321622 : Nat := 12233087041514510084881

theorem tailTrace_321622 : CollatzResearch.WordTrace tailWord_321622 prefixEnd_321622 12233087041514510084881 := by
  unfold tailWord_321622
  simp only [CollatzResearch.WordTrace]
  refine ⟨733157377551618594350945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7820345360550598339743413 733157377551618594350945)
  ·
    refine ⟨549868033163713945763209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 733157377551618594350945 549868033163713945763209)
    ·
      refine ⟨412401024872785459322407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 549868033163713945763209 412401024872785459322407)
      ·
        refine ⟨618601537309178188983611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 412401024872785459322407 618601537309178188983611)
        ·
          refine ⟨927902305963767283475417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 618601537309178188983611 927902305963767283475417)
          ·
            refine ⟨695926729472825462606563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 927902305963767283475417 695926729472825462606563)
            ·
              refine ⟨1043890094209238193909845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 695926729472825462606563 1043890094209238193909845)
              ·
                refine ⟨12233087041514510084881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1043890094209238193909845 12233087041514510084881)
                ·
                  rfl

theorem cell22_321622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 8].length) (baseStart_321622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_321622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_321622 prefixEnd_321622 := by exact prefixLift 321622
  have htrace : WordTrace (prefixWord ++ tailWord_321622) baseStart_321622 baseEnd_321622 := by
    simpa [prefixWord, tailWord_321622, baseEnd_321622] using wordTrace_append hprefix tailTrace_321622
  have hstable : (prefixWord ++ tailWord_321622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321622).length < 2 ^ (prefixWord ++ tailWord_321622).sum := by decide
  have hdescent : baseEnd_321622 < baseStart_321622 := by decide
  rcases family_descends (prefixWord ++ tailWord_321622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321654 : List Nat := [5, 1, 1, 2, 1, 4, 1, 1, 3, 3]
def baseStart_321654 : Nat := 118140960795 + 321654 * 2 ^ 59
def prefixEnd_321654 : Nat := 4983230072969 + 3 ^ 40 * 321654 * 2
def baseEnd_321654 : Nat := 110108737627593173963831

theorem tailTrace_321654 : CollatzResearch.WordTrace tailWord_321654 prefixEnd_321654 110108737627593173963831 := by
  unfold tailWord_321654
  simp only [CollatzResearch.WordTrace]
  refine ⟨733230323544372935923751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7821123451139977983186677 733230323544372935923751)
  ·
    refine ⟨1099845485316559403885627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 733230323544372935923751 1099845485316559403885627)
    ·
      refine ⟨1649768227974839105828441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1099845485316559403885627 1649768227974839105828441)
      ·
        refine ⟨1237326170981129329371331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1649768227974839105828441 1237326170981129329371331)
        ·
          refine ⟨1855989256471693994056997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1237326170981129329371331 1855989256471693994056997)
          ·
            refine ⟨347997985588442623885687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1855989256471693994056997 347997985588442623885687)
            ·
              refine ⟨521996978382663935828531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 347997985588442623885687 521996978382663935828531)
              ·
                refine ⟨782995467573995903742797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 521996978382663935828531 782995467573995903742797)
                ·
                  refine ⟨293623300340248463903549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 782995467573995903742797 293623300340248463903549)
                  ·
                    refine ⟨110108737627593173963831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 293623300340248463903549 110108737627593173963831)
                    ·
                      rfl

theorem cell22_321654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 1, 3, 3].length) (baseStart_321654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_321654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_321654 prefixEnd_321654 := by exact prefixLift 321654
  have htrace : WordTrace (prefixWord ++ tailWord_321654) baseStart_321654 baseEnd_321654 := by
    simpa [prefixWord, tailWord_321654, baseEnd_321654] using wordTrace_append hprefix tailTrace_321654
  have hstable : (prefixWord ++ tailWord_321654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321654).length < 2 ^ (prefixWord ++ tailWord_321654).sum := by decide
  have hdescent : baseEnd_321654 < baseStart_321654 := by decide
  rcases family_descends (prefixWord ++ tailWord_321654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321667 : List Nat := [1, 1, 1, 3, 3, 5, 2, 1, 5]
def baseStart_321667 : Nat := 118140960795 + 321667 * 2 ^ 59
def prefixEnd_321667 : Nat := 4983230072969 + 3 ^ 40 * 321667 * 2
def baseEnd_321667 : Nat := 36704395931088491129597

theorem tailTrace_321667 : CollatzResearch.WordTrace tailWord_321667 prefixEnd_321667 36704395931088491129597 := by
  unfold tailWord_321667
  simp only [CollatzResearch.WordTrace]
  refine ⟨11732159325662870195003255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7821439550441913463335503 11732159325662870195003255)
  ·
    refine ⟨17598238988494305292504883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11732159325662870195003255 17598238988494305292504883)
    ·
      refine ⟨26397358482741457938757325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17598238988494305292504883 26397358482741457938757325)
      ·
        refine ⟨9899009431028046727033997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26397358482741457938757325 9899009431028046727033997)
        ·
          refine ⟨3712128536635517522637749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9899009431028046727033997 3712128536635517522637749)
          ·
            refine ⟨348012050309579767747289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3712128536635517522637749 348012050309579767747289)
            ·
              refine ⟨261009037732184825810467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 348012050309579767747289 261009037732184825810467)
              ·
                refine ⟨391513556598277238715701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 261009037732184825810467 391513556598277238715701)
                ·
                  refine ⟨36704395931088491129597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 391513556598277238715701 36704395931088491129597)
                  ·
                    rfl

theorem cell22_321667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 2, 1, 5].length) (baseStart_321667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_321667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_321667 prefixEnd_321667 := by exact prefixLift 321667
  have htrace : WordTrace (prefixWord ++ tailWord_321667) baseStart_321667 baseEnd_321667 := by
    simpa [prefixWord, tailWord_321667, baseEnd_321667] using wordTrace_append hprefix tailTrace_321667
  have hstable : (prefixWord ++ tailWord_321667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321667).length < 2 ^ (prefixWord ++ tailWord_321667).sum := by decide
  have hdescent : baseEnd_321667 < baseStart_321667 := by decide
  rcases family_descends (prefixWord ++ tailWord_321667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321716 : List Nat := [2, 5, 3, 1, 1, 1, 1, 1, 2, 5]
def baseStart_321716 : Nat := 118140960795 + 321716 * 2 ^ 59
def prefixEnd_321716 : Nat := 4983230072969 + 3 ^ 40 * 321716 * 2
def baseEnd_321716 : Nat := 110129961494645678913641

theorem tailTrace_321716 : CollatzResearch.WordTrace tailWord_321716 prefixEnd_321716 110129961494645678913641 := by
  unfold tailWord_321716
  simp only [CollatzResearch.WordTrace]
  refine ⟨5866973251242675781768501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7822631001656901042358001 5866973251242675781768501)
  ·
    refine ⟨550028742304000854540797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5866973251242675781768501 550028742304000854540797)
    ·
      refine ⟨206260778364000320452799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 550028742304000854540797 206260778364000320452799)
      ·
        refine ⟨309391167546000480679199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206260778364000320452799 309391167546000480679199)
        ·
          refine ⟨464086751319000721018799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 309391167546000480679199 464086751319000721018799)
          ·
            refine ⟨696130126978501081528199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 464086751319000721018799 696130126978501081528199)
            ·
              refine ⟨1044195190467751622292299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 696130126978501081528199 1044195190467751622292299)
              ·
                refine ⟨1566292785701627433438449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1044195190467751622292299 1566292785701627433438449)
                ·
                  refine ⟨1174719589276220575078837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1566292785701627433438449 1174719589276220575078837)
                  ·
                    refine ⟨110129961494645678913641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1174719589276220575078837 110129961494645678913641)
                    ·
                      rfl

theorem cell22_321716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_321716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_321716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_321716 prefixEnd_321716 := by exact prefixLift 321716
  have htrace : WordTrace (prefixWord ++ tailWord_321716) baseStart_321716 baseEnd_321716 := by
    simpa [prefixWord, tailWord_321716, baseEnd_321716] using wordTrace_append hprefix tailTrace_321716
  have hstable : (prefixWord ++ tailWord_321716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321716).length < 2 ^ (prefixWord ++ tailWord_321716).sum := by decide
  have hdescent : baseEnd_321716 < baseStart_321716 := by decide
  rcases family_descends (prefixWord ++ tailWord_321716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321742 : List Nat := [4, 1, 1, 1, 4, 1, 3, 1, 2, 4]
def baseStart_321742 : Nat := 118140960795 + 321742 * 2 ^ 59
def prefixEnd_321742 : Nat := 4983230072969 + 3 ^ 40 * 321742 * 2
def baseEnd_321742 : Nat := 110138861825990277763561

theorem tailTrace_321742 : CollatzResearch.WordTrace tailWord_321742 prefixEnd_321742 110138861825990277763561 := by
  unfold tailWord_321742
  simp only [CollatzResearch.WordTrace]
  refine ⟨1466861850048894750497935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7823263200260772002655653 1466861850048894750497935)
  ·
    refine ⟨2200292775073342125746903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1466861850048894750497935 2200292775073342125746903)
    ·
      refine ⟨3300439162610013188620355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2200292775073342125746903 3300439162610013188620355)
      ·
        refine ⟨4950658743915019782930533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3300439162610013188620355 4950658743915019782930533)
        ·
          refine ⟨928248514484066209299475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4950658743915019782930533 928248514484066209299475)
          ·
            refine ⟨1392372771726099313949213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 928248514484066209299475 1392372771726099313949213)
            ·
              refine ⟨522139789397287242730955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1392372771726099313949213 522139789397287242730955)
              ·
                refine ⟨783209684095930864096433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 522139789397287242730955 783209684095930864096433)
                ·
                  refine ⟨587407263071948148072325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 783209684095930864096433 587407263071948148072325)
                  ·
                    refine ⟨110138861825990277763561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 587407263071948148072325 110138861825990277763561)
                    ·
                      rfl

theorem cell22_321742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 1, 2, 4].length) (baseStart_321742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_321742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_321742 prefixEnd_321742 := by exact prefixLift 321742
  have htrace : WordTrace (prefixWord ++ tailWord_321742) baseStart_321742 baseEnd_321742 := by
    simpa [prefixWord, tailWord_321742, baseEnd_321742] using wordTrace_append hprefix tailTrace_321742
  have hstable : (prefixWord ++ tailWord_321742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321742).length < 2 ^ (prefixWord ++ tailWord_321742).sum := by decide
  have hdescent : baseEnd_321742 < baseStart_321742 := by decide
  rcases family_descends (prefixWord ++ tailWord_321742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321772 : List Nat := [2, 2, 1, 1, 2, 3, 4, 1, 3, 3]
def baseStart_321772 : Nat := 118140960795 + 321772 * 2 ^ 59
def prefixEnd_321772 : Nat := 4983230072969 + 3 ^ 40 * 321772 * 2
def baseEnd_321772 : Nat := 110149131439080199513469

theorem tailTrace_321772 : CollatzResearch.WordTrace tailWord_321772 prefixEnd_321772 110149131439080199513469 := by
  unfold tailWord_321772
  simp only [CollatzResearch.WordTrace]
  refine ⟨5867994495141236563787785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7823992660188315418383713 5867994495141236563787785)
  ·
    refine ⟨4400995871355927422840839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5867994495141236563787785 4400995871355927422840839)
    ·
      refine ⟨6601493807033891134261259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4400995871355927422840839 6601493807033891134261259)
      ·
        refine ⟨9902240710550836701391889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6601493807033891134261259 9902240710550836701391889)
        ·
          refine ⟨7426680532913127526043917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9902240710550836701391889 7426680532913127526043917)
          ·
            refine ⟨2785005199842422822266469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7426680532913127526043917 2785005199842422822266469)
            ·
              refine ⟨522188474970454279174963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2785005199842422822266469 522188474970454279174963)
              ·
                refine ⟨783282712455681418762445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 522188474970454279174963 783282712455681418762445)
                ·
                  refine ⟨293731017170880532035917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 783282712455681418762445 293731017170880532035917)
                  ·
                    refine ⟨110149131439080199513469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 293731017170880532035917 110149131439080199513469)
                    ·
                      rfl

theorem cell22_321772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 3].length) (baseStart_321772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_321772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_321772 prefixEnd_321772 := by exact prefixLift 321772
  have htrace : WordTrace (prefixWord ++ tailWord_321772) baseStart_321772 baseEnd_321772 := by
    simpa [prefixWord, tailWord_321772, baseEnd_321772] using wordTrace_append hprefix tailTrace_321772
  have hstable : (prefixWord ++ tailWord_321772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321772).length < 2 ^ (prefixWord ++ tailWord_321772).sum := by decide
  have hdescent : baseEnd_321772 < baseStart_321772 := by decide
  rcases family_descends (prefixWord ++ tailWord_321772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321849 : List Nat := [1, 2, 1, 6, 1, 1, 3, 2, 1, 4]
def baseStart_321849 : Nat := 118140960795 + 321849 * 2 ^ 59
def prefixEnd_321849 : Nat := 4983230072969 + 3 ^ 40 * 321849 * 2
def baseEnd_321849 : Nat := 110175490112677665338233

theorem tailTrace_321849 : CollatzResearch.WordTrace tailWord_321849 prefixEnd_321849 110175490112677665338233 := by
  unfold tailWord_321849
  simp only [CollatzResearch.WordTrace]
  refine ⟨11738797411003515278128601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7825864940669010185419067 11738797411003515278128601)
  ·
    refine ⟨8804098058252636458596451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11738797411003515278128601 8804098058252636458596451)
    ·
      refine ⟨13206147087378954687894677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8804098058252636458596451 13206147087378954687894677)
      ·
        refine ⟨619038144720888500995063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 13206147087378954687894677 619038144720888500995063)
        ·
          refine ⟨928557217081332751492595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 619038144720888500995063 928557217081332751492595)
          ·
            refine ⟨1392835825621999127238893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 928557217081332751492595 1392835825621999127238893)
            ·
              refine ⟨522313434608249672714585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1392835825621999127238893 522313434608249672714585)
              ·
                refine ⟨391735075956187254535939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 522313434608249672714585 391735075956187254535939)
                ·
                  refine ⟨587602613934280881803909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 391735075956187254535939 587602613934280881803909)
                  ·
                    refine ⟨110175490112677665338233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 587602613934280881803909 110175490112677665338233)
                    ·
                      rfl

theorem cell22_321849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 2, 1, 4].length) (baseStart_321849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_321849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_321849 prefixEnd_321849 := by exact prefixLift 321849
  have htrace : WordTrace (prefixWord ++ tailWord_321849) baseStart_321849 baseEnd_321849 := by
    simpa [prefixWord, tailWord_321849, baseEnd_321849] using wordTrace_append hprefix tailTrace_321849
  have hstable : (prefixWord ++ tailWord_321849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321849).length < 2 ^ (prefixWord ++ tailWord_321849).sum := by decide
  have hdescent : baseEnd_321849 < baseStart_321849 := by decide
  rcases family_descends (prefixWord ++ tailWord_321849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321879 : List Nat := [1, 1, 3, 2, 3, 1, 4, 2, 2, 3]
def baseStart_321879 : Nat := 118140960795 + 321879 * 2 ^ 59
def prefixEnd_321879 : Nat := 4983230072969 + 3 ^ 40 * 321879 * 2
def baseEnd_321879 : Nat := 110185759725767587088141

theorem tailTrace_321879 : CollatzResearch.WordTrace tailWord_321879 prefixEnd_321879 110185759725767587088141 := by
  unfold tailWord_321879
  simp only [CollatzResearch.WordTrace]
  refine ⟨11739891600894830401720691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7826594400596553601147127 11739891600894830401720691)
  ·
    refine ⟨17609837401342245602581037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11739891600894830401720691 17609837401342245602581037)
    ·
      refine ⟨6603689025503342100967889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17609837401342245602581037 6603689025503342100967889)
      ·
        refine ⟨4952766769127506575725917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6603689025503342100967889 4952766769127506575725917)
        ·
          refine ⟨1857287538422814965897219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4952766769127506575725917 1857287538422814965897219)
          ·
            refine ⟨2785931307634222448845829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1857287538422814965897219 2785931307634222448845829)
            ·
              refine ⟨522362120181416709158593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2785931307634222448845829 522362120181416709158593)
              ·
                refine ⟨391771590136062531868945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 522362120181416709158593 391771590136062531868945)
                ·
                  refine ⟨293828692602046898901709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 391771590136062531868945 293828692602046898901709)
                  ·
                    refine ⟨110185759725767587088141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 293828692602046898901709 110185759725767587088141)
                    ·
                      rfl

theorem cell22_321879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 2, 2, 3].length) (baseStart_321879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_321879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_321879 prefixEnd_321879 := by exact prefixLift 321879
  have htrace : WordTrace (prefixWord ++ tailWord_321879) baseStart_321879 baseEnd_321879 := by
    simpa [prefixWord, tailWord_321879, baseEnd_321879] using wordTrace_append hprefix tailTrace_321879
  have hstable : (prefixWord ++ tailWord_321879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321879).length < 2 ^ (prefixWord ++ tailWord_321879).sum := by decide
  have hdescent : baseEnd_321879 < baseStart_321879 := by decide
  rcases family_descends (prefixWord ++ tailWord_321879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321905 : List Nat := [1, 2, 2, 2, 1, 2, 1, 1, 4, 6]
def baseStart_321905 : Nat := 118140960795 + 321905 * 2 ^ 59
def prefixEnd_321905 : Nat := 4983230072969 + 3 ^ 40 * 321905 * 2
def baseEnd_321905 : Nat := 110194660057112185938061

theorem tailTrace_321905 : CollatzResearch.WordTrace tailWord_321905 prefixEnd_321905 110194660057112185938061 := by
  unfold tailWord_321905
  simp only [CollatzResearch.WordTrace]
  refine ⟨11740839898800636842167169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7827226599200424561444779 11740839898800636842167169)
  ·
    refine ⟨8805629924100477631625377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11740839898800636842167169 8805629924100477631625377)
    ·
      refine ⟨6604222443075358223719033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8805629924100477631625377 6604222443075358223719033)
      ·
        refine ⟨4953166832306518667789275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6604222443075358223719033 4953166832306518667789275)
        ·
          refine ⟨7429750248459778001683913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4953166832306518667789275 7429750248459778001683913)
          ·
            refine ⟨5572312686344833501262935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7429750248459778001683913 5572312686344833501262935)
            ·
              refine ⟨8358469029517250251894403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5572312686344833501262935 8358469029517250251894403)
              ·
                refine ⟨12537703544275875377841605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8358469029517250251894403 12537703544275875377841605)
                ·
                  refine ⟨2350819414551726633345301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12537703544275875377841605 2350819414551726633345301)
                  ·
                    refine ⟨110194660057112185938061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2350819414551726633345301 110194660057112185938061)
                    ·
                      rfl

theorem cell22_321905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 6].length) (baseStart_321905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_321905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_321905 prefixEnd_321905 := by exact prefixLift 321905
  have htrace : WordTrace (prefixWord ++ tailWord_321905) baseStart_321905 baseEnd_321905 := by
    simpa [prefixWord, tailWord_321905, baseEnd_321905] using wordTrace_append hprefix tailTrace_321905
  have hstable : (prefixWord ++ tailWord_321905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321905).length < 2 ^ (prefixWord ++ tailWord_321905).sum := by decide
  have hdescent : baseEnd_321905 < baseStart_321905 := by decide
  rcases family_descends (prefixWord ++ tailWord_321905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321907 : List Nat := [1, 1, 1, 2, 2, 1, 2, 6, 3, 3]
def baseStart_321907 : Nat := 118140960795 + 321907 * 2 ^ 59
def prefixEnd_321907 : Nat := 4983230072969 + 3 ^ 40 * 321907 * 2
def baseEnd_321907 : Nat := 110195344697984847388055

theorem tailTrace_321907 : CollatzResearch.WordTrace tailWord_321907 prefixEnd_321907 110195344697984847388055 := by
  unfold tailWord_321907
  simp only [CollatzResearch.WordTrace]
  refine ⟨11740912844793391183739975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7827275229862260789159983 11740912844793391183739975)
  ·
    refine ⟨17611369267190086775609963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11740912844793391183739975 17611369267190086775609963)
    ·
      refine ⟨26417053900785130163414945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17611369267190086775609963 26417053900785130163414945)
      ·
        refine ⟨19812790425588847622561209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26417053900785130163414945 19812790425588847622561209)
        ·
          refine ⟨14859592819191635716920907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19812790425588847622561209 14859592819191635716920907)
          ·
            refine ⟨22289389228787453575381361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14859592819191635716920907 22289389228787453575381361)
            ·
              refine ⟨16717041921590590181536021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22289389228787453575381361 16717041921590590181536021)
              ·
                refine ⟨783611340074558914759501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16717041921590590181536021 783611340074558914759501)
                ·
                  refine ⟨293854252527959593034813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 783611340074558914759501 293854252527959593034813)
                  ·
                    refine ⟨110195344697984847388055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 293854252527959593034813 110195344697984847388055)
                    ·
                      rfl

theorem cell22_321907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 6, 3, 3].length) (baseStart_321907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_321907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_321907 prefixEnd_321907 := by exact prefixLift 321907
  have htrace : WordTrace (prefixWord ++ tailWord_321907) baseStart_321907 baseEnd_321907 := by
    simpa [prefixWord, tailWord_321907, baseEnd_321907] using wordTrace_append hprefix tailTrace_321907
  have hstable : (prefixWord ++ tailWord_321907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321907).length < 2 ^ (prefixWord ++ tailWord_321907).sum := by decide
  have hdescent : baseEnd_321907 < baseStart_321907 := by decide
  rcases family_descends (prefixWord ++ tailWord_321907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321909 : List Nat := [1, 3, 4, 1, 2, 2, 3, 6]
def baseStart_321909 : Nat := 118140960795 + 321909 * 2 ^ 59
def prefixEnd_321909 : Nat := 4983230072969 + 3 ^ 40 * 321909 * 2
def baseEnd_321909 : Nat := 12244003259873056537561

theorem tailTrace_321909 : CollatzResearch.WordTrace tailWord_321909 prefixEnd_321909 12244003259873056537561 := by
  unfold tailWord_321909
  simp only [CollatzResearch.WordTrace]
  refine ⟨11740985790786145525312781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7827323860524097016875187 11740985790786145525312781)
  ·
    refine ⟨4402869671544804571992293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11740985790786145525312781 4402869671544804571992293)
    ·
      refine ⟨825538063414650857248555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4402869671544804571992293 825538063414650857248555)
      ·
        refine ⟨1238307095121976285872833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 825538063414650857248555 1238307095121976285872833)
        ·
          refine ⟨928730321341482214404625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1238307095121976285872833 928730321341482214404625)
          ·
            refine ⟨696547741006111660803469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 928730321341482214404625 696547741006111660803469)
            ·
              refine ⟨261205402877291872801301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 696547741006111660803469 261205402877291872801301)
              ·
                refine ⟨12244003259873056537561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 261205402877291872801301 12244003259873056537561)
                ·
                  rfl

theorem cell22_321909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 3, 6].length) (baseStart_321909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_321909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_321909 prefixEnd_321909 := by exact prefixLift 321909
  have htrace : WordTrace (prefixWord ++ tailWord_321909) baseStart_321909 baseEnd_321909 := by
    simpa [prefixWord, tailWord_321909, baseEnd_321909] using wordTrace_append hprefix tailTrace_321909
  have hstable : (prefixWord ++ tailWord_321909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321909).length < 2 ^ (prefixWord ++ tailWord_321909).sum := by decide
  have hdescent : baseEnd_321909 < baseStart_321909 := by decide
  rcases family_descends (prefixWord ++ tailWord_321909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321930 : List Nat := [3, 1, 2, 5, 2, 1, 1, 2, 2, 3]
def baseStart_321930 : Nat := 118140960795 + 321930 * 2 ^ 59
def prefixEnd_321930 : Nat := 4983230072969 + 3 ^ 40 * 321930 * 2
def baseEnd_321930 : Nat := 110203218068020454062985

theorem tailTrace_321930 : CollatzResearch.WordTrace tailWord_321930 prefixEnd_321930 110203218068020454062985 := by
  unfold tailWord_321930
  simp only [CollatzResearch.WordTrace]
  refine ⟨2935437930927516527956811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7827834482473377407884829 2935437930927516527956811)
  ·
    refine ⟨4403156896391274791935217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2935437930927516527956811 4403156896391274791935217)
    ·
      refine ⟨3302367672293456093951413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4403156896391274791935217 3302367672293456093951413)
      ·
        refine ⟨309596969277511508807945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3302367672293456093951413 309596969277511508807945)
        ·
          refine ⟨232197726958133631605959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 309596969277511508807945 232197726958133631605959)
          ·
            refine ⟨348296590437200447408939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232197726958133631605959 348296590437200447408939)
            ·
              refine ⟨522444885655800671113409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 348296590437200447408939 522444885655800671113409)
              ·
                refine ⟨391833664241850503335057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 522444885655800671113409 391833664241850503335057)
                ·
                  refine ⟨293875248181387877501293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 391833664241850503335057 293875248181387877501293)
                  ·
                    refine ⟨110203218068020454062985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 293875248181387877501293 110203218068020454062985)
                    ·
                      rfl

theorem cell22_321930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 2, 2, 3].length) (baseStart_321930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_321930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_321930 prefixEnd_321930 := by exact prefixLift 321930
  have htrace : WordTrace (prefixWord ++ tailWord_321930) baseStart_321930 baseEnd_321930 := by
    simpa [prefixWord, tailWord_321930, baseEnd_321930] using wordTrace_append hprefix tailTrace_321930
  have hstable : (prefixWord ++ tailWord_321930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321930).length < 2 ^ (prefixWord ++ tailWord_321930).sum := by decide
  have hdescent : baseEnd_321930 < baseStart_321930 := by decide
  rcases family_descends (prefixWord ++ tailWord_321930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321952 : List Nat := [2, 1, 1, 4, 1, 3, 2, 1, 2, 5]
def baseStart_321952 : Nat := 118140960795 + 321952 * 2 ^ 59
def prefixEnd_321952 : Nat := 4983230072969 + 3 ^ 40 * 321952 * 2
def baseEnd_321952 : Nat := 110210749117619730012917

theorem tailTrace_321952 : CollatzResearch.WordTrace tailWord_321952 prefixEnd_321952 110210749117619730012917 := by
  unfold tailWord_321952
  simp only [CollatzResearch.WordTrace]
  refine ⟨5871277064815181934564055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7828369419753575912752073 5871277064815181934564055)
  ·
    refine ⟨8806915597222772901846083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5871277064815181934564055 8806915597222772901846083)
    ·
      refine ⟨13210373395834159352769125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8806915597222772901846083 13210373395834159352769125)
      ·
        refine ⟨2476945011718904878644211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13210373395834159352769125 2476945011718904878644211)
        ·
          refine ⟨3715417517578357317966317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2476945011718904878644211 3715417517578357317966317)
          ·
            refine ⟨1393281569091883994237369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3715417517578357317966317 1393281569091883994237369)
            ·
              refine ⟨1044961176818912995678027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1393281569091883994237369 1044961176818912995678027)
              ·
                refine ⟨1567441765228369493517041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1044961176818912995678027 1567441765228369493517041)
                ·
                  refine ⟨1175581323921277120137781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1567441765228369493517041 1175581323921277120137781)
                  ·
                    refine ⟨110210749117619730012917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1175581323921277120137781 110210749117619730012917)
                    ·
                      rfl

theorem cell22_321952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 2, 5].length) (baseStart_321952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_321952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_321952 prefixEnd_321952 := by exact prefixLift 321952
  have htrace : WordTrace (prefixWord ++ tailWord_321952) baseStart_321952 baseEnd_321952 := by
    simpa [prefixWord, tailWord_321952, baseEnd_321952] using wordTrace_append hprefix tailTrace_321952
  have hstable : (prefixWord ++ tailWord_321952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321952).length < 2 ^ (prefixWord ++ tailWord_321952).sum := by decide
  have hdescent : baseEnd_321952 < baseStart_321952 := by decide
  rcases family_descends (prefixWord ++ tailWord_321952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321982 : List Nat := [4, 2, 1, 1, 1, 1, 2, 2, 8]
def baseStart_321982 : Nat := 118140960795 + 321982 * 2 ^ 59
def prefixEnd_321982 : Nat := 4983230072969 + 3 ^ 40 * 321982 * 2
def baseEnd_321982 : Nat := 36740339576903217254275

theorem tailTrace_321982 : CollatzResearch.WordTrace tailWord_321982 prefixEnd_321982 36740339576903217254275 := by
  unfold tailWord_321982
  simp only [CollatzResearch.WordTrace]
  refine ⟨1467956039940209874090025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7829098879681119328480133 1467956039940209874090025)
  ·
    refine ⟨1100967029955157405567519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1467956039940209874090025 1100967029955157405567519)
    ·
      refine ⟨1651450544932736108351279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1100967029955157405567519 1651450544932736108351279)
      ·
        refine ⟨2477175817399104162526919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1651450544932736108351279 2477175817399104162526919)
        ·
          refine ⟨3715763726098656243790379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2477175817399104162526919 3715763726098656243790379)
          ·
            refine ⟨5573645589147984365685569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3715763726098656243790379 5573645589147984365685569)
            ·
              refine ⟨4180234191860988274264177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5573645589147984365685569 4180234191860988274264177)
              ·
                refine ⟨3135175643895741205698133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4180234191860988274264177 3135175643895741205698133)
                ·
                  refine ⟨36740339576903217254275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3135175643895741205698133 36740339576903217254275)
                  ·
                    rfl

theorem cell22_321982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_321982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_321982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_321982 prefixEnd_321982 := by exact prefixLift 321982
  have htrace : WordTrace (prefixWord ++ tailWord_321982) baseStart_321982 baseEnd_321982 := by
    simpa [prefixWord, tailWord_321982, baseEnd_321982] using wordTrace_append hprefix tailTrace_321982
  have hstable : (prefixWord ++ tailWord_321982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321982).length < 2 ^ (prefixWord ++ tailWord_321982).sum := by decide
  have hdescent : baseEnd_321982 < baseStart_321982 := by decide
  rcases family_descends (prefixWord ++ tailWord_321982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322018 : List Nat := [3, 3, 3, 2, 1, 1, 1, 1, 3, 4]
def baseStart_322018 : Nat := 118140960795 + 322018 * 2 ^ 59
def prefixEnd_322018 : Nat := 4983230072969 + 3 ^ 40 * 322018 * 2
def baseEnd_322018 : Nat := 110233342266417557862715

theorem tailTrace_322018 : CollatzResearch.WordTrace tailWord_322018 prefixEnd_322018 110233342266417557862715 := by
  unfold tailWord_322018
  simp only [CollatzResearch.WordTrace]
  refine ⟨2936240336847814285257677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7829974231594171427353805 2936240336847814285257677)
  ·
    refine ⟨1101090126317930356971629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2936240336847814285257677 1101090126317930356971629)
    ·
      refine ⟨412908797369223883864361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1101090126317930356971629 412908797369223883864361)
      ·
        refine ⟨309681598026917912898271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 412908797369223883864361 309681598026917912898271)
        ·
          refine ⟨464522397040376869347407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 309681598026917912898271 464522397040376869347407)
          ·
            refine ⟨696783595560565304021111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 464522397040376869347407 696783595560565304021111)
            ·
              refine ⟨1045175393340847956031667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 696783595560565304021111 1045175393340847956031667)
              ·
                refine ⟨1567763090011271934047501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1045175393340847956031667 1567763090011271934047501)
                ·
                  refine ⟨587911158754226975267813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1567763090011271934047501 587911158754226975267813)
                  ·
                    refine ⟨110233342266417557862715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 587911158754226975267813 110233342266417557862715)
                    ·
                      rfl

theorem cell22_322018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_322018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_322018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_322018 prefixEnd_322018 := by exact prefixLift 322018
  have htrace : WordTrace (prefixWord ++ tailWord_322018) baseStart_322018 baseEnd_322018 := by
    simpa [prefixWord, tailWord_322018, baseEnd_322018] using wordTrace_append hprefix tailTrace_322018
  have hstable : (prefixWord ++ tailWord_322018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322018).length < 2 ^ (prefixWord ++ tailWord_322018).sum := by decide
  have hdescent : baseEnd_322018 < baseStart_322018 := by decide
  rcases family_descends (prefixWord ++ tailWord_322018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322076 : List Nat := [2, 2, 3, 1, 2, 3, 1, 2, 3, 3]
def baseStart_322076 : Nat := 118140960795 + 322076 * 2 ^ 59
def prefixEnd_322076 : Nat := 4983230072969 + 3 ^ 40 * 322076 * 2
def baseEnd_322076 : Nat := 110253196851724739912537

theorem tailTrace_322076 : CollatzResearch.WordTrace tailWord_322076 prefixEnd_322076 110253196851724739912537 := by
  unfold tailWord_322076
  simp only [CollatzResearch.WordTrace]
  refine ⟨5873538390590566523321041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7831384520787422031094721 5873538390590566523321041)
  ·
    refine ⟨4405153792942924892490781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5873538390590566523321041 4405153792942924892490781)
    ·
      refine ⟨1651932672353596834684043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4405153792942924892490781 1651932672353596834684043)
      ·
        refine ⟨2477899008530395252026065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1651932672353596834684043 2477899008530395252026065)
        ·
          refine ⟨1858424256397796439019549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2477899008530395252026065 1858424256397796439019549)
          ·
            refine ⟨696909096149173664632331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1858424256397796439019549 696909096149173664632331)
            ·
              refine ⟨1045363644223760496948497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 696909096149173664632331 1045363644223760496948497)
              ·
                refine ⟨784022733167820372711373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1045363644223760496948497 784022733167820372711373)
                ·
                  refine ⟨294008524937932639766765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 784022733167820372711373 294008524937932639766765)
                  ·
                    refine ⟨110253196851724739912537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 294008524937932639766765 110253196851724739912537)
                    ·
                      rfl

theorem cell22_322076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 2, 3, 3].length) (baseStart_322076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_322076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_322076 prefixEnd_322076 := by exact prefixLift 322076
  have htrace : WordTrace (prefixWord ++ tailWord_322076) baseStart_322076 baseEnd_322076 := by
    simpa [prefixWord, tailWord_322076, baseEnd_322076] using wordTrace_append hprefix tailTrace_322076
  have hstable : (prefixWord ++ tailWord_322076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322076).length < 2 ^ (prefixWord ++ tailWord_322076).sum := by decide
  have hdescent : baseEnd_322076 < baseStart_322076 := by decide
  rcases family_descends (prefixWord ++ tailWord_322076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322106 : List Nat := [3, 1, 1, 1, 3, 5, 1, 2, 5]
def baseStart_322106 : Nat := 118140960795 + 322106 * 2 ^ 59
def prefixEnd_322106 : Nat := 4983230072969 + 3 ^ 40 * 322106 * 2
def baseEnd_322106 : Nat := 36754488821604887220815

theorem tailTrace_322106 : CollatzResearch.WordTrace tailWord_322106 prefixEnd_322106 36754488821604887220815 := by
  unfold tailWord_322106
  simp only [CollatzResearch.WordTrace]
  refine ⟨2937042742768112042558543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7832113980714965446822781 2937042742768112042558543)
  ·
    refine ⟨4405564114152168063837815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2937042742768112042558543 4405564114152168063837815)
    ·
      refine ⟨6608346171228252095756723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4405564114152168063837815 6608346171228252095756723)
      ·
        refine ⟨9912519256842378143635085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6608346171228252095756723 9912519256842378143635085)
        ·
          refine ⟨3717194721315891803863157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9912519256842378143635085 3717194721315891803863157)
          ·
            refine ⟨348487005123364856612171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3717194721315891803863157 348487005123364856612171)
            ·
              refine ⟨522730507685047284918257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 348487005123364856612171 522730507685047284918257)
              ·
                refine ⟨392047880763785463688693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 522730507685047284918257 392047880763785463688693)
                ·
                  refine ⟨36754488821604887220815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 392047880763785463688693 36754488821604887220815)
                  ·
                    rfl

theorem cell22_322106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 2, 5].length) (baseStart_322106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_322106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_322106 prefixEnd_322106 := by exact prefixLift 322106
  have htrace : WordTrace (prefixWord ++ tailWord_322106) baseStart_322106 baseEnd_322106 := by
    simpa [prefixWord, tailWord_322106, baseEnd_322106] using wordTrace_append hprefix tailTrace_322106
  have hstable : (prefixWord ++ tailWord_322106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322106).length < 2 ^ (prefixWord ++ tailWord_322106).sum := by decide
  have hdescent : baseEnd_322106 < baseStart_322106 := by decide
  rcases family_descends (prefixWord ++ tailWord_322106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322110 : List Nat := [4, 2, 1, 4, 1, 1, 2, 1, 3, 3]
def baseStart_322110 : Nat := 118140960795 + 322110 * 2 ^ 59
def prefixEnd_322110 : Nat := 4983230072969 + 3 ^ 40 * 322110 * 2
def baseEnd_322110 : Nat := 110264835746559984562433

theorem tailTrace_322110 : CollatzResearch.WordTrace tailWord_322110 prefixEnd_322110 110264835746559984562433 := by
  unfold tailWord_322110
  simp only [CollatzResearch.WordTrace]
  refine ⟨1468539607882244606672473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7832211242038637902253189 1468539607882244606672473)
  ·
    refine ⟨1101404705911683455004355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1468539607882244606672473 1101404705911683455004355)
    ·
      refine ⟨1652107058867525182506533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1101404705911683455004355 1652107058867525182506533)
      ·
        refine ⟨309770073537660971719975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1652107058867525182506533 309770073537660971719975)
        ·
          refine ⟨464655110306491457579963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 309770073537660971719975 464655110306491457579963)
          ·
            refine ⟨696982665459737186369945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 464655110306491457579963 696982665459737186369945)
            ·
              refine ⟨522736999094802889777459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 696982665459737186369945 522736999094802889777459)
              ·
                refine ⟨784105498642204334666189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 522736999094802889777459 784105498642204334666189)
                ·
                  refine ⟨294039561990826625499821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 784105498642204334666189 294039561990826625499821)
                  ·
                    refine ⟨110264835746559984562433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 294039561990826625499821 110264835746559984562433)
                    ·
                      rfl

theorem cell22_322110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 1, 3, 3].length) (baseStart_322110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_322110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_322110 prefixEnd_322110 := by exact prefixLift 322110
  have htrace : WordTrace (prefixWord ++ tailWord_322110) baseStart_322110 baseEnd_322110 := by
    simpa [prefixWord, tailWord_322110, baseEnd_322110] using wordTrace_append hprefix tailTrace_322110
  have hstable : (prefixWord ++ tailWord_322110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322110).length < 2 ^ (prefixWord ++ tailWord_322110).sum := by decide
  have hdescent : baseEnd_322110 < baseStart_322110 := by decide
  rcases family_descends (prefixWord ++ tailWord_322110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322196 : List Nat := [2, 4, 2, 2, 1, 1, 2, 8]
def baseStart_322196 : Nat := 118140960795 + 322196 * 2 ^ 59
def prefixEnd_322196 : Nat := 4983230072969 + 3 ^ 40 * 322196 * 2
def baseEnd_322196 : Nat := 12254919478231602990241

theorem tailTrace_322196 : CollatzResearch.WordTrace tailWord_322196 prefixEnd_322196 12254919478231602990241 := by
  unfold tailWord_322196
  simp only [CollatzResearch.WordTrace]
  refine ⟨5875726770373196770505221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7834302360497595694006961 5875726770373196770505221)
  ·
    refine ⟨1101698769444974394469729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5875726770373196770505221 1101698769444974394469729)
    ·
      refine ⟨826274077083730795852297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1101698769444974394469729 826274077083730795852297)
      ·
        refine ⟨619705557812798096889223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 826274077083730795852297 619705557812798096889223)
        ·
          refine ⟨929558336719197145333835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 619705557812798096889223 929558336719197145333835)
          ·
            refine ⟨1394337505078795718000753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 929558336719197145333835 1394337505078795718000753)
            ·
              refine ⟨1045753128809096788500565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1394337505078795718000753 1045753128809096788500565)
              ·
                refine ⟨12254919478231602990241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1045753128809096788500565 12254919478231602990241)
                ·
                  rfl

theorem cell22_322196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 8].length) (baseStart_322196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_322196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_322196 prefixEnd_322196 := by exact prefixLift 322196
  have htrace : WordTrace (prefixWord ++ tailWord_322196) baseStart_322196 baseEnd_322196 := by
    simpa [prefixWord, tailWord_322196, baseEnd_322196] using wordTrace_append hprefix tailTrace_322196
  have hstable : (prefixWord ++ tailWord_322196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322196).length < 2 ^ (prefixWord ++ tailWord_322196).sum := by decide
  have hdescent : baseEnd_322196 < baseStart_322196 := by decide
  rcases family_descends (prefixWord ++ tailWord_322196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322230 : List Nat := [5, 1, 3, 1, 2, 2, 1, 7]
def baseStart_322230 : Nat := 118140960795 + 322230 * 2 ^ 59
def prefixEnd_322230 : Nat := 4983230072969 + 3 ^ 40 * 322230 * 2
def baseEnd_322230 : Nat := 12256212688768852395785

theorem tailTrace_322230 : CollatzResearch.WordTrace tailWord_322230 prefixEnd_322230 12256212688768852395785 := by
  unfold tailWord_322230
  simp only [CollatzResearch.WordTrace]
  refine ⟨734543351413951084234259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7835129081748811565165429 734543351413951084234259)
  ·
    refine ⟨1101815027120926626351389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 734543351413951084234259 1101815027120926626351389)
    ·
      refine ⟨413180635170347484881771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1101815027120926626351389 413180635170347484881771)
      ·
        refine ⟨619770952755521227322657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 413180635170347484881771 619770952755521227322657)
        ·
          refine ⟨464828214566640920491993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 619770952755521227322657 464828214566640920491993)
          ·
            refine ⟨348621160924980690368995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 464828214566640920491993 348621160924980690368995)
            ·
              refine ⟨522931741387471035553493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 348621160924980690368995 522931741387471035553493)
              ·
                refine ⟨12256212688768852395785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 522931741387471035553493 12256212688768852395785)
                ·
                  rfl

theorem cell22_322230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 7].length) (baseStart_322230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_322230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_322230 prefixEnd_322230 := by exact prefixLift 322230
  have htrace : WordTrace (prefixWord ++ tailWord_322230) baseStart_322230 baseEnd_322230 := by
    simpa [prefixWord, tailWord_322230, baseEnd_322230] using wordTrace_append hprefix tailTrace_322230
  have hstable : (prefixWord ++ tailWord_322230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322230).length < 2 ^ (prefixWord ++ tailWord_322230).sum := by decide
  have hdescent : baseEnd_322230 < baseStart_322230 := by decide
  rcases family_descends (prefixWord ++ tailWord_322230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322239 : List Nat := [1, 1, 2, 2, 2, 4, 1, 1, 1, 7]
def baseStart_322239 : Nat := 118140960795 + 322239 * 2 ^ 59
def prefixEnd_322239 : Nat := 4983230072969 + 3 ^ 40 * 322239 * 2
def baseEnd_322239 : Nat := 110308995082846648087037

theorem tailTrace_322239 : CollatzResearch.WordTrace tailWord_322239 prefixEnd_322239 110308995082846648087037 := by
  unfold tailWord_322239
  simp only [CollatzResearch.WordTrace]
  refine ⟨11753021879590611884825771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7835347919727074589883847 11753021879590611884825771)
  ·
    refine ⟨17629532819385917827238657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11753021879590611884825771 17629532819385917827238657)
    ·
      refine ⟨13222149614539438370428993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17629532819385917827238657 13222149614539438370428993)
      ·
        refine ⟨9916612210904578777821745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13222149614539438370428993 9916612210904578777821745)
        ·
          refine ⟨7437459158178434083366309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9916612210904578777821745 7437459158178434083366309)
          ·
            refine ⟨1394523592158456390631183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7437459158178434083366309 1394523592158456390631183)
            ·
              refine ⟨2091785388237684585946775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1394523592158456390631183 2091785388237684585946775)
              ·
                refine ⟨3137678082356526878920163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2091785388237684585946775 3137678082356526878920163)
                ·
                  refine ⟨4706517123534790318380245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3137678082356526878920163 4706517123534790318380245)
                  ·
                    refine ⟨110308995082846648087037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4706517123534790318380245 110308995082846648087037)
                    ·
                      rfl

theorem cell22_322239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 7].length) (baseStart_322239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_322239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_322239 prefixEnd_322239 := by exact prefixLift 322239
  have htrace : WordTrace (prefixWord ++ tailWord_322239) baseStart_322239 baseEnd_322239 := by
    simpa [prefixWord, tailWord_322239, baseEnd_322239] using wordTrace_append hprefix tailTrace_322239
  have hstable : (prefixWord ++ tailWord_322239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322239).length < 2 ^ (prefixWord ++ tailWord_322239).sum := by decide
  have hdescent : baseEnd_322239 < baseStart_322239 := by decide
  rcases family_descends (prefixWord ++ tailWord_322239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322286 : List Nat := [4, 1, 2, 1, 1, 3, 1, 3, 6]
def baseStart_322286 : Nat := 118140960795 + 322286 * 2 ^ 59
def prefixEnd_322286 : Nat := 4983230072969 + 3 ^ 40 * 322286 * 2
def baseEnd_322286 : Nat := 36775028047784730720631

theorem tailTrace_322286 : CollatzResearch.WordTrace tailWord_322286 prefixEnd_322286 36775028047784730720631 := by
  unfold tailWord_322286
  simp only [CollatzResearch.WordTrace]
  refine ⟨1469342013802542363973339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7836490740280225941191141 1469342013802542363973339)
  ·
    refine ⟨2204013020703813545960009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1469342013802542363973339 2204013020703813545960009)
    ·
      refine ⟨1653009765527860159470007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2204013020703813545960009 1653009765527860159470007)
      ·
        refine ⟨2479514648291790239205011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1653009765527860159470007 2479514648291790239205011)
        ·
          refine ⟨3719271972437685358807517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2479514648291790239205011 3719271972437685358807517)
          ·
            refine ⟨1394726989664132009552819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3719271972437685358807517 1394726989664132009552819)
            ·
              refine ⟨2092090484496198014329229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1394726989664132009552819 2092090484496198014329229)
              ·
                refine ⟨784533931686074255373461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2092090484496198014329229 784533931686074255373461)
                ·
                  refine ⟨36775028047784730720631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 784533931686074255373461 36775028047784730720631)
                  ·
                    rfl

theorem cell22_322286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 3, 6].length) (baseStart_322286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_322286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_322286 prefixEnd_322286 := by exact prefixLift 322286
  have htrace : WordTrace (prefixWord ++ tailWord_322286) baseStart_322286 baseEnd_322286 := by
    simpa [prefixWord, tailWord_322286, baseEnd_322286] using wordTrace_append hprefix tailTrace_322286
  have hstable : (prefixWord ++ tailWord_322286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322286).length < 2 ^ (prefixWord ++ tailWord_322286).sum := by decide
  have hdescent : baseEnd_322286 < baseStart_322286 := by decide
  rcases family_descends (prefixWord ++ tailWord_322286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322316 : List Nat := [2, 2, 1, 2, 2, 1, 1, 5, 2, 4]
def baseStart_322316 : Nat := 118140960795 + 322316 * 2 ^ 59
def prefixEnd_322316 : Nat := 4983230072969 + 3 ^ 40 * 322316 * 2
def baseEnd_322316 : Nat := 110335353756444113911801

theorem tailTrace_322316 : CollatzResearch.WordTrace tailWord_322316 prefixEnd_322316 110335353756444113911801 := by
  unfold tailWord_322316
  simp only [CollatzResearch.WordTrace]
  refine ⟨5877915150155827017689401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7837220200207769356919201 5877915150155827017689401)
  ·
    refine ⟨4408436362616870263267051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5877915150155827017689401 4408436362616870263267051)
    ·
      refine ⟨6612654543925305394900577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4408436362616870263267051 6612654543925305394900577)
      ·
        refine ⟨4959490907943979046175433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6612654543925305394900577 4959490907943979046175433)
        ·
          refine ⟨3719618180957984284631575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4959490907943979046175433 3719618180957984284631575)
          ·
            refine ⟨5579427271436976426947363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3719618180957984284631575 5579427271436976426947363)
            ·
              refine ⟨8369140907155464640421045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5579427271436976426947363 8369140907155464640421045)
              ·
                refine ⟨784606960045824810039473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8369140907155464640421045 784606960045824810039473)
                ·
                  refine ⟨588455220034368607529605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 784606960045824810039473 588455220034368607529605)
                  ·
                    refine ⟨110335353756444113911801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 588455220034368607529605 110335353756444113911801)
                    ·
                      rfl

theorem cell22_322316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 5, 2, 4].length) (baseStart_322316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_322316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_322316 prefixEnd_322316 := by exact prefixLift 322316
  have htrace : WordTrace (prefixWord ++ tailWord_322316) baseStart_322316 baseEnd_322316 := by
    simpa [prefixWord, tailWord_322316, baseEnd_322316] using wordTrace_append hprefix tailTrace_322316
  have hstable : (prefixWord ++ tailWord_322316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322316).length < 2 ^ (prefixWord ++ tailWord_322316).sum := by decide
  have hdescent : baseEnd_322316 < baseStart_322316 := by decide
  rcases family_descends (prefixWord ++ tailWord_322316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322393 : List Nat := [1, 2, 1, 2, 2, 5, 2, 2, 5]
def baseStart_322393 : Nat := 118140960795 + 322393 * 2 ^ 59
def prefixEnd_322393 : Nat := 4983230072969 + 3 ^ 40 * 322393 * 2
def baseEnd_322393 : Nat := 36787237476680526578855

theorem tailTrace_322393 : CollatzResearch.WordTrace tailWord_322393 prefixEnd_322393 36787237476680526578855 := by
  unfold tailWord_322393
  simp only [CollatzResearch.WordTrace]
  refine ⟨11758638721032696185931833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7839092480688464123954555 11758638721032696185931833)
  ·
    refine ⟨8818979040774522139448875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11758638721032696185931833 8818979040774522139448875)
    ·
      refine ⟨13228468561161783209173313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8818979040774522139448875 13228468561161783209173313)
      ·
        refine ⟨9921351420871337406879985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13228468561161783209173313 9921351420871337406879985)
        ·
          refine ⟨7441013565653503055159989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9921351420871337406879985 7441013565653503055159989)
          ·
            refine ⟨697595021780015911421249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7441013565653503055159989 697595021780015911421249)
            ·
              refine ⟨523196266335011933565937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 697595021780015911421249 523196266335011933565937)
              ·
                refine ⟨392397199751258950174453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 523196266335011933565937 392397199751258950174453)
                ·
                  refine ⟨36787237476680526578855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 392397199751258950174453 36787237476680526578855)
                  ·
                    rfl

theorem cell22_322393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 2, 5].length) (baseStart_322393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_322393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_322393 prefixEnd_322393 := by exact prefixLift 322393
  have htrace : WordTrace (prefixWord ++ tailWord_322393) baseStart_322393 baseEnd_322393 := by
    simpa [prefixWord, tailWord_322393, baseEnd_322393] using wordTrace_append hprefix tailTrace_322393
  have hstable : (prefixWord ++ tailWord_322393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322393).length < 2 ^ (prefixWord ++ tailWord_322393).sum := by decide
  have hdescent : baseEnd_322393 < baseStart_322393 := by decide
  rcases family_descends (prefixWord ++ tailWord_322393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322408 : List Nat := [2, 1, 4, 2, 1, 3, 1, 1, 2, 5]
def baseStart_322408 : Nat := 118140960795 + 322408 * 2 ^ 59
def prefixEnd_322408 : Nat := 4983230072969 + 3 ^ 40 * 322408 * 2
def baseEnd_322408 : Nat := 110366847236586540611519

theorem tailTrace_322408 : CollatzResearch.WordTrace tailWord_322408 prefixEnd_322408 110366847236586540611519 := by
  unfold tailWord_322408
  simp only [CollatzResearch.WordTrace]
  refine ⟨5879592907989176873863939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7839457210652235831818585 5879592907989176873863939)
  ·
    refine ⟨8819389361983765310795909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5879592907989176873863939 8819389361983765310795909)
    ·
      refine ⟨1653635505371955995774233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8819389361983765310795909 1653635505371955995774233)
      ·
        refine ⟨1240226629028966996830675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1653635505371955995774233 1240226629028966996830675)
        ·
          refine ⟨1860339943543450495246013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1240226629028966996830675 1860339943543450495246013)
          ·
            refine ⟨697627478828793935717255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1860339943543450495246013 697627478828793935717255)
            ·
              refine ⟨1046441218243190903575883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 697627478828793935717255 1046441218243190903575883)
              ·
                refine ⟨1569661827364786355363825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1046441218243190903575883 1569661827364786355363825)
                ·
                  refine ⟨1177246370523589766522869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1569661827364786355363825 1177246370523589766522869)
                  ·
                    refine ⟨110366847236586540611519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1177246370523589766522869 110366847236586540611519)
                    ·
                      rfl

theorem cell22_322408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_322408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_322408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_322408 prefixEnd_322408 := by exact prefixLift 322408
  have htrace : WordTrace (prefixWord ++ tailWord_322408) baseStart_322408 baseEnd_322408 := by
    simpa [prefixWord, tailWord_322408, baseEnd_322408] using wordTrace_append hprefix tailTrace_322408
  have hstable : (prefixWord ++ tailWord_322408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322408).length < 2 ^ (prefixWord ++ tailWord_322408).sum := by decide
  have hdescent : baseEnd_322408 < baseStart_322408 := by decide
  rcases family_descends (prefixWord ++ tailWord_322408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322440 : List Nat := [2, 1, 3, 3, 2, 2, 1, 3, 1, 4]
def baseStart_322440 : Nat := 118140960795 + 322440 * 2 ^ 59
def prefixEnd_322440 : Nat := 4983230072969 + 3 ^ 40 * 322440 * 2
def baseEnd_322440 : Nat := 110377801490549123811421

theorem tailTrace_322440 : CollatzResearch.WordTrace tailWord_322440 prefixEnd_322440 110377801490549123811421 := by
  unfold tailWord_322440
  simp only [CollatzResearch.WordTrace]
  refine ⟨5880176475931211606446387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7840235301241615475261849 5880176475931211606446387)
  ·
    refine ⟨8820264713896817409669581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5880176475931211606446387 8820264713896817409669581)
    ·
      refine ⟨3307599267711306528626093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8820264713896817409669581 3307599267711306528626093)
      ·
        refine ⟨1240349725391739948234785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3307599267711306528626093 1240349725391739948234785)
        ·
          refine ⟨930262294043804961176089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1240349725391739948234785 930262294043804961176089)
          ·
            refine ⟨697696720532853720882067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 930262294043804961176089 697696720532853720882067)
            ·
              refine ⟨1046545080799280581323101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 697696720532853720882067 1046545080799280581323101)
              ·
                refine ⟨392454405299730217996163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1046545080799280581323101 392454405299730217996163)
                ·
                  refine ⟨588681607949595326994245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 392454405299730217996163 588681607949595326994245)
                  ·
                    refine ⟨110377801490549123811421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 588681607949595326994245 110377801490549123811421)
                    ·
                      rfl

theorem cell22_322440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 3, 1, 4].length) (baseStart_322440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_322440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_322440 prefixEnd_322440 := by exact prefixLift 322440
  have htrace : WordTrace (prefixWord ++ tailWord_322440) baseStart_322440 baseEnd_322440 := by
    simpa [prefixWord, tailWord_322440, baseEnd_322440] using wordTrace_append hprefix tailTrace_322440
  have hstable : (prefixWord ++ tailWord_322440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322440).length < 2 ^ (prefixWord ++ tailWord_322440).sum := by decide
  have hdescent : baseEnd_322440 < baseStart_322440 := by decide
  rcases family_descends (prefixWord ++ tailWord_322440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322603 : List Nat := [1, 1, 1, 1, 2, 1, 7, 1, 1, 6]
def baseStart_322603 : Nat := 118140960795 + 322603 * 2 ^ 59
def prefixEnd_322603 : Nat := 4983230072969 + 3 ^ 40 * 322603 * 2
def baseEnd_322603 : Nat := 110433599721671031985921

theorem tailTrace_322603 : CollatzResearch.WordTrace tailWord_322603 prefixEnd_322603 110433599721671031985921 := by
  unfold tailWord_322603
  simp only [CollatzResearch.WordTrace]
  refine ⟨11766298050271902051076463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7844198700181268034050975 11766298050271902051076463)
  ·
    refine ⟨17649447075407853076614695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11766298050271902051076463 17649447075407853076614695)
    ·
      refine ⟨26474170613111779614922043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17649447075407853076614695 26474170613111779614922043)
      ·
        refine ⟨39711255919667669422383065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26474170613111779614922043 39711255919667669422383065)
        ·
          refine ⟨29783441939750752066787299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39711255919667669422383065 29783441939750752066787299)
          ·
            refine ⟨44675162909626128100180949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29783441939750752066787299 44675162909626128100180949)
            ·
              refine ⟨1047074130694362377347991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 44675162909626128100180949 1047074130694362377347991)
              ·
                refine ⟨1570611196041543566021987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1047074130694362377347991 1570611196041543566021987)
                ·
                  refine ⟨2355916794062315349032981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1570611196041543566021987 2355916794062315349032981)
                  ·
                    refine ⟨110433599721671031985921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2355916794062315349032981 110433599721671031985921)
                    ·
                      rfl

theorem cell22_322603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 6].length) (baseStart_322603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_322603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_322603 prefixEnd_322603 := by exact prefixLift 322603
  have htrace : WordTrace (prefixWord ++ tailWord_322603) baseStart_322603 baseEnd_322603 := by
    simpa [prefixWord, tailWord_322603, baseEnd_322603] using wordTrace_append hprefix tailTrace_322603
  have hstable : (prefixWord ++ tailWord_322603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322603).length < 2 ^ (prefixWord ++ tailWord_322603).sum := by decide
  have hdescent : baseEnd_322603 < baseStart_322603 := by decide
  rcases family_descends (prefixWord ++ tailWord_322603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322650 : List Nat := [3, 1, 1, 2, 1, 1, 2, 3, 5, 3]
def baseStart_322650 : Nat := 118140960795 + 322650 * 2 ^ 59
def prefixEnd_322650 : Nat := 4983230072969 + 3 ^ 40 * 322650 * 2
def baseEnd_322650 : Nat := 110449688782178576060777

theorem tailTrace_322650 : CollatzResearch.WordTrace tailWord_322650 prefixEnd_322650 110449688782178576060777 := by
  unfold tailWord_322650
  simp only [CollatzResearch.WordTrace]
  refine ⟨2942003070275407269509351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7845341520734419385358269 2942003070275407269509351)
  ·
    refine ⟨4413004605413110904264027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2942003070275407269509351 4413004605413110904264027)
    ·
      refine ⟨6619506908119666356396041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4413004605413110904264027 6619506908119666356396041)
      ·
        refine ⟨4964630181089749767297031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6619506908119666356396041 4964630181089749767297031)
        ·
          refine ⟨7446945271634624650945547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4964630181089749767297031 7446945271634624650945547)
          ·
            refine ⟨11170417907451936976418321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7446945271634624650945547 11170417907451936976418321)
            ·
              refine ⟨8377813430588952732313741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11170417907451936976418321 8377813430588952732313741)
              ·
                refine ⟨3141680036470857274617653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8377813430588952732313741 3141680036470857274617653)
                ·
                  refine ⟨294532503419142869495405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3141680036470857274617653 294532503419142869495405)
                  ·
                    refine ⟨110449688782178576060777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 294532503419142869495405 110449688782178576060777)
                    ·
                      rfl

theorem cell22_322650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 5, 3].length) (baseStart_322650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_322650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_322650 prefixEnd_322650 := by exact prefixLift 322650
  have htrace : WordTrace (prefixWord ++ tailWord_322650) baseStart_322650 baseEnd_322650 := by
    simpa [prefixWord, tailWord_322650, baseEnd_322650] using wordTrace_append hprefix tailTrace_322650
  have hstable : (prefixWord ++ tailWord_322650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322650).length < 2 ^ (prefixWord ++ tailWord_322650).sum := by decide
  have hdescent : baseEnd_322650 < baseStart_322650 := by decide
  rcases family_descends (prefixWord ++ tailWord_322650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322654 : List Nat := [4, 4, 1, 1, 1, 1, 2, 1, 1, 6]
def baseStart_322654 : Nat := 118140960795 + 322654 * 2 ^ 59
def prefixEnd_322654 : Nat := 4983230072969 + 3 ^ 40 * 322654 * 2
def baseEnd_322654 : Nat := 110451058063923898960765

theorem tailTrace_322654 : CollatzResearch.WordTrace tailWord_322654 prefixEnd_322654 110451058063923898960765 := by
  unfold tailWord_322654
  simp only [CollatzResearch.WordTrace]
  refine ⟨1471019771635892220147877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7845438782058091840788677 1471019771635892220147877)
  ·
    refine ⟨275816207181729791277727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1471019771635892220147877 275816207181729791277727)
    ·
      refine ⟨413724310772594686916591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275816207181729791277727 413724310772594686916591)
      ·
        refine ⟨620586466158892030374887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 413724310772594686916591 620586466158892030374887)
        ·
          refine ⟨930879699238338045562331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 620586466158892030374887 930879699238338045562331)
          ·
            refine ⟨1396319548857507068343497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 930879699238338045562331 1396319548857507068343497)
            ·
              refine ⟨1047239661643130301257623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1396319548857507068343497 1047239661643130301257623)
              ·
                refine ⟨1570859492464695451886435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1047239661643130301257623 1570859492464695451886435)
                ·
                  refine ⟨2356289238697043177829653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1570859492464695451886435 2356289238697043177829653)
                  ·
                    refine ⟨110451058063923898960765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2356289238697043177829653 110451058063923898960765)
                    ·
                      rfl

theorem cell22_322654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_322654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_322654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_322654 prefixEnd_322654 := by exact prefixLift 322654
  have htrace : WordTrace (prefixWord ++ tailWord_322654) baseStart_322654 baseEnd_322654 := by
    simpa [prefixWord, tailWord_322654, baseEnd_322654] using wordTrace_append hprefix tailTrace_322654
  have hstable : (prefixWord ++ tailWord_322654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322654).length < 2 ^ (prefixWord ++ tailWord_322654).sum := by decide
  have hdescent : baseEnd_322654 < baseStart_322654 := by decide
  rcases family_descends (prefixWord ++ tailWord_322654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322686 : List Nat := [4, 2, 4, 1, 1, 1, 2, 7]
def baseStart_322686 : Nat := 118140960795 + 322686 * 2 ^ 59
def prefixEnd_322686 : Nat := 4983230072969 + 3 ^ 40 * 322686 * 2
def baseEnd_322686 : Nat := 12273556924209609128963

theorem tailTrace_322686 : CollatzResearch.WordTrace tailWord_322686 prefixEnd_322686 12273556924209609128963 := by
  unfold tailWord_322686
  simp only [CollatzResearch.WordTrace]
  refine ⟨1471165663621400903293489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7846216872647471484231941 1471165663621400903293489)
  ·
    refine ⟨1103374247716050677470117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1471165663621400903293489 1103374247716050677470117)
    ·
      refine ⟨206882671446759502025647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1103374247716050677470117 206882671446759502025647)
      ·
        refine ⟨310324007170139253038471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206882671446759502025647 310324007170139253038471)
        ·
          refine ⟨465486010755208879557707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 310324007170139253038471 465486010755208879557707)
          ·
            refine ⟨698229016132813319336561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 465486010755208879557707 698229016132813319336561)
            ·
              refine ⟨523671762099609989502421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 698229016132813319336561 523671762099609989502421)
              ·
                refine ⟨12273556924209609128963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 523671762099609989502421 12273556924209609128963)
                ·
                  rfl

theorem cell22_322686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 7].length) (baseStart_322686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_322686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_322686 prefixEnd_322686 := by exact prefixLift 322686
  have htrace : WordTrace (prefixWord ++ tailWord_322686) baseStart_322686 baseEnd_322686 := by
    simpa [prefixWord, tailWord_322686, baseEnd_322686] using wordTrace_append hprefix tailTrace_322686
  have hstable : (prefixWord ++ tailWord_322686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322686).length < 2 ^ (prefixWord ++ tailWord_322686).sum := by decide
  have hdescent : baseEnd_322686 < baseStart_322686 := by decide
  rcases family_descends (prefixWord ++ tailWord_322686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322697 : List Nat := [1, 2, 1, 1, 4, 3, 4, 1, 5]
def baseStart_322697 : Nat := 118140960795 + 322697 * 2 ^ 59
def prefixEnd_322697 : Nat := 4983230072969 + 3 ^ 40 * 322697 * 2
def baseEnd_322697 : Nat := 36821925947562040045211

theorem tailTrace_322697 : CollatzResearch.WordTrace tailWord_322697 prefixEnd_322697 36821925947562040045211 := by
  unfold tailWord_322697
  simp only [CollatzResearch.WordTrace]
  refine ⟨11769726511931356104998345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7846484341287570736665563 11769726511931356104998345)
  ·
    refine ⟨8827294883948517078748759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11769726511931356104998345 8827294883948517078748759)
    ·
      refine ⟨13240942325922775618123139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8827294883948517078748759 13240942325922775618123139)
      ·
        refine ⟨19861413488884163427184709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13240942325922775618123139 19861413488884163427184709)
        ·
          refine ⟨3724015029165780642597133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19861413488884163427184709 3724015029165780642597133)
          ·
            refine ⟨1396505635937167740973925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3724015029165780642597133 1396505635937167740973925)
            ·
              refine ⟨261844806738218951432611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1396505635937167740973925 261844806738218951432611)
              ·
                refine ⟨392767210107328427148917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 261844806738218951432611 392767210107328427148917)
                ·
                  refine ⟨36821925947562040045211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 392767210107328427148917 36821925947562040045211)
                  ·
                    rfl

theorem cell22_322697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 4, 1, 5].length) (baseStart_322697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_322697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_322697 prefixEnd_322697 := by exact prefixLift 322697
  have htrace : WordTrace (prefixWord ++ tailWord_322697) baseStart_322697 baseEnd_322697 := by
    simpa [prefixWord, tailWord_322697, baseEnd_322697] using wordTrace_append hprefix tailTrace_322697
  have hstable : (prefixWord ++ tailWord_322697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322697).length < 2 ^ (prefixWord ++ tailWord_322697).sum := by decide
  have hdescent : baseEnd_322697 < baseStart_322697 := by decide
  rcases family_descends (prefixWord ++ tailWord_322697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322853 : List Nat := [1, 3, 1, 2, 4, 2, 3, 2, 1, 3]
def baseStart_322853 : Nat := 118140960795 + 322853 * 2 ^ 59
def prefixEnd_322853 : Nat := 4983230072969 + 3 ^ 40 * 322853 * 2
def baseEnd_322853 : Nat := 110519179830753713235155

theorem tailTrace_322853 : CollatzResearch.WordTrace tailWord_322853 prefixEnd_322853 110519179830753713235155 := by
  unfold tailWord_322853
  simp only [CollatzResearch.WordTrace]
  refine ⟨11775416299366194747677213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7850277532910796498451475 11775416299366194747677213)
  ·
    refine ⟨4415781112262323030378955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11775416299366194747677213 4415781112262323030378955)
    ·
      refine ⟨6623671668393484545568433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4415781112262323030378955 6623671668393484545568433)
      ·
        refine ⟨4967753751295113409176325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6623671668393484545568433 4967753751295113409176325)
        ·
          refine ⟨931453828367833764220561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4967753751295113409176325 931453828367833764220561)
          ·
            refine ⟨698590371275875323165421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 931453828367833764220561 698590371275875323165421)
            ·
              refine ⟨261971389228453246187033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 698590371275875323165421 261971389228453246187033)
              ·
                refine ⟨196478541921339934640275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 261971389228453246187033 196478541921339934640275)
                ·
                  refine ⟨294717812882009901960413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 196478541921339934640275 294717812882009901960413)
                  ·
                    refine ⟨110519179830753713235155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 294717812882009901960413 110519179830753713235155)
                    ·
                      rfl

theorem cell22_322853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 3, 2, 1, 3].length) (baseStart_322853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_322853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_322853 prefixEnd_322853 := by exact prefixLift 322853
  have htrace : WordTrace (prefixWord ++ tailWord_322853) baseStart_322853 baseEnd_322853 := by
    simpa [prefixWord, tailWord_322853, baseEnd_322853] using wordTrace_append hprefix tailTrace_322853
  have hstable : (prefixWord ++ tailWord_322853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322853).length < 2 ^ (prefixWord ++ tailWord_322853).sum := by decide
  have hdescent : baseEnd_322853 < baseStart_322853 := by decide
  rcases family_descends (prefixWord ++ tailWord_322853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322866 : List Nat := [3, 2, 1, 1, 4, 3, 2, 1, 5]
def baseStart_322866 : Nat := 118140960795 + 322866 * 2 ^ 59
def prefixEnd_322866 : Nat := 4983230072969 + 3 ^ 40 * 322866 * 2
def baseEnd_322866 : Nat := 36841209998808670886705

theorem tailTrace_322866 : CollatzResearch.WordTrace tailWord_322866 prefixEnd_322866 36841209998808670886705 := by
  unfold tailWord_322866
  simp only [CollatzResearch.WordTrace]
  refine ⟨2943972612079774491975113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7850593632212731978600301 2943972612079774491975113)
  ·
    refine ⟨2207979459059830868981335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2943972612079774491975113 2207979459059830868981335)
    ·
      refine ⟨3311969188589746303472003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2207979459059830868981335 3311969188589746303472003)
      ·
        refine ⟨4967953782884619455208005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3311969188589746303472003 4967953782884619455208005)
        ·
          refine ⟨931491334290866147851501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4967953782884619455208005 931491334290866147851501)
          ·
            refine ⟨349309250359074805444313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 931491334290866147851501 349309250359074805444313)
            ·
              refine ⟨261981937769306104083235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 349309250359074805444313 261981937769306104083235)
              ·
                refine ⟨392972906653959156124853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 261981937769306104083235 392972906653959156124853)
                ·
                  refine ⟨36841209998808670886705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 392972906653959156124853 36841209998808670886705)
                  ·
                    rfl

theorem cell22_322866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 2, 1, 5].length) (baseStart_322866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_322866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_322866 prefixEnd_322866 := by exact prefixLift 322866
  have htrace : WordTrace (prefixWord ++ tailWord_322866) baseStart_322866 baseEnd_322866 := by
    simpa [prefixWord, tailWord_322866, baseEnd_322866] using wordTrace_append hprefix tailTrace_322866
  have hstable : (prefixWord ++ tailWord_322866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322866).length < 2 ^ (prefixWord ++ tailWord_322866).sum := by decide
  have hdescent : baseEnd_322866 < baseStart_322866 := by decide
  rcases family_descends (prefixWord ++ tailWord_322866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322879 : List Nat := [1, 1, 2, 2, 4, 2, 3, 2, 1, 4]
def baseStart_322879 : Nat := 118140960795 + 322879 * 2 ^ 59
def prefixEnd_322879 : Nat := 4983230072969 + 3 ^ 40 * 322879 * 2
def baseEnd_322879 : Nat := 110528080162098312085075

theorem tailTrace_322879 : CollatzResearch.WordTrace tailWord_322879 prefixEnd_322879 110528080162098312085075 := by
  unfold tailWord_322879
  simp only [CollatzResearch.WordTrace]
  refine ⟨11776364597272001188123691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7850909731514667458749127 11776364597272001188123691)
  ·
    refine ⟨17664546895908001782185537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11776364597272001188123691 17664546895908001782185537)
    ·
      refine ⟨13248410171931001336639153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17664546895908001782185537 13248410171931001336639153)
      ·
        refine ⟨9936307628948251002479365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13248410171931001336639153 9936307628948251002479365)
        ·
          refine ⟨1863057680427797062964881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9936307628948251002479365 1863057680427797062964881)
          ·
            refine ⟨1397293260320847797223661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1863057680427797062964881 1397293260320847797223661)
            ·
              refine ⟨523984972620317923958873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1397293260320847797223661 523984972620317923958873)
              ·
                refine ⟨392988729465238442969155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 523984972620317923958873 392988729465238442969155)
                ·
                  refine ⟨589483094197857664453733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 392988729465238442969155 589483094197857664453733)
                  ·
                    refine ⟨110528080162098312085075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 589483094197857664453733 110528080162098312085075)
                    ·
                      rfl

theorem cell22_322879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 2, 1, 4].length) (baseStart_322879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_322879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_322879 prefixEnd_322879 := by exact prefixLift 322879
  have htrace : WordTrace (prefixWord ++ tailWord_322879) baseStart_322879 baseEnd_322879 := by
    simpa [prefixWord, tailWord_322879, baseEnd_322879] using wordTrace_append hprefix tailTrace_322879
  have hstable : (prefixWord ++ tailWord_322879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322879).length < 2 ^ (prefixWord ++ tailWord_322879).sum := by decide
  have hdescent : baseEnd_322879 < baseStart_322879 := by decide
  rcases family_descends (prefixWord ++ tailWord_322879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322892 : List Nat := [2, 2, 1, 3, 2, 2, 1, 1, 3, 5]
def baseStart_322892 : Nat := 118140960795 + 322892 * 2 ^ 59
def prefixEnd_322892 : Nat := 4983230072969 + 3 ^ 40 * 322892 * 2
def baseEnd_322892 : Nat := 110532530327770611510035

theorem tailTrace_322892 : CollatzResearch.WordTrace tailWord_322892 prefixEnd_322892 110532530327770611510035 := by
  unfold tailWord_322892
  simp only [CollatzResearch.WordTrace]
  refine ⟨5888419373112452204173465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7851225830816602938897953 5888419373112452204173465)
  ·
    refine ⟨4416314529834339153130099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5888419373112452204173465 4416314529834339153130099)
    ·
      refine ⟨6624471794751508729695149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4416314529834339153130099 6624471794751508729695149)
      ·
        refine ⟨2484176923031815773635681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6624471794751508729695149 2484176923031815773635681)
        ·
          refine ⟨1863132692273861830226761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2484176923031815773635681 1863132692273861830226761)
          ·
            refine ⟨1397349519205396372670071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1863132692273861830226761 1397349519205396372670071)
            ·
              refine ⟨2096024278808094559005107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1397349519205396372670071 2096024278808094559005107)
              ·
                refine ⟨3144036418212141838507661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2096024278808094559005107 3144036418212141838507661)
                ·
                  refine ⟨1179013656829553189440373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3144036418212141838507661 1179013656829553189440373)
                  ·
                    refine ⟨110532530327770611510035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1179013656829553189440373 110532530327770611510035)
                    ·
                      rfl

theorem cell22_322892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 3, 5].length) (baseStart_322892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_322892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_322892 prefixEnd_322892 := by exact prefixLift 322892
  have htrace : WordTrace (prefixWord ++ tailWord_322892) baseStart_322892 baseEnd_322892 := by
    simpa [prefixWord, tailWord_322892, baseEnd_322892] using wordTrace_append hprefix tailTrace_322892
  have hstable : (prefixWord ++ tailWord_322892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322892).length < 2 ^ (prefixWord ++ tailWord_322892).sum := by decide
  have hdescent : baseEnd_322892 < baseStart_322892 := by decide
  rcases family_descends (prefixWord ++ tailWord_322892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
