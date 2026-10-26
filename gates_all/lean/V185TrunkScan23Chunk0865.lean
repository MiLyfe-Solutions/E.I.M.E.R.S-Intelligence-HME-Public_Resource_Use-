import V185TrunkScan23Chunk0864

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5119408 : List Nat := [2, 1, 1, 1, 2, 1, 1, 3, 2, 7, 2]
def baseStart_5119408 : Nat := 118140960795 + 5119408 * 2 ^ 59
def prefixEnd_5119408 : Nat := 4983230072969 + 3 ^ 40 * 5119408 * 2
def baseEnd_5119408 : Nat := 2628716970472611526356277

theorem tailTrace_5119408 : CollatzResearch.WordTrace tailWord_5119408 prefixEnd_5119408 2628716970472611526356277 := by
  unfold tailWord_5119408
  simp only [CollatzResearch.WordTrace]
  refine ⟨93360074718633308061459439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124480099624844410748612585 93360074718633308061459439)
  ·
    refine ⟨140040112077949962092189159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93360074718633308061459439 140040112077949962092189159)
    ·
      refine ⟨210060168116924943138283739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140040112077949962092189159 210060168116924943138283739)
      ·
        refine ⟨315090252175387414707425609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210060168116924943138283739 315090252175387414707425609)
        ·
          refine ⟨236317689131540561030569207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 315090252175387414707425609 236317689131540561030569207)
          ·
            refine ⟨354476533697310841545853811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236317689131540561030569207 354476533697310841545853811)
            ·
              refine ⟨531714800545966262318780717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 354476533697310841545853811 531714800545966262318780717)
              ·
                refine ⟨199393050204737348369542769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 531714800545966262318780717 199393050204737348369542769)
                ·
                  refine ⟨149544787653553011277157077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 199393050204737348369542769 149544787653553011277157077)
                  ·
                    refine ⟨3504955960630148701808369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 149544787653553011277157077 3504955960630148701808369)
                    ·
                      refine ⟨2628716970472611526356277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3504955960630148701808369 2628716970472611526356277)
                      ·
                        rfl

theorem cell23_5119408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 2, 7, 2].length) (baseStart_5119408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5119408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5119408 prefixEnd_5119408 := by exact prefixLift 5119408
  have htrace : WordTrace (prefixWord ++ tailWord_5119408) baseStart_5119408 baseEnd_5119408 := by
    simpa [prefixWord, tailWord_5119408, baseEnd_5119408] using wordTrace_append hprefix tailTrace_5119408
  have hstable : (prefixWord ++ tailWord_5119408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5119408).length < 2 ^ (prefixWord ++ tailWord_5119408).sum := by decide
  have hdescent : baseEnd_5119408 < baseStart_5119408 := by decide
  rcases family_descends (prefixWord ++ tailWord_5119408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5119411 : List Nat := [1, 1, 1, 2, 3, 1, 1, 2, 4, 2, 5]
def baseStart_5119411 : Nat := 118140960795 + 5119411 * 2 ^ 59
def prefixEnd_5119411 : Nat := 4983230072969 + 3 ^ 40 * 5119411 * 2
def baseEnd_5119411 : Nat := 2628718510914575014618763

theorem tailTrace_5119411 : CollatzResearch.WordTrace tailWord_5119411 prefixEnd_5119411 2628718510914575014618763 := by
  unfold tailWord_5119411
  simp only [CollatzResearch.WordTrace]
  refine ⟨186720258856255747635278087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124480172570837165090185391 186720258856255747635278087)
  ·
    refine ⟨280080388284383621452917131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186720258856255747635278087 280080388284383621452917131)
    ·
      refine ⟨420120582426575432179375697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280080388284383621452917131 420120582426575432179375697)
      ·
        refine ⟨315090436819931574134531773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 420120582426575432179375697 315090436819931574134531773)
        ·
          refine ⟨118158913807474340300449415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 315090436819931574134531773 118158913807474340300449415)
          ·
            refine ⟨177238370711211510450674123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118158913807474340300449415 177238370711211510450674123)
            ·
              refine ⟨265857556066817265676011185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177238370711211510450674123 265857556066817265676011185)
              ·
                refine ⟨199393167050112949257008389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 265857556066817265676011185 199393167050112949257008389)
                ·
                  refine ⟨37386218821896177985689073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 199393167050112949257008389 37386218821896177985689073)
                  ·
                    refine ⟨28039664116422133489266805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37386218821896177985689073 28039664116422133489266805)
                    ·
                      refine ⟨2628718510914575014618763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28039664116422133489266805 2628718510914575014618763)
                      ·
                        rfl

theorem cell23_5119411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 2, 5].length) (baseStart_5119411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5119411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5119411 prefixEnd_5119411 := by exact prefixLift 5119411
  have htrace : WordTrace (prefixWord ++ tailWord_5119411) baseStart_5119411 baseEnd_5119411 := by
    simpa [prefixWord, tailWord_5119411, baseEnd_5119411] using wordTrace_append hprefix tailTrace_5119411
  have hstable : (prefixWord ++ tailWord_5119411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5119411).length < 2 ^ (prefixWord ++ tailWord_5119411).sum := by decide
  have hdescent : baseEnd_5119411 < baseStart_5119411 := by decide
  rcases family_descends (prefixWord ++ tailWord_5119411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5119466 : List Nat := [3, 1, 3, 1, 4, 2, 2, 1, 2, 1, 3]
def baseStart_5119466 : Nat := 118140960795 + 5119466 * 2 ^ 59
def prefixEnd_5119466 : Nat := 4983230072969 + 3 ^ 40 * 5119466 * 2
def baseEnd_5119466 : Nat := 2628746752350572299431011

theorem tailTrace_5119466 : CollatzResearch.WordTrace tailWord_5119466 prefixEnd_5119466 2628746752350572299431011 := by
  unfold tailWord_5119466
  simp only [CollatzResearch.WordTrace]
  refine ⟨46680566217764123007132563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124481509914037661352353501 46680566217764123007132563)
  ·
    refine ⟨70020849326646184510698845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46680566217764123007132563 70020849326646184510698845)
    ·
      refine ⟨26257818497492319191512067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70020849326646184510698845 26257818497492319191512067)
      ·
        refine ⟨39386727746238478787268101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26257818497492319191512067 39386727746238478787268101)
        ·
          refine ⟨7385011452419714772612769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39386727746238478787268101 7385011452419714772612769)
          ·
            refine ⟨5538758589314786079459577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7385011452419714772612769 5538758589314786079459577)
            ·
              refine ⟨4154068941986089559594683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5538758589314786079459577 4154068941986089559594683)
              ·
                refine ⟨6231103412979134339392025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4154068941986089559594683 6231103412979134339392025)
                ·
                  refine ⟨4673327559734350754544019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6231103412979134339392025 4673327559734350754544019)
                  ·
                    refine ⟨7009991339601526131816029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4673327559734350754544019 7009991339601526131816029)
                    ·
                      refine ⟨2628746752350572299431011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7009991339601526131816029 2628746752350572299431011)
                      ·
                        rfl

theorem cell23_5119466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 2, 1, 2, 1, 3].length) (baseStart_5119466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5119466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5119466 prefixEnd_5119466 := by exact prefixLift 5119466
  have htrace : WordTrace (prefixWord ++ tailWord_5119466) baseStart_5119466 baseEnd_5119466 := by
    simpa [prefixWord, tailWord_5119466, baseEnd_5119466] using wordTrace_append hprefix tailTrace_5119466
  have hstable : (prefixWord ++ tailWord_5119466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5119466).length < 2 ^ (prefixWord ++ tailWord_5119466).sum := by decide
  have hdescent : baseEnd_5119466 < baseStart_5119466 := by decide
  rcases family_descends (prefixWord ++ tailWord_5119466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5119512 : List Nat := [2, 1, 2, 3, 4, 1, 1, 4, 5]
def baseStart_5119512 : Nat := 118140960795 + 5119512 * 2 ^ 59
def prefixEnd_5119512 : Nat := 4983230072969 + 3 ^ 40 * 5119512 * 2
def baseEnd_5119512 : Nat := 292085596940075457717311

theorem tailTrace_5119512 : CollatzResearch.WordTrace tailWord_5119512 prefixEnd_5119512 292085596940075457717311 := by
  unfold tailWord_5119512
  simp only [CollatzResearch.WordTrace]
  refine ⟨93361971314444920942352395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124482628419259894589803193 93361971314444920942352395)
  ·
    refine ⟨140042956971667381413528593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93361971314444920942352395 140042956971667381413528593)
    ·
      refine ⟨105032217728750536060146445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140042956971667381413528593 105032217728750536060146445)
      ·
        refine ⟨39387081648281451022554917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105032217728750536060146445 39387081648281451022554917)
        ·
          refine ⟨7385077809052772066729047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39387081648281451022554917 7385077809052772066729047)
          ·
            refine ⟨11077616713579158100093571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7385077809052772066729047 11077616713579158100093571)
            ·
              refine ⟨16616425070368737150140357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11077616713579158100093571 16616425070368737150140357)
              ·
                refine ⟨3115579700694138215651317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16616425070368737150140357 3115579700694138215651317)
                ·
                  refine ⟨292085596940075457717311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3115579700694138215651317 292085596940075457717311)
                  ·
                    rfl

theorem cell23_5119512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 4, 5].length) (baseStart_5119512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5119512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5119512 prefixEnd_5119512 := by exact prefixLift 5119512
  have htrace : WordTrace (prefixWord ++ tailWord_5119512) baseStart_5119512 baseEnd_5119512 := by
    simpa [prefixWord, tailWord_5119512, baseEnd_5119512] using wordTrace_append hprefix tailTrace_5119512
  have hstable : (prefixWord ++ tailWord_5119512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5119512).length < 2 ^ (prefixWord ++ tailWord_5119512).sum := by decide
  have hdescent : baseEnd_5119512 < baseStart_5119512 := by decide
  rcases family_descends (prefixWord ++ tailWord_5119512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5119542 : List Nat := [5, 1, 2, 1, 3, 1, 1, 1, 1, 7]
def baseStart_5119542 : Nat := 118140960795 + 5119542 * 2 ^ 59
def prefixEnd_5119542 : Nat := 4983230072969 + 3 ^ 40 * 5119542 * 2
def baseEnd_5119542 : Nat := 876261925626771334026887

theorem tailTrace_5119542 : CollatzResearch.WordTrace tailWord_5119542 prefixEnd_5119542 876261925626771334026887 := by
  unfold tailWord_5119542
  simp only [CollatzResearch.WordTrace]
  refine ⟨11670314801173822313018555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 124483357879187438005531253 11670314801173822313018555)
  ·
    refine ⟨17505472201760733469527833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11670314801173822313018555 17505472201760733469527833)
    ·
      refine ⟨13129104151320550102145875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17505472201760733469527833 13129104151320550102145875)
      ·
        refine ⟨19693656226980825153218813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13129104151320550102145875 19693656226980825153218813)
        ·
          refine ⟨7385121085117809432457055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19693656226980825153218813 7385121085117809432457055)
          ·
            refine ⟨11077681627676714148685583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7385121085117809432457055 11077681627676714148685583)
            ·
              refine ⟨16616522441515071223028375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11077681627676714148685583 16616522441515071223028375)
              ·
                refine ⟨24924783662272606834542563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16616522441515071223028375 24924783662272606834542563)
                ·
                  refine ⟨37387175493408910251813845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24924783662272606834542563 37387175493408910251813845)
                  ·
                    refine ⟨876261925626771334026887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37387175493408910251813845 876261925626771334026887)
                    ·
                      rfl

theorem cell23_5119542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_5119542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5119542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5119542 prefixEnd_5119542 := by exact prefixLift 5119542
  have htrace : WordTrace (prefixWord ++ tailWord_5119542) baseStart_5119542 baseEnd_5119542 := by
    simpa [prefixWord, tailWord_5119542, baseEnd_5119542] using wordTrace_append hprefix tailTrace_5119542
  have hstable : (prefixWord ++ tailWord_5119542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5119542).length < 2 ^ (prefixWord ++ tailWord_5119542).sum := by decide
  have hdescent : baseEnd_5119542 < baseStart_5119542 := by decide
  rcases family_descends (prefixWord ++ tailWord_5119542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5119545 : List Nat := [1, 2, 1, 5, 1, 3, 1, 1, 1, 3, 4]
def baseStart_5119545 : Nat := 118140960795 + 5119545 * 2 ^ 59
def prefixEnd_5119545 : Nat := 4983230072969 + 3 ^ 40 * 5119545 * 2
def baseEnd_5119545 : Nat := 2628787317322277490343147

theorem tailTrace_5119545 : CollatzResearch.WordTrace tailWord_5119545 prefixEnd_5119545 2628787317322277490343147 := by
  unfold tailWord_5119545
  simp only [CollatzResearch.WordTrace]
  refine ⟨186725146237770288520656089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124483430825180192347104059 186725146237770288520656089)
  ·
    refine ⟨140043859678327716390492067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186725146237770288520656089 140043859678327716390492067)
    ·
      refine ⟨210065789517491574585738101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140043859678327716390492067 210065789517491574585738101)
      ·
        refine ⟨19693667767264835117412947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 210065789517491574585738101 19693667767264835117412947)
        ·
          refine ⟨29540501650897252676119421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19693667767264835117412947 29540501650897252676119421)
          ·
            refine ⟨11077688119086469753544783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29540501650897252676119421 11077688119086469753544783)
            ·
              refine ⟨16616532178629704630317175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11077688119086469753544783 16616532178629704630317175)
              ·
                refine ⟨24924798267944556945475763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16616532178629704630317175 24924798267944556945475763)
                ·
                  refine ⟨37387197401916835418213645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24924798267944556945475763 37387197401916835418213645)
                  ·
                    refine ⟨14020199025718813281830117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37387197401916835418213645 14020199025718813281830117)
                    ·
                      refine ⟨2628787317322277490343147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14020199025718813281830117 2628787317322277490343147)
                      ·
                        rfl

theorem cell23_5119545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_5119545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5119545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5119545 prefixEnd_5119545 := by exact prefixLift 5119545
  have htrace : WordTrace (prefixWord ++ tailWord_5119545) baseStart_5119545 baseEnd_5119545 := by
    simpa [prefixWord, tailWord_5119545, baseEnd_5119545] using wordTrace_append hprefix tailTrace_5119545
  have hstable : (prefixWord ++ tailWord_5119545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5119545).length < 2 ^ (prefixWord ++ tailWord_5119545).sum := by decide
  have hdescent : baseEnd_5119545 < baseStart_5119545 := by decide
  rcases family_descends (prefixWord ++ tailWord_5119545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5119568 : List Nat := [2, 1, 1, 1, 1, 3, 5, 1, 8]
def baseStart_5119568 : Nat := 118140960795 + 5119568 * 2 ^ 59
def prefixEnd_5119568 : Nat := 4983230072969 + 3 ^ 40 * 5119568 * 2
def baseEnd_5119568 : Nat := 292088791930814544483949

theorem tailTrace_5119568 : CollatzResearch.WordTrace tailWord_5119568 prefixEnd_5119568 292088791930814544483949 := by
  unfold tailWord_5119568
  simp only [CollatzResearch.WordTrace]
  refine ⟨93362992558343481724371679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124483990077791308965828905 93362992558343481724371679)
  ·
    refine ⟨140044488837515222586557519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93362992558343481724371679 140044488837515222586557519)
    ·
      refine ⟨210066733256272833879836279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140044488837515222586557519 210066733256272833879836279)
      ·
        refine ⟨315100099884409250819754419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210066733256272833879836279 315100099884409250819754419)
        ·
          refine ⟨472650149826613876229631629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315100099884409250819754419 472650149826613876229631629)
          ·
            refine ⟨177243806184980203586111861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 472650149826613876229631629 177243806184980203586111861)
            ·
              refine ⟨16616606829841894086197987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 177243806184980203586111861 16616606829841894086197987)
              ·
                refine ⟨24924910244762841129296981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16616606829841894086197987 24924910244762841129296981)
                ·
                  refine ⟨292088791930814544483949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24924910244762841129296981 292088791930814544483949)
                  ·
                    rfl

theorem cell23_5119568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 8].length) (baseStart_5119568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5119568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5119568 prefixEnd_5119568 := by exact prefixLift 5119568
  have htrace : WordTrace (prefixWord ++ tailWord_5119568) baseStart_5119568 baseEnd_5119568 := by
    simpa [prefixWord, tailWord_5119568, baseEnd_5119568] using wordTrace_append hprefix tailTrace_5119568
  have hstable : (prefixWord ++ tailWord_5119568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5119568).length < 2 ^ (prefixWord ++ tailWord_5119568).sum := by decide
  have hdescent : baseEnd_5119568 < baseStart_5119568 := by decide
  rcases family_descends (prefixWord ++ tailWord_5119568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5119572 : List Nat := [2, 4, 1, 1, 1, 2, 4, 1, 3, 4]
def baseStart_5119572 : Nat := 118140960795 + 5119572 * 2 ^ 59
def prefixEnd_5119572 : Nat := 4983230072969 + 3 ^ 40 * 5119572 * 2
def baseEnd_5119572 : Nat := 876267060433316294901841

theorem tailTrace_5119572 : CollatzResearch.WordTrace tailWord_5119572 prefixEnd_5119572 876267060433316294901841 := by
  unfold tailWord_5119572
  simp only [CollatzResearch.WordTrace]
  refine ⟨93363065504336236065944485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124484087339114981421259313 93363065504336236065944485)
  ·
    refine ⟨17505574782063044262364591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93363065504336236065944485 17505574782063044262364591)
    ·
      refine ⟨26258362173094566393546887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17505574782063044262364591 26258362173094566393546887)
      ·
        refine ⟨39387543259641849590320331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26258362173094566393546887 39387543259641849590320331)
        ·
          refine ⟨59081314889462774385480497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39387543259641849590320331 59081314889462774385480497)
          ·
            refine ⟨44310986167097080789110373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59081314889462774385480497 44310986167097080789110373)
            ·
              refine ⟨8308309906330702647958195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44310986167097080789110373 8308309906330702647958195)
              ·
                refine ⟨12462464859496053971937293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8308309906330702647958195 12462464859496053971937293)
                ·
                  refine ⟨4673424322311020239476485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12462464859496053971937293 4673424322311020239476485)
                  ·
                    refine ⟨876267060433316294901841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4673424322311020239476485 876267060433316294901841)
                    ·
                      rfl

theorem cell23_5119572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 1, 3, 4].length) (baseStart_5119572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5119572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5119572 prefixEnd_5119572 := by exact prefixLift 5119572
  have htrace : WordTrace (prefixWord ++ tailWord_5119572) baseStart_5119572 baseEnd_5119572 := by
    simpa [prefixWord, tailWord_5119572, baseEnd_5119572] using wordTrace_append hprefix tailTrace_5119572
  have hstable : (prefixWord ++ tailWord_5119572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5119572).length < 2 ^ (prefixWord ++ tailWord_5119572).sum := by decide
  have hdescent : baseEnd_5119572 < baseStart_5119572 := by decide
  rcases family_descends (prefixWord ++ tailWord_5119572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5119606 : List Nat := [5, 1, 1, 2, 2, 1, 3, 3, 1, 4]
def baseStart_5119606 : Nat := 118140960795 + 5119606 * 2 ^ 59
def prefixEnd_5119606 : Nat := 4983230072969 + 3 ^ 40 * 5119606 * 2
def baseEnd_5119606 : Nat := 876272879880733917226789

theorem tailTrace_5119606 : CollatzResearch.WordTrace tailWord_5119606 prefixEnd_5119606 876272879880733917226789 := by
  unfold tailWord_5119606
  simp only [CollatzResearch.WordTrace]
  refine ⟨11670460693159330996164167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 124484914060366197292417781 11670460693159330996164167)
  ·
    refine ⟨17505691039738996494246251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11670460693159330996164167 17505691039738996494246251)
    ·
      refine ⟨26258536559608494741369377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17505691039738996494246251 26258536559608494741369377)
      ·
        refine ⟨19693902419706371056027033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26258536559608494741369377 19693902419706371056027033)
        ·
          refine ⟨14770426814779778292020275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19693902419706371056027033 14770426814779778292020275)
          ·
            refine ⟨22155640222169667438030413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14770426814779778292020275 22155640222169667438030413)
            ·
              refine ⟨8308365083313625289261405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22155640222169667438030413 8308365083313625289261405)
              ·
                refine ⟨3115636906242609483473027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8308365083313625289261405 3115636906242609483473027)
                ·
                  refine ⟨4673455359363914225209541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3115636906242609483473027 4673455359363914225209541)
                  ·
                    refine ⟨876272879880733917226789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4673455359363914225209541 876272879880733917226789)
                    ·
                      rfl

theorem cell23_5119606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 3, 1, 4].length) (baseStart_5119606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5119606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5119606 prefixEnd_5119606 := by exact prefixLift 5119606
  have htrace : WordTrace (prefixWord ++ tailWord_5119606) baseStart_5119606 baseEnd_5119606 := by
    simpa [prefixWord, tailWord_5119606, baseEnd_5119606] using wordTrace_append hprefix tailTrace_5119606
  have hstable : (prefixWord ++ tailWord_5119606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5119606).length < 2 ^ (prefixWord ++ tailWord_5119606).sum := by decide
  have hdescent : baseEnd_5119606 < baseStart_5119606 := by decide
  rcases family_descends (prefixWord ++ tailWord_5119606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5119608 : List Nat := [2, 1, 2, 1, 1, 1, 2, 1, 1, 6, 5]
def baseStart_5119608 : Nat := 118140960795 + 5119608 * 2 ^ 59
def prefixEnd_5119608 : Nat := 4983230072969 + 3 ^ 40 * 5119608 * 2
def baseEnd_5119608 : Nat := 2628819666603510743855357

theorem tailTrace_5119608 : CollatzResearch.WordTrace tailWord_5119608 prefixEnd_5119608 2628819666603510743855357 := by
  unfold tailWord_5119608
  simp only [CollatzResearch.WordTrace]
  refine ⟨93363722018271025140099739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124484962691028033520132985 93363722018271025140099739)
  ·
    refine ⟨140045583027406537710149609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93363722018271025140099739 140045583027406537710149609)
    ·
      refine ⟨105034187270554903282612207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140045583027406537710149609 105034187270554903282612207)
      ·
        refine ⟨157551280905832354923918311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105034187270554903282612207 157551280905832354923918311)
        ·
          refine ⟨236326921358748532385877467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157551280905832354923918311 236326921358748532385877467)
          ·
            refine ⟨354490382038122798578816201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236326921358748532385877467 354490382038122798578816201)
            ·
              refine ⟨265867786528592098934112151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 354490382038122798578816201 265867786528592098934112151)
              ·
                refine ⟨398801679792888148401168227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 265867786528592098934112151 398801679792888148401168227)
                ·
                  refine ⟨598202519689332222601752341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 398801679792888148401168227 598202519689332222601752341)
                  ·
                    refine ⟨28040743110437447934457141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 598202519689332222601752341 28040743110437447934457141)
                    ·
                      refine ⟨2628819666603510743855357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28040743110437447934457141 2628819666603510743855357)
                      ·
                        rfl

theorem cell23_5119608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 1, 6, 5].length) (baseStart_5119608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5119608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5119608 prefixEnd_5119608 := by exact prefixLift 5119608
  have htrace : WordTrace (prefixWord ++ tailWord_5119608) baseStart_5119608 baseEnd_5119608 := by
    simpa [prefixWord, tailWord_5119608, baseEnd_5119608] using wordTrace_append hprefix tailTrace_5119608
  have hstable : (prefixWord ++ tailWord_5119608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5119608).length < 2 ^ (prefixWord ++ tailWord_5119608).sum := by decide
  have hdescent : baseEnd_5119608 < baseStart_5119608 := by decide
  rcases family_descends (prefixWord ++ tailWord_5119608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5119636 : List Nat := [2, 4, 2, 2, 2, 2, 2, 1, 6]
def baseStart_5119636 : Nat := 118140960795 + 5119636 * 2 ^ 59
def prefixEnd_5119636 : Nat := 4983230072969 + 3 ^ 40 * 5119636 * 2
def baseEnd_5119636 : Nat := 292092671562426292700581

theorem tailTrace_5119636 : CollatzResearch.WordTrace tailWord_5119636 prefixEnd_5119636 292092671562426292700581 := by
  unfold tailWord_5119636
  simp only [CollatzResearch.WordTrace]
  refine ⟨93364232640220305531109381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124485643520293740708145841 93364232640220305531109381)
  ·
    refine ⟨17505793620041307287083009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93364232640220305531109381 17505793620041307287083009)
    ·
      refine ⟨13129345215030980465312257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17505793620041307287083009 13129345215030980465312257)
      ·
        refine ⟨9847008911273235348984193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13129345215030980465312257 9847008911273235348984193)
        ·
          refine ⟨7385256683454926511738145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9847008911273235348984193 7385256683454926511738145)
          ·
            refine ⟨5538942512591194883803609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7385256683454926511738145 5538942512591194883803609)
            ·
              refine ⟨4154206884443396162852707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5538942512591194883803609 4154206884443396162852707)
              ·
                refine ⟨6231310326665094244279061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4154206884443396162852707 6231310326665094244279061)
                ·
                  refine ⟨292092671562426292700581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6231310326665094244279061 292092671562426292700581)
                  ·
                    rfl

theorem cell23_5119636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 2, 1, 6].length) (baseStart_5119636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5119636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5119636 prefixEnd_5119636 := by exact prefixLift 5119636
  have htrace : WordTrace (prefixWord ++ tailWord_5119636) baseStart_5119636 baseEnd_5119636 := by
    simpa [prefixWord, tailWord_5119636, baseEnd_5119636] using wordTrace_append hprefix tailTrace_5119636
  have hstable : (prefixWord ++ tailWord_5119636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5119636).length < 2 ^ (prefixWord ++ tailWord_5119636).sum := by decide
  have hdescent : baseEnd_5119636 < baseStart_5119636 := by decide
  rcases family_descends (prefixWord ++ tailWord_5119636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5119645 : List Nat := [1, 4, 2, 1, 1, 1, 1, 5, 1, 6]
def baseStart_5119645 : Nat := 118140960795 + 5119645 * 2 ^ 59
def prefixEnd_5119645 : Nat := 4983230072969 + 3 ^ 40 * 5119645 * 2
def baseEnd_5119645 : Nat := 876279555129242366364229

theorem tailTrace_5119645 : CollatzResearch.WordTrace tailWord_5119645 prefixEnd_5119645 876279555129242366364229 := by
  unfold tailWord_5119645
  simp only [CollatzResearch.WordTrace]
  refine ⟨186728793537408005599296389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124485862358272003732864259 186728793537408005599296389)
  ·
    refine ⟨35011648788264001049868073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 186728793537408005599296389 35011648788264001049868073)
    ·
      refine ⟨26258736591198000787401055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35011648788264001049868073 26258736591198000787401055)
      ·
        refine ⟨39388104886797001181101583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26258736591198000787401055 39388104886797001181101583)
        ·
          refine ⟨59082157330195501771652375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39388104886797001181101583 59082157330195501771652375)
          ·
            refine ⟨88623235995293252657478563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59082157330195501771652375 88623235995293252657478563)
            ·
              refine ⟨132934853992939878986217845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88623235995293252657478563 132934853992939878986217845)
              ·
                refine ⟨12462642561838113654957923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 132934853992939878986217845 12462642561838113654957923)
                ·
                  refine ⟨18693963842757170482436885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12462642561838113654957923 18693963842757170482436885)
                  ·
                    refine ⟨876279555129242366364229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18693963842757170482436885 876279555129242366364229)
                    ·
                      rfl

theorem cell23_5119645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 5, 1, 6].length) (baseStart_5119645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5119645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5119645 prefixEnd_5119645 := by exact prefixLift 5119645
  have htrace : WordTrace (prefixWord ++ tailWord_5119645) baseStart_5119645 baseEnd_5119645 := by
    simpa [prefixWord, tailWord_5119645, baseEnd_5119645] using wordTrace_append hprefix tailTrace_5119645
  have hstable : (prefixWord ++ tailWord_5119645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5119645).length < 2 ^ (prefixWord ++ tailWord_5119645).sum := by decide
  have hdescent : baseEnd_5119645 < baseStart_5119645 := by decide
  rcases family_descends (prefixWord ++ tailWord_5119645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5119649 : List Nat := [1, 2, 3, 3, 2, 3, 1, 2, 1, 5]
def baseStart_5119649 : Nat := 118140960795 + 5119649 * 2 ^ 59
def prefixEnd_5119649 : Nat := 4983230072969 + 3 ^ 40 * 5119649 * 2
def baseEnd_5119649 : Nat := 876280239770115027814223

theorem tailTrace_5119649 : CollatzResearch.WordTrace tailWord_5119649 prefixEnd_5119649 876280239770115027814223 := by
  unfold tailWord_5119649
  simp only [CollatzResearch.WordTrace]
  refine ⟨186728939429393514282442001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124485959619595676188294667 186728939429393514282442001)
  ·
    refine ⟨140046704572045135711831501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186728939429393514282442001 140046704572045135711831501)
    ·
      refine ⟨52517514214516925891936813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140046704572045135711831501 52517514214516925891936813)
      ·
        refine ⟨19694067830443847209476305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52517514214516925891936813 19694067830443847209476305)
        ·
          refine ⟨14770550872832885407107229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19694067830443847209476305 14770550872832885407107229)
          ·
            refine ⟨5538956577312332027665211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14770550872832885407107229 5538956577312332027665211)
            ·
              refine ⟨8308434865968498041497817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5538956577312332027665211 8308434865968498041497817)
              ·
                refine ⟨6231326149476373531123363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8308434865968498041497817 6231326149476373531123363)
                ·
                  refine ⟨9346989224214560296685045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6231326149476373531123363 9346989224214560296685045)
                  ·
                    refine ⟨876280239770115027814223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9346989224214560296685045 876280239770115027814223)
                    ·
                      rfl

theorem cell23_5119649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 2, 1, 5].length) (baseStart_5119649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5119649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5119649 prefixEnd_5119649 := by exact prefixLift 5119649
  have htrace : WordTrace (prefixWord ++ tailWord_5119649) baseStart_5119649 baseEnd_5119649 := by
    simpa [prefixWord, tailWord_5119649, baseEnd_5119649] using wordTrace_append hprefix tailTrace_5119649
  have hstable : (prefixWord ++ tailWord_5119649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5119649).length < 2 ^ (prefixWord ++ tailWord_5119649).sum := by decide
  have hdescent : baseEnd_5119649 < baseStart_5119649 := by decide
  rcases family_descends (prefixWord ++ tailWord_5119649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5119652 : List Nat := [2, 3, 1, 2, 2, 3, 1, 1, 3, 1, 4]
def baseStart_5119652 : Nat := 118140960795 + 5119652 * 2 ^ 59
def prefixEnd_5119652 : Nat := 4983230072969 + 3 ^ 40 * 5119652 * 2
def baseEnd_5119652 : Nat := 2628842259752308571705155

theorem tailTrace_5119652 : CollatzResearch.WordTrace tailWord_5119652 prefixEnd_5119652 2628842259752308571705155 := by
  unfold tailWord_5119652
  simp only [CollatzResearch.WordTrace]
  refine ⟨93364524424191322897400605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124486032565588430529867473 93364524424191322897400605)
  ·
    refine ⟨35011696659071746086525227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93364524424191322897400605 35011696659071746086525227)
    ·
      refine ⟨52517544988607619129787841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35011696659071746086525227 52517544988607619129787841)
      ·
        refine ⟨39388158741455714347340881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52517544988607619129787841 39388158741455714347340881)
        ·
          refine ⟨29541119056091785760505661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39388158741455714347340881 29541119056091785760505661)
          ·
            refine ⟨11077919646034419660189623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29541119056091785760505661 11077919646034419660189623)
            ·
              refine ⟨16616879469051629490284435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11077919646034419660189623 16616879469051629490284435)
              ·
                refine ⟨24925319203577444235426653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16616879469051629490284435 24925319203577444235426653)
                ·
                  refine ⟨9346994701341541588284995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24925319203577444235426653 9346994701341541588284995)
                  ·
                    refine ⟨14020492052012312382427493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9346994701341541588284995 14020492052012312382427493)
                    ·
                      refine ⟨2628842259752308571705155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14020492052012312382427493 2628842259752308571705155)
                      ·
                        rfl

theorem cell23_5119652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_5119652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5119652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5119652 prefixEnd_5119652 := by exact prefixLift 5119652
  have htrace : WordTrace (prefixWord ++ tailWord_5119652) baseStart_5119652 baseEnd_5119652 := by
    simpa [prefixWord, tailWord_5119652, baseEnd_5119652] using wordTrace_append hprefix tailTrace_5119652
  have hstable : (prefixWord ++ tailWord_5119652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5119652).length < 2 ^ (prefixWord ++ tailWord_5119652).sum := by decide
  have hdescent : baseEnd_5119652 < baseStart_5119652 := by decide
  rcases family_descends (prefixWord ++ tailWord_5119652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5119672 : List Nat := [2, 1, 2, 1, 2, 1, 1, 7, 1, 2, 3]
def baseStart_5119672 : Nat := 118140960795 + 5119672 * 2 ^ 59
def prefixEnd_5119672 : Nat := 4983230072969 + 3 ^ 40 * 5119672 * 2
def baseEnd_5119672 : Nat := 2628852529365398493455063

theorem tailTrace_5119672 : CollatzResearch.WordTrace tailWord_5119672 prefixEnd_5119672 2628852529365398493455063 := by
  unfold tailWord_5119672
  simp only [CollatzResearch.WordTrace]
  refine ⟨93364889154155094605264635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124486518872206792807019513 93364889154155094605264635)
  ·
    refine ⟨140047333731232641907896953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93364889154155094605264635 140047333731232641907896953)
    ·
      refine ⟨105035500298424481430922715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140047333731232641907896953 105035500298424481430922715)
      ·
        refine ⟨157553250447636722146384073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105035500298424481430922715 157553250447636722146384073)
        ·
          refine ⟨118164937835727541609788055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157553250447636722146384073 118164937835727541609788055)
          ·
            refine ⟨177247406753591312414682083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118164937835727541609788055 177247406753591312414682083)
            ·
              refine ⟨265871110130386968622023125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177247406753591312414682083 265871110130386968622023125)
              ·
                refine ⟨6231354143680944577078667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 265871110130386968622023125 6231354143680944577078667)
                ·
                  refine ⟨9347031215521416865618001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6231354143680944577078667 9347031215521416865618001)
                  ·
                    refine ⟨7010273411641062649213501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9347031215521416865618001 7010273411641062649213501)
                    ·
                      refine ⟨2628852529365398493455063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7010273411641062649213501 2628852529365398493455063)
                      ·
                        rfl

theorem cell23_5119672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 7, 1, 2, 3].length) (baseStart_5119672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5119672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5119672 prefixEnd_5119672 := by exact prefixLift 5119672
  have htrace : WordTrace (prefixWord ++ tailWord_5119672) baseStart_5119672 baseEnd_5119672 := by
    simpa [prefixWord, tailWord_5119672, baseEnd_5119672] using wordTrace_append hprefix tailTrace_5119672
  have hstable : (prefixWord ++ tailWord_5119672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5119672).length < 2 ^ (prefixWord ++ tailWord_5119672).sum := by decide
  have hdescent : baseEnd_5119672 < baseStart_5119672 := by decide
  rcases family_descends (prefixWord ++ tailWord_5119672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5119686 : List Nat := [6, 1, 2, 1, 1, 1, 1, 2, 3, 1, 4]
def baseStart_5119686 : Nat := 118140960795 + 5119686 * 2 ^ 59
def prefixEnd_5119686 : Nat := 4983230072969 + 3 ^ 40 * 5119686 * 2
def baseEnd_5119686 : Nat := 2628859718094561438679999

theorem tailTrace_5119686 : CollatzResearch.WordTrace tailWord_5119686 prefixEnd_5119686 2628859718094561438679999 := by
  unfold tailWord_5119686
  simp only [CollatzResearch.WordTrace]
  refine ⟨5835321529070608425048091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 124486859286839646401025941 5835321529070608425048091)
  ·
    refine ⟨8752982293605912637572137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5835321529070608425048091 8752982293605912637572137)
    ·
      refine ⟨6564736720204434478179103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8752982293605912637572137 6564736720204434478179103)
      ·
        refine ⟨9847105080306651717268655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6564736720204434478179103 9847105080306651717268655)
        ·
          refine ⟨14770657620459977575902983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9847105080306651717268655 14770657620459977575902983)
          ·
            refine ⟨22155986430689966363854475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14770657620459977575902983 22155986430689966363854475)
            ·
              refine ⟨33233979646034949545781713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22155986430689966363854475 33233979646034949545781713)
              ·
                refine ⟨24925484734526212159336285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33233979646034949545781713 24925484734526212159336285)
                ·
                  refine ⟨9347056775447329559751107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24925484734526212159336285 9347056775447329559751107)
                  ·
                    refine ⟨14020585163170994339626661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9347056775447329559751107 14020585163170994339626661)
                    ·
                      refine ⟨2628859718094561438679999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14020585163170994339626661 2628859718094561438679999)
                      ·
                        rfl

theorem cell23_5119686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_5119686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5119686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5119686 prefixEnd_5119686 := by exact prefixLift 5119686
  have htrace : WordTrace (prefixWord ++ tailWord_5119686) baseStart_5119686 baseEnd_5119686 := by
    simpa [prefixWord, tailWord_5119686, baseEnd_5119686] using wordTrace_append hprefix tailTrace_5119686
  have hstable : (prefixWord ++ tailWord_5119686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5119686).length < 2 ^ (prefixWord ++ tailWord_5119686).sum := by decide
  have hdescent : baseEnd_5119686 < baseStart_5119686 := by decide
  rcases family_descends (prefixWord ++ tailWord_5119686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5119735 : List Nat := [1, 1, 3, 1, 1, 1, 5, 2, 2, 6]
def baseStart_5119735 : Nat := 118140960795 + 5119735 * 2 ^ 59
def prefixEnd_5119735 : Nat := 4983230072969 + 3 ^ 40 * 5119735 * 2
def baseEnd_5119735 : Nat := 876294959548877248989091

theorem tailTrace_5119735 : CollatzResearch.WordTrace tailWord_5119735 prefixEnd_5119735 876294959548877248989091 := by
  unfold tailWord_5119735
  simp only [CollatzResearch.WordTrace]
  refine ⟨186732076107081950970072659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124488050738054633980048439 186732076107081950970072659)
  ·
    refine ⟨280098114160622926455108989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186732076107081950970072659 280098114160622926455108989)
    ·
      refine ⟨105036792810233597420665871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 280098114160622926455108989 105036792810233597420665871)
      ·
        refine ⟨157555189215350396130998807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105036792810233597420665871 157555189215350396130998807)
        ·
          refine ⟨236332783823025594196498211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157555189215350396130998807 236332783823025594196498211)
          ·
            refine ⟨354499175734538391294747317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236332783823025594196498211 354499175734538391294747317)
            ·
              refine ⟨33234297725112974183882561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 354499175734538391294747317 33234297725112974183882561)
              ·
                refine ⟨24925723293834730637911921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33234297725112974183882561 24925723293834730637911921)
                ·
                  refine ⟨18694292470376047978433941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24925723293834730637911921 18694292470376047978433941)
                  ·
                    refine ⟨876294959548877248989091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18694292470376047978433941 876294959548877248989091)
                    ·
                      rfl

theorem cell23_5119735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 2, 6].length) (baseStart_5119735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5119735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5119735 prefixEnd_5119735 := by exact prefixLift 5119735
  have htrace : WordTrace (prefixWord ++ tailWord_5119735) baseStart_5119735 baseEnd_5119735 := by
    simpa [prefixWord, tailWord_5119735, baseEnd_5119735] using wordTrace_append hprefix tailTrace_5119735
  have hstable : (prefixWord ++ tailWord_5119735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5119735).length < 2 ^ (prefixWord ++ tailWord_5119735).sum := by decide
  have hdescent : baseEnd_5119735 < baseStart_5119735 := by decide
  rcases family_descends (prefixWord ++ tailWord_5119735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5119750 : List Nat := [6, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6]
def baseStart_5119750 : Nat := 118140960795 + 5119750 * 2 ^ 59
def prefixEnd_5119750 : Nat := 4983230072969 + 3 ^ 40 * 5119750 * 2
def baseEnd_5119750 : Nat := 2628892580856449188279705

theorem tailTrace_5119750 : CollatzResearch.WordTrace tailWord_5119750 prefixEnd_5119750 2628892580856449188279705 := by
  unfold tailWord_5119750
  simp only [CollatzResearch.WordTrace]
  refine ⟨5835394475063362766620897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 124488415468018405687912469 5835394475063362766620897)
  ·
    refine ⟨4376545856297522074965673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5835394475063362766620897 4376545856297522074965673)
    ·
      refine ⟨3282409392223141556224255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4376545856297522074965673 3282409392223141556224255)
      ·
        refine ⟨4923614088334712334336383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3282409392223141556224255 4923614088334712334336383)
        ·
          refine ⟨7385421132502068501504575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4923614088334712334336383 7385421132502068501504575)
          ·
            refine ⟨11078131698753102752256863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7385421132502068501504575 11078131698753102752256863)
            ·
              refine ⟨16617197548129654128385295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11078131698753102752256863 16617197548129654128385295)
              ·
                refine ⟨24925796322194481192577943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16617197548129654128385295 24925796322194481192577943)
                ·
                  refine ⟨37388694483291721788866915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24925796322194481192577943 37388694483291721788866915)
                  ·
                    refine ⟨56083041724937582683300373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37388694483291721788866915 56083041724937582683300373)
                    ·
                      refine ⟨2628892580856449188279705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56083041724937582683300373 2628892580856449188279705)
                      ·
                        rfl

theorem cell23_5119750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_5119750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5119750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5119750 prefixEnd_5119750 := by exact prefixLift 5119750
  have htrace : WordTrace (prefixWord ++ tailWord_5119750) baseStart_5119750 baseEnd_5119750 := by
    simpa [prefixWord, tailWord_5119750, baseEnd_5119750] using wordTrace_append hprefix tailTrace_5119750
  have hstable : (prefixWord ++ tailWord_5119750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5119750).length < 2 ^ (prefixWord ++ tailWord_5119750).sum := by decide
  have hdescent : baseEnd_5119750 < baseStart_5119750 := by decide
  rcases family_descends (prefixWord ++ tailWord_5119750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5119757 : List Nat := [1, 7, 2, 1, 1, 1, 2, 2, 1, 2, 3]
def baseStart_5119757 : Nat := 118140960795 + 5119757 * 2 ^ 59
def prefixEnd_5119757 : Nat := 4983230072969 + 3 ^ 40 * 5119757 * 2
def baseEnd_5119757 : Nat := 2628896175221030660892173

theorem tailTrace_5119757 : CollatzResearch.WordTrace tailWord_5119757 prefixEnd_5119757 2628896175221030660892173 := by
  unfold tailWord_5119757
  simp only [CollatzResearch.WordTrace]
  refine ⟨186732878513002248727373525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124488585675334832484915683 186732878513002248727373525)
  ·
    refine ⟨4376551840148490204547817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 186732878513002248727373525 4376551840148490204547817)
    ·
      refine ⟨3282413880111367653410863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4376551840148490204547817 3282413880111367653410863)
      ·
        refine ⟨4923620820167051480116295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3282413880111367653410863 4923620820167051480116295)
        ·
          refine ⟨7385431230250577220174443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4923620820167051480116295 7385431230250577220174443)
          ·
            refine ⟨11078146845375865830261665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7385431230250577220174443 11078146845375865830261665)
            ·
              refine ⟨8308610134031899372696249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11078146845375865830261665 8308610134031899372696249)
              ·
                refine ⟨6231457600523924529522187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8308610134031899372696249 6231457600523924529522187)
                ·
                  refine ⟨9347186400785886794283281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6231457600523924529522187 9347186400785886794283281)
                  ·
                    refine ⟨7010389800589415095712461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9347186400785886794283281 7010389800589415095712461)
                    ·
                      refine ⟨2628896175221030660892173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7010389800589415095712461 2628896175221030660892173)
                      ·
                        rfl

theorem cell23_5119757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_5119757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5119757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5119757 prefixEnd_5119757 := by exact prefixLift 5119757
  have htrace : WordTrace (prefixWord ++ tailWord_5119757) baseStart_5119757 baseEnd_5119757 := by
    simpa [prefixWord, tailWord_5119757, baseEnd_5119757] using wordTrace_append hprefix tailTrace_5119757
  have hstable : (prefixWord ++ tailWord_5119757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5119757).length < 2 ^ (prefixWord ++ tailWord_5119757).sum := by decide
  have hdescent : baseEnd_5119757 < baseStart_5119757 := by decide
  rcases family_descends (prefixWord ++ tailWord_5119757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5119829 : List Nat := [1, 3, 2, 2, 2, 3, 2, 1, 2, 5]
def baseStart_5119829 : Nat := 118140960795 + 5119829 * 2 ^ 59
def prefixEnd_5119829 : Nat := 4983230072969 + 3 ^ 40 * 5119829 * 2
def baseEnd_5119829 : Nat := 876311048609384793063947

theorem tailTrace_5119829 : CollatzResearch.WordTrace tailWord_5119829 prefixEnd_5119829 876311048609384793063947 := by
  unfold tailWord_5119829
  simp only [CollatzResearch.WordTrace]
  refine ⟨186735504568741405023994541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124490336379160936682663027 186735504568741405023994541)
  ·
    refine ⟨70025814213278026883997953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186735504568741405023994541 70025814213278026883997953)
    ·
      refine ⟨52519360659958520162998465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70025814213278026883997953 52519360659958520162998465)
      ·
        refine ⟨39389520494968890122248849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52519360659958520162998465 39389520494968890122248849)
        ·
          refine ⟨29542140371226667591686637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39389520494968890122248849 29542140371226667591686637)
          ·
            refine ⟨11078302639210000346882489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29542140371226667591686637 11078302639210000346882489)
            ·
              refine ⟨8308726979407500260161867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11078302639210000346882489 8308726979407500260161867)
              ·
                refine ⟨12463090469111250390242801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8308726979407500260161867 12463090469111250390242801)
                ·
                  refine ⟨9347317851833437792682101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12463090469111250390242801 9347317851833437792682101)
                  ·
                    refine ⟨876311048609384793063947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9347317851833437792682101 876311048609384793063947)
                    ·
                      rfl

theorem cell23_5119829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 1, 2, 5].length) (baseStart_5119829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5119829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5119829 prefixEnd_5119829 := by exact prefixLift 5119829
  have htrace : WordTrace (prefixWord ++ tailWord_5119829) baseStart_5119829 baseEnd_5119829 := by
    simpa [prefixWord, tailWord_5119829, baseEnd_5119829] using wordTrace_append hprefix tailTrace_5119829
  have hstable : (prefixWord ++ tailWord_5119829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5119829).length < 2 ^ (prefixWord ++ tailWord_5119829).sum := by decide
  have hdescent : baseEnd_5119829 < baseStart_5119829 := by decide
  rcases family_descends (prefixWord ++ tailWord_5119829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5119850 : List Nat := [3, 1, 3, 4, 1, 2, 2, 2, 5]
def baseStart_5119850 : Nat := 118140960795 + 5119850 * 2 ^ 59
def prefixEnd_5119850 : Nat := 4983230072969 + 3 ^ 40 * 5119850 * 2
def baseEnd_5119850 : Nat := 292104880991322088558805

theorem tailTrace_5119850 : CollatzResearch.WordTrace tailWord_5119850 prefixEnd_5119850 292104880991322088558805 := by
  unfold tailWord_5119850
  simp only [CollatzResearch.WordTrace]
  refine ⟨46684067625416331402627251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124490847001110217073672669 46684067625416331402627251)
  ·
    refine ⟨70026101438124497103940877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46684067625416331402627251 70026101438124497103940877)
    ·
      refine ⟨26259788039296686413977829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70026101438124497103940877 26259788039296686413977829)
      ·
        refine ⟨4923710257368128702620843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26259788039296686413977829 4923710257368128702620843)
        ·
          refine ⟨7385565386052193053931265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4923710257368128702620843 7385565386052193053931265)
          ·
            refine ⟨5539174039539144790448449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7385565386052193053931265 5539174039539144790448449)
            ·
              refine ⟨4154380529654358592836337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5539174039539144790448449 4154380529654358592836337)
              ·
                refine ⟨3115785397240768944627253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4154380529654358592836337 3115785397240768944627253)
                ·
                  refine ⟨292104880991322088558805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3115785397240768944627253 292104880991322088558805)
                  ·
                    rfl

theorem cell23_5119850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 2, 2, 5].length) (baseStart_5119850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5119850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5119850 prefixEnd_5119850 := by exact prefixLift 5119850
  have htrace : WordTrace (prefixWord ++ tailWord_5119850) baseStart_5119850 baseEnd_5119850 := by
    simpa [prefixWord, tailWord_5119850, baseEnd_5119850] using wordTrace_append hprefix tailTrace_5119850
  have hstable : (prefixWord ++ tailWord_5119850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5119850).length < 2 ^ (prefixWord ++ tailWord_5119850).sum := by decide
  have hdescent : baseEnd_5119850 < baseStart_5119850 := by decide
  rcases family_descends (prefixWord ++ tailWord_5119850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5119872 : List Nat := [2, 1, 1, 2, 1, 2, 3, 5, 6]
def baseStart_5119872 : Nat := 118140960795 + 5119872 * 2 ^ 59
def prefixEnd_5119872 : Nat := 4983230072969 + 3 ^ 40 * 5119872 * 2
def baseEnd_5119872 : Nat := 292106136166255301217127

theorem tailTrace_5119872 : CollatzResearch.WordTrace tailWord_5119872 prefixEnd_5119872 292106136166255301217127 := by
  unfold tailWord_5119872
  simp only [CollatzResearch.WordTrace]
  refine ⟨93368536453792811683904935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124491381938390415578539913 93368536453792811683904935)
  ·
    refine ⟨140052804680689217525857403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93368536453792811683904935 140052804680689217525857403)
    ·
      refine ⟨210079207021033826288786105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140052804680689217525857403 210079207021033826288786105)
      ·
        refine ⟨157559405265775369716589579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210079207021033826288786105 157559405265775369716589579)
        ·
          refine ⟨236339107898663054574884369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157559405265775369716589579 236339107898663054574884369)
          ·
            refine ⟨177254330923997290931163277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 236339107898663054574884369 177254330923997290931163277)
            ·
              refine ⟨66470374096498984099186229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 177254330923997290931163277 66470374096498984099186229)
              ·
                refine ⟨6231597571546779759298709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66470374096498984099186229 6231597571546779759298709)
                ·
                  refine ⟨292106136166255301217127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6231597571546779759298709 292106136166255301217127)
                  ·
                    rfl

theorem cell23_5119872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 5, 6].length) (baseStart_5119872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5119872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5119872 prefixEnd_5119872 := by exact prefixLift 5119872
  have htrace : WordTrace (prefixWord ++ tailWord_5119872) baseStart_5119872 baseEnd_5119872 := by
    simpa [prefixWord, tailWord_5119872, baseEnd_5119872] using wordTrace_append hprefix tailTrace_5119872
  have hstable : (prefixWord ++ tailWord_5119872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5119872).length < 2 ^ (prefixWord ++ tailWord_5119872).sum := by decide
  have hdescent : baseEnd_5119872 < baseStart_5119872 := by decide
  rcases family_descends (prefixWord ++ tailWord_5119872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5119956 : List Nat := [2, 4, 1, 2, 1, 1, 1, 5, 1, 1, 4]
def baseStart_5119956 : Nat := 118140960795 + 5119956 * 2 ^ 59
def prefixEnd_5119956 : Nat := 4983230072969 + 3 ^ 40 * 5119956 * 2
def baseEnd_5119956 : Nat := 2628998357871275382303757

theorem tailTrace_5119956 : CollatzResearch.WordTrace tailWord_5119956 prefixEnd_5119956 2628998357871275382303757 := by
  unfold tailWord_5119956
  simp only [CollatzResearch.WordTrace]
  refine ⟨93370068319640652856933861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124493424426187537142578481 93370068319640652856933861)
  ·
    refine ⟨17506887809932622410675099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93370068319640652856933861 17506887809932622410675099)
    ·
      refine ⟨26260331714898933616012649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17506887809932622410675099 26260331714898933616012649)
      ·
        refine ⟨19695248786174200212009487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26260331714898933616012649 19695248786174200212009487)
        ·
          refine ⟨29542873179261300318014231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19695248786174200212009487 29542873179261300318014231)
          ·
            refine ⟨44314309768891950477021347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29542873179261300318014231 44314309768891950477021347)
            ·
              refine ⟨66471464653337925715532021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44314309768891950477021347 66471464653337925715532021)
              ·
                refine ⟨6231699811250430535831127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66471464653337925715532021 6231699811250430535831127)
                ·
                  refine ⟨9347549716875645803746691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6231699811250430535831127 9347549716875645803746691)
                  ·
                    refine ⟨14021324575313468705620037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9347549716875645803746691 14021324575313468705620037)
                    ·
                      refine ⟨2628998357871275382303757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14021324575313468705620037 2628998357871275382303757)
                      ·
                        rfl

theorem cell23_5119956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_5119956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5119956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5119956 prefixEnd_5119956 := by exact prefixLift 5119956
  have htrace : WordTrace (prefixWord ++ tailWord_5119956) baseStart_5119956 baseEnd_5119956 := by
    simpa [prefixWord, tailWord_5119956, baseEnd_5119956] using wordTrace_append hprefix tailTrace_5119956
  have hstable : (prefixWord ++ tailWord_5119956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5119956).length < 2 ^ (prefixWord ++ tailWord_5119956).sum := by decide
  have hdescent : baseEnd_5119956 < baseStart_5119956 := by decide
  rcases family_descends (prefixWord ++ tailWord_5119956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5119959 : List Nat := [1, 1, 3, 2, 1, 1, 6, 1, 1, 1, 5]
def baseStart_5119959 : Nat := 118140960795 + 5119959 * 2 ^ 59
def prefixEnd_5119959 : Nat := 4983230072969 + 3 ^ 40 * 5119959 * 2
def baseEnd_5119959 : Nat := 2628999898313238870566243

theorem tailTrace_5119959 : CollatzResearch.WordTrace tailWord_5119959 prefixEnd_5119959 2628999898313238870566243 := by
  unfold tailWord_5119959
  simp only [CollatzResearch.WordTrace]
  refine ⟨186740246058270437226226931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124493497372180291484151287 186740246058270437226226931)
  ·
    refine ⟨280110369087405655839340397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186740246058270437226226931 280110369087405655839340397)
    ·
      refine ⟨105041388407777120939752649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 280110369087405655839340397 105041388407777120939752649)
      ·
        refine ⟨78781041305832840704814487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105041388407777120939752649 78781041305832840704814487)
        ·
          refine ⟨118171561958749261057221731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78781041305832840704814487 118171561958749261057221731)
          ·
            refine ⟨177257342938123891585832597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118171561958749261057221731 177257342938123891585832597)
            ·
              refine ⟨8308937950224557418085903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 177257342938123891585832597 8308937950224557418085903)
              ·
                refine ⟨12463406925336836127128855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8308937950224557418085903 12463406925336836127128855)
                ·
                  refine ⟨18695110388005254190693283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12463406925336836127128855 18695110388005254190693283)
                  ·
                    refine ⟨28042665582007881286039925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18695110388005254190693283 28042665582007881286039925)
                    ·
                      refine ⟨2628999898313238870566243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28042665582007881286039925 2628999898313238870566243)
                      ·
                        rfl

theorem cell23_5119959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 1, 1, 1, 5].length) (baseStart_5119959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5119959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5119959 prefixEnd_5119959 := by exact prefixLift 5119959
  have htrace : WordTrace (prefixWord ++ tailWord_5119959) baseStart_5119959 baseEnd_5119959 := by
    simpa [prefixWord, tailWord_5119959, baseEnd_5119959] using wordTrace_append hprefix tailTrace_5119959
  have hstable : (prefixWord ++ tailWord_5119959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5119959).length < 2 ^ (prefixWord ++ tailWord_5119959).sum := by decide
  have hdescent : baseEnd_5119959 < baseStart_5119959 := by decide
  rcases family_descends (prefixWord ++ tailWord_5119959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5119990 : List Nat := [5, 1, 1, 1, 4, 2, 1, 2, 1, 1, 4]
def baseStart_5119990 : Nat := 118140960795 + 5119990 * 2 ^ 59
def prefixEnd_5119990 : Nat := 4983230072969 + 3 ^ 40 * 5119990 * 2
def baseEnd_5119990 : Nat := 2629015816213528249278601

theorem tailTrace_5119990 : CollatzResearch.WordTrace tailWord_5119990 prefixEnd_5119990 2629015816213528249278601 := by
  unfold tailWord_5119990
  simp only [CollatzResearch.WordTrace]
  refine ⟨11671336045072383095037839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 124494251147438753013736949 11671336045072383095037839)
  ·
    refine ⟨17507004067608574642556759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11671336045072383095037839 17507004067608574642556759)
    ·
      refine ⟨26260506101412861963835139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17507004067608574642556759 26260506101412861963835139)
      ·
        refine ⟨39390759152119292945752709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26260506101412861963835139 39390759152119292945752709)
        ·
          refine ⟨7385767341022367427328633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39390759152119292945752709 7385767341022367427328633)
          ·
            refine ⟨5539325505766775570496475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7385767341022367427328633 5539325505766775570496475)
            ·
              refine ⟨8308988258650163355744713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5539325505766775570496475 8308988258650163355744713)
              ·
                refine ⟨6231741193987622516808535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8308988258650163355744713 6231741193987622516808535)
                ·
                  refine ⟨9347611790981433775212803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6231741193987622516808535 9347611790981433775212803)
                  ·
                    refine ⟨14021417686472150662819205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9347611790981433775212803 14021417686472150662819205)
                    ·
                      refine ⟨2629015816213528249278601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14021417686472150662819205 2629015816213528249278601)
                      ·
                        rfl

theorem cell23_5119990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 2, 1, 1, 4].length) (baseStart_5119990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5119990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5119990 prefixEnd_5119990 := by exact prefixLift 5119990
  have htrace : WordTrace (prefixWord ++ tailWord_5119990) baseStart_5119990 baseEnd_5119990 := by
    simpa [prefixWord, tailWord_5119990, baseEnd_5119990] using wordTrace_append hprefix tailTrace_5119990
  have hstable : (prefixWord ++ tailWord_5119990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5119990).length < 2 ^ (prefixWord ++ tailWord_5119990).sum := by decide
  have hdescent : baseEnd_5119990 < baseStart_5119990 := by decide
  rcases family_descends (prefixWord ++ tailWord_5119990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5119993 : List Nat := [1, 2, 1, 3, 1, 6, 1, 2, 1, 2, 3]
def baseStart_5119993 : Nat := 118140960795 + 5119993 * 2 ^ 59
def prefixEnd_5119993 : Nat := 4983230072969 + 3 ^ 40 * 5119993 * 2
def baseEnd_5119993 : Nat := 2629017356655491737541087

theorem tailTrace_5119993 : CollatzResearch.WordTrace tailWord_5119993 prefixEnd_5119993 2629017356655491737541087 := by
  unfold tailWord_5119993
  simp only [CollatzResearch.WordTrace]
  refine ⟨186741486140147261032964633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124494324093431507355309755 186741486140147261032964633)
  ·
    refine ⟨140056114605110445774723475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186741486140147261032964633 140056114605110445774723475)
    ·
      refine ⟨210084171907665668662085213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140056114605110445774723475 210084171907665668662085213)
      ·
        refine ⟨78781564465374625748281955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 210084171907665668662085213 78781564465374625748281955)
        ·
          refine ⟨118172346698061938622422933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78781564465374625748281955 118172346698061938622422933)
          ·
            refine ⟨5539328751471653372926075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 118172346698061938622422933 5539328751471653372926075)
            ·
              refine ⟨8308993127207480059389113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5539328751471653372926075 8308993127207480059389113)
              ·
                refine ⟨6231744845405610044541835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8308993127207480059389113 6231744845405610044541835)
                ·
                  refine ⟨9347617268108415066812753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6231744845405610044541835 9347617268108415066812753)
                  ·
                    refine ⟨7010712951081311300109565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9347617268108415066812753 7010712951081311300109565)
                    ·
                      refine ⟨2629017356655491737541087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7010712951081311300109565 2629017356655491737541087)
                      ·
                        rfl

theorem cell23_5119993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 2, 1, 2, 3].length) (baseStart_5119993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5119993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5119993 prefixEnd_5119993 := by exact prefixLift 5119993
  have htrace : WordTrace (prefixWord ++ tailWord_5119993) baseStart_5119993 baseEnd_5119993 := by
    simpa [prefixWord, tailWord_5119993, baseEnd_5119993] using wordTrace_append hprefix tailTrace_5119993
  have hstable : (prefixWord ++ tailWord_5119993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5119993).length < 2 ^ (prefixWord ++ tailWord_5119993).sum := by decide
  have hdescent : baseEnd_5119993 < baseStart_5119993 := by decide
  rcases family_descends (prefixWord ++ tailWord_5119993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5120010 : List Nat := [3, 1, 2, 2, 4, 1, 3, 1, 1, 2, 3]
def baseStart_5120010 : Nat := 118140960795 + 5120010 * 2 ^ 59
def prefixEnd_5120010 : Nat := 4983230072969 + 3 ^ 40 * 5120010 * 2
def baseEnd_5120010 : Nat := 2629026085826618171028509

theorem tailTrace_5120010 : CollatzResearch.WordTrace tailWord_5120010 prefixEnd_5120010 2629026085826618171028509 := by
  unfold tailWord_5120010
  simp only [CollatzResearch.WordTrace]
  refine ⟨46685526545271418234083371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124494737454057115290888989 46685526545271418234083371)
  ·
    refine ⟨70028289817907127351125057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46685526545271418234083371 70028289817907127351125057)
    ·
      refine ⟨52521217363430345513343793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70028289817907127351125057 52521217363430345513343793)
      ·
        refine ⟨39390913022572759135007845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52521217363430345513343793 39390913022572759135007845)
        ·
          refine ⟨7385796191732392337813971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39390913022572759135007845 7385796191732392337813971)
          ·
            refine ⟨11078694287598588506720957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7385796191732392337813971 11078694287598588506720957)
            ·
              refine ⟨4154510357849470690020359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11078694287598588506720957 4154510357849470690020359)
              ·
                refine ⟨6231765536774206035030539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4154510357849470690020359 6231765536774206035030539)
                ·
                  refine ⟨9347648305161309052545809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6231765536774206035030539 9347648305161309052545809)
                  ·
                    refine ⟨7010736228870981789409357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9347648305161309052545809 7010736228870981789409357)
                    ·
                      refine ⟨2629026085826618171028509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7010736228870981789409357 2629026085826618171028509)
                      ·
                        rfl

theorem cell23_5120010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 3, 1, 1, 2, 3].length) (baseStart_5120010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5120010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5120010 prefixEnd_5120010 := by exact prefixLift 5120010
  have htrace : WordTrace (prefixWord ++ tailWord_5120010) baseStart_5120010 baseEnd_5120010 := by
    simpa [prefixWord, tailWord_5120010, baseEnd_5120010] using wordTrace_append hprefix tailTrace_5120010
  have hstable : (prefixWord ++ tailWord_5120010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5120010).length < 2 ^ (prefixWord ++ tailWord_5120010).sum := by decide
  have hdescent : baseEnd_5120010 < baseStart_5120010 := by decide
  rcases family_descends (prefixWord ++ tailWord_5120010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5120013 : List Nat := [1, 7, 1, 2, 1, 11]
def baseStart_5120013 : Nat := 118140960795 + 5120013 * 2 ^ 59
def prefixEnd_5120013 : Nat := 4983230072969 + 3 ^ 40 * 5120013 * 2
def baseEnd_5120013 : Nat := 10819043729500336046465

theorem tailTrace_5120013 : CollatzResearch.WordTrace tailWord_5120013 prefixEnd_5120013 10819043729500336046465 := by
  unfold tailWord_5120013
  simp only [CollatzResearch.WordTrace]
  refine ⟨186742215600074804448692693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124494810400049869632461795 186742215600074804448692693)
  ·
    refine ⟨4376770678126753229266235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 186742215600074804448692693 4376770678126753229266235)
    ·
      refine ⟨6565156017190129843899353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4376770678126753229266235 6565156017190129843899353)
      ·
        refine ⟨4923867012892597382924515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6565156017190129843899353 4923867012892597382924515)
        ·
          refine ⟨7385800519338896074386773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4923867012892597382924515 7385800519338896074386773)
          ·
            refine ⟨10819043729500336046465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 7385800519338896074386773 10819043729500336046465)
            ·
              rfl

theorem cell23_5120013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 11].length) (baseStart_5120013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5120013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5120013 prefixEnd_5120013 := by exact prefixLift 5120013
  have htrace : WordTrace (prefixWord ++ tailWord_5120013) baseStart_5120013 baseEnd_5120013 := by
    simpa [prefixWord, tailWord_5120013, baseEnd_5120013] using wordTrace_append hprefix tailTrace_5120013
  have hstable : (prefixWord ++ tailWord_5120013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5120013).length < 2 ^ (prefixWord ++ tailWord_5120013).sum := by decide
  have hdescent : baseEnd_5120013 < baseStart_5120013 := by decide
  rcases family_descends (prefixWord ++ tailWord_5120013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5120040 : List Nat := [2, 1, 5, 3, 1, 1, 2, 1, 1, 3, 3]
def baseStart_5120040 : Nat := 118140960795 + 5120040 * 2 ^ 59
def prefixEnd_5120040 : Nat := 4983230072969 + 3 ^ 40 * 5120040 * 2
def baseEnd_5120040 : Nat := 2629041490246253053653371

theorem tailTrace_5120040 : CollatzResearch.WordTrace tailWord_5120040 prefixEnd_5120040 2629041490246253053653371 := by
  unfold tailWord_5120040
  simp only [CollatzResearch.WordTrace]
  refine ⟨93371600185488494029962787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124495466913984658706617049 93371600185488494029962787)
  ·
    refine ⟨140057400278232741044944181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93371600185488494029962787 140057400278232741044944181)
    ·
      refine ⟨13130381276084319472963517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 140057400278232741044944181 13130381276084319472963517)
      ·
        refine ⟨4923892978531619802361319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13130381276084319472963517 4923892978531619802361319)
        ·
          refine ⟨7385839467797429703541979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4923892978531619802361319 7385839467797429703541979)
          ·
            refine ⟨11078759201696144555312969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7385839467797429703541979 11078759201696144555312969)
            ·
              refine ⟨8309069401272108416484727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11078759201696144555312969 8309069401272108416484727)
              ·
                refine ⟨12463604101908162624727091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8309069401272108416484727 12463604101908162624727091)
                ·
                  refine ⟨18695406152862243937090637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12463604101908162624727091 18695406152862243937090637)
                  ·
                    refine ⟨7010777307323341476408989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18695406152862243937090637 7010777307323341476408989)
                    ·
                      refine ⟨2629041490246253053653371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7010777307323341476408989 2629041490246253053653371)
                      ·
                        rfl

theorem cell23_5120040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_5120040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5120040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5120040 prefixEnd_5120040 := by exact prefixLift 5120040
  have htrace : WordTrace (prefixWord ++ tailWord_5120040) baseStart_5120040 baseEnd_5120040 := by
    simpa [prefixWord, tailWord_5120040, baseEnd_5120040] using wordTrace_append hprefix tailTrace_5120040
  have hstable : (prefixWord ++ tailWord_5120040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5120040).length < 2 ^ (prefixWord ++ tailWord_5120040).sum := by decide
  have hdescent : baseEnd_5120040 < baseStart_5120040 := by decide
  rcases family_descends (prefixWord ++ tailWord_5120040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5120079 : List Nat := [1, 1, 2, 1, 1, 2, 2, 2, 3, 5, 3]
def baseStart_5120079 : Nat := 118140960795 + 5120079 * 2 ^ 59
def prefixEnd_5120079 : Nat := 4983230072969 + 3 ^ 40 * 5120079 * 2
def baseEnd_5120079 : Nat := 2629061515991778401065691

theorem tailTrace_5120079 : CollatzResearch.WordTrace tailWord_5120079 prefixEnd_5120079 2629061515991778401065691 := by
  unfold tailWord_5120079
  simp only [CollatzResearch.WordTrace]
  refine ⟨186744622817835697720595291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124496415211890465147063527 186744622817835697720595291)
  ·
    refine ⟨280116934226753546580892937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186744622817835697720595291 280116934226753546580892937)
    ·
      refine ⟨210087700670065159935669703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 280116934226753546580892937 210087700670065159935669703)
      ·
        refine ⟨315131551005097739903504555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210087700670065159935669703 315131551005097739903504555)
        ·
          refine ⟨472697326507646609855256833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315131551005097739903504555 472697326507646609855256833)
          ·
            refine ⟨354522994880734957391442625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 472697326507646609855256833 354522994880734957391442625)
            ·
              refine ⟨265892246160551218043581969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 354522994880734957391442625 265892246160551218043581969)
              ·
                refine ⟨199419184620413413532686477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 265892246160551218043581969 199419184620413413532686477)
                ·
                  refine ⟨74782194232655030074757429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 199419184620413413532686477 74782194232655030074757429)
                  ·
                    refine ⟨7010830709311409069508509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 74782194232655030074757429 7010830709311409069508509)
                    ·
                      refine ⟨2629061515991778401065691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7010830709311409069508509 2629061515991778401065691)
                      ·
                        rfl

theorem cell23_5120079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 5, 3].length) (baseStart_5120079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5120079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5120079 prefixEnd_5120079 := by exact prefixLift 5120079
  have htrace : WordTrace (prefixWord ++ tailWord_5120079) baseStart_5120079 baseEnd_5120079 := by
    simpa [prefixWord, tailWord_5120079, baseEnd_5120079] using wordTrace_append hprefix tailTrace_5120079
  have hstable : (prefixWord ++ tailWord_5120079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5120079).length < 2 ^ (prefixWord ++ tailWord_5120079).sum := by decide
  have hdescent : baseEnd_5120079 < baseStart_5120079 := by decide
  rcases family_descends (prefixWord ++ tailWord_5120079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5120093 : List Nat := [1, 4, 4, 1, 1, 1, 2, 1, 2, 2, 4]
def baseStart_5120093 : Nat := 118140960795 + 5120093 * 2 ^ 59
def prefixEnd_5120093 : Nat := 4983230072969 + 3 ^ 40 * 5120093 * 2
def baseEnd_5120093 : Nat := 2629068704720941346290627

theorem tailTrace_5120093 : CollatzResearch.WordTrace tailWord_5120093 prefixEnd_5120093 2629068704720941346290627 := by
  unfold tailWord_5120093
  simp only [CollatzResearch.WordTrace]
  refine ⟨186745133439784978111604933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124496755626523318741069955 186745133439784978111604933)
  ·
    refine ⟨35014712519959683395925925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 186745133439784978111604933 35014712519959683395925925)
    ·
      refine ⟨6565258597492440636736111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35014712519959683395925925 6565258597492440636736111)
      ·
        refine ⟨9847887896238660955104167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6565258597492440636736111 9847887896238660955104167)
        ·
          refine ⟨14771831844357991432656251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9847887896238660955104167 14771831844357991432656251)
          ·
            refine ⟨22157747766536987148984377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14771831844357991432656251 22157747766536987148984377)
            ·
              refine ⟨16618310824902740361738283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22157747766536987148984377 16618310824902740361738283)
              ·
                refine ⟨24927466237354110542607425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16618310824902740361738283 24927466237354110542607425)
                ·
                  refine ⟨18695599678015582906955569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24927466237354110542607425 18695599678015582906955569)
                  ·
                    refine ⟨14021699758511687180216677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18695599678015582906955569 14021699758511687180216677)
                    ·
                      refine ⟨2629068704720941346290627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14021699758511687180216677 2629068704720941346290627)
                      ·
                        rfl

theorem cell23_5120093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_5120093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5120093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5120093 prefixEnd_5120093 := by exact prefixLift 5120093
  have htrace : WordTrace (prefixWord ++ tailWord_5120093) baseStart_5120093 baseEnd_5120093 := by
    simpa [prefixWord, tailWord_5120093, baseEnd_5120093] using wordTrace_append hprefix tailTrace_5120093
  have hstable : (prefixWord ++ tailWord_5120093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5120093).length < 2 ^ (prefixWord ++ tailWord_5120093).sum := by decide
  have hdescent : baseEnd_5120093 < baseStart_5120093 := by decide
  rcases family_descends (prefixWord ++ tailWord_5120093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5120096 : List Nat := [2, 1, 1, 3, 2, 3, 2, 1, 2, 3, 3]
def baseStart_5120096 : Nat := 118140960795 + 5120096 * 2 ^ 59
def prefixEnd_5120096 : Nat := 4983230072969 + 3 ^ 40 * 5120096 * 2
def baseEnd_5120096 : Nat := 2629070245162904834553113

theorem tailTrace_5120096 : CollatzResearch.WordTrace tailWord_5120096 prefixEnd_5120096 2629070245162904834553113 := by
  unfold tailWord_5120096
  simp only [CollatzResearch.WordTrace]
  refine ⟨93372621429387054811982071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124496828572516073082642761 93372621429387054811982071)
  ·
    refine ⟨140058932144080582217973107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93372621429387054811982071 140058932144080582217973107)
    ·
      refine ⟨210088398216120873326959661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140058932144080582217973107 210088398216120873326959661)
      ·
        refine ⟨78783149331045327497609873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 210088398216120873326959661 78783149331045327497609873)
        ·
          refine ⟨59087361998283995623207405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78783149331045327497609873 59087361998283995623207405)
          ·
            refine ⟨22157760749356498358702777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59087361998283995623207405 22157760749356498358702777)
            ·
              refine ⟨16618320562017373769027083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22157760749356498358702777 16618320562017373769027083)
              ·
                refine ⟨24927480843026060653540625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16618320562017373769027083 24927480843026060653540625)
                ·
                  refine ⟨18695610632269545490155469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24927480843026060653540625 18695610632269545490155469)
                  ·
                    refine ⟨7010853987101079558808301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18695610632269545490155469 7010853987101079558808301)
                    ·
                      refine ⟨2629070245162904834553113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7010853987101079558808301 2629070245162904834553113)
                      ·
                        rfl

theorem cell23_5120096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 2, 3, 3].length) (baseStart_5120096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5120096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5120096 prefixEnd_5120096 := by exact prefixLift 5120096
  have htrace : WordTrace (prefixWord ++ tailWord_5120096) baseStart_5120096 baseEnd_5120096 := by
    simpa [prefixWord, tailWord_5120096, baseEnd_5120096] using wordTrace_append hprefix tailTrace_5120096
  have hstable : (prefixWord ++ tailWord_5120096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5120096).length < 2 ^ (prefixWord ++ tailWord_5120096).sum := by decide
  have hdescent : baseEnd_5120096 < baseStart_5120096 := by decide
  rcases family_descends (prefixWord ++ tailWord_5120096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5120099 : List Nat := [1, 1, 1, 5, 1, 1, 3, 2, 1, 7]
def baseStart_5120099 : Nat := 118140960795 + 5120099 * 2 ^ 59
def prefixEnd_5120099 : Nat := 4983230072969 + 3 ^ 40 * 5120099 * 2
def baseEnd_5120099 : Nat := 876357261868289440938533

theorem tailTrace_5120099 : CollatzResearch.WordTrace tailWord_5120099 prefixEnd_5120099 876357261868289440938533 := by
  unfold tailWord_5120099
  simp only [CollatzResearch.WordTrace]
  refine ⟨186745352277763241136323351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124496901518508827424215567 186745352277763241136323351)
  ·
    refine ⟨280118028416644861704485027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186745352277763241136323351 280118028416644861704485027)
    ·
      refine ⟨420177042624967292556727541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280118028416644861704485027 420177042624967292556727541)
      ·
        refine ⟨39391597746090683677193207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 420177042624967292556727541 39391597746090683677193207)
        ·
          refine ⟨59087396619136025515789811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39391597746090683677193207 59087396619136025515789811)
          ·
            refine ⟨88631094928704038273684717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59087396619136025515789811 88631094928704038273684717)
            ·
              refine ⟨33236660598264014352631769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88631094928704038273684717 33236660598264014352631769)
              ·
                refine ⟨24927495448698010764473827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33236660598264014352631769 24927495448698010764473827)
                ·
                  refine ⟨37391243173047016146710741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24927495448698010764473827 37391243173047016146710741)
                  ·
                    refine ⟨876357261868289440938533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37391243173047016146710741 876357261868289440938533)
                    ·
                      rfl

theorem cell23_5120099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 7].length) (baseStart_5120099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5120099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5120099 prefixEnd_5120099 := by exact prefixLift 5120099
  have htrace : WordTrace (prefixWord ++ tailWord_5120099) baseStart_5120099 baseEnd_5120099 := by
    simpa [prefixWord, tailWord_5120099, baseEnd_5120099] using wordTrace_append hprefix tailTrace_5120099
  have hstable : (prefixWord ++ tailWord_5120099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5120099).length < 2 ^ (prefixWord ++ tailWord_5120099).sum := by decide
  have hdescent : baseEnd_5120099 < baseStart_5120099 := by decide
  rcases family_descends (prefixWord ++ tailWord_5120099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5120148 : List Nat := [2, 4, 2, 3, 2, 1, 2, 1, 2, 2, 2]
def baseStart_5120148 : Nat := 118140960795 + 5120148 * 2 ^ 59
def prefixEnd_5120148 : Nat := 4983230072969 + 3 ^ 40 * 5120148 * 2
def baseEnd_5120148 : Nat := 2629096946156938631102875

theorem tailTrace_5120148 : CollatzResearch.WordTrace tailWord_5120148 prefixEnd_5120148 2629096946156938631102875 := by
  unfold tailWord_5120148
  simp only [CollatzResearch.WordTrace]
  refine ⟨93373569727292861252428549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124498092969723815003238065 93373569727292861252428549)
  ·
    refine ⟨17507544323867411484830353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93373569727292861252428549 17507544323867411484830353)
    ·
      refine ⟨13130658242900558613622765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17507544323867411484830353 13130658242900558613622765)
      ·
        refine ⟨4923996841087709480108537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13130658242900558613622765 4923996841087709480108537)
        ·
          refine ⟨3692997630815782110081403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4923996841087709480108537 3692997630815782110081403)
          ·
            refine ⟨5539496446223673165122105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3692997630815782110081403 5539496446223673165122105)
            ·
              refine ⟨4154622334667754873841579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5539496446223673165122105 4154622334667754873841579)
              ·
                refine ⟨6231933502001632310762369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4154622334667754873841579 6231933502001632310762369)
                ·
                  refine ⟨4673950126501224233071777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6231933502001632310762369 4673950126501224233071777)
                  ·
                    refine ⟨3505462594875918174803833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4673950126501224233071777 3505462594875918174803833)
                    ·
                      refine ⟨2629096946156938631102875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3505462594875918174803833 2629096946156938631102875)
                      ·
                        rfl

theorem cell23_5120148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_5120148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5120148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5120148 prefixEnd_5120148 := by exact prefixLift 5120148
  have htrace : WordTrace (prefixWord ++ tailWord_5120148) baseStart_5120148 baseEnd_5120148 := by
    simpa [prefixWord, tailWord_5120148, baseEnd_5120148] using wordTrace_append hprefix tailTrace_5120148
  have hstable : (prefixWord ++ tailWord_5120148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5120148).length < 2 ^ (prefixWord ++ tailWord_5120148).sum := by decide
  have hdescent : baseEnd_5120148 < baseStart_5120148 := by decide
  rcases family_descends (prefixWord ++ tailWord_5120148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5120179 : List Nat := [1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 8]
def baseStart_5120179 : Nat := 118140960795 + 5120179 * 2 ^ 59
def prefixEnd_5120179 : Nat := 4983230072969 + 3 ^ 40 * 5120179 * 2
def baseEnd_5120179 : Nat := 2629112864057228009815231

theorem tailTrace_5120179 : CollatzResearch.WordTrace tailWord_5120179 prefixEnd_5120179 2629112864057228009815231 := by
  unfold tailWord_5120179
  simp only [CollatzResearch.WordTrace]
  refine ⟨186748270117473414799235591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124498846744982276532823727 186748270117473414799235591)
  ·
    refine ⟨280122405176210122198853387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186748270117473414799235591 280122405176210122198853387)
    ·
      refine ⟨420183607764315183298280081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280122405176210122198853387 420183607764315183298280081)
      ·
        refine ⟨315137705823236387473710061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 420183607764315183298280081 315137705823236387473710061)
        ·
          refine ⟨118176639683713645302641273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 315137705823236387473710061 118176639683713645302641273)
          ·
            refine ⟨88632479762785233976980955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118176639683713645302641273 88632479762785233976980955)
            ·
              refine ⟨132948719644177850965471433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88632479762785233976980955 132948719644177850965471433)
              ·
                refine ⟨99711539733133388224103575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 132948719644177850965471433 99711539733133388224103575)
                ·
                  refine ⟨149567309599700082336155363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99711539733133388224103575 149567309599700082336155363)
                  ·
                    refine ⟨224350964399550123504233045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 149567309599700082336155363 224350964399550123504233045)
                    ·
                      refine ⟨2629112864057228009815231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 224350964399550123504233045 2629112864057228009815231)
                      ·
                        rfl

theorem cell23_5120179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 8].length) (baseStart_5120179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5120179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5120179 prefixEnd_5120179 := by exact prefixLift 5120179
  have htrace : WordTrace (prefixWord ++ tailWord_5120179) baseStart_5120179 baseEnd_5120179 := by
    simpa [prefixWord, tailWord_5120179, baseEnd_5120179] using wordTrace_append hprefix tailTrace_5120179
  have hstable : (prefixWord ++ tailWord_5120179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5120179).length < 2 ^ (prefixWord ++ tailWord_5120179).sum := by decide
  have hdescent : baseEnd_5120179 < baseStart_5120179 := by decide
  rcases family_descends (prefixWord ++ tailWord_5120179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5120203 : List Nat := [1, 1, 1, 1, 3, 2, 4, 3, 3, 1, 3]
def baseStart_5120203 : Nat := 118140960795 + 5120203 * 2 ^ 59
def prefixEnd_5120203 : Nat := 4983230072969 + 3 ^ 40 * 5120203 * 2
def baseEnd_5120203 : Nat := 2629125187592935915915121

theorem tailTrace_5120203 : CollatzResearch.WordTrace tailWord_5120203 prefixEnd_5120203 2629125187592935915915121 := by
  unfold tailWord_5120203
  simp only [CollatzResearch.WordTrace]
  refine ⟨186749145469386466898109263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124499430312924311265406175 186749145469386466898109263)
  ·
    refine ⟨280123718204079700347163895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186749145469386466898109263 280123718204079700347163895)
    ·
      refine ⟨420185577306119550520745843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280123718204079700347163895 420185577306119550520745843)
      ·
        refine ⟨630278365959179325781118765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 420185577306119550520745843 630278365959179325781118765)
        ·
          refine ⟨236354387234692247167919537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 630278365959179325781118765 236354387234692247167919537)
          ·
            refine ⟨177265790426019185375939653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 236354387234692247167919537 177265790426019185375939653)
            ·
              refine ⟨33237335704878597257988685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 177265790426019185375939653 33237335704878597257988685)
              ·
                refine ⟨12464000889329473971745757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33237335704878597257988685 12464000889329473971745757)
                ·
                  refine ⟨4674000333498552739404659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12464000889329473971745757 4674000333498552739404659)
                  ·
                    refine ⟨7011000500247829109106989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4674000333498552739404659 7011000500247829109106989)
                    ·
                      refine ⟨2629125187592935915915121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7011000500247829109106989 2629125187592935915915121)
                      ·
                        rfl

theorem cell23_5120203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 3, 3, 1, 3].length) (baseStart_5120203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5120203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5120203 prefixEnd_5120203 := by exact prefixLift 5120203
  have htrace : WordTrace (prefixWord ++ tailWord_5120203) baseStart_5120203 baseEnd_5120203 := by
    simpa [prefixWord, tailWord_5120203, baseEnd_5120203] using wordTrace_append hprefix tailTrace_5120203
  have hstable : (prefixWord ++ tailWord_5120203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5120203).length < 2 ^ (prefixWord ++ tailWord_5120203).sum := by decide
  have hdescent : baseEnd_5120203 < baseStart_5120203 := by decide
  rcases family_descends (prefixWord ++ tailWord_5120203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5120236 : List Nat := [2, 2, 1, 1, 2, 3, 1, 4, 1, 6]
def baseStart_5120236 : Nat := 118140960795 + 5120236 * 2 ^ 59
def prefixEnd_5120236 : Nat := 4983230072969 + 3 ^ 40 * 5120236 * 2
def baseEnd_5120236 : Nat := 876380710818178095600823

theorem tailTrace_5120236 : CollatzResearch.WordTrace tailWord_5120236 prefixEnd_5120236 876380710818178095600823 := by
  unfold tailWord_5120236
  simp only [CollatzResearch.WordTrace]
  refine ⟨93375174539133456767030281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124500232718844609022707041 93375174539133456767030281)
  ·
    refine ⟨70031380904350092575272711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93375174539133456767030281 70031380904350092575272711)
    ·
      refine ⟨105047071356525138862909067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70031380904350092575272711 105047071356525138862909067)
      ·
        refine ⟨157570607034787708294363601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105047071356525138862909067 157570607034787708294363601)
        ·
          refine ⟨118177955276090781220772701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157570607034787708294363601 118177955276090781220772701)
          ·
            refine ⟨44316733228534042957789763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118177955276090781220772701 44316733228534042957789763)
            ·
              refine ⟨66475099842801064436684645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44316733228534042957789763 66475099842801064436684645)
              ·
                refine ⟨12464081220525199581878371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66475099842801064436684645 12464081220525199581878371)
                ·
                  refine ⟨18696121830787799372817557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12464081220525199581878371 18696121830787799372817557)
                  ·
                    refine ⟨876380710818178095600823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18696121830787799372817557 876380710818178095600823)
                    ·
                      rfl

theorem cell23_5120236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 6].length) (baseStart_5120236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5120236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5120236 prefixEnd_5120236 := by exact prefixLift 5120236
  have htrace : WordTrace (prefixWord ++ tailWord_5120236) baseStart_5120236 baseEnd_5120236 := by
    simpa [prefixWord, tailWord_5120236, baseEnd_5120236] using wordTrace_append hprefix tailTrace_5120236
  have hstable : (prefixWord ++ tailWord_5120236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5120236).length < 2 ^ (prefixWord ++ tailWord_5120236).sum := by decide
  have hdescent : baseEnd_5120236 < baseStart_5120236 := by decide
  rcases family_descends (prefixWord ++ tailWord_5120236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5120243 : List Nat := [1, 1, 1, 2, 2, 4, 3, 3, 1, 1, 4]
def baseStart_5120243 : Nat := 118140960795 + 5120243 * 2 ^ 59
def prefixEnd_5120243 : Nat := 4983230072969 + 3 ^ 40 * 5120243 * 2
def baseEnd_5120243 : Nat := 2629145726819115759414937

theorem tailTrace_5120243 : CollatzResearch.WordTrace tailWord_5120243 prefixEnd_5120243 2629145726819115759414937 := by
  unfold tailWord_5120243
  simp only [CollatzResearch.WordTrace]
  refine ⟨186750604389241553729565383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124500402926161035819710255 186750604389241553729565383)
  ·
    refine ⟨280125906583862330594348075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186750604389241553729565383 280125906583862330594348075)
    ·
      refine ⟨420188859875793495891522113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280125906583862330594348075 420188859875793495891522113)
      ·
        refine ⟨315141644906845121918641585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 420188859875793495891522113 315141644906845121918641585)
        ·
          refine ⟨236356233680133841438981189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 315141644906845121918641585 236356233680133841438981189)
          ·
            refine ⟨44316793815025095269808973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 236356233680133841438981189 44316793815025095269808973)
            ·
              refine ⟨16618797680634410726178365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44316793815025095269808973 16618797680634410726178365)
              ·
                refine ⟨6232049130237904022316887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16618797680634410726178365 6232049130237904022316887)
                ·
                  refine ⟨9348073695356856033475331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6232049130237904022316887 9348073695356856033475331)
                  ·
                    refine ⟨14022110543035284050212997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9348073695356856033475331 14022110543035284050212997)
                    ·
                      refine ⟨2629145726819115759414937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14022110543035284050212997 2629145726819115759414937)
                      ·
                        rfl

theorem cell23_5120243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 3, 1, 1, 4].length) (baseStart_5120243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5120243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5120243 prefixEnd_5120243 := by exact prefixLift 5120243
  have htrace : WordTrace (prefixWord ++ tailWord_5120243) baseStart_5120243 baseEnd_5120243 := by
    simpa [prefixWord, tailWord_5120243, baseEnd_5120243] using wordTrace_append hprefix tailTrace_5120243
  have hstable : (prefixWord ++ tailWord_5120243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5120243).length < 2 ^ (prefixWord ++ tailWord_5120243).sum := by decide
  have hdescent : baseEnd_5120243 < baseStart_5120243 := by decide
  rcases family_descends (prefixWord ++ tailWord_5120243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5120256 : List Nat := [2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 4]
def baseStart_5120256 : Nat := 118140960795 + 5120256 * 2 ^ 59
def prefixEnd_5120256 : Nat := 4983230072969 + 3 ^ 40 * 5120256 * 2
def baseEnd_5120256 : Nat := 2629152402067624208552377

theorem tailTrace_5120256 : CollatzResearch.WordTrace tailWord_5120256 prefixEnd_5120256 2629152402067624208552377 := by
  unfold tailWord_5120256
  simp only [CollatzResearch.WordTrace]
  refine ⟨93375539269097228474894311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124500719025462971299859081 93375539269097228474894311)
  ·
    refine ⟨140063308903645842712341467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93375539269097228474894311 140063308903645842712341467)
    ·
      refine ⟨210094963355468764068512201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140063308903645842712341467 210094963355468764068512201)
      ·
        refine ⟨157571222516601573051384151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210094963355468764068512201 157571222516601573051384151)
        ·
          refine ⟨236356833774902359577076227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157571222516601573051384151 236356833774902359577076227)
          ·
            refine ⟨354535250662353539365614341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236356833774902359577076227 354535250662353539365614341)
            ·
              refine ⟨66475359499191288631052689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 354535250662353539365614341 66475359499191288631052689)
              ·
                refine ⟨49856519624393466473289517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66475359499191288631052689 49856519624393466473289517)
                ·
                  refine ⟨18696194859147549927483569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49856519624393466473289517 18696194859147549927483569)
                  ·
                    refine ⟨14022146144360662445612677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18696194859147549927483569 14022146144360662445612677)
                    ·
                      refine ⟨2629152402067624208552377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14022146144360662445612677 2629152402067624208552377)
                      ·
                        rfl

theorem cell23_5120256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 4].length) (baseStart_5120256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5120256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5120256 prefixEnd_5120256 := by exact prefixLift 5120256
  have htrace : WordTrace (prefixWord ++ tailWord_5120256) baseStart_5120256 baseEnd_5120256 := by
    simpa [prefixWord, tailWord_5120256, baseEnd_5120256] using wordTrace_append hprefix tailTrace_5120256
  have hstable : (prefixWord ++ tailWord_5120256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5120256).length < 2 ^ (prefixWord ++ tailWord_5120256).sum := by decide
  have hdescent : baseEnd_5120256 < baseStart_5120256 := by decide
  rcases family_descends (prefixWord ++ tailWord_5120256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5120273 : List Nat := [1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 4]
def baseStart_5120273 : Nat := 118140960795 + 5120273 * 2 ^ 59
def prefixEnd_5120273 : Nat := 4983230072969 + 3 ^ 40 * 5120273 * 2
def baseEnd_5120273 : Nat := 2629161131238750642039799

theorem tailTrace_5120273 : CollatzResearch.WordTrace tailWord_5120273 prefixEnd_5120273 2629161131238750642039799 := by
  unfold tailWord_5120273
  simp only [CollatzResearch.WordTrace]
  refine ⟨186751698579132868853157473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124501132386088579235438315 186751698579132868853157473)
  ·
    refine ⟨140063773934349651639868105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186751698579132868853157473 140063773934349651639868105)
    ·
      refine ⟨105047830450762238729901079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140063773934349651639868105 105047830450762238729901079)
      ·
        refine ⟨157571745676143358094851619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105047830450762238729901079 157571745676143358094851619)
        ·
          refine ⟨236357618514215037142277429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157571745676143358094851619 236357618514215037142277429)
          ·
            refine ⟨22158526735707659732088509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 236357618514215037142277429 22158526735707659732088509)
            ·
              refine ⟨8309447525890372399533191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22158526735707659732088509 8309447525890372399533191)
              ·
                refine ⟨12464171288835558599299787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8309447525890372399533191 12464171288835558599299787)
                ·
                  refine ⟨18696256933253337898949681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12464171288835558599299787 18696256933253337898949681)
                  ·
                    refine ⟨14022192699940003424212261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18696256933253337898949681 14022192699940003424212261)
                    ·
                      refine ⟨2629161131238750642039799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14022192699940003424212261 2629161131238750642039799)
                      ·
                        rfl

theorem cell23_5120273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 4].length) (baseStart_5120273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5120273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5120273 prefixEnd_5120273 := by exact prefixLift 5120273
  have htrace : WordTrace (prefixWord ++ tailWord_5120273) baseStart_5120273 baseEnd_5120273 := by
    simpa [prefixWord, tailWord_5120273, baseEnd_5120273] using wordTrace_append hprefix tailTrace_5120273
  have hstable : (prefixWord ++ tailWord_5120273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5120273).length < 2 ^ (prefixWord ++ tailWord_5120273).sum := by decide
  have hdescent : baseEnd_5120273 < baseStart_5120273 := by decide
  rcases family_descends (prefixWord ++ tailWord_5120273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5120280 : List Nat := [2, 1, 2, 3, 1, 2, 4, 2, 1, 2, 3]
def baseStart_5120280 : Nat := 118140960795 + 5120280 * 2 ^ 59
def prefixEnd_5120280 : Nat := 4983230072969 + 3 ^ 40 * 5120280 * 2
def baseEnd_5120280 : Nat := 2629164725603332114652267

theorem tailTrace_5120280 : CollatzResearch.WordTrace tailWord_5120280 prefixEnd_5120280 2629164725603332114652267 := by
  unfold tailWord_5120280
  simp only [CollatzResearch.WordTrace]
  refine ⟨93375976945053754524331147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124501302593405006032441529 93375976945053754524331147)
  ·
    refine ⟨140063965417580631786496721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93375976945053754524331147 140063965417580631786496721)
    ·
      refine ⟨105047974063185473839872541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140063965417580631786496721 105047974063185473839872541)
      ·
        refine ⟨39392990273694552689952203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105047974063185473839872541 39392990273694552689952203)
        ·
          refine ⟨59089485410541829034928305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39392990273694552689952203 59089485410541829034928305)
          ·
            refine ⟨44317114057906371776196229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59089485410541829034928305 44317114057906371776196229)
            ·
              refine ⟨8309458885857444708036793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44317114057906371776196229 8309458885857444708036793)
              ·
                refine ⟨6232094164393083531027595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8309458885857444708036793 6232094164393083531027595)
                ·
                  refine ⟨9348141246589625296541393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6232094164393083531027595 9348141246589625296541393)
                  ·
                    refine ⟨7011105934942218972406045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9348141246589625296541393 7011105934942218972406045)
                    ·
                      refine ⟨2629164725603332114652267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7011105934942218972406045 2629164725603332114652267)
                      ·
                        rfl

theorem cell23_5120280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 2, 1, 2, 3].length) (baseStart_5120280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5120280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5120280 prefixEnd_5120280 := by exact prefixLift 5120280
  have htrace : WordTrace (prefixWord ++ tailWord_5120280) baseStart_5120280 baseEnd_5120280 := by
    simpa [prefixWord, tailWord_5120280, baseEnd_5120280] using wordTrace_append hprefix tailTrace_5120280
  have hstable : (prefixWord ++ tailWord_5120280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5120280).length < 2 ^ (prefixWord ++ tailWord_5120280).sum := by decide
  have hdescent : baseEnd_5120280 < baseStart_5120280 := by decide
  rcases family_descends (prefixWord ++ tailWord_5120280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5120321 : List Nat := [1, 2, 5, 2, 3, 1, 2, 1, 2, 4]
def baseStart_5120321 : Nat := 118140960795 + 5120321 * 2 ^ 59
def prefixEnd_5120321 : Nat := 4983230072969 + 3 ^ 40 * 5120321 * 2
def baseEnd_5120321 : Nat := 876395259436722151413193

theorem tailTrace_5120321 : CollatzResearch.WordTrace tailWord_5120321 prefixEnd_5120321 876395259436722151413193 := by
  unfold tailWord_5120321
  simp only [CollatzResearch.WordTrace]
  refine ⟨186753449282958973050904817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124502299521972648700603211 186753449282958973050904817)
  ·
    refine ⟨140065086962219229788178613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186753449282958973050904817 140065086962219229788178613)
    ·
      refine ⟨13131101902708052792641745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 140065086962219229788178613 13131101902708052792641745)
      ·
        refine ⟨9848326427031039594481309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13131101902708052792641745 9848326427031039594481309)
        ·
          refine ⟨3693122410136639847930491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9848326427031039594481309 3693122410136639847930491)
          ·
            refine ⟨5539683615204959771895737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3693122410136639847930491 5539683615204959771895737)
            ·
              refine ⟨4154762711403719828921803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5539683615204959771895737 4154762711403719828921803)
              ·
                refine ⟨6232144067105579743382705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4154762711403719828921803 6232144067105579743382705)
                ·
                  refine ⟨4674108050329184807537029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6232144067105579743382705 4674108050329184807537029)
                  ·
                    refine ⟨876395259436722151413193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4674108050329184807537029 876395259436722151413193)
                    ·
                      rfl

theorem cell23_5120321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_5120321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5120321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5120321 prefixEnd_5120321 := by exact prefixLift 5120321
  have htrace : WordTrace (prefixWord ++ tailWord_5120321) baseStart_5120321 baseEnd_5120321 := by
    simpa [prefixWord, tailWord_5120321, baseEnd_5120321] using wordTrace_append hprefix tailTrace_5120321
  have hstable : (prefixWord ++ tailWord_5120321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5120321).length < 2 ^ (prefixWord ++ tailWord_5120321).sum := by decide
  have hdescent : baseEnd_5120321 < baseStart_5120321 := by decide
  rcases family_descends (prefixWord ++ tailWord_5120321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5120337 : List Nat := [1, 2, 2, 1, 4, 2, 3, 2, 1, 3, 2]
def baseStart_5120337 : Nat := 118140960795 + 5120337 * 2 ^ 59
def prefixEnd_5120337 : Nat := 4983230072969 + 3 ^ 40 * 5120337 * 2
def baseEnd_5120337 : Nat := 2629193994000638391639505

theorem tailTrace_5120337 : CollatzResearch.WordTrace tailWord_5120337 prefixEnd_5120337 2629193994000638391639505 := by
  unfold tailWord_5120337
  simp only [CollatzResearch.WordTrace]
  refine ⟨186754032850901007783487265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124502688567267338522324843 186754032850901007783487265)
  ·
    refine ⟨140065524638175755837615449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186754032850901007783487265 140065524638175755837615449)
    ·
      refine ⟨105049143478631816878211587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140065524638175755837615449 105049143478631816878211587)
      ·
        refine ⟨157573715217947725317317381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105049143478631816878211587 157573715217947725317317381)
        ·
          refine ⟨29545071603365198496997009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 157573715217947725317317381 29545071603365198496997009)
          ·
            refine ⟨22158803702523898872747757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29545071603365198496997009 22158803702523898872747757)
            ·
              refine ⟨8309551388446462077280409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22158803702523898872747757 8309551388446462077280409)
              ·
                refine ⟨6232163541334846557960307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8309551388446462077280409 6232163541334846557960307)
                ·
                  refine ⟨9348245312002269836940461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6232163541334846557960307 9348245312002269836940461)
                  ·
                    refine ⟨3505591992000851188852673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9348245312002269836940461 3505591992000851188852673)
                    ·
                      refine ⟨2629193994000638391639505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3505591992000851188852673 2629193994000638391639505)
                      ·
                        rfl

theorem cell23_5120337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 2, 1, 3, 2].length) (baseStart_5120337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5120337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5120337 prefixEnd_5120337 := by exact prefixLift 5120337
  have htrace : WordTrace (prefixWord ++ tailWord_5120337) baseStart_5120337 baseEnd_5120337 := by
    simpa [prefixWord, tailWord_5120337, baseEnd_5120337] using wordTrace_append hprefix tailTrace_5120337
  have hstable : (prefixWord ++ tailWord_5120337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5120337).length < 2 ^ (prefixWord ++ tailWord_5120337).sum := by decide
  have hdescent : baseEnd_5120337 < baseStart_5120337 := by decide
  rcases family_descends (prefixWord ++ tailWord_5120337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5120383 : List Nat := [1, 1, 2, 2, 1, 1, 2, 5, 2, 3, 3]
def baseStart_5120383 : Nat := 118140960795 + 5120383 * 2 ^ 59
def prefixEnd_5120383 : Nat := 4983230072969 + 3 ^ 40 * 5120383 * 2
def baseEnd_5120383 : Nat := 2629217614110745211664293

theorem tailTrace_5120383 : CollatzResearch.WordTrace tailWord_5120383 prefixEnd_5120383 2629217614110745211664293 := by
  unfold tailWord_5120383
  simp only [CollatzResearch.WordTrace]
  refine ⟨186755710608734357639661803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124503807072489571759774535 186755710608734357639661803)
  ·
    refine ⟨280133565913101536459492705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186755710608734357639661803 280133565913101536459492705)
    ·
      refine ⟨210100174434826152344619529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 280133565913101536459492705 210100174434826152344619529)
      ·
        refine ⟨157575130826119614258464647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210100174434826152344619529 157575130826119614258464647)
        ·
          refine ⟨236362696239179421387696971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157575130826119614258464647 236362696239179421387696971)
          ·
            refine ⟨354544044358769132081545457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236362696239179421387696971 354544044358769132081545457)
            ·
              refine ⟨265908033269076849061159093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 354544044358769132081545457 265908033269076849061159093)
              ·
                refine ⟨24928878118975954599483665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 265908033269076849061159093 24928878118975954599483665)
                ·
                  refine ⟨18696658589231965949612749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24928878118975954599483665 18696658589231965949612749)
                  ·
                    refine ⟨7011246970961987231104781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18696658589231965949612749 7011246970961987231104781)
                    ·
                      refine ⟨2629217614110745211664293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7011246970961987231104781 2629217614110745211664293)
                      ·
                        rfl

theorem cell23_5120383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 2, 3, 3].length) (baseStart_5120383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5120383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5120383 prefixEnd_5120383 := by exact prefixLift 5120383
  have htrace : WordTrace (prefixWord ++ tailWord_5120383) baseStart_5120383 baseEnd_5120383 := by
    simpa [prefixWord, tailWord_5120383, baseEnd_5120383] using wordTrace_append hprefix tailTrace_5120383
  have hstable : (prefixWord ++ tailWord_5120383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5120383).length < 2 ^ (prefixWord ++ tailWord_5120383).sum := by decide
  have hdescent : baseEnd_5120383 < baseStart_5120383 := by decide
  rcases family_descends (prefixWord ++ tailWord_5120383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5120477 : List Nat := [1, 4, 3, 1, 1, 1, 3, 2, 2, 2, 3]
def baseStart_5120477 : Nat := 118140960795 + 5120477 * 2 ^ 59
def prefixEnd_5120477 : Nat := 4983230072969 + 3 ^ 40 * 5120477 * 2
def baseEnd_5120477 : Nat := 2629265881292267843888861

theorem tailTrace_5120477 : CollatzResearch.WordTrace tailWord_5120477 prefixEnd_5120477 2629265881292267843888861 := by
  unfold tailWord_5120477
  simp only [CollatzResearch.WordTrace]
  refine ⟨186759139070393811693583685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124506092713595874462389123 186759139070393811693583685)
  ·
    refine ⟨35017338575698839692546941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 186759139070393811693583685 35017338575698839692546941)
    ·
      refine ⟨13131501965887064884705103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35017338575698839692546941 13131501965887064884705103)
      ·
        refine ⟨19697252948830597327057655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13131501965887064884705103 19697252948830597327057655)
        ·
          refine ⟨29545879423245895990586483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19697252948830597327057655 29545879423245895990586483)
          ·
            refine ⟨44318819134868843985879725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29545879423245895990586483 44318819134868843985879725)
            ·
              refine ⟨16619557175575816494704897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44318819134868843985879725 16619557175575816494704897)
              ·
                refine ⟨12464667881681862371028673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16619557175575816494704897 12464667881681862371028673)
                ·
                  refine ⟨9348500911261396778271505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12464667881681862371028673 9348500911261396778271505)
                  ·
                    refine ⟨7011375683446047583703629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9348500911261396778271505 7011375683446047583703629)
                    ·
                      refine ⟨2629265881292267843888861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7011375683446047583703629 2629265881292267843888861)
                      ·
                        rfl

theorem cell23_5120477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_5120477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5120477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5120477 prefixEnd_5120477 := by exact prefixLift 5120477
  have htrace : WordTrace (prefixWord ++ tailWord_5120477) baseStart_5120477 baseEnd_5120477 := by
    simpa [prefixWord, tailWord_5120477, baseEnd_5120477] using wordTrace_append hprefix tailTrace_5120477
  have hstable : (prefixWord ++ tailWord_5120477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5120477).length < 2 ^ (prefixWord ++ tailWord_5120477).sum := by decide
  have hdescent : baseEnd_5120477 < baseStart_5120477 := by decide
  rcases family_descends (prefixWord ++ tailWord_5120477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5120517 : List Nat := [1, 3, 1, 1, 2, 2, 3, 3, 2, 3, 2]
def baseStart_5120517 : Nat := 118140960795 + 5120517 * 2 ^ 59
def prefixEnd_5120517 : Nat := 4983230072969 + 3 ^ 40 * 5120517 * 2
def baseEnd_5120517 : Nat := 2629286420518447687388677

theorem tailTrace_5120517 : CollatzResearch.WordTrace tailWord_5120517 prefixEnd_5120517 2629286420518447687388677 := by
  unfold tailWord_5120517
  simp only [CollatzResearch.WordTrace]
  refine ⟨186760597990248898525039805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124507065326832599016693203 186760597990248898525039805)
  ·
    refine ⟨70035224246343336946889927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186760597990248898525039805 70035224246343336946889927)
    ·
      refine ⟨105052836369515005420334891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70035224246343336946889927 105052836369515005420334891)
      ·
        refine ⟨157579254554272508130502337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105052836369515005420334891 157579254554272508130502337)
        ·
          refine ⟨118184440915704381097876753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157579254554272508130502337 118184440915704381097876753)
          ·
            refine ⟨88638330686778285823407565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118184440915704381097876753 88638330686778285823407565)
            ·
              refine ⟨33239374007541857183777837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88638330686778285823407565 33239374007541857183777837)
              ·
                refine ⟨12464765252828196443916689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33239374007541857183777837 12464765252828196443916689)
                ·
                  refine ⟨9348573939621147332937517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12464765252828196443916689 9348573939621147332937517)
                  ·
                    refine ⟨3505715227357930249851569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9348573939621147332937517 3505715227357930249851569)
                    ·
                      refine ⟨2629286420518447687388677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3505715227357930249851569 2629286420518447687388677)
                      ·
                        rfl

theorem cell23_5120517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 3, 2, 3, 2].length) (baseStart_5120517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5120517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5120517 prefixEnd_5120517 := by exact prefixLift 5120517
  have htrace : WordTrace (prefixWord ++ tailWord_5120517) baseStart_5120517 baseEnd_5120517 := by
    simpa [prefixWord, tailWord_5120517, baseEnd_5120517] using wordTrace_append hprefix tailTrace_5120517
  have hstable : (prefixWord ++ tailWord_5120517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5120517).length < 2 ^ (prefixWord ++ tailWord_5120517).sum := by decide
  have hdescent : baseEnd_5120517 < baseStart_5120517 := by decide
  rcases family_descends (prefixWord ++ tailWord_5120517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5120535 : List Nat := [1, 1, 3, 6, 2, 1, 2, 2, 1, 4]
def baseStart_5120535 : Nat := 118140960795 + 5120535 * 2 ^ 59
def prefixEnd_5120535 : Nat := 4983230072969 + 3 ^ 40 * 5120535 * 2
def baseEnd_5120535 : Nat := 876431887723409538987865

theorem tailTrace_5120535 : CollatzResearch.WordTrace tailWord_5120535 prefixEnd_5120535 876431887723409538987865 := by
  unfold tailWord_5120535
  simp only [CollatzResearch.WordTrace]
  refine ⟨186761254504183687599195059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124507503002789125066130039 186761254504183687599195059)
  ·
    refine ⟨280141881756275531398792589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186761254504183687599195059 280141881756275531398792589)
    ·
      refine ⟨105053205658603324274547221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 280141881756275531398792589 105053205658603324274547221)
      ·
        refine ⟨4924369015247030825369401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 105053205658603324274547221 4924369015247030825369401)
        ·
          refine ⟨3693276761435273119027051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4924369015247030825369401 3693276761435273119027051)
          ·
            refine ⟨5539915142152909678540577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3693276761435273119027051 5539915142152909678540577)
            ·
              refine ⟨4154936356614682258905433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5539915142152909678540577 4154936356614682258905433)
              ·
                refine ⟨3116202267461011694179075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4154936356614682258905433 3116202267461011694179075)
                ·
                  refine ⟨4674303401191517541268613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3116202267461011694179075 4674303401191517541268613)
                  ·
                    refine ⟨876431887723409538987865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4674303401191517541268613 876431887723409538987865)
                    ·
                      rfl

theorem cell23_5120535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 2, 2, 1, 4].length) (baseStart_5120535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5120535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5120535 prefixEnd_5120535 := by exact prefixLift 5120535
  have htrace : WordTrace (prefixWord ++ tailWord_5120535) baseStart_5120535 baseEnd_5120535 := by
    simpa [prefixWord, tailWord_5120535, baseEnd_5120535] using wordTrace_append hprefix tailTrace_5120535
  have hstable : (prefixWord ++ tailWord_5120535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5120535).length < 2 ^ (prefixWord ++ tailWord_5120535).sum := by decide
  have hdescent : baseEnd_5120535 < baseStart_5120535 := by decide
  rcases family_descends (prefixWord ++ tailWord_5120535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5120541 : List Nat := [1, 4, 2, 2, 1, 3, 1, 4, 1, 1, 3]
def baseStart_5120541 : Nat := 118140960795 + 5120541 * 2 ^ 59
def prefixEnd_5120541 : Nat := 4983230072969 + 3 ^ 40 * 5120541 * 2
def baseEnd_5120541 : Nat := 2629298744054155593488567

theorem tailTrace_5120541 : CollatzResearch.WordTrace tailWord_5120541 prefixEnd_5120541 2629298744054155593488567 := by
  unfold tailWord_5120541
  simp only [CollatzResearch.WordTrace]
  refine ⟨186761473342161950623913477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124507648894774633749275651 186761473342161950623913477)
  ·
    refine ⟨35017776251655365741983777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 186761473342161950623913477 35017776251655365741983777)
    ·
      refine ⟨26263332188741524306487833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35017776251655365741983777 26263332188741524306487833)
      ·
        refine ⟨19697499141556143229865875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26263332188741524306487833 19697499141556143229865875)
        ·
          refine ⟨29546248712334214844798813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19697499141556143229865875 29546248712334214844798813)
          ·
            refine ⟨11079843267125330566799555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29546248712334214844798813 11079843267125330566799555)
            ·
              refine ⟨16619764900687995850199333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11079843267125330566799555 16619764900687995850199333)
              ·
                refine ⟨3116205918878999221912375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16619764900687995850199333 3116205918878999221912375)
                ·
                  refine ⟨4674308878318498832868563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3116205918878999221912375 4674308878318498832868563)
                  ·
                    refine ⟨7011463317477748249302845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4674308878318498832868563 7011463317477748249302845)
                    ·
                      refine ⟨2629298744054155593488567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7011463317477748249302845 2629298744054155593488567)
                      ·
                        rfl

theorem cell23_5120541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 4, 1, 1, 3].length) (baseStart_5120541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5120541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5120541 prefixEnd_5120541 := by exact prefixLift 5120541
  have htrace : WordTrace (prefixWord ++ tailWord_5120541) baseStart_5120541 baseEnd_5120541 := by
    simpa [prefixWord, tailWord_5120541, baseEnd_5120541] using wordTrace_append hprefix tailTrace_5120541
  have hstable : (prefixWord ++ tailWord_5120541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5120541).length < 2 ^ (prefixWord ++ tailWord_5120541).sum := by decide
  have hdescent : baseEnd_5120541 < baseStart_5120541 := by decide
  rcases family_descends (prefixWord ++ tailWord_5120541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5120560 : List Nat := [2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 4]
def baseStart_5120560 : Nat := 118140960795 + 5120560 * 2 ^ 59
def prefixEnd_5120560 : Nat := 4983230072969 + 3 ^ 40 * 5120560 * 2
def baseEnd_5120560 : Nat := 2629308500186591019150979

theorem tailTrace_5120560 : CollatzResearch.WordTrace tailWord_5120560 prefixEnd_5120560 2629308500186591019150979 := by
  unfold tailWord_5120560
  simp only [CollatzResearch.WordTrace]
  refine ⟨93381083164546558434427567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124508110886062077912570089 93381083164546558434427567)
  ·
    refine ⟨140071624746819837651641351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93381083164546558434427567 140071624746819837651641351)
    ·
      refine ⟨210107437120229756477462027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140071624746819837651641351 210107437120229756477462027)
      ·
        refine ⟨315161155680344634716193041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210107437120229756477462027 315161155680344634716193041)
        ·
          refine ⟨236370866760258476037144781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 315161155680344634716193041 236370866760258476037144781)
          ·
            refine ⟨88639075035096928513929293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 236370866760258476037144781 88639075035096928513929293)
            ·
              refine ⟨33239653138161348192723485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88639075035096928513929293 33239653138161348192723485)
              ·
                refine ⟨12464869926810505572271307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33239653138161348192723485 12464869926810505572271307)
                ·
                  refine ⟨18697304890215758358406961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12464869926810505572271307 18697304890215758358406961)
                  ·
                    refine ⟨14022978667661818768805221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18697304890215758358406961 14022978667661818768805221)
                    ·
                      refine ⟨2629308500186591019150979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14022978667661818768805221 2629308500186591019150979)
                      ·
                        rfl

theorem cell23_5120560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 4].length) (baseStart_5120560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5120560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5120560 prefixEnd_5120560 := by exact prefixLift 5120560
  have htrace : WordTrace (prefixWord ++ tailWord_5120560) baseStart_5120560 baseEnd_5120560 := by
    simpa [prefixWord, tailWord_5120560, baseEnd_5120560] using wordTrace_append hprefix tailTrace_5120560
  have hstable : (prefixWord ++ tailWord_5120560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5120560).length < 2 ^ (prefixWord ++ tailWord_5120560).sum := by decide
  have hdescent : baseEnd_5120560 < baseStart_5120560 := by decide
  rcases family_descends (prefixWord ++ tailWord_5120560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5120567 : List Nat := [1, 1, 3, 1, 2, 3, 2, 4, 1, 2, 3]
def baseStart_5120567 : Nat := 118140960795 + 5120567 * 2 ^ 59
def prefixEnd_5120567 : Nat := 4983230072969 + 3 ^ 40 * 5120567 * 2
def baseEnd_5120567 : Nat := 2629312094551172491763447

theorem tailTrace_5120567 : CollatzResearch.WordTrace tailWord_5120567 prefixEnd_5120567 2629312094551172491763447 := by
  unfold tailWord_5120567
  simp only [CollatzResearch.WordTrace]
  refine ⟨186762421640067757064359955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124508281093378504709573303 186762421640067757064359955)
  ·
    refine ⟨280143632460101635596539933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186762421640067757064359955 280143632460101635596539933)
    ·
      refine ⟨105053862172538113348702475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 280143632460101635596539933 105053862172538113348702475)
      ·
        refine ⟨157580793258807170023053713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105053862172538113348702475 157580793258807170023053713)
        ·
          refine ⟨118185594944105377517290285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157580793258807170023053713 118185594944105377517290285)
          ·
            refine ⟨44319598104039516568983857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118185594944105377517290285 44319598104039516568983857)
            ·
              refine ⟨33239698578029637426737893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44319598104039516568983857 33239698578029637426737893)
              ·
                refine ⟨6232443483380557017513355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33239698578029637426737893 6232443483380557017513355)
                ·
                  refine ⟨9348665225070835526270033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6232443483380557017513355 9348665225070835526270033)
                  ·
                    refine ⟨7011498918803126644702525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9348665225070835526270033 7011498918803126644702525)
                    ·
                      refine ⟨2629312094551172491763447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7011498918803126644702525 2629312094551172491763447)
                      ·
                        rfl

theorem cell23_5120567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 4, 1, 2, 3].length) (baseStart_5120567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5120567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5120567 prefixEnd_5120567 := by exact prefixLift 5120567
  have htrace : WordTrace (prefixWord ++ tailWord_5120567) baseStart_5120567 baseEnd_5120567 := by
    simpa [prefixWord, tailWord_5120567, baseEnd_5120567] using wordTrace_append hprefix tailTrace_5120567
  have hstable : (prefixWord ++ tailWord_5120567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5120567).length < 2 ^ (prefixWord ++ tailWord_5120567).sum := by decide
  have hdescent : baseEnd_5120567 < baseStart_5120567 := by decide
  rcases family_descends (prefixWord ++ tailWord_5120567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5120577 : List Nat := [1, 2, 5, 1, 1, 2, 2, 2, 1, 2, 4]
def baseStart_5120577 : Nat := 118140960795 + 5120577 * 2 ^ 59
def prefixEnd_5120577 : Nat := 4983230072969 + 3 ^ 40 * 5120577 * 2
def baseEnd_5120577 : Nat := 2629317229357717452638401

theorem tailTrace_5120577 : CollatzResearch.WordTrace tailWord_5120577 prefixEnd_5120577 2629317229357717452638401 := by
  unfold tailWord_5120577
  simp only [CollatzResearch.WordTrace]
  refine ⟨186762786370031528772223985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124508524246687685848149323 186762786370031528772223985)
  ·
    refine ⟨140072089777523646579167989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186762786370031528772223985 140072089777523646579167989)
    ·
      refine ⟨13131758416642841866796999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 140072089777523646579167989 13131758416642841866796999)
      ·
        refine ⟨19697637624964262800195499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13131758416642841866796999 19697637624964262800195499)
        ·
          refine ⟨29546456437446394200293249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19697637624964262800195499 29546456437446394200293249)
          ·
            refine ⟨22159842328084795650219937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29546456437446394200293249 22159842328084795650219937)
            ·
              refine ⟨16619881746063596737664953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22159842328084795650219937 16619881746063596737664953)
              ·
                refine ⟨12464911309547697553248715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16619881746063596737664953 12464911309547697553248715)
                ·
                  refine ⟨18697366964321546329873073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12464911309547697553248715 18697366964321546329873073)
                  ·
                    refine ⟨14023025223241159747404805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18697366964321546329873073 14023025223241159747404805)
                    ·
                      refine ⟨2629317229357717452638401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14023025223241159747404805 2629317229357717452638401)
                      ·
                        rfl

theorem cell23_5120577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_5120577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5120577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5120577 prefixEnd_5120577 := by exact prefixLift 5120577
  have htrace : WordTrace (prefixWord ++ tailWord_5120577) baseStart_5120577 baseEnd_5120577 := by
    simpa [prefixWord, tailWord_5120577, baseEnd_5120577] using wordTrace_append hprefix tailTrace_5120577
  have hstable : (prefixWord ++ tailWord_5120577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5120577).length < 2 ^ (prefixWord ++ tailWord_5120577).sum := by decide
  have hdescent : baseEnd_5120577 < baseStart_5120577 := by decide
  rcases family_descends (prefixWord ++ tailWord_5120577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5120581 : List Nat := [1, 3, 1, 1, 1, 5, 1, 5, 1, 2, 2]
def baseStart_5120581 : Nat := 118140960795 + 5120581 * 2 ^ 59
def prefixEnd_5120581 : Nat := 4983230072969 + 3 ^ 40 * 5120581 * 2
def baseEnd_5120581 : Nat := 2629319283280335436988383

theorem tailTrace_5120581 : CollatzResearch.WordTrace tailWord_5120581 prefixEnd_5120581 2629319283280335436988383 := by
  unfold tailWord_5120581
  simp only [CollatzResearch.WordTrace]
  refine ⟨186762932262017037455369597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124508621508011358303579731 186762932262017037455369597)
  ·
    refine ⟨70036099598256389045763599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186762932262017037455369597 70036099598256389045763599)
    ·
      refine ⟨105054149397384583568645399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70036099598256389045763599 105054149397384583568645399)
      ·
        refine ⟨157581224096076875352968099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105054149397384583568645399 157581224096076875352968099)
        ·
          refine ⟨236371836144115313029452149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157581224096076875352968099 236371836144115313029452149)
          ·
            refine ⟨22159859638510810596511139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 236371836144115313029452149 22159859638510810596511139)
            ·
              refine ⟨33239789457766215894766709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22159859638510810596511139 33239789457766215894766709)
              ·
                refine ⟨3116230261665582740134379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33239789457766215894766709 3116230261665582740134379)
                ·
                  refine ⟨4674345392498374110201569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3116230261665582740134379 4674345392498374110201569)
                  ·
                    refine ⟨3505759044373780582651177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4674345392498374110201569 3505759044373780582651177)
                    ·
                      refine ⟨2629319283280335436988383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3505759044373780582651177 2629319283280335436988383)
                      ·
                        rfl

theorem cell23_5120581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 5, 1, 2, 2].length) (baseStart_5120581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5120581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5120581 prefixEnd_5120581 := by exact prefixLift 5120581
  have htrace : WordTrace (prefixWord ++ tailWord_5120581) baseStart_5120581 baseEnd_5120581 := by
    simpa [prefixWord, tailWord_5120581, baseEnd_5120581] using wordTrace_append hprefix tailTrace_5120581
  have hstable : (prefixWord ++ tailWord_5120581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5120581).length < 2 ^ (prefixWord ++ tailWord_5120581).sum := by decide
  have hdescent : baseEnd_5120581 < baseStart_5120581 := by decide
  rcases family_descends (prefixWord ++ tailWord_5120581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5120607 : List Nat := [1, 1, 2, 3, 1, 1, 1, 3, 5, 3, 2]
def baseStart_5120607 : Nat := 118140960795 + 5120607 * 2 ^ 59
def prefixEnd_5120607 : Nat := 4983230072969 + 3 ^ 40 * 5120607 * 2
def baseEnd_5120607 : Nat := 2629332633777352335263263

theorem tailTrace_5120607 : CollatzResearch.WordTrace tailWord_5120607 prefixEnd_5120607 2629332633777352335263263 := by
  unfold tailWord_5120607
  simp only [CollatzResearch.WordTrace]
  refine ⟨186763880559922843895816075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124509253706615229263877383 186763880559922843895816075)
  ·
    refine ⟨280145820839884265843724113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186763880559922843895816075 280145820839884265843724113)
    ·
      refine ⟨210109365629913199382793085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 280145820839884265843724113 210109365629913199382793085)
      ·
        refine ⟨78791012111217449768547407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 210109365629913199382793085 78791012111217449768547407)
        ·
          refine ⟨118186518166826174652821111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78791012111217449768547407 118186518166826174652821111)
          ·
            refine ⟨177279777250239261979231667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118186518166826174652821111 177279777250239261979231667)
            ·
              refine ⟨265919665875358892968847501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177279777250239261979231667 265919665875358892968847501)
              ·
                refine ⟨99719874703259584863317813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 265919665875358892968847501 99719874703259584863317813)
                ·
                  refine ⟨9348738253430586080936045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 99719874703259584863317813 9348738253430586080936045)
                  ·
                    refine ⟨3505776845036469780351017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9348738253430586080936045 3505776845036469780351017)
                    ·
                      refine ⟨2629332633777352335263263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3505776845036469780351017 2629332633777352335263263)
                      ·
                        rfl

theorem cell23_5120607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 5, 3, 2].length) (baseStart_5120607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5120607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5120607 prefixEnd_5120607 := by exact prefixLift 5120607
  have htrace : WordTrace (prefixWord ++ tailWord_5120607) baseStart_5120607 baseEnd_5120607 := by
    simpa [prefixWord, tailWord_5120607, baseEnd_5120607] using wordTrace_append hprefix tailTrace_5120607
  have hstable : (prefixWord ++ tailWord_5120607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5120607).length < 2 ^ (prefixWord ++ tailWord_5120607).sum := by decide
  have hdescent : baseEnd_5120607 < baseStart_5120607 := by decide
  rcases family_descends (prefixWord ++ tailWord_5120607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5120620 : List Nat := [2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 4]
def baseStart_5120620 : Nat := 118140960795 + 5120620 * 2 ^ 59
def prefixEnd_5120620 : Nat := 4983230072969 + 3 ^ 40 * 5120620 * 2
def baseEnd_5120620 : Nat := 2629339309025860784400703

theorem tailTrace_5120620 : CollatzResearch.WordTrace tailWord_5120620 prefixEnd_5120620 2629339309025860784400703 := by
  unfold tailWord_5120620
  simp only [CollatzResearch.WordTrace]
  refine ⟨93382177354437873558019657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124509569805917164744026209 93382177354437873558019657)
  ·
    refine ⟨70036633015828405168514743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93382177354437873558019657 70036633015828405168514743)
    ·
      refine ⟨105054949523742607752772115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70036633015828405168514743 105054949523742607752772115)
      ·
        refine ⟨157582424285613911629158173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105054949523742607752772115 157582424285613911629158173)
        ·
          refine ⟨59093409107105216860934315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 157582424285613911629158173 59093409107105216860934315)
          ·
            refine ⟨88640113660657825291401473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59093409107105216860934315 88640113660657825291401473)
            ·
              refine ⟨66480085245493368968551105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88640113660657825291401473 66480085245493368968551105)
              ·
                refine ⟨49860063934120026726413329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66480085245493368968551105 49860063934120026726413329)
                ·
                  refine ⟨37395047950590020044809997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49860063934120026726413329 37395047950590020044809997)
                  ·
                    refine ⟨14023142981471257516803749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37395047950590020044809997 14023142981471257516803749)
                    ·
                      refine ⟨2629339309025860784400703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14023142981471257516803749 2629339309025860784400703)
                      ·
                        rfl

theorem cell23_5120620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 4].length) (baseStart_5120620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5120620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5120620 prefixEnd_5120620 := by exact prefixLift 5120620
  have htrace : WordTrace (prefixWord ++ tailWord_5120620) baseStart_5120620 baseEnd_5120620 := by
    simpa [prefixWord, tailWord_5120620, baseEnd_5120620] using wordTrace_append hprefix tailTrace_5120620
  have hstable : (prefixWord ++ tailWord_5120620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5120620).length < 2 ^ (prefixWord ++ tailWord_5120620).sum := by decide
  have hdescent : baseEnd_5120620 < baseStart_5120620 := by decide
  rcases family_descends (prefixWord ++ tailWord_5120620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5120640 : List Nat := [2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 5]
def baseStart_5120640 : Nat := 118140960795 + 5120640 * 2 ^ 59
def prefixEnd_5120640 : Nat := 4983230072969 + 3 ^ 40 * 5120640 * 2
def baseEnd_5120640 : Nat := 2629349578638950706150611

theorem tailTrace_5120640 : CollatzResearch.WordTrace tailWord_5120640 prefixEnd_5120640 2629349578638950706150611 := by
  unfold tailWord_5120640
  simp only [CollatzResearch.WordTrace]
  refine ⟨93382542084401645265883687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124510056112535527021178249 93382542084401645265883687)
  ·
    refine ⟨140073813126602467898825531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93382542084401645265883687 140073813126602467898825531)
    ·
      refine ⟨210110719689903701848238297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140073813126602467898825531 210110719689903701848238297)
      ·
        refine ⟨157583039767427776386178723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210110719689903701848238297 157583039767427776386178723)
        ·
          refine ⟨236374559651141664579268085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157583039767427776386178723 236374559651141664579268085)
          ·
            refine ⟨22160114967294531054306383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 236374559651141664579268085 22160114967294531054306383)
            ·
              refine ⟨33240172450941796581459575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22160114967294531054306383 33240172450941796581459575)
              ·
                refine ⟨49860258676412694872189363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33240172450941796581459575 49860258676412694872189363)
                ·
                  refine ⟨74790388014619042308284045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49860258676412694872189363 74790388014619042308284045)
                  ·
                    refine ⟨28046395505482140865606517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 74790388014619042308284045 28046395505482140865606517)
                    ·
                      refine ⟨2629349578638950706150611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28046395505482140865606517 2629349578638950706150611)
                      ·
                        rfl

theorem cell23_5120640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 5].length) (baseStart_5120640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5120640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5120640 prefixEnd_5120640 := by exact prefixLift 5120640
  have htrace : WordTrace (prefixWord ++ tailWord_5120640) baseStart_5120640 baseEnd_5120640 := by
    simpa [prefixWord, tailWord_5120640, baseEnd_5120640] using wordTrace_append hprefix tailTrace_5120640
  have hstable : (prefixWord ++ tailWord_5120640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5120640).length < 2 ^ (prefixWord ++ tailWord_5120640).sum := by decide
  have hdescent : baseEnd_5120640 < baseStart_5120640 := by decide
  rcases family_descends (prefixWord ++ tailWord_5120640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5120714 : List Nat := [3, 1, 2, 1, 4, 1, 1, 1, 2, 5, 2]
def baseStart_5120714 : Nat := 118140960795 + 5120714 * 2 ^ 59
def prefixEnd_5120714 : Nat := 4983230072969 + 3 ^ 40 * 5120714 * 2
def baseEnd_5120714 : Nat := 2629387576207383416625271

theorem tailTrace_5120714 : CollatzResearch.WordTrace tailWord_5120714 prefixEnd_5120714 2629387576207383416625271 := by
  unfold tailWord_5120714
  simp only [CollatzResearch.WordTrace]
  refine ⟨46691945792633800292490299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124511855447023467446640797 46691945792633800292490299)
  ·
    refine ⟨70037918688950700438735449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46691945792633800292490299 70037918688950700438735449)
    ·
      refine ⟨52528439016713025329051587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70037918688950700438735449 52528439016713025329051587)
      ·
        refine ⟨78792658525069537993577381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52528439016713025329051587 78792658525069537993577381)
        ·
          refine ⟨14773623473450538373795759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78792658525069537993577381 14773623473450538373795759)
          ·
            refine ⟨22160435210175807560693639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14773623473450538373795759 22160435210175807560693639)
            ·
              refine ⟨33240652815263711341040459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22160435210175807560693639 33240652815263711341040459)
              ·
                refine ⟨49860979222895567011560689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33240652815263711341040459 49860979222895567011560689)
                ·
                  refine ⟨37395734417171675258670517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49860979222895567011560689 37395734417171675258670517)
                  ·
                    refine ⟨3505850101609844555500361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37395734417171675258670517 3505850101609844555500361)
                    ·
                      refine ⟨2629387576207383416625271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3505850101609844555500361 2629387576207383416625271)
                      ·
                        rfl

theorem cell23_5120714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 2, 5, 2].length) (baseStart_5120714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5120714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5120714 prefixEnd_5120714 := by exact prefixLift 5120714
  have htrace : WordTrace (prefixWord ++ tailWord_5120714) baseStart_5120714 baseEnd_5120714 := by
    simpa [prefixWord, tailWord_5120714, baseEnd_5120714] using wordTrace_append hprefix tailTrace_5120714
  have hstable : (prefixWord ++ tailWord_5120714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5120714).length < 2 ^ (prefixWord ++ tailWord_5120714).sum := by decide
  have hdescent : baseEnd_5120714 < baseStart_5120714 := by decide
  rcases family_descends (prefixWord ++ tailWord_5120714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5120744 : List Nat := [2, 1, 4, 1, 4, 1, 1, 1, 1, 3, 4]
def baseStart_5120744 : Nat := 118140960795 + 5120744 * 2 ^ 59
def prefixEnd_5120744 : Nat := 4983230072969 + 3 ^ 40 * 5120744 * 2
def baseEnd_5120744 : Nat := 2629402980627018299250133

theorem tailTrace_5120744 : CollatzResearch.WordTrace tailWord_5120744 prefixEnd_5120744 2629402980627018299250133 := by
  unfold tailWord_5120744
  simp only [CollatzResearch.WordTrace]
  refine ⟨93384438680213258146776643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124512584906951010862368857 93384438680213258146776643)
  ·
    refine ⟨140076658020319887220164965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93384438680213258146776643 140076658020319887220164965)
    ·
      refine ⟨26264373378809978853780931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 140076658020319887220164965 26264373378809978853780931)
      ·
        refine ⟨39396560068214968280671397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26264373378809978853780931 39396560068214968280671397)
        ·
          refine ⟨7386855012790306552625887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39396560068214968280671397 7386855012790306552625887)
          ·
            refine ⟨11080282519185459828938831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7386855012790306552625887 11080282519185459828938831)
            ·
              refine ⟨16620423778778189743408247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11080282519185459828938831 16620423778778189743408247)
              ·
                refine ⟨24930635668167284615112371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16620423778778189743408247 24930635668167284615112371)
                ·
                  refine ⟨37395953502250926922668557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24930635668167284615112371 37395953502250926922668557)
                  ·
                    refine ⟨14023482563344097596000709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37395953502250926922668557 14023482563344097596000709)
                    ·
                      refine ⟨2629402980627018299250133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14023482563344097596000709 2629402980627018299250133)
                      ·
                        rfl

theorem cell23_5120744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 1, 3, 4].length) (baseStart_5120744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5120744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5120744 prefixEnd_5120744 := by exact prefixLift 5120744
  have htrace : WordTrace (prefixWord ++ tailWord_5120744) baseStart_5120744 baseEnd_5120744 := by
    simpa [prefixWord, tailWord_5120744, baseEnd_5120744] using wordTrace_append hprefix tailTrace_5120744
  have hstable : (prefixWord ++ tailWord_5120744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5120744).length < 2 ^ (prefixWord ++ tailWord_5120744).sum := by decide
  have hdescent : baseEnd_5120744 < baseStart_5120744 := by decide
  rcases family_descends (prefixWord ++ tailWord_5120744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5120821 : List Nat := [1, 3, 3, 1, 3, 1, 1, 1, 4, 3, 2]
def baseStart_5120821 : Nat := 118140960795 + 5120821 * 2 ^ 59
def prefixEnd_5120821 : Nat := 4983230072969 + 3 ^ 40 * 5120821 * 2
def baseEnd_5120821 : Nat := 2629442518637414497987279

theorem tailTrace_5120821 : CollatzResearch.WordTrace tailWord_5120821 prefixEnd_5120821 2629442518637414497987279 := by
  unfold tailWord_5120821
  simp only [CollatzResearch.WordTrace]
  refine ⟨186771685781147558444106317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124514457187431705629404211 186771685781147558444106317)
  ·
    refine ⟨70039382167930334416539869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186771685781147558444106317 70039382167930334416539869)
    ·
      refine ⟨26264768312973875406202451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70039382167930334416539869 26264768312973875406202451)
      ·
        refine ⟨39397152469460813109303677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26264768312973875406202451 39397152469460813109303677)
        ·
          refine ⟨14773932176047804915988879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39397152469460813109303677 14773932176047804915988879)
          ·
            refine ⟨22160898264071707373983319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14773932176047804915988879 22160898264071707373983319)
            ·
              refine ⟨33241347396107561060974979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22160898264071707373983319 33241347396107561060974979)
              ·
                refine ⟨49862021094161341591462469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33241347396107561060974979 49862021094161341591462469)
                ·
                  refine ⟨9349128955155251548399213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49862021094161341591462469 9349128955155251548399213)
                  ·
                    refine ⟨3505923358183219330649705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9349128955155251548399213 3505923358183219330649705)
                    ·
                      refine ⟨2629442518637414497987279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3505923358183219330649705 2629442518637414497987279)
                      ·
                        rfl

theorem cell23_5120821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 4, 3, 2].length) (baseStart_5120821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5120821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5120821 prefixEnd_5120821 := by exact prefixLift 5120821
  have htrace : WordTrace (prefixWord ++ tailWord_5120821) baseStart_5120821 baseEnd_5120821 := by
    simpa [prefixWord, tailWord_5120821, baseEnd_5120821] using wordTrace_append hprefix tailTrace_5120821
  have hstable : (prefixWord ++ tailWord_5120821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5120821).length < 2 ^ (prefixWord ++ tailWord_5120821).sum := by decide
  have hdescent : baseEnd_5120821 < baseStart_5120821 := by decide
  rcases family_descends (prefixWord ++ tailWord_5120821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5120822 : List Nat := [5, 1, 2, 2, 2, 1, 3, 2, 1, 4]
def baseStart_5120822 : Nat := 118140960795 + 5120822 * 2 ^ 59
def prefixEnd_5120822 : Nat := 4983230072969 + 3 ^ 40 * 5120822 * 2
def baseEnd_5120822 : Nat := 876481010706022998024925

theorem tailTrace_5120822 : CollatzResearch.WordTrace tailWord_5120822 prefixEnd_5120822 876481010706022998024925 := by
  unfold tailWord_5120822
  simp only [CollatzResearch.WordTrace]
  refine ⟨11673232640883995975930795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 124514481502762623743261813 11673232640883995975930795)
  ·
    refine ⟨17509848961325993963896193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11673232640883995975930795 17509848961325993963896193)
    ·
      refine ⟨13132386720994495472922145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17509848961325993963896193 13132386720994495472922145)
      ·
        refine ⟨9849290040745871604691609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13132386720994495472922145 9849290040745871604691609)
        ·
          refine ⟨7386967530559403703518707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9849290040745871604691609 7386967530559403703518707)
          ·
            refine ⟨11080451295839105555278061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7386967530559403703518707 11080451295839105555278061)
            ·
              refine ⟨4155169235939664583229273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11080451295839105555278061 4155169235939664583229273)
              ·
                refine ⟨3116376926954748437421955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4155169235939664583229273 3116376926954748437421955)
                ·
                  refine ⟨4674565390432122656132933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3116376926954748437421955 4674565390432122656132933)
                  ·
                    refine ⟨876481010706022998024925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4674565390432122656132933 876481010706022998024925)
                    ·
                      rfl

theorem cell23_5120822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_5120822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5120822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5120822 prefixEnd_5120822 := by exact prefixLift 5120822
  have htrace : WordTrace (prefixWord ++ tailWord_5120822) baseStart_5120822 baseEnd_5120822 := by
    simpa [prefixWord, tailWord_5120822, baseEnd_5120822] using wordTrace_append hprefix tailTrace_5120822
  have hstable : (prefixWord ++ tailWord_5120822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5120822).length < 2 ^ (prefixWord ++ tailWord_5120822).sum := by decide
  have hdescent : baseEnd_5120822 < baseStart_5120822 := by decide
  rcases family_descends (prefixWord ++ tailWord_5120822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5120837 : List Nat := [1, 3, 1, 1, 1, 2, 2, 3, 3, 1, 5]
def baseStart_5120837 : Nat := 118140960795 + 5120837 * 2 ^ 59
def prefixEnd_5120837 : Nat := 4983230072969 + 3 ^ 40 * 5120837 * 2
def baseEnd_5120837 : Nat := 2629450734327886435387205

theorem tailTrace_5120837 : CollatzResearch.WordTrace tailWord_5120837 prefixEnd_5120837 2629450734327886435387205 := by
  unfold tailWord_5120837
  simp only [CollatzResearch.WordTrace]
  refine ⟨186772269349089593176688765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124514846232726395451125843 186772269349089593176688765)
  ·
    refine ⟨70039601005908597441258287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186772269349089593176688765 70039601005908597441258287)
    ·
      refine ⟨105059401508862896161887431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70039601005908597441258287 105059401508862896161887431)
      ·
        refine ⟨157589102263294344242831147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105059401508862896161887431 157589102263294344242831147)
        ·
          refine ⟨236383653394941516364246721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157589102263294344242831147 236383653394941516364246721)
          ·
            refine ⟨177287740046206137273185041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 236383653394941516364246721 177287740046206137273185041)
            ·
              refine ⟨132965805034654602954888781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 177287740046206137273185041 132965805034654602954888781)
              ·
                refine ⟨49862176887995476108083293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 132965805034654602954888781 49862176887995476108083293)
                ·
                  refine ⟨18698316332998303540531235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49862176887995476108083293 18698316332998303540531235)
                  ·
                    refine ⟨28047474499497455310796853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18698316332998303540531235 28047474499497455310796853)
                    ·
                      refine ⟨2629450734327886435387205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28047474499497455310796853 2629450734327886435387205)
                      ·
                        rfl

theorem cell23_5120837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 3, 1, 5].length) (baseStart_5120837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5120837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5120837 prefixEnd_5120837 := by exact prefixLift 5120837
  have htrace : WordTrace (prefixWord ++ tailWord_5120837) baseStart_5120837 baseEnd_5120837 := by
    simpa [prefixWord, tailWord_5120837, baseEnd_5120837] using wordTrace_append hprefix tailTrace_5120837
  have hstable : (prefixWord ++ tailWord_5120837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5120837).length < 2 ^ (prefixWord ++ tailWord_5120837).sum := by decide
  have hdescent : baseEnd_5120837 < baseStart_5120837 := by decide
  rcases family_descends (prefixWord ++ tailWord_5120837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5120847 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 7, 2, 4]
def baseStart_5120847 : Nat := 118140960795 + 5120847 * 2 ^ 59
def prefixEnd_5120847 : Nat := 4983230072969 + 3 ^ 40 * 5120847 * 2
def baseEnd_5120847 : Nat := 2629455869134431396262159

theorem tailTrace_5120847 : CollatzResearch.WordTrace tailWord_5120847 prefixEnd_5120847 2629455869134431396262159 := by
  unfold tailWord_5120847
  simp only [CollatzResearch.WordTrace]
  refine ⟨186772634079053364884552795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124515089386035576589701863 186772634079053364884552795)
  ·
    refine ⟨280158951118580047326829193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186772634079053364884552795 280158951118580047326829193)
    ·
      refine ⟨210119213338935035495121895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 280158951118580047326829193 210119213338935035495121895)
      ·
        refine ⟨315178820008402553242682843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210119213338935035495121895 315178820008402553242682843)
        ·
          refine ⟨472768230012603829864024265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315178820008402553242682843 472768230012603829864024265)
          ·
            refine ⟨354576172509452872398018199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 472768230012603829864024265 354576172509452872398018199)
            ·
              refine ⟨531864258764179308597027299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 354576172509452872398018199 531864258764179308597027299)
              ·
                refine ⟨797796388146268962895540949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 531864258764179308597027299 797796388146268962895540949)
                ·
                  refine ⟨18698352847178178817864241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 797796388146268962895540949 18698352847178178817864241)
                  ·
                    refine ⟨14023764635383634113398181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18698352847178178817864241 14023764635383634113398181)
                    ·
                      refine ⟨2629455869134431396262159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14023764635383634113398181 2629455869134431396262159)
                      ·
                        rfl

theorem cell23_5120847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 7, 2, 4].length) (baseStart_5120847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5120847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5120847 prefixEnd_5120847 := by exact prefixLift 5120847
  have htrace : WordTrace (prefixWord ++ tailWord_5120847) baseStart_5120847 baseEnd_5120847 := by
    simpa [prefixWord, tailWord_5120847, baseEnd_5120847] using wordTrace_append hprefix tailTrace_5120847
  have hstable : (prefixWord ++ tailWord_5120847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5120847).length < 2 ^ (prefixWord ++ tailWord_5120847).sum := by decide
  have hdescent : baseEnd_5120847 < baseStart_5120847 := by decide
  rcases family_descends (prefixWord ++ tailWord_5120847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5120851 : List Nat := [1, 1, 1, 2, 1, 1, 3, 6, 3, 2, 2]
def baseStart_5120851 : Nat := 118140960795 + 5120851 * 2 ^ 59
def prefixEnd_5120851 : Nat := 4983230072969 + 3 ^ 40 * 5120851 * 2
def baseEnd_5120851 : Nat := 2629457923057049380612141

theorem tailTrace_5120851 : CollatzResearch.WordTrace tailWord_5120851 prefixEnd_5120851 2629457923057049380612141 := by
  unfold tailWord_5120851
  simp only [CollatzResearch.WordTrace]
  refine ⟨186772779971038873567698407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124515186647359249045132271 186772779971038873567698407)
  ·
    refine ⟨280159169956558310351547611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186772779971038873567698407 280159169956558310351547611)
    ·
      refine ⟨420238754934837465527321417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280159169956558310351547611 420238754934837465527321417)
      ·
        refine ⟨315179066201128099145491063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 420238754934837465527321417 315179066201128099145491063)
        ·
          refine ⟨472768599301692148718236595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315179066201128099145491063 472768599301692148718236595)
          ·
            refine ⟨709152898952538223077354893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 472768599301692148718236595 709152898952538223077354893)
            ·
              refine ⟨265932337107201833654008085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 709152898952538223077354893 265932337107201833654008085)
              ·
                refine ⟨12465578301900085952531629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 265932337107201833654008085 12465578301900085952531629)
                ·
                  refine ⟨4674591863212532232199361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12465578301900085952531629 4674591863212532232199361)
                  ·
                    refine ⟨3505943897409399174149521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4674591863212532232199361 3505943897409399174149521)
                    ·
                      refine ⟨2629457923057049380612141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3505943897409399174149521 2629457923057049380612141)
                      ·
                        rfl

theorem cell23_5120851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 6, 3, 2, 2].length) (baseStart_5120851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5120851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5120851 prefixEnd_5120851 := by exact prefixLift 5120851
  have htrace : WordTrace (prefixWord ++ tailWord_5120851) baseStart_5120851 baseEnd_5120851 := by
    simpa [prefixWord, tailWord_5120851, baseEnd_5120851] using wordTrace_append hprefix tailTrace_5120851
  have hstable : (prefixWord ++ tailWord_5120851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5120851).length < 2 ^ (prefixWord ++ tailWord_5120851).sum := by decide
  have hdescent : baseEnd_5120851 < baseStart_5120851 := by decide
  rcases family_descends (prefixWord ++ tailWord_5120851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5120857 : List Nat := [1, 2, 1, 2, 2, 4, 2, 9]
def baseStart_5120857 : Nat := 118140960795 + 5120857 * 2 ^ 59
def prefixEnd_5120857 : Nat := 4983230072969 + 3 ^ 40 * 5120857 * 2
def baseEnd_5120857 : Nat := 97387444590406531745819

theorem tailTrace_5120857 : CollatzResearch.WordTrace tailWord_5120857 prefixEnd_5120857 97387444590406531745819 := by
  unfold tailWord_5120857
  simp only [CollatzResearch.WordTrace]
  refine ⟨186772998809017136592416825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124515332539344757728277883 186772998809017136592416825)
  ·
    refine ⟨140079749106762852444312619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186772998809017136592416825 140079749106762852444312619)
    ·
      refine ⟨210119623660144278666468929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140079749106762852444312619 210119623660144278666468929)
      ·
        refine ⟨157589717745108208999851697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210119623660144278666468929 157589717745108208999851697)
        ·
          refine ⟨118192288308831156749888773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157589717745108208999851697 118192288308831156749888773)
          ·
            refine ⟨22161054057905841890604145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 118192288308831156749888773 22161054057905841890604145)
            ·
              refine ⟨16620790543429381417953109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22161054057905841890604145 16620790543429381417953109)
              ·
                refine ⟨97387444590406531745819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16620790543429381417953109 97387444590406531745819)
                ·
                  rfl

theorem cell23_5120857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 9].length) (baseStart_5120857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5120857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5120857 prefixEnd_5120857 := by exact prefixLift 5120857
  have htrace : WordTrace (prefixWord ++ tailWord_5120857) baseStart_5120857 baseEnd_5120857 := by
    simpa [prefixWord, tailWord_5120857, baseEnd_5120857] using wordTrace_append hprefix tailTrace_5120857
  have hstable : (prefixWord ++ tailWord_5120857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5120857).length < 2 ^ (prefixWord ++ tailWord_5120857).sum := by decide
  have hdescent : baseEnd_5120857 < baseStart_5120857 := by decide
  rcases family_descends (prefixWord ++ tailWord_5120857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5120864 : List Nat := [2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 4]
def baseStart_5120864 : Nat := 118140960795 + 5120864 * 2 ^ 59
def prefixEnd_5120864 : Nat := 4983230072969 + 3 ^ 40 * 5120864 * 2
def baseEnd_5120864 : Nat := 2629464598305557829749581

theorem tailTrace_5120864 : CollatzResearch.WordTrace tailWord_5120864 prefixEnd_5120864 2629464598305557829749581 := by
  unfold tailWord_5120864
  simp only [CollatzResearch.WordTrace]
  refine ⟨93386627059995888393960823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124515502746661184525281097 93386627059995888393960823)
  ·
    refine ⟨140079940589993832590941235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93386627059995888393960823 140079940589993832590941235)
    ·
      refine ⟨210119910884990748886411853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140079940589993832590941235 210119910884990748886411853)
      ·
        refine ⟨78794966581871530832404445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 210119910884990748886411853 78794966581871530832404445)
        ·
          refine ⟨29548112468201824062151667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78794966581871530832404445 29548112468201824062151667)
          ·
            refine ⟨44322168702302736093227501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29548112468201824062151667 44322168702302736093227501)
            ·
              refine ⟨16620813263363526034960313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44322168702302736093227501 16620813263363526034960313)
              ·
                refine ⟨12465609947522644526220235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16620813263363526034960313 12465609947522644526220235)
                ·
                  refine ⟨18698414921283966789330353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12465609947522644526220235 18698414921283966789330353)
                  ·
                    refine ⟨14023811190962975091997765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18698414921283966789330353 14023811190962975091997765)
                    ·
                      refine ⟨2629464598305557829749581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14023811190962975091997765 2629464598305557829749581)
                      ·
                        rfl

theorem cell23_5120864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 4].length) (baseStart_5120864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5120864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5120864 prefixEnd_5120864 := by exact prefixLift 5120864
  have htrace : WordTrace (prefixWord ++ tailWord_5120864) baseStart_5120864 baseEnd_5120864 := by
    simpa [prefixWord, tailWord_5120864, baseEnd_5120864] using wordTrace_append hprefix tailTrace_5120864
  have hstable : (prefixWord ++ tailWord_5120864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5120864).length < 2 ^ (prefixWord ++ tailWord_5120864).sum := by decide
  have hdescent : baseEnd_5120864 < baseStart_5120864 := by decide
  rcases family_descends (prefixWord ++ tailWord_5120864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5120868 : List Nat := [2, 3, 1, 1, 4, 2, 3, 1, 1, 1, 4]
def baseStart_5120868 : Nat := 118140960795 + 5120868 * 2 ^ 59
def prefixEnd_5120868 : Nat := 4983230072969 + 3 ^ 40 * 5120868 * 2
def baseEnd_5120868 : Nat := 2629466652228175814099563

theorem tailTrace_5120868 : CollatzResearch.WordTrace tailWord_5120868 prefixEnd_5120868 2629466652228175814099563 := by
  unfold tailWord_5120868
  simp only [CollatzResearch.WordTrace]
  refine ⟨93386700005988642735533629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124515600007984856980711505 93386700005988642735533629)
  ·
    refine ⟨35020012502245741025825111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93386700005988642735533629 35020012502245741025825111)
    ·
      refine ⟨52530018753368611538737667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35020012502245741025825111 52530018753368611538737667)
      ·
        refine ⟨78795028130052917308106501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52530018753368611538737667 78795028130052917308106501)
        ·
          refine ⟨14774067774384921995269969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78795028130052917308106501 14774067774384921995269969)
          ·
            refine ⟨11080550830788691496452477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14774067774384921995269969 11080550830788691496452477)
            ·
              refine ⟨4155206561545759311169679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11080550830788691496452477 4155206561545759311169679)
              ·
                refine ⟨6232809842318638966754519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4155206561545759311169679 6232809842318638966754519)
                ·
                  refine ⟨9349214763477958450131779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6232809842318638966754519 9349214763477958450131779)
                  ·
                    refine ⟨14023822145216937675197669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9349214763477958450131779 14023822145216937675197669)
                    ·
                      refine ⟨2629466652228175814099563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14023822145216937675197669 2629466652228175814099563)
                      ·
                        rfl

theorem cell23_5120868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 3, 1, 1, 1, 4].length) (baseStart_5120868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5120868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5120868 prefixEnd_5120868 := by exact prefixLift 5120868
  have htrace : WordTrace (prefixWord ++ tailWord_5120868) baseStart_5120868 baseEnd_5120868 := by
    simpa [prefixWord, tailWord_5120868, baseEnd_5120868] using wordTrace_append hprefix tailTrace_5120868
  have hstable : (prefixWord ++ tailWord_5120868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5120868).length < 2 ^ (prefixWord ++ tailWord_5120868).sum := by decide
  have hdescent : baseEnd_5120868 < baseStart_5120868 := by decide
  rcases family_descends (prefixWord ++ tailWord_5120868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5120871 : List Nat := [1, 1, 5, 1, 2, 4, 1, 1, 1, 1, 5]
def baseStart_5120871 : Nat := 118140960795 + 5120871 * 2 ^ 59
def prefixEnd_5120871 : Nat := 4983230072969 + 3 ^ 40 * 5120871 * 2
def baseEnd_5120871 : Nat := 2629468192670139302362049

theorem tailTrace_5120871 : CollatzResearch.WordTrace tailWord_5120871 prefixEnd_5120871 2629468192670139302362049 := by
  unfold tailWord_5120871
  simp only [CollatzResearch.WordTrace]
  refine ⟨186773509430966416983426467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124515672953977611322284311 186773509430966416983426467)
  ·
    refine ⟨280160264146449625475139701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186773509430966416983426467 280160264146449625475139701)
    ·
      refine ⟨26265024763729652388294347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 280160264146449625475139701 26265024763729652388294347)
      ·
        refine ⟨39397537145594478582441521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26265024763729652388294347 39397537145594478582441521)
        ·
          refine ⟨29548152859195858936831141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39397537145594478582441521 29548152859195858936831141)
          ·
            refine ⟨5540278661099223550655839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29548152859195858936831141 5540278661099223550655839)
            ·
              refine ⟨8310417991648835325983759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5540278661099223550655839 8310417991648835325983759)
              ·
                refine ⟨12465626987473252988975639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8310417991648835325983759 12465626987473252988975639)
                ·
                  refine ⟨18698440481209879483463459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12465626987473252988975639 18698440481209879483463459)
                  ·
                    refine ⟨28047660721814819225195189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18698440481209879483463459 28047660721814819225195189)
                    ·
                      refine ⟨2629468192670139302362049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28047660721814819225195189 2629468192670139302362049)
                      ·
                        rfl

theorem cell23_5120871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 1, 1, 1, 5].length) (baseStart_5120871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5120871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5120871 prefixEnd_5120871 := by exact prefixLift 5120871
  have htrace : WordTrace (prefixWord ++ tailWord_5120871) baseStart_5120871 baseEnd_5120871 := by
    simpa [prefixWord, tailWord_5120871, baseEnd_5120871] using wordTrace_append hprefix tailTrace_5120871
  have hstable : (prefixWord ++ tailWord_5120871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5120871).length < 2 ^ (prefixWord ++ tailWord_5120871).sum := by decide
  have hdescent : baseEnd_5120871 < baseStart_5120871 := by decide
  rcases family_descends (prefixWord ++ tailWord_5120871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5120901 : List Nat := [1, 3, 1, 1, 3, 4, 2, 1, 1, 3, 3]
def baseStart_5120901 : Nat := 118140960795 + 5120901 * 2 ^ 59
def prefixEnd_5120901 : Nat := 4983230072969 + 3 ^ 40 * 5120901 * 2
def baseEnd_5120901 : Nat := 2629483597089774184986911

theorem tailTrace_5120901 : CollatzResearch.WordTrace tailWord_5120901 prefixEnd_5120901 2629483597089774184986911 := by
  unfold tailWord_5120901
  simp only [CollatzResearch.WordTrace]
  refine ⟨186774603620857732107018557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124516402413905154738012371 186774603620857732107018557)
  ·
    refine ⟨70040476357821649540131959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186774603620857732107018557 70040476357821649540131959)
    ·
      refine ⟨105060714536732474310197939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70040476357821649540131959 105060714536732474310197939)
      ·
        refine ⟨157591071805098711465296909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105060714536732474310197939 157591071805098711465296909)
        ·
          refine ⟨59096651926912016799486341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 157591071805098711465296909 59096651926912016799486341)
          ·
            refine ⟨11080622236296003149903689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59096651926912016799486341 11080622236296003149903689)
            ·
              refine ⟨8310466677222002362427767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11080622236296003149903689 8310466677222002362427767)
              ·
                refine ⟨12465700015833003543641651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8310466677222002362427767 12465700015833003543641651)
                ·
                  refine ⟨18698550023749505315462477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12465700015833003543641651 18698550023749505315462477)
                  ·
                    refine ⟨7011956258906064493298429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18698550023749505315462477 7011956258906064493298429)
                    ·
                      refine ⟨2629483597089774184986911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7011956258906064493298429 2629483597089774184986911)
                      ·
                        rfl

theorem cell23_5120901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 1, 1, 3, 3].length) (baseStart_5120901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5120901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5120901 prefixEnd_5120901 := by exact prefixLift 5120901
  have htrace : WordTrace (prefixWord ++ tailWord_5120901) baseStart_5120901 baseEnd_5120901 := by
    simpa [prefixWord, tailWord_5120901, baseEnd_5120901] using wordTrace_append hprefix tailTrace_5120901
  have hstable : (prefixWord ++ tailWord_5120901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5120901).length < 2 ^ (prefixWord ++ tailWord_5120901).sum := by decide
  have hdescent : baseEnd_5120901 < baseStart_5120901 := by decide
  rcases family_descends (prefixWord ++ tailWord_5120901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5120922 : List Nat := [3, 1, 1, 4, 4, 1, 2, 1, 1, 2, 3]
def baseStart_5120922 : Nat := 118140960795 + 5120922 * 2 ^ 59
def prefixEnd_5120922 : Nat := 4983230072969 + 3 ^ 40 * 5120922 * 2
def baseEnd_5120922 : Nat := 2629494380183518602824315

theorem tailTrace_5120922 : CollatzResearch.WordTrace tailWord_5120922 prefixEnd_5120922 2629494380183518602824315 := by
  unfold tailWord_5120922
  simp only [CollatzResearch.WordTrace]
  refine ⟨46693842388445413173383255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124516913035854435129022013 46693842388445413173383255)
  ·
    refine ⟨70040763582668119760074883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46693842388445413173383255 70040763582668119760074883)
    ·
      refine ⟨105061145374002179640112325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70040763582668119760074883 105061145374002179640112325)
      ·
        refine ⟨19698964757625408682521061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105061145374002179640112325 19698964757625408682521061)
        ·
          refine ⟨3693555892054764127972699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19698964757625408682521061 3693555892054764127972699)
          ·
            refine ⟨5540333838082146191959049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3693555892054764127972699 5540333838082146191959049)
            ·
              refine ⟨4155250378561609643969287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5540333838082146191959049 4155250378561609643969287)
              ·
                refine ⟨6232875567842414465953931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4155250378561609643969287 6232875567842414465953931)
                ·
                  refine ⟨9349313351763621698930897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6232875567842414465953931 9349313351763621698930897)
                  ·
                    refine ⟨7011985013822716274198173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9349313351763621698930897 7011985013822716274198173)
                    ·
                      refine ⟨2629494380183518602824315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7011985013822716274198173 2629494380183518602824315)
                      ·
                        rfl

theorem cell23_5120922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 2, 1, 1, 2, 3].length) (baseStart_5120922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5120922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5120922 prefixEnd_5120922 := by exact prefixLift 5120922
  have htrace : WordTrace (prefixWord ++ tailWord_5120922) baseStart_5120922 baseEnd_5120922 := by
    simpa [prefixWord, tailWord_5120922, baseEnd_5120922] using wordTrace_append hprefix tailTrace_5120922
  have hstable : (prefixWord ++ tailWord_5120922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5120922).length < 2 ^ (prefixWord ++ tailWord_5120922).sum := by decide
  have hdescent : baseEnd_5120922 < baseStart_5120922 := by decide
  rcases family_descends (prefixWord ++ tailWord_5120922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5120954 : List Nat := [3, 1, 1, 1, 2, 1, 3, 3, 2, 2, 4]
def baseStart_5120954 : Nat := 118140960795 + 5120954 * 2 ^ 59
def prefixEnd_5120954 : Nat := 4983230072969 + 3 ^ 40 * 5120954 * 2
def baseEnd_5120954 : Nat := 2629510811564462477624167

theorem tailTrace_5120954 : CollatzResearch.WordTrace tailWord_5120954 prefixEnd_5120954 2629510811564462477624167 := by
  unfold tailWord_5120954
  simp only [CollatzResearch.WordTrace]
  refine ⟨46694134172416430539674479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124517691126443814772465277 46694134172416430539674479)
  ·
    refine ⟨70041201258624645809511719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46694134172416430539674479 70041201258624645809511719)
    ·
      refine ⟨105061801887936968714267579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70041201258624645809511719 105061801887936968714267579)
      ·
        refine ⟨157592702831905453071401369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105061801887936968714267579 157592702831905453071401369)
        ·
          refine ⟨118194527123929089803551027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157592702831905453071401369 118194527123929089803551027)
          ·
            refine ⟨177291790685893634705326541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118194527123929089803551027 177291790685893634705326541)
            ·
              refine ⟨66484421507210113014497453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 177291790685893634705326541 66484421507210113014497453)
              ·
                refine ⟨24931658065203792380436545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66484421507210113014497453 24931658065203792380436545)
                ·
                  refine ⟨18698743548902844285327409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24931658065203792380436545 18698743548902844285327409)
                  ·
                    refine ⟨14024057661677133213995557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18698743548902844285327409 14024057661677133213995557)
                    ·
                      refine ⟨2629510811564462477624167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14024057661677133213995557 2629510811564462477624167)
                      ·
                        rfl

theorem cell23_5120954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 2, 2, 4].length) (baseStart_5120954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5120954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5120954 prefixEnd_5120954 := by exact prefixLift 5120954
  have htrace : WordTrace (prefixWord ++ tailWord_5120954) baseStart_5120954 baseEnd_5120954 := by
    simpa [prefixWord, tailWord_5120954, baseEnd_5120954] using wordTrace_append hprefix tailTrace_5120954
  have hstable : (prefixWord ++ tailWord_5120954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5120954).length < 2 ^ (prefixWord ++ tailWord_5120954).sum := by decide
  have hdescent : baseEnd_5120954 < baseStart_5120954 := by decide
  rcases family_descends (prefixWord ++ tailWord_5120954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5121085 : List Nat := [1, 4, 1, 3, 1, 4, 1, 1, 2, 2, 3]
def baseStart_5121085 : Nat := 118140960795 + 5121085 * 2 ^ 59
def prefixEnd_5121085 : Nat := 4983230072969 + 3 ^ 40 * 5121085 * 2
def baseEnd_5121085 : Nat := 2629578077530201465086065

theorem tailTrace_5121085 : CollatzResearch.WordTrace tailWord_5121085 prefixEnd_5121085 2629578077530201465086065 := by
  unfold tailWord_5121085
  simp only [CollatzResearch.WordTrace]
  refine ⟨186781314652191131531716709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124520876434794087687811139 186781314652191131531716709)
  ·
    refine ⟨35021496497285837162196883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 186781314652191131531716709 35021496497285837162196883)
    ·
      refine ⟨52532244745928755743295325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35021496497285837162196883 52532244745928755743295325)
      ·
        refine ⟨19699591779723283403735747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52532244745928755743295325 19699591779723283403735747)
        ·
          refine ⟨29549387669584925105603621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19699591779723283403735747 29549387669584925105603621)
          ·
            refine ⟨5540510188047173457300679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29549387669584925105603621 5540510188047173457300679)
            ·
              refine ⟨8310765282070760185951019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5540510188047173457300679 8310765282070760185951019)
              ·
                refine ⟨12466147923106140278926529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8310765282070760185951019 12466147923106140278926529)
                ·
                  refine ⟨9349610942329605209194897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12466147923106140278926529 9349610942329605209194897)
                  ·
                    refine ⟨7012208206747203906896173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9349610942329605209194897 7012208206747203906896173)
                    ·
                      refine ⟨2629578077530201465086065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7012208206747203906896173 2629578077530201465086065)
                      ·
                        rfl

theorem cell23_5121085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_5121085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5121085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5121085 prefixEnd_5121085 := by exact prefixLift 5121085
  have htrace : WordTrace (prefixWord ++ tailWord_5121085) baseStart_5121085 baseEnd_5121085 := by
    simpa [prefixWord, tailWord_5121085, baseEnd_5121085] using wordTrace_append hprefix tailTrace_5121085
  have hstable : (prefixWord ++ tailWord_5121085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5121085).length < 2 ^ (prefixWord ++ tailWord_5121085).sum := by decide
  have hdescent : baseEnd_5121085 < baseStart_5121085 := by decide
  rcases family_descends (prefixWord ++ tailWord_5121085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5121121 : List Nat := [1, 2, 3, 1, 1, 2, 2, 1, 5, 1, 4]
def baseStart_5121121 : Nat := 118140960795 + 5121121 * 2 ^ 59
def prefixEnd_5121121 : Nat := 4983230072969 + 3 ^ 40 * 5121121 * 2
def baseEnd_5121121 : Nat := 2629596562833763324235899

theorem tailTrace_5121121 : CollatzResearch.WordTrace tailWord_5121121 prefixEnd_5121121 2629596562833763324235899 := by
  unfold tailWord_5121121
  simp only [CollatzResearch.WordTrace]
  refine ⟨186782627680060709680027217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124521751786707139786684811 186782627680060709680027217)
  ·
    refine ⟨140086970760045532260020413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186782627680060709680027217 140086970760045532260020413)
    ·
      refine ⟨52532614035017074597507655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140086970760045532260020413 52532614035017074597507655)
      ·
        refine ⟨78798921052525611896261483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52532614035017074597507655 78798921052525611896261483)
        ·
          refine ⟨118198381578788417844392225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78798921052525611896261483 118198381578788417844392225)
          ·
            refine ⟨88648786184091313383294169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118198381578788417844392225 88648786184091313383294169)
            ·
              refine ⟨66486589638068485037470627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88648786184091313383294169 66486589638068485037470627)
              ·
                refine ⟨99729884457102727556205941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66486589638068485037470627 99729884457102727556205941)
                ·
                  refine ⟨9349676667853380708394307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 99729884457102727556205941 9349676667853380708394307)
                  ·
                    refine ⟨14024515001780071062591461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9349676667853380708394307 14024515001780071062591461)
                    ·
                      refine ⟨2629596562833763324235899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14024515001780071062591461 2629596562833763324235899)
                      ·
                        rfl

theorem cell23_5121121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 5, 1, 4].length) (baseStart_5121121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5121121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5121121 prefixEnd_5121121 := by exact prefixLift 5121121
  have htrace : WordTrace (prefixWord ++ tailWord_5121121) baseStart_5121121 baseEnd_5121121 := by
    simpa [prefixWord, tailWord_5121121, baseEnd_5121121] using wordTrace_append hprefix tailTrace_5121121
  have hstable : (prefixWord ++ tailWord_5121121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5121121).length < 2 ^ (prefixWord ++ tailWord_5121121).sum := by decide
  have hdescent : baseEnd_5121121 < baseStart_5121121 := by decide
  rcases family_descends (prefixWord ++ tailWord_5121121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5121138 : List Nat := [3, 2, 1, 2, 2, 1, 1, 1, 2, 6, 2]
def baseStart_5121138 : Nat := 118140960795 + 5121138 * 2 ^ 59
def prefixEnd_5121138 : Nat := 4983230072969 + 3 ^ 40 * 5121138 * 2
def baseEnd_5121138 : Nat := 2629605292004889757723321

theorem tailTrace_5121138 : CollatzResearch.WordTrace tailWord_5121138 prefixEnd_5121138 2629605292004889757723321 := by
  unfold tailWord_5121138
  simp only [CollatzResearch.WordTrace]
  refine ⟨46695811930249780395849017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124522165147332747722264045 46695811930249780395849017)
  ·
    refine ⟨35021858947687335296886763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46695811930249780395849017 35021858947687335296886763)
    ·
      refine ⟨52532788421531002945330145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35021858947687335296886763 52532788421531002945330145)
      ·
        refine ⟨39399591316148252208997609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52532788421531002945330145 39399591316148252208997609)
        ·
          refine ⟨29549693487111189156748207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39399591316148252208997609 29549693487111189156748207)
          ·
            refine ⟨44324540230666783735122311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29549693487111189156748207 44324540230666783735122311)
            ·
              refine ⟨66486810346000175602683467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44324540230666783735122311 66486810346000175602683467)
              ·
                refine ⟨99730215519000263404025201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66486810346000175602683467 99730215519000263404025201)
                ·
                  refine ⟨74797661639250197553018901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99730215519000263404025201 74797661639250197553018901)
                  ·
                    refine ⟨3506140389339853010297761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 74797661639250197553018901 3506140389339853010297761)
                    ·
                      refine ⟨2629605292004889757723321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3506140389339853010297761 2629605292004889757723321)
                      ·
                        rfl

theorem cell23_5121138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 2, 6, 2].length) (baseStart_5121138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5121138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5121138 prefixEnd_5121138 := by exact prefixLift 5121138
  have htrace : WordTrace (prefixWord ++ tailWord_5121138) baseStart_5121138 baseEnd_5121138 := by
    simpa [prefixWord, tailWord_5121138, baseEnd_5121138] using wordTrace_append hprefix tailTrace_5121138
  have hstable : (prefixWord ++ tailWord_5121138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5121138).length < 2 ^ (prefixWord ++ tailWord_5121138).sum := by decide
  have hdescent : baseEnd_5121138 < baseStart_5121138 := by decide
  rcases family_descends (prefixWord ++ tailWord_5121138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5121161 : List Nat := [1, 2, 1, 1, 4, 5, 9]
def baseStart_5121161 : Nat := 118140960795 + 5121161 * 2 ^ 59
def prefixEnd_5121161 : Nat := 4983230072969 + 3 ^ 40 * 5121161 * 2
def baseEnd_5121161 : Nat := 32464408667406705774515

theorem tailTrace_5121161 : CollatzResearch.WordTrace tailWord_5121161 prefixEnd_5121161 32464408667406705774515 := by
  unfold tailWord_5121161
  simp only [CollatzResearch.WordTrace]
  refine ⟨186784086599915796511483337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124522724399943864340988891 186784086599915796511483337)
  ·
    refine ⟨140088064949936847383612503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186784086599915796511483337 140088064949936847383612503)
    ·
      refine ⟨210132097424905271075418755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140088064949936847383612503 210132097424905271075418755)
      ·
        refine ⟨315198146137357906613128133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210132097424905271075418755 315198146137357906613128133)
        ·
          refine ⟨59099652400754607489961525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 315198146137357906613128133 59099652400754607489961525)
          ·
            refine ⟨5540592412570744452183893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59099652400754607489961525 5540592412570744452183893)
            ·
              refine ⟨32464408667406705774515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5540592412570744452183893 32464408667406705774515)
              ·
                rfl

theorem cell23_5121161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 9].length) (baseStart_5121161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5121161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5121161 prefixEnd_5121161 := by exact prefixLift 5121161
  have htrace : WordTrace (prefixWord ++ tailWord_5121161) baseStart_5121161 baseEnd_5121161 := by
    simpa [prefixWord, tailWord_5121161, baseEnd_5121161] using wordTrace_append hprefix tailTrace_5121161
  have hstable : (prefixWord ++ tailWord_5121161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5121161).length < 2 ^ (prefixWord ++ tailWord_5121161).sum := by decide
  have hdescent : baseEnd_5121161 < baseStart_5121161 := by decide
  rcases family_descends (prefixWord ++ tailWord_5121161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5121178 : List Nat := [3, 1, 1, 5, 1, 2, 2, 8]
def baseStart_5121178 : Nat := 118140960795 + 5121178 * 2 ^ 59
def prefixEnd_5121178 : Nat := 4983230072969 + 3 ^ 40 * 5121178 * 2
def baseEnd_5121178 : Nat := 97393549304854429674931

theorem tailTrace_5121178 : CollatzResearch.WordTrace tailWord_5121178 prefixEnd_5121178 97393549304854429674931 := by
  unfold tailWord_5121178
  simp only [CollatzResearch.WordTrace]
  refine ⟨46696176660213552103713047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124523137760569472276568125 46696176660213552103713047)
  ·
    refine ⟨70044264990320328155569571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46696176660213552103713047 70044264990320328155569571)
    ·
      refine ⟨105066397485480492233354357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70044264990320328155569571 105066397485480492233354357)
      ·
        refine ⟨9849974764263796146876971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 105066397485480492233354357 9849974764263796146876971)
        ·
          refine ⟨14774962146395694220315457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9849974764263796146876971 14774962146395694220315457)
          ·
            refine ⟨11081221609796770665236593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14774962146395694220315457 11081221609796770665236593)
            ·
              refine ⟨8310916207347577998927445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11081221609796770665236593 8310916207347577998927445)
              ·
                refine ⟨97393549304854429674931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8310916207347577998927445 97393549304854429674931)
                ·
                  rfl

theorem cell23_5121178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 8].length) (baseStart_5121178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5121178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5121178 prefixEnd_5121178 := by exact prefixLift 5121178
  have htrace : WordTrace (prefixWord ++ tailWord_5121178) baseStart_5121178 baseEnd_5121178 := by
    simpa [prefixWord, tailWord_5121178, baseEnd_5121178] using wordTrace_append hprefix tailTrace_5121178
  have hstable : (prefixWord ++ tailWord_5121178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5121178).length < 2 ^ (prefixWord ++ tailWord_5121178).sum := by decide
  have hdescent : baseEnd_5121178 < baseStart_5121178 := by decide
  rcases family_descends (prefixWord ++ tailWord_5121178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5121181 : List Nat := [1, 4, 2, 1, 1, 2, 1, 1, 2, 2, 6]
def baseStart_5121181 : Nat := 118140960795 + 5121181 * 2 ^ 59
def prefixEnd_5121181 : Nat := 4983230072969 + 3 ^ 40 * 5121181 * 2
def baseEnd_5121181 : Nat := 2629627371673033089485623

theorem tailTrace_5121181 : CollatzResearch.WordTrace tailWord_5121181 prefixEnd_5121181 2629627371673033089485623 := by
  unfold tailWord_5121181
  simp only [CollatzResearch.WordTrace]
  refine ⟨186784816059843339927211397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124523210706562226618140931 186784816059843339927211397)
  ·
    refine ⟨35022153011220626236352137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 186784816059843339927211397 35022153011220626236352137)
    ·
      refine ⟨26266614758415469677264103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35022153011220626236352137 26266614758415469677264103)
      ·
        refine ⟨39399922137623204515896155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26266614758415469677264103 39399922137623204515896155)
        ·
          refine ⟨59099883206434806773844233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39399922137623204515896155 59099883206434806773844233)
          ·
            refine ⟨44324912404826105080383175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59099883206434806773844233 44324912404826105080383175)
            ·
              refine ⟨66487368607239157620574763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44324912404826105080383175 66487368607239157620574763)
              ·
                refine ⟨99731052910858736430862145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66487368607239157620574763 99731052910858736430862145)
                ·
                  refine ⟨74798289683144052323146609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99731052910858736430862145 74798289683144052323146609)
                  ·
                    refine ⟨56098717262358039242359957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 74798289683144052323146609 56098717262358039242359957)
                    ·
                      refine ⟨2629627371673033089485623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56098717262358039242359957 2629627371673033089485623)
                      ·
                        rfl

theorem cell23_5121181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_5121181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5121181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5121181 prefixEnd_5121181 := by exact prefixLift 5121181
  have htrace : WordTrace (prefixWord ++ tailWord_5121181) baseStart_5121181 baseEnd_5121181 := by
    simpa [prefixWord, tailWord_5121181, baseEnd_5121181] using wordTrace_append hprefix tailTrace_5121181
  have hstable : (prefixWord ++ tailWord_5121181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5121181).length < 2 ^ (prefixWord ++ tailWord_5121181).sum := by decide
  have hdescent : baseEnd_5121181 < baseStart_5121181 := by decide
  rcases family_descends (prefixWord ++ tailWord_5121181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5121182 : List Nat := [4, 3, 1, 1, 2, 2, 1, 3, 2, 4]
def baseStart_5121182 : Nat := 118140960795 + 5121182 * 2 ^ 59
def prefixEnd_5121182 : Nat := 4983230072969 + 3 ^ 40 * 5121182 * 2
def baseEnd_5121182 : Nat := 876542628384562528524373

theorem tailTrace_5121182 : CollatzResearch.WordTrace tailWord_5121182 prefixEnd_5121182 876542628384562528524373 := by
  unfold tailWord_5121182
  simp only [CollatzResearch.WordTrace]
  refine ⟨23348106566604964637249725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124523235021893144731998533 23348106566604964637249725)
  ·
    refine ⟨8755539962476861738968647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23348106566604964637249725 8755539962476861738968647)
    ·
      refine ⟨13133309943715292608452971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8755539962476861738968647 13133309943715292608452971)
      ·
        refine ⟨19699964915572938912679457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13133309943715292608452971 19699964915572938912679457)
        ·
          refine ⟨14774973686679704184509593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19699964915572938912679457 14774973686679704184509593)
          ·
            refine ⟨11081230265009778138382195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14774973686679704184509593 11081230265009778138382195)
            ·
              refine ⟨16621845397514667207573293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11081230265009778138382195 16621845397514667207573293)
              ·
                refine ⟨6233192024068000202839985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16621845397514667207573293 6233192024068000202839985)
                ·
                  refine ⟨4674894018051000152129989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6233192024068000202839985 4674894018051000152129989)
                  ·
                    refine ⟨876542628384562528524373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4674894018051000152129989 876542628384562528524373)
                    ·
                      rfl

theorem cell23_5121182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_5121182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5121182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5121182 prefixEnd_5121182 := by exact prefixLift 5121182
  have htrace : WordTrace (prefixWord ++ tailWord_5121182) baseStart_5121182 baseEnd_5121182 := by
    simpa [prefixWord, tailWord_5121182, baseEnd_5121182] using wordTrace_append hprefix tailTrace_5121182
  have hstable : (prefixWord ++ tailWord_5121182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5121182).length < 2 ^ (prefixWord ++ tailWord_5121182).sum := by decide
  have hdescent : baseEnd_5121182 < baseStart_5121182 := by decide
  rcases family_descends (prefixWord ++ tailWord_5121182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5121206 : List Nat := [5, 1, 3, 2, 1, 1, 3, 1, 1, 1, 4]
def baseStart_5121206 : Nat := 118140960795 + 5121206 * 2 ^ 59
def prefixEnd_5121206 : Nat := 4983230072969 + 3 ^ 40 * 5121206 * 2
def baseEnd_5121206 : Nat := 2629640208689395491673009

theorem tailTrace_5121206 : CollatzResearch.WordTrace tailWord_5121206 prefixEnd_5121206 2629640208689395491673009 := by
  unfold tailWord_5121206
  simp only [CollatzResearch.WordTrace]
  refine ⟨11674107992797048074804467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 124523818589835179464580981 11674107992797048074804467)
  ·
    refine ⟨17511161989195572112206701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11674107992797048074804467 17511161989195572112206701)
    ·
      refine ⟨6566685745948339542077513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17511161989195572112206701 6566685745948339542077513)
      ·
        refine ⟨4925014309461254656558135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6566685745948339542077513 4925014309461254656558135)
        ·
          refine ⟨7387521464191881984837203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4925014309461254656558135 7387521464191881984837203)
          ·
            refine ⟨11081282196287822977255805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7387521464191881984837203 11081282196287822977255805)
            ·
              refine ⟨4155480823607933616470927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11081282196287822977255805 4155480823607933616470927)
              ·
                refine ⟨6233221235411900424706391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4155480823607933616470927 6233221235411900424706391)
                ·
                  refine ⟨9349831853117850637059587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6233221235411900424706391 9349831853117850637059587)
                  ·
                    refine ⟨14024747779676775955589381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9349831853117850637059587 14024747779676775955589381)
                    ·
                      refine ⟨2629640208689395491673009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14024747779676775955589381 2629640208689395491673009)
                      ·
                        rfl

theorem cell23_5121206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_5121206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5121206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5121206 prefixEnd_5121206 := by exact prefixLift 5121206
  have htrace : WordTrace (prefixWord ++ tailWord_5121206) baseStart_5121206 baseEnd_5121206 := by
    simpa [prefixWord, tailWord_5121206, baseEnd_5121206] using wordTrace_append hprefix tailTrace_5121206
  have hstable : (prefixWord ++ tailWord_5121206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5121206).length < 2 ^ (prefixWord ++ tailWord_5121206).sum := by decide
  have hdescent : baseEnd_5121206 < baseStart_5121206 := by decide
  rcases family_descends (prefixWord ++ tailWord_5121206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5121215 : List Nat := [1, 1, 2, 2, 2, 2, 2, 5, 1, 3, 2]
def baseStart_5121215 : Nat := 118140960795 + 5121215 * 2 ^ 59
def prefixEnd_5121215 : Nat := 4983230072969 + 3 ^ 40 * 5121215 * 2
def baseEnd_5121215 : Nat := 2629644830015285956460467

theorem tailTrace_5121215 : CollatzResearch.WordTrace tailWord_5121215 prefixEnd_5121215 2629644830015285956460467 := by
  unfold tailWord_5121215
  simp only [CollatzResearch.WordTrace]
  refine ⟨186786056141720163733949099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124524037427813442489299399 186786056141720163733949099)
  ·
    refine ⟨280179084212580245600923649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186786056141720163733949099 280179084212580245600923649)
    ·
      refine ⟨210134313159435184200692737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 280179084212580245600923649 210134313159435184200692737)
      ·
        refine ⟨157600734869576388150519553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210134313159435184200692737 157600734869576388150519553)
        ·
          refine ⟨118200551152182291112889665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157600734869576388150519553 118200551152182291112889665)
          ·
            refine ⟨88650413364136718334667249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118200551152182291112889665 88650413364136718334667249)
            ·
              refine ⟨66487810023102538751000437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88650413364136718334667249 66487810023102538751000437)
              ·
                refine ⟨6233232189665863007906291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66487810023102538751000437 6233232189665863007906291)
                ·
                  refine ⟨9349848284498794511859437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6233232189665863007906291 9349848284498794511859437)
                  ·
                    refine ⟨3506193106687047941947289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9349848284498794511859437 3506193106687047941947289)
                    ·
                      refine ⟨2629644830015285956460467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3506193106687047941947289 2629644830015285956460467)
                      ·
                        rfl

theorem cell23_5121215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 5, 1, 3, 2].length) (baseStart_5121215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5121215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5121215 prefixEnd_5121215 := by exact prefixLift 5121215
  have htrace : WordTrace (prefixWord ++ tailWord_5121215) baseStart_5121215 baseEnd_5121215 := by
    simpa [prefixWord, tailWord_5121215, baseEnd_5121215] using wordTrace_append hprefix tailTrace_5121215
  have hstable : (prefixWord ++ tailWord_5121215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5121215).length < 2 ^ (prefixWord ++ tailWord_5121215).sum := by decide
  have hdescent : baseEnd_5121215 < baseStart_5121215 := by decide
  rcases family_descends (prefixWord ++ tailWord_5121215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5121221 : List Nat := [1, 3, 1, 1, 1, 1, 3, 4, 2, 6]
def baseStart_5121221 : Nat := 118140960795 + 5121221 * 2 ^ 59
def prefixEnd_5121221 : Nat := 4983230072969 + 3 ^ 40 * 5121221 * 2
def baseEnd_5121221 : Nat := 876549303633070977661813

theorem tailTrace_5121221 : CollatzResearch.WordTrace tailWord_5121221 prefixEnd_5121221 876549303633070977661813 := by
  unfold tailWord_5121221
  simp only [CollatzResearch.WordTrace]
  refine ⟨186786274979698426758667517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124524183319798951172445011 186786274979698426758667517)
  ·
    refine ⟨70044853117386910034500319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186786274979698426758667517 70044853117386910034500319)
    ·
      refine ⟨105067279676080365051750479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70044853117386910034500319 105067279676080365051750479)
      ·
        refine ⟨157600919514120547577625719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105067279676080365051750479 157600919514120547577625719)
        ·
          refine ⟨236401379271180821366438579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157600919514120547577625719 236401379271180821366438579)
          ·
            refine ⟨354602068906771232049657869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236401379271180821366438579 354602068906771232049657869)
            ·
              refine ⟨132975775840039212018621701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 354602068906771232049657869 132975775840039212018621701)
              ·
                refine ⟨24932957970007352253491569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 132975775840039212018621701 24932957970007352253491569)
                ·
                  refine ⟨18699718477505514190118677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24932957970007352253491569 18699718477505514190118677)
                  ·
                    refine ⟨876549303633070977661813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18699718477505514190118677 876549303633070977661813)
                    ·
                      rfl

theorem cell23_5121221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 2, 6].length) (baseStart_5121221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5121221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5121221 prefixEnd_5121221 := by exact prefixLift 5121221
  have htrace : WordTrace (prefixWord ++ tailWord_5121221) baseStart_5121221 baseEnd_5121221 := by
    simpa [prefixWord, tailWord_5121221, baseEnd_5121221] using wordTrace_append hprefix tailTrace_5121221
  have hstable : (prefixWord ++ tailWord_5121221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5121221).length < 2 ^ (prefixWord ++ tailWord_5121221).sum := by decide
  have hdescent : baseEnd_5121221 < baseStart_5121221 := by decide
  rcases family_descends (prefixWord ++ tailWord_5121221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5121229 : List Nat := [1, 6, 2, 2, 2, 1, 1, 8]
def baseStart_5121229 : Nat := 118140960795 + 5121229 * 2 ^ 59
def prefixEnd_5121229 : Nat := 4983230072969 + 3 ^ 40 * 5121229 * 2
def baseEnd_5121229 : Nat := 97394519212757366729089

theorem tailTrace_5121229 : CollatzResearch.WordTrace tailWord_5121229 prefixEnd_5121229 97394519212757366729089 := by
  unfold tailWord_5121229
  simp only [CollatzResearch.WordTrace]
  refine ⟨186786566763669444124958741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124524377842446296083305827 186786566763669444124958741)
  ·
    refine ⟨8755620317047005193357441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 186786566763669444124958741 8755620317047005193357441)
    ·
      refine ⟨6566715237785253895018081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8755620317047005193357441 6566715237785253895018081)
      ·
        refine ⟨4925036428338940421263561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6566715237785253895018081 4925036428338940421263561)
        ·
          refine ⟨3693777321254205315947671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4925036428338940421263561 3693777321254205315947671)
          ·
            refine ⟨5540665981881307973921507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3693777321254205315947671 5540665981881307973921507)
            ·
              refine ⟨8310998972821961960882261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5540665981881307973921507 8310998972821961960882261)
              ·
                refine ⟨97394519212757366729089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8310998972821961960882261 97394519212757366729089)
                ·
                  rfl

theorem cell23_5121229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 8].length) (baseStart_5121229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5121229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5121229 prefixEnd_5121229 := by exact prefixLift 5121229
  have htrace : WordTrace (prefixWord ++ tailWord_5121229) baseStart_5121229 baseEnd_5121229 := by
    simpa [prefixWord, tailWord_5121229, baseEnd_5121229] using wordTrace_append hprefix tailTrace_5121229
  have hstable : (prefixWord ++ tailWord_5121229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5121229).length < 2 ^ (prefixWord ++ tailWord_5121229).sum := by decide
  have hdescent : baseEnd_5121229 < baseStart_5121229 := by decide
  rcases family_descends (prefixWord ++ tailWord_5121229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5121231 : List Nat := [1, 1, 2, 1, 1, 3, 2, 2, 4, 1, 5]
def baseStart_5121231 : Nat := 118140960795 + 5121231 * 2 ^ 59
def prefixEnd_5121231 : Nat := 4983230072969 + 3 ^ 40 * 5121231 * 2
def baseEnd_5121231 : Nat := 2629653045705757893860393

theorem tailTrace_5121231 : CollatzResearch.WordTrace tailWord_5121231 prefixEnd_5121231 2629653045705757893860393 := by
  unfold tailWord_5121231
  simp only [CollatzResearch.WordTrace]
  refine ⟨186786639709662198466531547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124524426473108132311021031 186786639709662198466531547)
  ·
    refine ⟨280179959564493297699797321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186786639709662198466531547 280179959564493297699797321)
    ·
      refine ⟨210134969673369973274847991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 280179959564493297699797321 210134969673369973274847991)
      ·
        refine ⟨315202454510054959912271987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210134969673369973274847991 315202454510054959912271987)
        ·
          refine ⟨472803681765082439868407981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315202454510054959912271987 472803681765082439868407981)
          ·
            refine ⟨177301380661905914950652993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 472803681765082439868407981 177301380661905914950652993)
            ·
              refine ⟨132976035496429436212989745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 177301380661905914950652993 132976035496429436212989745)
              ·
                refine ⟨99732026622322077159742309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 132976035496429436212989745 99732026622322077159742309)
                ·
                  refine ⟨18699754991685389467451683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 99732026622322077159742309 18699754991685389467451683)
                  ·
                    refine ⟨28049632487528084201177525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18699754991685389467451683 28049632487528084201177525)
                    ·
                      refine ⟨2629653045705757893860393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28049632487528084201177525 2629653045705757893860393)
                      ·
                        rfl

theorem cell23_5121231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 4, 1, 5].length) (baseStart_5121231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5121231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5121231 prefixEnd_5121231 := by exact prefixLift 5121231
  have htrace : WordTrace (prefixWord ++ tailWord_5121231) baseStart_5121231 baseEnd_5121231 := by
    simpa [prefixWord, tailWord_5121231, baseEnd_5121231] using wordTrace_append hprefix tailTrace_5121231
  have hstable : (prefixWord ++ tailWord_5121231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5121231).length < 2 ^ (prefixWord ++ tailWord_5121231).sum := by decide
  have hdescent : baseEnd_5121231 < baseStart_5121231 := by decide
  rcases family_descends (prefixWord ++ tailWord_5121231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5121266 : List Nat := [3, 2, 1, 3, 3, 2, 2, 1, 1, 3, 2]
def baseStart_5121266 : Nat := 118140960795 + 5121266 * 2 ^ 59
def prefixEnd_5121266 : Nat := 4983230072969 + 3 ^ 40 * 5121266 * 2
def baseEnd_5121266 : Nat := 2629671017528665256922733

theorem tailTrace_5121266 : CollatzResearch.WordTrace tailWord_5121266 prefixEnd_5121266 2629671017528665256922733 := by
  unfold tailWord_5121266
  simp only [CollatzResearch.WordTrace]
  refine ⟨46696979066133849861013913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124525277509690266296037101 46696979066133849861013913)
  ·
    refine ⟨35022734299600387395760435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46696979066133849861013913 35022734299600387395760435)
    ·
      refine ⟨52534101449400581093640653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35022734299600387395760435 52534101449400581093640653)
      ·
        refine ⟨19700288043525217910115245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52534101449400581093640653 19700288043525217910115245)
        ·
          refine ⟨7387608016321956716293217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19700288043525217910115245 7387608016321956716293217)
          ·
            refine ⟨5540706012241467537219913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7387608016321956716293217 5540706012241467537219913)
            ·
              refine ⟨4155529509181100652914935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5540706012241467537219913 4155529509181100652914935)
              ·
                refine ⟨6233294263771650979372403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4155529509181100652914935 6233294263771650979372403)
                ·
                  refine ⟨9349941395657476469058605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6233294263771650979372403 9349941395657476469058605)
                  ·
                    refine ⟨3506228023371553675896977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9349941395657476469058605 3506228023371553675896977)
                    ·
                      refine ⟨2629671017528665256922733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3506228023371553675896977 2629671017528665256922733)
                      ·
                        rfl

theorem cell23_5121266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 2, 1, 1, 3, 2].length) (baseStart_5121266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5121266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5121266 prefixEnd_5121266 := by exact prefixLift 5121266
  have htrace : WordTrace (prefixWord ++ tailWord_5121266) baseStart_5121266 baseEnd_5121266 := by
    simpa [prefixWord, tailWord_5121266, baseEnd_5121266] using wordTrace_append hprefix tailTrace_5121266
  have hstable : (prefixWord ++ tailWord_5121266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5121266).length < 2 ^ (prefixWord ++ tailWord_5121266).sum := by decide
  have hdescent : baseEnd_5121266 < baseStart_5121266 := by decide
  rcases family_descends (prefixWord ++ tailWord_5121266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5121279 : List Nat := [1, 1, 2, 2, 1, 7, 1, 2, 2, 2, 2]
def baseStart_5121279 : Nat := 118140960795 + 5121279 * 2 ^ 59
def prefixEnd_5121279 : Nat := 4983230072969 + 3 ^ 40 * 5121279 * 2
def baseEnd_5121279 : Nat := 2629677692777173706060173

theorem tailTrace_5121279 : CollatzResearch.WordTrace tailWord_5121279 prefixEnd_5121279 2629677692777173706060173 := by
  unfold tailWord_5121279
  simp only [CollatzResearch.WordTrace]
  refine ⟨186788390413488302664278891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124525593608992201776185927 186788390413488302664278891)
  ·
    refine ⟨280182585620232453996418337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186788390413488302664278891 280182585620232453996418337)
    ·
      refine ⟨210136939215174340497313753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 280182585620232453996418337 210136939215174340497313753)
      ·
        refine ⟨157602704411380755372985315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210136939215174340497313753 157602704411380755372985315)
        ·
          refine ⟨236404056617071133059477973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157602704411380755372985315 236404056617071133059477973)
          ·
            refine ⟨5540720076962604681081515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 236404056617071133059477973 5540720076962604681081515)
            ·
              refine ⟨8311080115443907021622273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5540720076962604681081515 8311080115443907021622273)
              ·
                refine ⟨6233310086582930266216705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8311080115443907021622273 6233310086582930266216705)
                ·
                  refine ⟨4674982564937197699662529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6233310086582930266216705 4674982564937197699662529)
                  ·
                    refine ⟨3506236923702898274746897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4674982564937197699662529 3506236923702898274746897)
                    ·
                      refine ⟨2629677692777173706060173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3506236923702898274746897 2629677692777173706060173)
                      ·
                        rfl

theorem cell23_5121279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 2, 2, 2, 2].length) (baseStart_5121279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5121279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5121279 prefixEnd_5121279 := by exact prefixLift 5121279
  have htrace : WordTrace (prefixWord ++ tailWord_5121279) baseStart_5121279 baseEnd_5121279 := by
    simpa [prefixWord, tailWord_5121279, baseEnd_5121279] using wordTrace_append hprefix tailTrace_5121279
  have hstable : (prefixWord ++ tailWord_5121279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5121279).length < 2 ^ (prefixWord ++ tailWord_5121279).sum := by decide
  have hdescent : baseEnd_5121279 < baseStart_5121279 := by decide
  rcases family_descends (prefixWord ++ tailWord_5121279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5121385 : List Nat := [1, 2, 1, 1, 1, 3, 2, 1, 7, 1, 3]
def baseStart_5121385 : Nat := 118140960795 + 5121385 * 2 ^ 59
def prefixEnd_5121385 : Nat := 4983230072969 + 3 ^ 40 * 5121385 * 2
def baseEnd_5121385 : Nat := 2629732121726550291334685

theorem tailTrace_5121385 : CollatzResearch.WordTrace tailWord_5121385 prefixEnd_5121385 2629732121726550291334685 := by
  unfold tailWord_5121385
  simp only [CollatzResearch.WordTrace]
  refine ⟨186792256551104282767637609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124528171034069521845091739 186792256551104282767637609)
  ·
    refine ⟨140094192413328212075728207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186792256551104282767637609 140094192413328212075728207)
    ·
      refine ⟨210141288619992318113592311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140094192413328212075728207 210141288619992318113592311)
      ·
        refine ⟨315211932929988477170388467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210141288619992318113592311 315211932929988477170388467)
        ·
          refine ⟨472817899394982715755582701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315211932929988477170388467 472817899394982715755582701)
          ·
            refine ⟨177306712273118518408343513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 472817899394982715755582701 177306712273118518408343513)
            ·
              refine ⟨132980034204838888806257635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 177306712273118518408343513 132980034204838888806257635)
              ·
                refine ⟨199470051307258333209386453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132980034204838888806257635 199470051307258333209386453)
                ·
                  refine ⟨4675079327513867184594995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 199470051307258333209386453 4675079327513867184594995)
                  ·
                    refine ⟨7012618991270800776892493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4675079327513867184594995 7012618991270800776892493)
                    ·
                      refine ⟨2629732121726550291334685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7012618991270800776892493 2629732121726550291334685)
                      ·
                        rfl

theorem cell23_5121385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 7, 1, 3].length) (baseStart_5121385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5121385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5121385 prefixEnd_5121385 := by exact prefixLift 5121385
  have htrace : WordTrace (prefixWord ++ tailWord_5121385) baseStart_5121385 baseEnd_5121385 := by
    simpa [prefixWord, tailWord_5121385, baseEnd_5121385] using wordTrace_append hprefix tailTrace_5121385
  have hstable : (prefixWord ++ tailWord_5121385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5121385).length < 2 ^ (prefixWord ++ tailWord_5121385).sum := by decide
  have hdescent : baseEnd_5121385 < baseStart_5121385 := by decide
  rcases family_descends (prefixWord ++ tailWord_5121385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5121425 : List Nat := [1, 2, 2, 1, 1, 1, 2, 3, 2, 6, 2]
def baseStart_5121425 : Nat := 118140960795 + 5121425 * 2 ^ 59
def prefixEnd_5121425 : Nat := 4983230072969 + 3 ^ 40 * 5121425 * 2
def baseEnd_5121425 : Nat := 2629752660952730134834501

theorem tailTrace_5121425 : CollatzResearch.WordTrace tailWord_5121425 prefixEnd_5121425 2629752660952730134834501 := by
  unfold tailWord_5121425
  simp only [CollatzResearch.WordTrace]
  refine ⟨186793715470959369599093729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124529143647306246399395819 186793715470959369599093729)
  ·
    refine ⟨140095286603219527199320297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186793715470959369599093729 140095286603219527199320297)
    ·
      refine ⟨105071464952414645399490223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140095286603219527199320297 105071464952414645399490223)
      ·
        refine ⟨157607197428621968099235335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105071464952414645399490223 157607197428621968099235335)
        ·
          refine ⟨236410796142932952148853003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157607197428621968099235335 236410796142932952148853003)
          ·
            refine ⟨354616194214399428223279505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236410796142932952148853003 354616194214399428223279505)
            ·
              refine ⟨265962145660799571167459629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 354616194214399428223279505 265962145660799571167459629)
              ·
                refine ⟨99735804622799839187797361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 265962145660799571167459629 99735804622799839187797361)
                ·
                  refine ⟨74801853467099879390848021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99735804622799839187797361 74801853467099879390848021)
                  ·
                    refine ⟨3506336881270306846446001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 74801853467099879390848021 3506336881270306846446001)
                    ·
                      refine ⟨2629752660952730134834501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3506336881270306846446001 2629752660952730134834501)
                      ·
                        rfl

theorem cell23_5121425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 6, 2].length) (baseStart_5121425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5121425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5121425 prefixEnd_5121425 := by exact prefixLift 5121425
  have htrace : WordTrace (prefixWord ++ tailWord_5121425) baseStart_5121425 baseEnd_5121425 := by
    simpa [prefixWord, tailWord_5121425, baseEnd_5121425] using wordTrace_append hprefix tailTrace_5121425
  have hstable : (prefixWord ++ tailWord_5121425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5121425).length < 2 ^ (prefixWord ++ tailWord_5121425).sum := by decide
  have hdescent : baseEnd_5121425 < baseStart_5121425 := by decide
  rcases family_descends (prefixWord ++ tailWord_5121425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5121439 : List Nat := [1, 1, 2, 5, 1, 4, 2, 1, 1, 5]
def baseStart_5121439 : Nat := 118140960795 + 5121439 * 2 ^ 59
def prefixEnd_5121439 : Nat := 4983230072969 + 3 ^ 40 * 5121439 * 2
def baseEnd_5121439 : Nat := 876586616560631026686479

theorem tailTrace_5121439 : CollatzResearch.WordTrace tailWord_5121439 prefixEnd_5121439 876586616560631026686479 := by
  unfold tailWord_5121439
  simp only [CollatzResearch.WordTrace]
  refine ⟨186794226092908649990103371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124529484061939099993402247 186794226092908649990103371)
  ·
    refine ⟨280191339139362974985155057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186794226092908649990103371 280191339139362974985155057)
    ·
      refine ⟨210143504354522231238866293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 280191339139362974985155057 210143504354522231238866293)
      ·
        refine ⟨19700953533236459178643715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 210143504354522231238866293 19700953533236459178643715)
        ·
          refine ⟨29551430299854688767965573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19700953533236459178643715 29551430299854688767965573)
          ·
            refine ⟨5540893181222754143993545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29551430299854688767965573 5540893181222754143993545)
            ·
              refine ⟨4155669885917065607995159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5540893181222754143993545 4155669885917065607995159)
              ·
                refine ⟨6233504828875598411992739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4155669885917065607995159 6233504828875598411992739)
                ·
                  refine ⟨9350257243313397617989109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6233504828875598411992739 9350257243313397617989109)
                  ·
                    refine ⟨876586616560631026686479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9350257243313397617989109 876586616560631026686479)
                    ·
                      rfl

theorem cell23_5121439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 2, 1, 1, 5].length) (baseStart_5121439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5121439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5121439 prefixEnd_5121439 := by exact prefixLift 5121439
  have htrace : WordTrace (prefixWord ++ tailWord_5121439) baseStart_5121439 baseEnd_5121439 := by
    simpa [prefixWord, tailWord_5121439, baseEnd_5121439] using wordTrace_append hprefix tailTrace_5121439
  have hstable : (prefixWord ++ tailWord_5121439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5121439).length < 2 ^ (prefixWord ++ tailWord_5121439).sum := by decide
  have hdescent : baseEnd_5121439 < baseStart_5121439 := by decide
  rcases family_descends (prefixWord ++ tailWord_5121439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5121445 : List Nat := [1, 3, 1, 2, 1, 1, 2, 2, 5, 2, 3]
def baseStart_5121445 : Nat := 118140960795 + 5121445 * 2 ^ 59
def prefixEnd_5121445 : Nat := 4983230072969 + 3 ^ 40 * 5121445 * 2
def baseEnd_5121445 : Nat := 2629762930565820056584409

theorem tailTrace_5121445 : CollatzResearch.WordTrace tailWord_5121445 prefixEnd_5121445 2629762930565820056584409 := by
  unfold tailWord_5121445
  simp only [CollatzResearch.WordTrace]
  refine ⟨186794444930886913014821789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124529629953924608676547859 186794444930886913014821789)
  ·
    refine ⟨70047916849082592380558171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186794444930886913014821789 70047916849082592380558171)
    ·
      refine ⟨105071875273623888570837257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70047916849082592380558171 105071875273623888570837257)
      ·
        refine ⟨78803906455217916428127943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105071875273623888570837257 78803906455217916428127943)
        ·
          refine ⟨118205859682826874642191915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78803906455217916428127943 118205859682826874642191915)
          ·
            refine ⟨177308789524240311963287873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118205859682826874642191915 177308789524240311963287873)
            ·
              refine ⟨132981592143180233972465905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 177308789524240311963287873 132981592143180233972465905)
              ·
                refine ⟨99736194107385175479349429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 132981592143180233972465905 99736194107385175479349429)
                ·
                  refine ⟨9350268197567360201189009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 99736194107385175479349429 9350268197567360201189009)
                  ·
                    refine ⟨7012701148175520150891757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9350268197567360201189009 7012701148175520150891757)
                    ·
                      refine ⟨2629762930565820056584409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7012701148175520150891757 2629762930565820056584409)
                      ·
                        rfl

theorem cell23_5121445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 5, 2, 3].length) (baseStart_5121445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5121445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5121445 prefixEnd_5121445 := by exact prefixLift 5121445
  have htrace : WordTrace (prefixWord ++ tailWord_5121445) baseStart_5121445 baseEnd_5121445 := by
    simpa [prefixWord, tailWord_5121445, baseEnd_5121445] using wordTrace_append hprefix tailTrace_5121445
  have hstable : (prefixWord ++ tailWord_5121445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5121445).length < 2 ^ (prefixWord ++ tailWord_5121445).sum := by decide
  have hdescent : baseEnd_5121445 < baseStart_5121445 := by decide
  rcases family_descends (prefixWord ++ tailWord_5121445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5121452 : List Nat := [2, 2, 1, 1, 1, 1, 7, 2, 2, 4]
def baseStart_5121452 : Nat := 118140960795 + 5121452 * 2 ^ 59
def prefixEnd_5121452 : Nat := 4983230072969 + 3 ^ 40 * 5121452 * 2
def baseEnd_5121452 : Nat := 876588841643467176398959

theorem tailTrace_5121452 : CollatzResearch.WordTrace tailWord_5121452 prefixEnd_5121452 876588841643467176398959 := by
  unfold tailWord_5121452
  simp only [CollatzResearch.WordTrace]
  refine ⟨93397350120930776605163305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124529800161241035473551073 93397350120930776605163305)
  ·
    refine ⟨70048012590698082453872479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93397350120930776605163305 70048012590698082453872479)
    ·
      refine ⟨105072018886047123680808719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70048012590698082453872479 105072018886047123680808719)
      ·
        refine ⟨157608028329070685521213079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105072018886047123680808719 157608028329070685521213079)
        ·
          refine ⟨236412042493606028281819619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157608028329070685521213079 236412042493606028281819619)
          ·
            refine ⟨354618063740409042422729429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236412042493606028281819619 354618063740409042422729429)
            ·
              refine ⟨8311360868915836931782721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 354618063740409042422729429 8311360868915836931782721)
              ·
                refine ⟨6233520651686877698837041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8311360868915836931782721 6233520651686877698837041)
                ·
                  refine ⟨4675140488765158274127781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6233520651686877698837041 4675140488765158274127781)
                  ·
                    refine ⟨876588841643467176398959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4675140488765158274127781 876588841643467176398959)
                    ·
                      rfl

theorem cell23_5121452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 4].length) (baseStart_5121452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5121452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5121452 prefixEnd_5121452 := by exact prefixLift 5121452
  have htrace : WordTrace (prefixWord ++ tailWord_5121452) baseStart_5121452 baseEnd_5121452 := by
    simpa [prefixWord, tailWord_5121452, baseEnd_5121452] using wordTrace_append hprefix tailTrace_5121452
  have hstable : (prefixWord ++ tailWord_5121452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5121452).length < 2 ^ (prefixWord ++ tailWord_5121452).sum := by decide
  have hdescent : baseEnd_5121452 < baseStart_5121452 := by decide
  rcases family_descends (prefixWord ++ tailWord_5121452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5121469 : List Nat := [1, 4, 1, 2, 2, 1, 5, 1, 2, 4]
def baseStart_5121469 : Nat := 118140960795 + 5121469 * 2 ^ 59
def prefixEnd_5121469 : Nat := 4983230072969 + 3 ^ 40 * 5121469 * 2
def baseEnd_5121469 : Nat := 876591751367175987561433

theorem tailTrace_5121469 : CollatzResearch.WordTrace tailWord_5121469 prefixEnd_5121469 876591751367175987561433 := by
  unfold tailWord_5121469
  simp only [CollatzResearch.WordTrace]
  refine ⟨186795320282799965113695461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124530213521866643409130307 186795320282799965113695461)
  ·
    refine ⟨35024122553024993458817899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 186795320282799965113695461 35024122553024993458817899)
    ·
      refine ⟨52536183829537490188226849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35024122553024993458817899 52536183829537490188226849)
      ·
        refine ⟨39402137872153117641170137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52536183829537490188226849 39402137872153117641170137)
        ·
          refine ⟨29551603404114838230877603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39402137872153117641170137 29551603404114838230877603)
          ·
            refine ⟨44327405106172257346316405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29551603404114838230877603 44327405106172257346316405)
            ·
              refine ⟨4155694228703649126217163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44327405106172257346316405 4155694228703649126217163)
              ·
                refine ⟨6233541343055473689325745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4155694228703649126217163 6233541343055473689325745)
                ·
                  refine ⟨4675156007291605266994309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6233541343055473689325745 4675156007291605266994309)
                  ·
                    refine ⟨876591751367175987561433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4675156007291605266994309 876591751367175987561433)
                    ·
                      rfl

theorem cell23_5121469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 5, 1, 2, 4].length) (baseStart_5121469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5121469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5121469 prefixEnd_5121469 := by exact prefixLift 5121469
  have htrace : WordTrace (prefixWord ++ tailWord_5121469) baseStart_5121469 baseEnd_5121469 := by
    simpa [prefixWord, tailWord_5121469, baseEnd_5121469] using wordTrace_append hprefix tailTrace_5121469
  have hstable : (prefixWord ++ tailWord_5121469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5121469).length < 2 ^ (prefixWord ++ tailWord_5121469).sum := by decide
  have hdescent : baseEnd_5121469 < baseStart_5121469 := by decide
  rcases family_descends (prefixWord ++ tailWord_5121469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5121476 : List Nat := [2, 3, 3, 2, 1, 1, 2, 2, 3, 2, 2]
def baseStart_5121476 : Nat := 118140960795 + 5121476 * 2 ^ 59
def prefixEnd_5121476 : Nat := 4983230072969 + 3 ^ 40 * 5121476 * 2
def baseEnd_5121476 : Nat := 2629778848466109435296767

theorem tailTrace_5121476 : CollatzResearch.WordTrace tailWord_5121476 prefixEnd_5121476 2629778848466109435296767 := by
  unfold tailWord_5121476
  simp only [CollatzResearch.WordTrace]
  refine ⟨93397787796887302654600141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124530383729183070206133521 93397787796887302654600141)
  ·
    refine ⟨35024170423832738495475053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93397787796887302654600141 35024170423832738495475053)
    ·
      refine ⟨13134063908937276935803145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35024170423832738495475053 13134063908937276935803145)
      ·
        refine ⟨9850547931702957701852359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13134063908937276935803145 9850547931702957701852359)
        ·
          refine ⟨14775821897554436552778539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9850547931702957701852359 14775821897554436552778539)
          ·
            refine ⟨22163732846331654829167809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14775821897554436552778539 22163732846331654829167809)
            ·
              refine ⟨16622799634748741121875857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22163732846331654829167809 16622799634748741121875857)
              ·
                refine ⟨12467099726061555841406893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16622799634748741121875857 12467099726061555841406893)
                ·
                  refine ⟨4675162397273083440527585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12467099726061555841406893 4675162397273083440527585)
                  ·
                    refine ⟨3506371797954812580395689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4675162397273083440527585 3506371797954812580395689)
                    ·
                      refine ⟨2629778848466109435296767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3506371797954812580395689 2629778848466109435296767)
                      ·
                        rfl

theorem cell23_5121476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_5121476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5121476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5121476 prefixEnd_5121476 := by exact prefixLift 5121476
  have htrace : WordTrace (prefixWord ++ tailWord_5121476) baseStart_5121476 baseEnd_5121476 := by
    simpa [prefixWord, tailWord_5121476, baseEnd_5121476] using wordTrace_append hprefix tailTrace_5121476
  have hstable : (prefixWord ++ tailWord_5121476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5121476).length < 2 ^ (prefixWord ++ tailWord_5121476).sum := by decide
  have hdescent : baseEnd_5121476 < baseStart_5121476 := by decide
  rcases family_descends (prefixWord ++ tailWord_5121476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5121482 : List Nat := [3, 1, 2, 1, 2, 5, 2, 7]
def baseStart_5121482 : Nat := 118140960795 + 5121482 * 2 ^ 59
def prefixEnd_5121482 : Nat := 4983230072969 + 3 ^ 40 * 5121482 * 2
def baseEnd_5121482 : Nat := 97399330716668015252657

theorem tailTrace_5121482 : CollatzResearch.WordTrace tailWord_5121482 prefixEnd_5121482 97399330716668015252657 := by
  unfold tailWord_5121482
  simp only [CollatzResearch.WordTrace]
  refine ⟨46698948607938217083479675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124530529621168578889279133 46698948607938217083479675)
  ·
    refine ⟨70048422911907325625219513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46698948607938217083479675 70048422911907325625219513)
    ·
      refine ⟨52536317183930494218914635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70048422911907325625219513 52536317183930494218914635)
      ·
        refine ⟨78804475775895741328371953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52536317183930494218914635 78804475775895741328371953)
        ·
          refine ⟨59103356831921805996278965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78804475775895741328371953 59103356831921805996278965)
          ·
            refine ⟨5540939702992669312151153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59103356831921805996278965 5540939702992669312151153)
            ·
              refine ⟨4155704777244501984113365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5540939702992669312151153 4155704777244501984113365)
              ·
                refine ⟨97399330716668015252657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4155704777244501984113365 97399330716668015252657)
                ·
                  rfl

theorem cell23_5121482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 2, 7].length) (baseStart_5121482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5121482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5121482 prefixEnd_5121482 := by exact prefixLift 5121482
  have htrace : WordTrace (prefixWord ++ tailWord_5121482) baseStart_5121482 baseEnd_5121482 := by
    simpa [prefixWord, tailWord_5121482, baseEnd_5121482] using wordTrace_append hprefix tailTrace_5121482
  have hstable : (prefixWord ++ tailWord_5121482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5121482).length < 2 ^ (prefixWord ++ tailWord_5121482).sum := by decide
  have hdescent : baseEnd_5121482 < baseStart_5121482 := by decide
  rcases family_descends (prefixWord ++ tailWord_5121482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5121509 : List Nat := [1, 3, 1, 5, 1, 1, 2, 1, 4, 1, 3]
def baseStart_5121509 : Nat := 118140960795 + 5121509 * 2 ^ 59
def prefixEnd_5121509 : Nat := 4983230072969 + 3 ^ 40 * 5121509 * 2
def baseEnd_5121509 : Nat := 2629795793327707806184115

theorem tailTrace_5121509 : CollatzResearch.WordTrace tailWord_5121509 prefixEnd_5121509 2629795793327707806184115 := by
  unfold tailWord_5121509
  simp only [CollatzResearch.WordTrace]
  refine ⟨186796779202655051945151581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124531186135103367963434387 186796779202655051945151581)
  ·
    refine ⟨70048792200995644479431843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186796779202655051945151581 70048792200995644479431843)
    ·
      refine ⟨105073188301493466719147765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70048792200995644479431843 105073188301493466719147765)
      ·
        refine ⟨9850611403265012504920103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 105073188301493466719147765 9850611403265012504920103)
        ·
          refine ⟨14775917104897518757380155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9850611403265012504920103 14775917104897518757380155)
          ·
            refine ⟨22163875657346278136070233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14775917104897518757380155 22163875657346278136070233)
            ·
              refine ⟨16622906743009708602052675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22163875657346278136070233 16622906743009708602052675)
              ·
                refine ⟨24934360114514562903079013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16622906743009708602052675 24934360114514562903079013)
                ·
                  refine ⟨4675192521471480544327315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24934360114514562903079013 4675192521471480544327315)
                  ·
                    refine ⟨7012788782207220816490973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4675192521471480544327315 7012788782207220816490973)
                    ·
                      refine ⟨2629795793327707806184115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7012788782207220816490973 2629795793327707806184115)
                      ·
                        rfl

theorem cell23_5121509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_5121509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5121509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5121509 prefixEnd_5121509 := by exact prefixLift 5121509
  have htrace : WordTrace (prefixWord ++ tailWord_5121509) baseStart_5121509 baseEnd_5121509 := by
    simpa [prefixWord, tailWord_5121509, baseEnd_5121509] using wordTrace_append hprefix tailTrace_5121509
  have hstable : (prefixWord ++ tailWord_5121509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5121509).length < 2 ^ (prefixWord ++ tailWord_5121509).sum := by decide
  have hdescent : baseEnd_5121509 < baseStart_5121509 := by decide
  rcases family_descends (prefixWord ++ tailWord_5121509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5121526 : List Nat := [5, 1, 1, 1, 2, 3, 1, 3, 2, 1, 3]
def baseStart_5121526 : Nat := 118140960795 + 5121526 * 2 ^ 59
def prefixEnd_5121526 : Nat := 4983230072969 + 3 ^ 40 * 5121526 * 2
def baseEnd_5121526 : Nat := 2629804522498834239671537

theorem tailTrace_5121526 : CollatzResearch.WordTrace tailWord_5121526 prefixEnd_5121526 2629804522498834239671537 := by
  unfold tailWord_5121526
  simp only [CollatzResearch.WordTrace]
  refine ⟨11674837452724591490532527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 124531599495728975899013621 11674837452724591490532527)
  ·
    refine ⟨17512256179086887235798791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11674837452724591490532527 17512256179086887235798791)
    ·
      refine ⟨26268384268630330853698187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17512256179086887235798791 26268384268630330853698187)
      ·
        refine ⟨39402576402945496280547281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26268384268630330853698187 39402576402945496280547281)
        ·
          refine ⟨29551932302209122210410461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39402576402945496280547281 29551932302209122210410461)
          ·
            refine ⟨11081974613328420828903923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29551932302209122210410461 11081974613328420828903923)
            ·
              refine ⟨16622961919992631243355885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11081974613328420828903923 16622961919992631243355885)
              ·
                refine ⟨6233610719997236716258457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16622961919992631243355885 6233610719997236716258457)
                ·
                  refine ⟨4675208039997927537193843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6233610719997236716258457 4675208039997927537193843)
                  ·
                    refine ⟨7012812059996891305790765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4675208039997927537193843 7012812059996891305790765)
                    ·
                      refine ⟨2629804522498834239671537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7012812059996891305790765 2629804522498834239671537)
                      ·
                        rfl

theorem cell23_5121526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 3, 2, 1, 3].length) (baseStart_5121526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5121526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5121526 prefixEnd_5121526 := by exact prefixLift 5121526
  have htrace : WordTrace (prefixWord ++ tailWord_5121526) baseStart_5121526 baseEnd_5121526 := by
    simpa [prefixWord, tailWord_5121526, baseEnd_5121526] using wordTrace_append hprefix tailTrace_5121526
  have hstable : (prefixWord ++ tailWord_5121526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5121526).length < 2 ^ (prefixWord ++ tailWord_5121526).sum := by decide
  have hdescent : baseEnd_5121526 < baseStart_5121526 := by decide
  rcases family_descends (prefixWord ++ tailWord_5121526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5121535 : List Nat := [1, 1, 2, 2, 1, 2, 2, 1, 4, 4, 3]
def baseStart_5121535 : Nat := 118140960795 + 5121535 * 2 ^ 59
def prefixEnd_5121535 : Nat := 4983230072969 + 3 ^ 40 * 5121535 * 2
def baseEnd_5121535 : Nat := 2629809143824724704458995

theorem tailTrace_5121535 : CollatzResearch.WordTrace tailWord_5121535 prefixEnd_5121535 2629809143824724704458995 := by
  unfold tailWord_5121535
  simp only [CollatzResearch.WordTrace]
  refine ⟨186797727500560858385598059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124531818333707238923732039 186797727500560858385598059)
  ·
    refine ⟨280196591250841287578397089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186797727500560858385598059 280196591250841287578397089)
    ·
      refine ⟨210147443438130965683797817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 280196591250841287578397089 210147443438130965683797817)
      ·
        refine ⟨157610582578598224262848363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210147443438130965683797817 157610582578598224262848363)
        ·
          refine ⟨236415873867897336394272545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157610582578598224262848363 236415873867897336394272545)
          ·
            refine ⟨177311905400923002295704409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 236415873867897336394272545 177311905400923002295704409)
            ·
              refine ⟨132983929050692251721778307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 177311905400923002295704409 132983929050692251721778307)
              ·
                refine ⟨199475893576038377582667461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132983929050692251721778307 199475893576038377582667461)
                ·
                  refine ⟨37401730045507195796750149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 199475893576038377582667461 37401730045507195796750149)
                  ·
                    refine ⟨7012824383532599211890653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37401730045507195796750149 7012824383532599211890653)
                    ·
                      refine ⟨2629809143824724704458995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7012824383532599211890653 2629809143824724704458995)
                      ·
                        rfl

theorem cell23_5121535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 4, 3].length) (baseStart_5121535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5121535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5121535 prefixEnd_5121535 := by exact prefixLift 5121535
  have htrace : WordTrace (prefixWord ++ tailWord_5121535) baseStart_5121535 baseEnd_5121535 := by
    simpa [prefixWord, tailWord_5121535, baseEnd_5121535] using wordTrace_append hprefix tailTrace_5121535
  have hstable : (prefixWord ++ tailWord_5121535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5121535).length < 2 ^ (prefixWord ++ tailWord_5121535).sum := by decide
  have hdescent : baseEnd_5121535 < baseStart_5121535 := by decide
  rcases family_descends (prefixWord ++ tailWord_5121535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5121585 : List Nat := [1, 2, 2, 3, 1, 1, 1, 4, 1, 7]
def baseStart_5121585 : Nat := 118140960795 + 5121585 * 2 ^ 59
def prefixEnd_5121585 : Nat := 4983230072969 + 3 ^ 40 * 5121585 * 2
def baseEnd_5121585 : Nat := 876611605952483169611255

theorem tailTrace_5121585 : CollatzResearch.WordTrace tailWord_5121585 prefixEnd_5121585 876611605952483169611255 := by
  unfold tailWord_5121585
  simp only [CollatzResearch.WordTrace]
  refine ⟨186799551150379716924918209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124533034100253144616612139 186799551150379716924918209)
  ·
    refine ⟨140099663362784787693688657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186799551150379716924918209 140099663362784787693688657)
    ·
      refine ⟨105074747522088590770266493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140099663362784787693688657 105074747522088590770266493)
      ·
        refine ⟨39403030320783221538849935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105074747522088590770266493 39403030320783221538849935)
        ·
          refine ⟨59104545481174832308274903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39403030320783221538849935 59104545481174832308274903)
          ·
            refine ⟨88656818221762248462412355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59104545481174832308274903 88656818221762248462412355)
            ·
              refine ⟨132985227332643372693618533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88656818221762248462412355 132985227332643372693618533)
              ·
                refine ⟨24934730124870632380053475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 132985227332643372693618533 24934730124870632380053475)
                ·
                  refine ⟨37402095187305948570080213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24934730124870632380053475 37402095187305948570080213)
                  ·
                    refine ⟨876611605952483169611255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37402095187305948570080213 876611605952483169611255)
                    ·
                      rfl

theorem cell23_5121585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 7].length) (baseStart_5121585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5121585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5121585 prefixEnd_5121585 := by exact prefixLift 5121585
  have htrace : WordTrace (prefixWord ++ tailWord_5121585) baseStart_5121585 baseEnd_5121585 := by
    simpa [prefixWord, tailWord_5121585, baseEnd_5121585] using wordTrace_append hprefix tailTrace_5121585
  have hstable : (prefixWord ++ tailWord_5121585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5121585).length < 2 ^ (prefixWord ++ tailWord_5121585).sum := by decide
  have hdescent : baseEnd_5121585 < baseStart_5121585 := by decide
  rcases family_descends (prefixWord ++ tailWord_5121585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5121625 : List Nat := [1, 2, 1, 2, 2, 1, 1, 3, 2, 3, 5]
def baseStart_5121625 : Nat := 118140960795 + 5121625 * 2 ^ 59
def prefixEnd_5121625 : Nat := 4983230072969 + 3 ^ 40 * 5121625 * 2
def baseEnd_5121625 : Nat := 2629855357083629352333581

theorem tailTrace_5121625 : CollatzResearch.WordTrace tailWord_5121625 prefixEnd_5121625 2629855357083629352333581 := by
  unfold tailWord_5121625
  simp only [CollatzResearch.WordTrace]
  refine ⟨186801010070234803756374329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124534006713489869170916219 186801010070234803756374329)
  ·
    refine ⟨140100757552676102817280747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186801010070234803756374329 140100757552676102817280747)
    ·
      refine ⟨210151136329014154225921121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140100757552676102817280747 210151136329014154225921121)
      ·
        refine ⟨157613352246760615669440841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210151136329014154225921121 157613352246760615669440841)
        ·
          refine ⟨118210014185070461752080631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157613352246760615669440841 118210014185070461752080631)
          ·
            refine ⟨177315021277605692628120947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118210014185070461752080631 177315021277605692628120947)
            ·
              refine ⟨265972531916408538942181421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177315021277605692628120947 265972531916408538942181421)
              ·
                refine ⟨99739699468653202103318033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 265972531916408538942181421 99739699468653202103318033)
                ·
                  refine ⟨74804774601489901577488525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99739699468653202103318033 74804774601489901577488525)
                  ·
                    refine ⟨28051790475558713091558197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 74804774601489901577488525 28051790475558713091558197)
                    ·
                      refine ⟨2629855357083629352333581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28051790475558713091558197 2629855357083629352333581)
                      ·
                        rfl

theorem cell23_5121625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 3, 5].length) (baseStart_5121625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5121625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5121625 prefixEnd_5121625 := by exact prefixLift 5121625
  have htrace : WordTrace (prefixWord ++ tailWord_5121625) baseStart_5121625 baseEnd_5121625 := by
    simpa [prefixWord, tailWord_5121625, baseEnd_5121625] using wordTrace_append hprefix tailTrace_5121625
  have hstable : (prefixWord ++ tailWord_5121625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5121625).length < 2 ^ (prefixWord ++ tailWord_5121625).sum := by decide
  have hdescent : baseEnd_5121625 < baseStart_5121625 := by decide
  rcases family_descends (prefixWord ++ tailWord_5121625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5121639 : List Nat := [1, 1, 5, 1, 1, 1, 4, 1, 2, 4, 2]
def baseStart_5121639 : Nat := 118140960795 + 5121639 * 2 ^ 59
def prefixEnd_5121639 : Nat := 4983230072969 + 3 ^ 40 * 5121639 * 2
def baseEnd_5121639 : Nat := 2629862545812792297558517

theorem tailTrace_5121639 : CollatzResearch.WordTrace tailWord_5121639 prefixEnd_5121639 2629862545812792297558517 := by
  unfold tailWord_5121639
  simp only [CollatzResearch.WordTrace]
  refine ⟨186801520692184084147383971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124534347128122722764922647 186801520692184084147383971)
  ·
    refine ⟨280202281038276126221075957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186801520692184084147383971 280202281038276126221075957)
    ·
      refine ⟨26268963847338386833225871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 280202281038276126221075957 26268963847338386833225871)
      ·
        refine ⟨39403445771007580249838807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26268963847338386833225871 39403445771007580249838807)
        ·
          refine ⟨59105168656511370374758211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39403445771007580249838807 59105168656511370374758211)
          ·
            refine ⟨88657752984767055562137317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59105168656511370374758211 88657752984767055562137317)
            ·
              refine ⟨16623328684643822917900747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88657752984767055562137317 16623328684643822917900747)
              ·
                refine ⟨24934993026965734376851121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16623328684643822917900747 24934993026965734376851121)
                ·
                  refine ⟨18701244770224300782638341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24934993026965734376851121 18701244770224300782638341)
                  ·
                    refine ⟨3506483394417056396744689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18701244770224300782638341 3506483394417056396744689)
                    ·
                      refine ⟨2629862545812792297558517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3506483394417056396744689 2629862545812792297558517)
                      ·
                        rfl

theorem cell23_5121639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 2, 4, 2].length) (baseStart_5121639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5121639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5121639 prefixEnd_5121639 := by exact prefixLift 5121639
  have htrace : WordTrace (prefixWord ++ tailWord_5121639) baseStart_5121639 baseEnd_5121639 := by
    simpa [prefixWord, tailWord_5121639, baseEnd_5121639] using wordTrace_append hprefix tailTrace_5121639
  have hstable : (prefixWord ++ tailWord_5121639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5121639).length < 2 ^ (prefixWord ++ tailWord_5121639).sum := by decide
  have hdescent : baseEnd_5121639 < baseStart_5121639 := by decide
  rcases family_descends (prefixWord ++ tailWord_5121639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5121689 : List Nat := [1, 2, 1, 2, 1, 2, 2, 5, 3, 1, 3]
def baseStart_5121689 : Nat := 118140960795 + 5121689 * 2 ^ 59
def prefixEnd_5121689 : Nat := 4983230072969 + 3 ^ 40 * 5121689 * 2
def baseEnd_5121689 : Nat := 2629888219845517101933287

theorem tailTrace_5121689 : CollatzResearch.WordTrace tailWord_5121689 prefixEnd_5121689 2629888219845517101933287 := by
  unfold tailWord_5121689
  simp only [CollatzResearch.WordTrace]
  refine ⟨186803344342002942686704121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124535562894668628457802747 186803344342002942686704121)
  ·
    refine ⟨140102508256502207015028091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186803344342002942686704121 140102508256502207015028091)
    ·
      refine ⟨210153762384753310522542137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140102508256502207015028091 210153762384753310522542137)
      ·
        refine ⟨157615321788564982891906603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210153762384753310522542137 157615321788564982891906603)
        ·
          refine ⟨236422982682847474337859905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157615321788564982891906603 236422982682847474337859905)
          ·
            refine ⟨177317237012135605753394929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 236422982682847474337859905 177317237012135605753394929)
            ·
              refine ⟨132987927759101704315046197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 177317237012135605753394929 132987927759101704315046197)
              ·
                refine ⟨12467618227415784779535581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 132987927759101704315046197 12467618227415784779535581)
                ·
                  refine ⟨4675356835280919292325843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12467618227415784779535581 4675356835280919292325843)
                  ·
                    refine ⟨7013035252921378938488765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4675356835280919292325843 7013035252921378938488765)
                    ·
                      refine ⟨2629888219845517101933287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7013035252921378938488765 2629888219845517101933287)
                      ·
                        rfl

theorem cell23_5121689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 5, 3, 1, 3].length) (baseStart_5121689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5121689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5121689 prefixEnd_5121689 := by exact prefixLift 5121689
  have htrace : WordTrace (prefixWord ++ tailWord_5121689) baseStart_5121689 baseEnd_5121689 := by
    simpa [prefixWord, tailWord_5121689, baseEnd_5121689] using wordTrace_append hprefix tailTrace_5121689
  have hstable : (prefixWord ++ tailWord_5121689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5121689).length < 2 ^ (prefixWord ++ tailWord_5121689).sum := by decide
  have hdescent : baseEnd_5121689 < baseStart_5121689 := by decide
  rcases family_descends (prefixWord ++ tailWord_5121689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5121696 : List Nat := [2, 1, 1, 4, 3, 3, 2, 1, 6]
def baseStart_5121696 : Nat := 118140960795 + 5121696 * 2 ^ 59
def prefixEnd_5121696 : Nat := 4983230072969 + 3 ^ 40 * 5121696 * 2
def baseEnd_5121696 : Nat := 292210201578899841616195

theorem tailTrace_5121696 : CollatzResearch.WordTrace tailWord_5121696 prefixEnd_5121696 292210201578899841616195 := by
  unfold tailWord_5121696
  simp only [CollatzResearch.WordTrace]
  refine ⟨93401799826488791441104471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124535733101985055254805961 93401799826488791441104471)
  ·
    refine ⟨140102699739733187161656707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93401799826488791441104471 140102699739733187161656707)
    ·
      refine ⟨210154049609599780742485061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140102699739733187161656707 210154049609599780742485061)
      ·
        refine ⟨39403884301799958889215949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 210154049609599780742485061 39403884301799958889215949)
        ·
          refine ⟨14776456613174984583455981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39403884301799958889215949 14776456613174984583455981)
          ·
            refine ⟨5541171229940619218795993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14776456613174984583455981 5541171229940619218795993)
            ·
              refine ⟨4155878422455464414096995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5541171229940619218795993 4155878422455464414096995)
              ·
                refine ⟨6233817633683196621145493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4155878422455464414096995 6233817633683196621145493)
                ·
                  refine ⟨292210201578899841616195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6233817633683196621145493 292210201578899841616195)
                  ·
                    rfl

theorem cell23_5121696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 2, 1, 6].length) (baseStart_5121696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5121696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5121696 prefixEnd_5121696 := by exact prefixLift 5121696
  have htrace : WordTrace (prefixWord ++ tailWord_5121696) baseStart_5121696 baseEnd_5121696 := by
    simpa [prefixWord, tailWord_5121696, baseEnd_5121696] using wordTrace_append hprefix tailTrace_5121696
  have hstable : (prefixWord ++ tailWord_5121696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5121696).length < 2 ^ (prefixWord ++ tailWord_5121696).sum := by decide
  have hdescent : baseEnd_5121696 < baseStart_5121696 := by decide
  rcases family_descends (prefixWord ++ tailWord_5121696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5121699 : List Nat := [1, 1, 1, 4, 1, 1, 3, 2, 4, 3, 2]
def baseStart_5121699 : Nat := 118140960795 + 5121699 * 2 ^ 59
def prefixEnd_5121699 : Nat := 4983230072969 + 3 ^ 40 * 5121699 * 2
def baseEnd_5121699 : Nat := 2629893354652062062808241

theorem tailTrace_5121699 : CollatzResearch.WordTrace tailWord_5121699 prefixEnd_5121699 2629893354652062062808241 := by
  unfold tailWord_5121699
  simp only [CollatzResearch.WordTrace]
  refine ⟨186803709071966714394568151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124535806047977809596378767 186803709071966714394568151)
  ·
    refine ⟨280205563607950071591852227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186803709071966714394568151 280205563607950071591852227)
    ·
      refine ⟨420308345411925107387778341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280205563607950071591852227 420308345411925107387778341)
      ·
        refine ⟨78807814764735957635208439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 420308345411925107387778341 78807814764735957635208439)
        ·
          refine ⟨118211722147103936452812659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78807814764735957635208439 118211722147103936452812659)
          ·
            refine ⟨177317583220655904679218989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118211722147103936452812659 177317583220655904679218989)
            ·
              refine ⟨66494093707745964254707121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 177317583220655904679218989 66494093707745964254707121)
              ·
                refine ⟨49870570280809473191030341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66494093707745964254707121 49870570280809473191030341)
                ·
                  refine ⟨9350731927651776223318189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49870570280809473191030341 9350731927651776223318189)
                  ·
                    refine ⟨3506524472869416083744321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9350731927651776223318189 3506524472869416083744321)
                    ·
                      refine ⟨2629893354652062062808241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3506524472869416083744321 2629893354652062062808241)
                      ·
                        rfl

theorem cell23_5121699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 4, 3, 2].length) (baseStart_5121699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5121699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5121699 prefixEnd_5121699 := by exact prefixLift 5121699
  have htrace : WordTrace (prefixWord ++ tailWord_5121699) baseStart_5121699 baseEnd_5121699 := by
    simpa [prefixWord, tailWord_5121699, baseEnd_5121699] using wordTrace_append hprefix tailTrace_5121699
  have hstable : (prefixWord ++ tailWord_5121699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5121699).length < 2 ^ (prefixWord ++ tailWord_5121699).sum := by decide
  have hdescent : baseEnd_5121699 < baseStart_5121699 := by decide
  rcases family_descends (prefixWord ++ tailWord_5121699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5121709 : List Nat := [1, 5, 2, 1, 1, 1, 3, 1, 3, 5]
def baseStart_5121709 : Nat := 118140960795 + 5121709 * 2 ^ 59
def prefixEnd_5121709 : Nat := 4983230072969 + 3 ^ 40 * 5121709 * 2
def baseEnd_5121709 : Nat := 876632829819535674561065

theorem tailTrace_5121709 : CollatzResearch.WordTrace tailWord_5121709 prefixEnd_5121709 876632829819535674561065 := by
  unfold tailWord_5121709
  simp only [CollatzResearch.WordTrace]
  refine ⟨186804073801930486102432181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124536049201286990734954787 186804073801930486102432181)
  ·
    refine ⟨17512881918930983072103017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 186804073801930486102432181 17512881918930983072103017)
    ·
      refine ⟨13134661439198237304077263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17512881918930983072103017 13134661439198237304077263)
      ·
        refine ⟨19701992158797355956115895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13134661439198237304077263 19701992158797355956115895)
        ·
          refine ⟨29552988238196033934173843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19701992158797355956115895 29552988238196033934173843)
          ·
            refine ⟨44329482357294050901260765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29552988238196033934173843 44329482357294050901260765)
            ·
              refine ⟨16623555883985269087972787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44329482357294050901260765 16623555883985269087972787)
              ·
                refine ⟨24935333825977903631959181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16623555883985269087972787 24935333825977903631959181)
                ·
                  refine ⟨9350750184741713861984693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24935333825977903631959181 9350750184741713861984693)
                  ·
                    refine ⟨876632829819535674561065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9350750184741713861984693 876632829819535674561065)
                    ·
                      rfl

theorem cell23_5121709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_5121709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5121709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5121709 prefixEnd_5121709 := by exact prefixLift 5121709
  have htrace : WordTrace (prefixWord ++ tailWord_5121709) baseStart_5121709 baseEnd_5121709 := by
    simpa [prefixWord, tailWord_5121709, baseEnd_5121709] using wordTrace_append hprefix tailTrace_5121709
  have hstable : (prefixWord ++ tailWord_5121709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5121709).length < 2 ^ (prefixWord ++ tailWord_5121709).sum := by decide
  have hdescent : baseEnd_5121709 < baseStart_5121709 := by decide
  rcases family_descends (prefixWord ++ tailWord_5121709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5121722 : List Nat := [3, 1, 1, 1, 2, 4, 1, 1, 3, 6]
def baseStart_5121722 : Nat := 118140960795 + 5121722 * 2 ^ 59
def prefixEnd_5121722 : Nat := 4983230072969 + 3 ^ 40 * 5121722 * 2
def baseEnd_5121722 : Nat := 876635054902371824273545

theorem tailTrace_5121722 : CollatzResearch.WordTrace tailWord_5121722 prefixEnd_5121722 876635054902371824273545 := by
  unfold tailWord_5121722
  simp only [CollatzResearch.WordTrace]
  refine ⟨46701136987720847330663855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124536365300588926215103613 46701136987720847330663855)
  ·
    refine ⟨70051705481581270995995783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46701136987720847330663855 70051705481581270995995783)
    ·
      refine ⟨105077558222371906493993675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70051705481581270995995783 105077558222371906493993675)
      ·
        refine ⟨157616337333557859740990513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105077558222371906493993675 157616337333557859740990513)
        ·
          refine ⟨118212253000168394805742885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157616337333557859740990513 118212253000168394805742885)
          ·
            refine ⟨22164797437531574026076791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 118212253000168394805742885 22164797437531574026076791)
            ·
              refine ⟨33247196156297361039115187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22164797437531574026076791 33247196156297361039115187)
              ·
                refine ⟨49870794234446041558672781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33247196156297361039115187 49870794234446041558672781)
                ·
                  refine ⟨18701547837917265584502293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49870794234446041558672781 18701547837917265584502293)
                  ·
                    refine ⟨876635054902371824273545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18701547837917265584502293 876635054902371824273545)
                    ·
                      rfl

theorem cell23_5121722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 3, 6].length) (baseStart_5121722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5121722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5121722 prefixEnd_5121722 := by exact prefixLift 5121722
  have htrace : WordTrace (prefixWord ++ tailWord_5121722) baseStart_5121722 baseEnd_5121722 := by
    simpa [prefixWord, tailWord_5121722, baseEnd_5121722] using wordTrace_append hprefix tailTrace_5121722
  have hstable : (prefixWord ++ tailWord_5121722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5121722).length < 2 ^ (prefixWord ++ tailWord_5121722).sum := by decide
  have hdescent : baseEnd_5121722 < baseStart_5121722 := by decide
  rcases family_descends (prefixWord ++ tailWord_5121722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5121730 : List Nat := [3, 5, 1, 2, 1, 1, 2, 2, 6]
def baseStart_5121730 : Nat := 118140960795 + 5121730 * 2 ^ 59
def prefixEnd_5121730 : Nat := 4983230072969 + 3 ^ 40 * 5121730 * 2
def baseEnd_5121730 : Nat := 292212141394705715724511

theorem tailTrace_5121730 : CollatzResearch.WordTrace tailWord_5121730 prefixEnd_5121730 292212141394705715724511 := by
  unfold tailWord_5121730
  simp only [CollatzResearch.WordTrace]
  refine ⟨46701209933713601672236661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124536559823236271125964429 46701209933713601672236661)
  ·
    refine ⟨4378238431285650156772187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46701209933713601672236661 4378238431285650156772187)
    ·
      refine ⟨6567357646928475235158281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4378238431285650156772187 6567357646928475235158281)
      ·
        refine ⟨4925518235196356426368711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6567357646928475235158281 4925518235196356426368711)
        ·
          refine ⟨7388277352794534639553067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4925518235196356426368711 7388277352794534639553067)
          ·
            refine ⟨11082416029191801959329601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7388277352794534639553067 11082416029191801959329601)
            ·
              refine ⟨8311812021893851469497201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11082416029191801959329601 8311812021893851469497201)
              ·
                refine ⟨6233859016420388602122901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8311812021893851469497201 6233859016420388602122901)
                ·
                  refine ⟨292212141394705715724511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6233859016420388602122901 292212141394705715724511)
                  ·
                    rfl

theorem cell23_5121730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_5121730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5121730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5121730 prefixEnd_5121730 := by exact prefixLift 5121730
  have htrace : WordTrace (prefixWord ++ tailWord_5121730) baseStart_5121730 baseEnd_5121730 := by
    simpa [prefixWord, tailWord_5121730, baseEnd_5121730] using wordTrace_append hprefix tailTrace_5121730
  have hstable : (prefixWord ++ tailWord_5121730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5121730).length < 2 ^ (prefixWord ++ tailWord_5121730).sum := by decide
  have hdescent : baseEnd_5121730 < baseStart_5121730 := by decide
  rcases family_descends (prefixWord ++ tailWord_5121730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5121734 : List Nat := [6, 1, 2, 1, 1, 3, 2, 2, 1, 4]
def baseStart_5121734 : Nat := 118140960795 + 5121734 * 2 ^ 59
def prefixEnd_5121734 : Nat := 4983230072969 + 3 ^ 40 * 5121734 * 2
def baseEnd_5121734 : Nat := 876637108824989808623527

theorem tailTrace_5121734 : CollatzResearch.WordTrace tailWord_5121734 prefixEnd_5121734 876637108824989808623527 := by
  unfold tailWord_5121734
  simp only [CollatzResearch.WordTrace]
  refine ⟨5837655800838747355377883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 124536657084559943581394837 5837655800838747355377883)
  ·
    refine ⟨8756483701258121033066825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5837655800838747355377883 8756483701258121033066825)
    ·
      refine ⟨6567362775943590774800119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8756483701258121033066825 6567362775943590774800119)
      ·
        refine ⟨9851044163915386162200179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6567362775943590774800119 9851044163915386162200179)
        ·
          refine ⟨14776566245873079243300269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9851044163915386162200179 14776566245873079243300269)
          ·
            refine ⟨5541212342202404716237601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14776566245873079243300269 5541212342202404716237601)
            ·
              refine ⟨4155909256651803537178201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5541212342202404716237601 4155909256651803537178201)
              ·
                refine ⟨3116931942488852652883651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4155909256651803537178201 3116931942488852652883651)
                ·
                  refine ⟨4675397913733278979325477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3116931942488852652883651 4675397913733278979325477)
                  ·
                    refine ⟨876637108824989808623527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4675397913733278979325477 876637108824989808623527)
                    ·
                      rfl

theorem cell23_5121734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_5121734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5121734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5121734 prefixEnd_5121734 := by exact prefixLift 5121734
  have htrace : WordTrace (prefixWord ++ tailWord_5121734) baseStart_5121734 baseEnd_5121734 := by
    simpa [prefixWord, tailWord_5121734, baseEnd_5121734] using wordTrace_append hprefix tailTrace_5121734
  have hstable : (prefixWord ++ tailWord_5121734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5121734).length < 2 ^ (prefixWord ++ tailWord_5121734).sum := by decide
  have hdescent : baseEnd_5121734 < baseStart_5121734 := by decide
  rcases family_descends (prefixWord ++ tailWord_5121734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5121740 : List Nat := [2, 2, 1, 5, 2, 1, 1, 4, 1, 1, 3]
def baseStart_5121740 : Nat := 118140960795 + 5121740 * 2 ^ 59
def prefixEnd_5121740 : Nat := 4983230072969 + 3 ^ 40 * 5121740 * 2
def baseEnd_5121740 : Nat := 2629914407358896402395553

theorem tailTrace_5121740 : CollatzResearch.WordTrace tailWord_5121740 prefixEnd_5121740 2629914407358896402395553 := by
  unfold tailWord_5121740
  simp only [CollatzResearch.WordTrace]
  refine ⟨93402602232409089198405337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124536802976545452264540449 93402602232409089198405337)
  ·
    refine ⟨70051951674306816898804003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93402602232409089198405337 70051951674306816898804003)
    ·
      refine ⟨105077927511460225348206005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70051951674306816898804003 105077927511460225348206005)
      ·
        refine ⟨9851055704199396126394313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 105077927511460225348206005 9851055704199396126394313)
        ·
          refine ⟨7388291778149547094795735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9851055704199396126394313 7388291778149547094795735)
          ·
            refine ⟨11082437667224320642193603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7388291778149547094795735 11082437667224320642193603)
            ·
              refine ⟨16623656500836480963290405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11082437667224320642193603 16623656500836480963290405)
              ·
                refine ⟨3116935593906840180616951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16623656500836480963290405 3116935593906840180616951)
                ·
                  refine ⟨4675403390860260270925427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3116935593906840180616951 4675403390860260270925427)
                  ·
                    refine ⟨7013105086290390406388141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4675403390860260270925427 7013105086290390406388141)
                    ·
                      refine ⟨2629914407358896402395553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7013105086290390406388141 2629914407358896402395553)
                      ·
                        rfl

theorem cell23_5121740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_5121740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5121740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5121740 prefixEnd_5121740 := by exact prefixLift 5121740
  have htrace : WordTrace (prefixWord ++ tailWord_5121740) baseStart_5121740 baseEnd_5121740 := by
    simpa [prefixWord, tailWord_5121740, baseEnd_5121740] using wordTrace_append hprefix tailTrace_5121740
  have hstable : (prefixWord ++ tailWord_5121740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5121740).length < 2 ^ (prefixWord ++ tailWord_5121740).sum := by decide
  have hdescent : baseEnd_5121740 < baseStart_5121740 := by decide
  rcases family_descends (prefixWord ++ tailWord_5121740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5121759 : List Nat := [1, 1, 2, 3, 2, 2, 4, 1, 1, 2, 4]
def baseStart_5121759 : Nat := 118140960795 + 5121759 * 2 ^ 59
def prefixEnd_5121759 : Nat := 4983230072969 + 3 ^ 40 * 5121759 * 2
def baseEnd_5121759 : Nat := 2629924163491331828057965

theorem tailTrace_5121759 : CollatzResearch.WordTrace tailWord_5121759 prefixEnd_5121759 2629924163491331828057965 := by
  unfold tailWord_5121759
  simp only [CollatzResearch.WordTrace]
  refine ⟨186805897451749344641752331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124537264967832896427834887 186805897451749344641752331)
  ·
    refine ⟨280208846177624016962628497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186805897451749344641752331 280208846177624016962628497)
    ·
      refine ⟨210156634633218012721971373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 280208846177624016962628497 210156634633218012721971373)
      ·
        refine ⟨78808737987456754770739265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 210156634633218012721971373 78808737987456754770739265)
        ·
          refine ⟨59106553490592566078054449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78808737987456754770739265 59106553490592566078054449)
          ·
            refine ⟨44329915117944424558540837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59106553490592566078054449 44329915117944424558540837)
            ·
              refine ⟨8311859084614579604726407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44329915117944424558540837 8311859084614579604726407)
              ·
                refine ⟨12467788626921869407089611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8311859084614579604726407 12467788626921869407089611)
                ·
                  refine ⟨18701682940382804110634417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12467788626921869407089611 18701682940382804110634417)
                  ·
                    refine ⟨14026262205287103082975813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18701682940382804110634417 14026262205287103082975813)
                    ·
                      refine ⟨2629924163491331828057965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14026262205287103082975813 2629924163491331828057965)
                      ·
                        rfl

theorem cell23_5121759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 1, 1, 2, 4].length) (baseStart_5121759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5121759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5121759 prefixEnd_5121759 := by exact prefixLift 5121759
  have htrace : WordTrace (prefixWord ++ tailWord_5121759) baseStart_5121759 baseEnd_5121759 := by
    simpa [prefixWord, tailWord_5121759, baseEnd_5121759] using wordTrace_append hprefix tailTrace_5121759
  have hstable : (prefixWord ++ tailWord_5121759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5121759).length < 2 ^ (prefixWord ++ tailWord_5121759).sum := by decide
  have hdescent : baseEnd_5121759 < baseStart_5121759 := by decide
  rcases family_descends (prefixWord ++ tailWord_5121759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5121767 : List Nat := [1, 1, 5, 4, 2, 1, 1, 1, 2, 3, 2]
def baseStart_5121767 : Nat := 118140960795 + 5121767 * 2 ^ 59
def prefixEnd_5121767 : Nat := 4983230072969 + 3 ^ 40 * 5121767 * 2
def baseEnd_5121767 : Nat := 2629928271336567796757929

theorem tailTrace_5121767 : CollatzResearch.WordTrace tailWord_5121767 prefixEnd_5121767 2629928271336567796757929 := by
  unfold tailWord_5121767
  simp only [CollatzResearch.WordTrace]
  refine ⟨186806189235720362008043555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124537459490480241338695703 186806189235720362008043555)
  ·
    refine ⟨280209283853580543012065333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186806189235720362008043555 280209283853580543012065333)
    ·
      refine ⟨26269620361273175907381125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 280209283853580543012065333 26269620361273175907381125)
      ·
        refine ⟨4925553817738720482633961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26269620361273175907381125 4925553817738720482633961)
        ·
          refine ⟨3694165363304040361975471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4925553817738720482633961 3694165363304040361975471)
          ·
            refine ⟨5541248044956060542963207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3694165363304040361975471 5541248044956060542963207)
            ·
              refine ⟨8311872067434090814444811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5541248044956060542963207 8311872067434090814444811)
              ·
                refine ⟨12467808101151136221667217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8311872067434090814444811 12467808101151136221667217)
                ·
                  refine ⟨9350856075863352166250413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12467808101151136221667217 9350856075863352166250413)
                  ·
                    refine ⟨3506571028448757062343905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9350856075863352166250413 3506571028448757062343905)
                    ·
                      refine ⟨2629928271336567796757929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3506571028448757062343905 2629928271336567796757929)
                      ·
                        rfl

theorem cell23_5121767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_5121767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5121767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5121767 prefixEnd_5121767 := by exact prefixLift 5121767
  have htrace : WordTrace (prefixWord ++ tailWord_5121767) baseStart_5121767 baseEnd_5121767 := by
    simpa [prefixWord, tailWord_5121767, baseEnd_5121767] using wordTrace_append hprefix tailTrace_5121767
  have hstable : (prefixWord ++ tailWord_5121767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5121767).length < 2 ^ (prefixWord ++ tailWord_5121767).sum := by decide
  have hdescent : baseEnd_5121767 < baseStart_5121767 := by decide
  rcases family_descends (prefixWord ++ tailWord_5121767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5121779 : List Nat := [1, 1, 1, 2, 2, 3, 4, 2, 1, 3, 3]
def baseStart_5121779 : Nat := 118140960795 + 5121779 * 2 ^ 59
def prefixEnd_5121779 : Nat := 4983230072969 + 3 ^ 40 * 5121779 * 2
def baseEnd_5121779 : Nat := 2629934433104421749807873

theorem tailTrace_5121779 : CollatzResearch.WordTrace tailWord_5121779 prefixEnd_5121779 2629934433104421749807873 := by
  unfold tailWord_5121779
  simp only [CollatzResearch.WordTrace]
  refine ⟨186806626911676888057480391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124537751274451258704986927 186806626911676888057480391)
  ·
    refine ⟨280209940367515332086220587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186806626911676888057480391 280209940367515332086220587)
    ·
      refine ⟨420314910551272998129330881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280209940367515332086220587 420314910551272998129330881)
      ·
        refine ⟨315236182913454748596998161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 420314910551272998129330881 315236182913454748596998161)
        ·
          refine ⟨236427137185091061447748621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 315236182913454748596998161 236427137185091061447748621)
          ·
            refine ⟨88660176444409148042905733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 236427137185091061447748621 88660176444409148042905733)
            ·
              refine ⟨16623783083326715258044825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88660176444409148042905733 16623783083326715258044825)
              ·
                refine ⟨12467837312495036443533619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16623783083326715258044825 12467837312495036443533619)
                ·
                  refine ⟨18701755968742554665300429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12467837312495036443533619 18701755968742554665300429)
                  ·
                    refine ⟨7013158488278457999487661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18701755968742554665300429 7013158488278457999487661)
                    ·
                      refine ⟨2629934433104421749807873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7013158488278457999487661 2629934433104421749807873)
                      ·
                        rfl

theorem cell23_5121779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 2, 1, 3, 3].length) (baseStart_5121779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5121779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5121779 prefixEnd_5121779 := by exact prefixLift 5121779
  have htrace : WordTrace (prefixWord ++ tailWord_5121779) baseStart_5121779 baseEnd_5121779 := by
    simpa [prefixWord, tailWord_5121779, baseEnd_5121779] using wordTrace_append hprefix tailTrace_5121779
  have hstable : (prefixWord ++ tailWord_5121779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5121779).length < 2 ^ (prefixWord ++ tailWord_5121779).sum := by decide
  have hdescent : baseEnd_5121779 < baseStart_5121779 := by decide
  rcases family_descends (prefixWord ++ tailWord_5121779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5121780 : List Nat := [2, 6, 1, 1, 1, 2, 1, 3, 1, 1, 4]
def baseStart_5121780 : Nat := 118140960795 + 5121780 * 2 ^ 59
def prefixEnd_5121780 : Nat := 4983230072969 + 3 ^ 40 * 5121780 * 2
def baseEnd_5121780 : Nat := 2629934946585076245895369

theorem tailTrace_5121780 : CollatzResearch.WordTrace tailWord_5121780 prefixEnd_5121780 2629934946585076245895369 := by
  unfold tailWord_5121780
  simp only [CollatzResearch.WordTrace]
  refine ⟨93403331692336632614133397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124537775589782176818844529 93403331692336632614133397)
  ·
    refine ⟨4378281173078279653787503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 93403331692336632614133397 4378281173078279653787503)
    ·
      refine ⟨6567421759617419480681255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4378281173078279653787503 6567421759617419480681255)
      ·
        refine ⟨9851132639426129221021883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6567421759617419480681255 9851132639426129221021883)
        ·
          refine ⟨14776698959139193831532825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9851132639426129221021883 14776698959139193831532825)
          ·
            refine ⟨11082524219354395373649619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14776698959139193831532825 11082524219354395373649619)
            ·
              refine ⟨16623786329031593060474429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11082524219354395373649619 16623786329031593060474429)
              ·
                refine ⟨6233919873386847397677911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16623786329031593060474429 6233919873386847397677911)
                ·
                  refine ⟨9350879810080271096516867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6233919873386847397677911 9350879810080271096516867)
                  ·
                    refine ⟨14026319715120406644775301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9350879810080271096516867 14026319715120406644775301)
                    ·
                      refine ⟨2629934946585076245895369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14026319715120406644775301 2629934946585076245895369)
                      ·
                        rfl

theorem cell23_5121780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_5121780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5121780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5121780 prefixEnd_5121780 := by exact prefixLift 5121780
  have htrace : WordTrace (prefixWord ++ tailWord_5121780) baseStart_5121780 baseEnd_5121780 := by
    simpa [prefixWord, tailWord_5121780, baseEnd_5121780] using wordTrace_append hprefix tailTrace_5121780
  have hstable : (prefixWord ++ tailWord_5121780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5121780).length < 2 ^ (prefixWord ++ tailWord_5121780).sum := by decide
  have hdescent : baseEnd_5121780 < baseStart_5121780 := by decide
  rcases family_descends (prefixWord ++ tailWord_5121780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5121790 : List Nat := [4, 2, 2, 1, 3, 2, 1, 2, 2, 4]
def baseStart_5121790 : Nat := 118140960795 + 5121790 * 2 ^ 59
def prefixEnd_5121790 : Nat := 4983230072969 + 3 ^ 40 * 5121790 * 2
def baseEnd_5121790 : Nat := 876646693797207068923441

theorem tailTrace_5121790 : CollatzResearch.WordTrace tailWord_5121790 prefixEnd_5121790 876646693797207068923441 := by
  unfold tailWord_5121790
  simp only [CollatzResearch.WordTrace]
  refine ⟨23350878514329629617016353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124538018743091357957420549 23350878514329629617016353)
  ·
    refine ⟨17513158885747222212762265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23350878514329629617016353 17513158885747222212762265)
    ·
      refine ⟨13134869164310416659571699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17513158885747222212762265 13134869164310416659571699)
      ·
        refine ⟨19702303746465624989357549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13134869164310416659571699 19702303746465624989357549)
        ·
          refine ⟨7388363904924609371009081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19702303746465624989357549 7388363904924609371009081)
          ·
            refine ⟨5541272928693457028256811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7388363904924609371009081 5541272928693457028256811)
            ·
              refine ⟨8311909393040185542385217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5541272928693457028256811 8311909393040185542385217)
              ·
                refine ⟨6233932044780139156788913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8311909393040185542385217 6233932044780139156788913)
                ·
                  refine ⟨4675449033585104367591685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6233932044780139156788913 4675449033585104367591685)
                  ·
                    refine ⟨876646693797207068923441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4675449033585104367591685 876646693797207068923441)
                    ·
                      rfl

theorem cell23_5121790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_5121790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5121790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5121790 prefixEnd_5121790 := by exact prefixLift 5121790
  have htrace : WordTrace (prefixWord ++ tailWord_5121790) baseStart_5121790 baseEnd_5121790 := by
    simpa [prefixWord, tailWord_5121790, baseEnd_5121790] using wordTrace_append hprefix tailTrace_5121790
  have hstable : (prefixWord ++ tailWord_5121790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5121790).length < 2 ^ (prefixWord ++ tailWord_5121790).sum := by decide
  have hdescent : baseEnd_5121790 < baseStart_5121790 := by decide
  rcases family_descends (prefixWord ++ tailWord_5121790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5121792 : List Nat := [2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 5]
def baseStart_5121792 : Nat := 118140960795 + 5121792 * 2 ^ 59
def prefixEnd_5121792 : Nat := 4983230072969 + 3 ^ 40 * 5121792 * 2
def baseEnd_5121792 : Nat := 2629941108352930198945313

theorem tailTrace_5121792 : CollatzResearch.WordTrace tailWord_5121792 prefixEnd_5121792 2629941108352930198945313 := by
  unfold tailWord_5121792
  simp only [CollatzResearch.WordTrace]
  refine ⟨93403550530314895638851815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124538067373753194185135753 93403550530314895638851815)
  ·
    refine ⟨140105325795472343458277723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93403550530314895638851815 140105325795472343458277723)
    ·
      refine ⟨210157988693208515187416585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140105325795472343458277723 210157988693208515187416585)
      ·
        refine ⟨157618491519906386390562439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210157988693208515187416585 157618491519906386390562439)
        ·
          refine ⟨236427737279859579585843659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157618491519906386390562439 236427737279859579585843659)
          ·
            refine ⟨354641605919789369378765489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236427737279859579585843659 354641605919789369378765489)
            ·
              refine ⟨265981204439842027034074117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 354641605919789369378765489 265981204439842027034074117)
              ·
                refine ⟨49871475832470380068888897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 265981204439842027034074117 49871475832470380068888897)
                ·
                  refine ⟨37403606874352785051666673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49871475832470380068888897 37403606874352785051666673)
                  ·
                    refine ⟨28052705155764588788750005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37403606874352785051666673 28052705155764588788750005)
                    ·
                      refine ⟨2629941108352930198945313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28052705155764588788750005 2629941108352930198945313)
                      ·
                        rfl

theorem cell23_5121792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 5].length) (baseStart_5121792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5121792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5121792 prefixEnd_5121792 := by exact prefixLift 5121792
  have htrace : WordTrace (prefixWord ++ tailWord_5121792) baseStart_5121792 baseEnd_5121792 := by
    simpa [prefixWord, tailWord_5121792, baseEnd_5121792] using wordTrace_append hprefix tailTrace_5121792
  have hstable : (prefixWord ++ tailWord_5121792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5121792).length < 2 ^ (prefixWord ++ tailWord_5121792).sum := by decide
  have hdescent : baseEnd_5121792 < baseStart_5121792 := by decide
  rcases family_descends (prefixWord ++ tailWord_5121792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5121806 : List Nat := [4, 1, 1, 2, 1, 1, 2, 1, 5, 3, 2]
def baseStart_5121806 : Nat := 118140960795 + 5121806 * 2 ^ 59
def prefixEnd_5121806 : Nat := 4983230072969 + 3 ^ 40 * 5121806 * 2
def baseEnd_5121806 : Nat := 2629948297082093144170249

theorem tailTrace_5121806 : CollatzResearch.WordTrace tailWord_5121806 prefixEnd_5121806 2629948297082093144170249 := by
  unfold tailWord_5121806
  simp only [CollatzResearch.WordTrace]
  refine ⟨23350951460322383958589159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124538407788386047779142181 23350951460322383958589159)
  ·
    refine ⟨35026427190483575937883739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23350951460322383958589159 35026427190483575937883739)
    ·
      refine ⟨52539640785725363906825609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35026427190483575937883739 52539640785725363906825609)
      ·
        refine ⟨39404730589294022930119207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52539640785725363906825609 39404730589294022930119207)
        ·
          refine ⟨59107095883941034395178811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39404730589294022930119207 59107095883941034395178811)
          ·
            refine ⟨88660643825911551592768217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59107095883941034395178811 88660643825911551592768217)
            ·
              refine ⟨66495482869433663694576163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88660643825911551592768217 66495482869433663694576163)
              ·
                refine ⟨99743224304150495541864245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66495482869433663694576163 99743224304150495541864245)
                ·
                  refine ⟨9350927278514108957049773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 99743224304150495541864245 9350927278514108957049773)
                  ·
                    refine ⟨3506597729442790858893665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9350927278514108957049773 3506597729442790858893665)
                    ·
                      refine ⟨2629948297082093144170249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3506597729442790858893665 2629948297082093144170249)
                      ·
                        rfl

theorem cell23_5121806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 5, 3, 2].length) (baseStart_5121806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5121806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5121806 prefixEnd_5121806 := by exact prefixLift 5121806
  have htrace : WordTrace (prefixWord ++ tailWord_5121806) baseStart_5121806 baseEnd_5121806 := by
    simpa [prefixWord, tailWord_5121806, baseEnd_5121806] using wordTrace_append hprefix tailTrace_5121806
  have hstable : (prefixWord ++ tailWord_5121806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5121806).length < 2 ^ (prefixWord ++ tailWord_5121806).sum := by decide
  have hdescent : baseEnd_5121806 < baseStart_5121806 := by decide
  rcases family_descends (prefixWord ++ tailWord_5121806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5121823 : List Nat := [1, 1, 2, 4, 2, 1, 4, 2, 1, 3, 2]
def baseStart_5121823 : Nat := 118140960795 + 5121823 * 2 ^ 59
def prefixEnd_5121823 : Nat := 4983230072969 + 3 ^ 40 * 5121823 * 2
def baseEnd_5121823 : Nat := 2629957026253219577657671

theorem tailTrace_5121823 : CollatzResearch.WordTrace tailWord_5121823 prefixEnd_5121823 2629957026253219577657671 := by
  unfold tailWord_5121823
  simp only [CollatzResearch.WordTrace]
  refine ⟨186808231723517483572082123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124538821149011655714721415 186808231723517483572082123)
  ·
    refine ⟨280212347585276225358123185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186808231723517483572082123 280212347585276225358123185)
    ·
      refine ⟨210159260688957169018592389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 280212347585276225358123185 210159260688957169018592389)
      ·
        refine ⟨39404861379179469190986073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 210159260688957169018592389 39404861379179469190986073)
        ·
          refine ⟨29553646034384601893239555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39404861379179469190986073 29553646034384601893239555)
          ·
            refine ⟨44330469051576902839859333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29553646034384601893239555 44330469051576902839859333)
            ·
              refine ⟨8311962947170669282473625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44330469051576902839859333 8311962947170669282473625)
              ·
                refine ⟨6233972210378001961855219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8311962947170669282473625 6233972210378001961855219)
                ·
                  refine ⟨9350958315567002942782829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6233972210378001961855219 9350958315567002942782829)
                  ·
                    refine ⟨3506609368337626103543561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9350958315567002942782829 3506609368337626103543561)
                    ·
                      refine ⟨2629957026253219577657671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3506609368337626103543561 2629957026253219577657671)
                      ·
                        rfl

theorem cell23_5121823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 2, 1, 3, 2].length) (baseStart_5121823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5121823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5121823 prefixEnd_5121823 := by exact prefixLift 5121823
  have htrace : WordTrace (prefixWord ++ tailWord_5121823) baseStart_5121823 baseEnd_5121823 := by
    simpa [prefixWord, tailWord_5121823, baseEnd_5121823] using wordTrace_append hprefix tailTrace_5121823
  have hstable : (prefixWord ++ tailWord_5121823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5121823).length < 2 ^ (prefixWord ++ tailWord_5121823).sum := by decide
  have hdescent : baseEnd_5121823 < baseStart_5121823 := by decide
  rcases family_descends (prefixWord ++ tailWord_5121823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5121859 : List Nat := [1, 1, 1, 3, 1, 5, 3, 1, 7]
def baseStart_5121859 : Nat := 118140960795 + 5121859 * 2 ^ 59
def prefixEnd_5121859 : Nat := 4983230072969 + 3 ^ 40 * 5121859 * 2
def baseEnd_5121859 : Nat := 292219501284086826311945

theorem tailTrace_5121859 : CollatzResearch.WordTrace tailWord_5121859 prefixEnd_5121859 292219501284086826311945 := by
  unfold tailWord_5121859
  simp only [CollatzResearch.WordTrace]
  refine ⟨186809544751387061720392631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124539696500924707813595087 186809544751387061720392631)
  ·
    refine ⟨280214317127080592580588947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186809544751387061720392631 280214317127080592580588947)
    ·
      refine ⟨420321475690620888870883421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280214317127080592580588947 420321475690620888870883421)
      ·
        refine ⟨157620553383982833326581283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 420321475690620888870883421 157620553383982833326581283)
        ·
          refine ⟨236430830075974249989871925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157620553383982833326581283 236430830075974249989871925)
          ·
            refine ⟨22165390319622585936550493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 236430830075974249989871925 22165390319622585936550493)
            ·
              refine ⟨8312021369858469726206435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22165390319622585936550493 8312021369858469726206435)
              ·
                refine ⟨12468032054787704589309653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8312021369858469726206435 12468032054787704589309653)
                ·
                  refine ⟨292219501284086826311945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12468032054787704589309653 292219501284086826311945)
                  ·
                    rfl

theorem cell23_5121859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 1, 7].length) (baseStart_5121859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5121859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5121859 prefixEnd_5121859 := by exact prefixLift 5121859
  have htrace : WordTrace (prefixWord ++ tailWord_5121859) baseStart_5121859 baseEnd_5121859 := by
    simpa [prefixWord, tailWord_5121859, baseEnd_5121859] using wordTrace_append hprefix tailTrace_5121859
  have hstable : (prefixWord ++ tailWord_5121859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5121859).length < 2 ^ (prefixWord ++ tailWord_5121859).sum := by decide
  have hdescent : baseEnd_5121859 < baseStart_5121859 := by decide
  rcases family_descends (prefixWord ++ tailWord_5121859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5121910 : List Nat := [5, 1, 1, 3, 2, 1, 1, 4, 5]
def baseStart_5121910 : Nat := 118140960795 + 5121910 * 2 ^ 59
def prefixEnd_5121910 : Nat := 4983230072969 + 3 ^ 40 * 5121910 * 2
def baseEnd_5121910 : Nat := 292222411007795637474419

theorem tailTrace_5121910 : CollatzResearch.WordTrace tailWord_5121910 prefixEnd_5121910 292222411007795637474419 := by
  unfold tailWord_5121910
  simp only [CollatzResearch.WordTrace]
  refine ⟨11675712804637643589406199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 124540936582801531620332789 11675712804637643589406199)
  ·
    refine ⟨17513569206956465384109299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11675712804637643589406199 17513569206956465384109299)
    ·
      refine ⟨26270353810434698076163949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17513569206956465384109299 26270353810434698076163949)
      ·
        refine ⟨9851382678913011778561481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26270353810434698076163949 9851382678913011778561481)
        ·
          refine ⟨7388537009184758833921111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9851382678913011778561481 7388537009184758833921111)
          ·
            refine ⟨11082805513777138250881667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7388537009184758833921111 11082805513777138250881667)
            ·
              refine ⟨16624208270665707376322501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11082805513777138250881667 16624208270665707376322501)
              ·
                refine ⟨3117039050749820133060469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16624208270665707376322501 3117039050749820133060469)
                ·
                  refine ⟨292222411007795637474419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3117039050749820133060469 292222411007795637474419)
                  ·
                    rfl

theorem cell23_5121910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 4, 5].length) (baseStart_5121910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5121910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5121910 prefixEnd_5121910 := by exact prefixLift 5121910
  have htrace : WordTrace (prefixWord ++ tailWord_5121910) baseStart_5121910 baseEnd_5121910 := by
    simpa [prefixWord, tailWord_5121910, baseEnd_5121910] using wordTrace_append hprefix tailTrace_5121910
  have hstable : (prefixWord ++ tailWord_5121910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5121910).length < 2 ^ (prefixWord ++ tailWord_5121910).sum := by decide
  have hdescent : baseEnd_5121910 < baseStart_5121910 := by decide
  rcases family_descends (prefixWord ++ tailWord_5121910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5121943 : List Nat := [1, 1, 3, 3, 1, 5, 1, 1, 2, 1, 4]
def baseStart_5121943 : Nat := 118140960795 + 5121943 * 2 ^ 59
def prefixEnd_5121943 : Nat := 4983230072969 + 3 ^ 40 * 5121943 * 2
def baseEnd_5121943 : Nat := 2630018643931759108157119

theorem tailTrace_5121943 : CollatzResearch.WordTrace tailWord_5121943 prefixEnd_5121943 2630018643931759108157119 := by
  unfold tailWord_5121943
  simp only [CollatzResearch.WordTrace]
  refine ⟨186812608483082744066450483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124541738988721829377633655 186812608483082744066450483)
  ·
    refine ⟨280218912724624116099675725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186812608483082744066450483 280218912724624116099675725)
    ·
      refine ⟨105082092271734043537378397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 280218912724624116099675725 105082092271734043537378397)
      ·
        refine ⟨39405784601900266326516899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105082092271734043537378397 39405784601900266326516899)
        ·
          refine ⟨59108676902850399489775349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39405784601900266326516899 59108676902850399489775349)
          ·
            refine ⟨5541438459642224952166439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59108676902850399489775349 5541438459642224952166439)
            ·
              refine ⟨8312157689463337428249659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5541438459642224952166439 8312157689463337428249659)
              ·
                refine ⟨12468236534195006142374489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8312157689463337428249659 12468236534195006142374489)
                ·
                  refine ⟨9351177400646254606780867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12468236534195006142374489 9351177400646254606780867)
                  ·
                    refine ⟨14026766100969381910171301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9351177400646254606780867 14026766100969381910171301)
                    ·
                      refine ⟨2630018643931759108157119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14026766100969381910171301 2630018643931759108157119)
                      ·
                        rfl

theorem cell23_5121943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 1, 2, 1, 4].length) (baseStart_5121943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5121943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5121943 prefixEnd_5121943 := by exact prefixLift 5121943
  have htrace : WordTrace (prefixWord ++ tailWord_5121943) baseStart_5121943 baseEnd_5121943 := by
    simpa [prefixWord, tailWord_5121943, baseEnd_5121943] using wordTrace_append hprefix tailTrace_5121943
  have hstable : (prefixWord ++ tailWord_5121943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5121943).length < 2 ^ (prefixWord ++ tailWord_5121943).sum := by decide
  have hdescent : baseEnd_5121943 < baseStart_5121943 := by decide
  rcases family_descends (prefixWord ++ tailWord_5121943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5122053 : List Nat := [1, 3, 1, 1, 2, 5, 1, 1, 3, 2, 3]
def baseStart_5122053 : Nat := 118140960795 + 5122053 * 2 ^ 59
def prefixEnd_5122053 : Nat := 4983230072969 + 3 ^ 40 * 5122053 * 2
def baseEnd_5122053 : Nat := 2630075126803753677781613

theorem tailTrace_5122053 : CollatzResearch.WordTrace tailWord_5122053 prefixEnd_5122053 2630075126803753677781613 := by
  unfold tailWord_5122053
  simp only [CollatzResearch.WordTrace]
  refine ⟨186816620512684232852954813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124544413675122821901969875 186816620512684232852954813)
  ·
    refine ⟨70056232692256587319858055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186816620512684232852954813 70056232692256587319858055)
    ·
      refine ⟨105084349038384880979787083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70056232692256587319858055 105084349038384880979787083)
      ·
        refine ⟨157626523557577321469680625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105084349038384880979787083 157626523557577321469680625)
        ·
          refine ⟨118219892668182991102260469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157626523557577321469680625 118219892668182991102260469)
          ·
            refine ⟨11083114937642155415836919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 118219892668182991102260469 11083114937642155415836919)
            ·
              refine ⟨16624672406463233123755379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11083114937642155415836919 16624672406463233123755379)
              ·
                refine ⟨24937008609694849685633069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16624672406463233123755379 24937008609694849685633069)
                ·
                  refine ⟨9351378228635568632112401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24937008609694849685633069 9351378228635568632112401)
                  ·
                    refine ⟨7013533671476676474084301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9351378228635568632112401 7013533671476676474084301)
                    ·
                      refine ⟨2630075126803753677781613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7013533671476676474084301 2630075126803753677781613)
                      ·
                        rfl

theorem cell23_5122053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 3, 2, 3].length) (baseStart_5122053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5122053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5122053 prefixEnd_5122053 := by exact prefixLift 5122053
  have htrace : WordTrace (prefixWord ++ tailWord_5122053) baseStart_5122053 baseEnd_5122053 := by
    simpa [prefixWord, tailWord_5122053, baseEnd_5122053] using wordTrace_append hprefix tailTrace_5122053
  have hstable : (prefixWord ++ tailWord_5122053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5122053).length < 2 ^ (prefixWord ++ tailWord_5122053).sum := by decide
  have hdescent : baseEnd_5122053 < baseStart_5122053 := by decide
  rcases family_descends (prefixWord ++ tailWord_5122053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5122106 : List Nat := [3, 1, 1, 1, 3, 1, 1, 1, 4, 3, 4]
def baseStart_5122106 : Nat := 118140960795 + 5122106 * 2 ^ 59
def prefixEnd_5122106 : Nat := 4983230072969 + 3 ^ 40 * 5122106 * 2
def baseEnd_5122106 : Nat := 2630102341278441970418869

theorem tailTrace_5122106 : CollatzResearch.WordTrace tailWord_5122106 prefixEnd_5122106 2630102341278441970418869 := by
  unfold tailWord_5122106
  simp only [CollatzResearch.WordTrace]
  refine ⟨46704638395373055726158543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124545702387661481936422781 46704638395373055726158543)
  ·
    refine ⟨70056957593059583589237815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46704638395373055726158543 70056957593059583589237815)
    ·
      refine ⟨105085436389589375383856723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70056957593059583589237815 105085436389589375383856723)
      ·
        refine ⟨157628154584384063075785085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105085436389589375383856723 157628154584384063075785085)
        ·
          refine ⟨59110557969144023653419407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 157628154584384063075785085 59110557969144023653419407)
          ·
            refine ⟨88665836953716035480129111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59110557969144023653419407 88665836953716035480129111)
            ·
              refine ⟨132998755430574053220193667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88665836953716035480129111 132998755430574053220193667)
              ·
                refine ⟨199498133145861079830290501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132998755430574053220193667 199498133145861079830290501)
                ·
                  refine ⟨37405899964848952468179469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 199498133145861079830290501 37405899964848952468179469)
                  ·
                    refine ⟨14027212486818357175567301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37405899964848952468179469 14027212486818357175567301)
                    ·
                      refine ⟨2630102341278441970418869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14027212486818357175567301 2630102341278441970418869)
                      ·
                        rfl

theorem cell23_5122106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 4, 3, 4].length) (baseStart_5122106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5122106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5122106 prefixEnd_5122106 := by exact prefixLift 5122106
  have htrace : WordTrace (prefixWord ++ tailWord_5122106) baseStart_5122106 baseEnd_5122106 := by
    simpa [prefixWord, tailWord_5122106, baseEnd_5122106] using wordTrace_append hprefix tailTrace_5122106
  have hstable : (prefixWord ++ tailWord_5122106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5122106).length < 2 ^ (prefixWord ++ tailWord_5122106).sum := by decide
  have hdescent : baseEnd_5122106 < baseStart_5122106 := by decide
  rcases family_descends (prefixWord ++ tailWord_5122106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5122134 : List Nat := [5, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3]
def baseStart_5122134 : Nat := 118140960795 + 5122134 * 2 ^ 59
def prefixEnd_5122134 : Nat := 4983230072969 + 3 ^ 40 * 5122134 * 2
def baseEnd_5122134 : Nat := 2630116718736767860868741

theorem tailTrace_5122134 : CollatzResearch.WordTrace tailWord_5122134 prefixEnd_5122134 2630116718736767860868741 := by
  unfold tailWord_5122134
  simp only [CollatzResearch.WordTrace]
  refine ⟨11676223426586923980415841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 124546383216927189124435637 11676223426586923980415841)
  ·
    refine ⟨8757167569940192985311881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11676223426586923980415841 8757167569940192985311881)
    ·
      refine ⟨6567875677455144738983911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8757167569940192985311881 6567875677455144738983911)
      ·
        refine ⟨9851813516182717108475867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6567875677455144738983911 9851813516182717108475867)
        ·
          refine ⟨14777720274274075662713801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9851813516182717108475867 14777720274274075662713801)
          ·
            refine ⟨11083290205705556747035351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14777720274274075662713801 11083290205705556747035351)
            ·
              refine ⟨16624935308558335120553027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11083290205705556747035351 16624935308558335120553027)
              ·
                refine ⟨24937402962837502680829541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16624935308558335120553027 24937402962837502680829541)
                ·
                  refine ⟨4675763055532031752655539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24937402962837502680829541 4675763055532031752655539)
                  ·
                    refine ⟨7013644583298047628983309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4675763055532031752655539 7013644583298047628983309)
                    ·
                      refine ⟨2630116718736767860868741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7013644583298047628983309 2630116718736767860868741)
                      ·
                        rfl

theorem cell23_5122134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_5122134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5122134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5122134 prefixEnd_5122134 := by exact prefixLift 5122134
  have htrace : WordTrace (prefixWord ++ tailWord_5122134) baseStart_5122134 baseEnd_5122134 := by
    simpa [prefixWord, tailWord_5122134, baseEnd_5122134] using wordTrace_append hprefix tailTrace_5122134
  have hstable : (prefixWord ++ tailWord_5122134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5122134).length < 2 ^ (prefixWord ++ tailWord_5122134).sum := by decide
  have hdescent : baseEnd_5122134 < baseStart_5122134 := by decide
  rcases family_descends (prefixWord ++ tailWord_5122134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5122213 : List Nat := [1, 3, 1, 2, 1, 3, 1, 2, 4, 1, 4]
def baseStart_5122213 : Nat := 118140960795 + 5122213 * 2 ^ 59
def prefixEnd_5122213 : Nat := 4983230072969 + 3 ^ 40 * 5122213 * 2
def baseEnd_5122213 : Nat := 2630157283708473051780877

theorem tailTrace_5122213 : CollatzResearch.WordTrace tailWord_5122213 prefixEnd_5122213 2630157283708473051780877 := by
  unfold tailWord_5122213
  simp only [CollatzResearch.WordTrace]
  refine ⟨186822456192104580178779293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124548304128069720119186195 186822456192104580178779293)
  ·
    refine ⟨70058421072039217567042235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186822456192104580178779293 70058421072039217567042235)
    ·
      refine ⟨105087631608058826350563353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70058421072039217567042235 105087631608058826350563353)
      ·
        refine ⟨78815723706044119762922515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105087631608058826350563353 78815723706044119762922515)
        ·
          refine ⟨118223585559066179644383773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78815723706044119762922515 118223585559066179644383773)
          ·
            refine ⟨44333844584649817366643915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118223585559066179644383773 44333844584649817366643915)
            ·
              refine ⟨66500766876974726049965873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44333844584649817366643915 66500766876974726049965873)
              ·
                refine ⟨49875575157731044537474405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66500766876974726049965873 49875575157731044537474405)
                ·
                  refine ⟨9351670342074570850776451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49875575157731044537474405 9351670342074570850776451)
                  ·
                    refine ⟨14027505513111856276164677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9351670342074570850776451 14027505513111856276164677)
                    ·
                      refine ⟨2630157283708473051780877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14027505513111856276164677 2630157283708473051780877)
                      ·
                        rfl

theorem cell23_5122213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 4, 1, 4].length) (baseStart_5122213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5122213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5122213 prefixEnd_5122213 := by exact prefixLift 5122213
  have htrace : WordTrace (prefixWord ++ tailWord_5122213) baseStart_5122213 baseEnd_5122213 := by
    simpa [prefixWord, tailWord_5122213, baseEnd_5122213] using wordTrace_append hprefix tailTrace_5122213
  have hstable : (prefixWord ++ tailWord_5122213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5122213).length < 2 ^ (prefixWord ++ tailWord_5122213).sum := by decide
  have hdescent : baseEnd_5122213 < baseStart_5122213 := by decide
  rcases family_descends (prefixWord ++ tailWord_5122213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5122223 : List Nat := [1, 1, 2, 1, 2, 3, 1, 3, 5, 4]
def baseStart_5122223 : Nat := 118140960795 + 5122223 * 2 ^ 59
def prefixEnd_5122223 : Nat := 4983230072969 + 3 ^ 40 * 5122223 * 2
def baseEnd_5122223 : Nat := 876720806171672670885277

theorem tailTrace_5122223 : CollatzResearch.WordTrace tailWord_5122223 prefixEnd_5122223 876720806171672670885277 := by
  unfold tailWord_5122223
  simp only [CollatzResearch.WordTrace]
  refine ⟨186822820922068351886643323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124548547281378901257762215 186822820922068351886643323)
  ·
    refine ⟨280234231383102527829964985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186822820922068351886643323 280234231383102527829964985)
    ·
      refine ⟨210175673537326895872473739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 280234231383102527829964985 210175673537326895872473739)
      ·
        refine ⟨315263510305990343808710609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210175673537326895872473739 315263510305990343808710609)
        ·
          refine ⟨236447632729492757856532957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 315263510305990343808710609 236447632729492757856532957)
          ·
            refine ⟨88667862273559784196199859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 236447632729492757856532957 88667862273559784196199859)
            ·
              refine ⟨133001793410339676294299789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88667862273559784196199859 133001793410339676294299789)
              ·
                refine ⟨49875672528877378610362421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 133001793410339676294299789 49875672528877378610362421)
                ·
                  refine ⟨4675844299582254244721477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49875672528877378610362421 4675844299582254244721477)
                  ·
                    refine ⟨876720806171672670885277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4675844299582254244721477 876720806171672670885277)
                    ·
                      rfl

theorem cell23_5122223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 5, 4].length) (baseStart_5122223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5122223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5122223 prefixEnd_5122223 := by exact prefixLift 5122223
  have htrace : WordTrace (prefixWord ++ tailWord_5122223) baseStart_5122223 baseEnd_5122223 := by
    simpa [prefixWord, tailWord_5122223, baseEnd_5122223] using wordTrace_append hprefix tailTrace_5122223
  have hstable : (prefixWord ++ tailWord_5122223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5122223).length < 2 ^ (prefixWord ++ tailWord_5122223).sum := by decide
  have hdescent : baseEnd_5122223 < baseStart_5122223 := by decide
  rcases family_descends (prefixWord ++ tailWord_5122223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5122250 : List Nat := [3, 1, 2, 1, 3, 1, 1, 4, 2, 2, 3]
def baseStart_5122250 : Nat := 118140960795 + 5122250 * 2 ^ 59
def prefixEnd_5122250 : Nat := 4983230072969 + 3 ^ 40 * 5122250 * 2
def baseEnd_5122250 : Nat := 2630176282492689407018207

theorem tailTrace_5122250 : CollatzResearch.WordTrace tailWord_5122250 prefixEnd_5122250 2630176282492689407018207 := by
  unfold tailWord_5122250
  simp only [CollatzResearch.WordTrace]
  refine ⟨46705951423242633874469051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124549203795313690331917469 46705951423242633874469051)
  ·
    refine ⟨70058927134863950811703577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46705951423242633874469051 70058927134863950811703577)
    ·
      refine ⟨52544195351147963108777683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70058927134863950811703577 52544195351147963108777683)
      ·
        refine ⟨78816293026721944663166525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52544195351147963108777683 78816293026721944663166525)
        ·
          refine ⟨29556109885020729248687447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78816293026721944663166525 29556109885020729248687447)
          ·
            refine ⟨44334164827531093873031171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29556109885020729248687447 44334164827531093873031171)
            ·
              refine ⟨66501247241296640809546757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44334164827531093873031171 66501247241296640809546757)
              ·
                refine ⟨12468983857743120151790017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66501247241296640809546757 12468983857743120151790017)
                ·
                  refine ⟨9351737893307340113842513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12468983857743120151790017 9351737893307340113842513)
                  ·
                    refine ⟨7013803419980505085381885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9351737893307340113842513 7013803419980505085381885)
                    ·
                      refine ⟨2630176282492689407018207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7013803419980505085381885 2630176282492689407018207)
                      ·
                        rfl

theorem cell23_5122250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 4, 2, 2, 3].length) (baseStart_5122250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5122250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5122250 prefixEnd_5122250 := by exact prefixLift 5122250
  have htrace : WordTrace (prefixWord ++ tailWord_5122250) baseStart_5122250 baseEnd_5122250 := by
    simpa [prefixWord, tailWord_5122250, baseEnd_5122250] using wordTrace_append hprefix tailTrace_5122250
  have hstable : (prefixWord ++ tailWord_5122250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5122250).length < 2 ^ (prefixWord ++ tailWord_5122250).sum := by decide
  have hdescent : baseEnd_5122250 < baseStart_5122250 := by decide
  rcases family_descends (prefixWord ++ tailWord_5122250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5122263 : List Nat := [1, 1, 3, 2, 1, 2, 1, 2, 2, 5, 3]
def baseStart_5122263 : Nat := 118140960795 + 5122263 * 2 ^ 59
def prefixEnd_5122263 : Nat := 4983230072969 + 3 ^ 40 * 5122263 * 2
def baseEnd_5122263 : Nat := 2630182957741197856155647

theorem tailTrace_5122263 : CollatzResearch.WordTrace tailWord_5122263 prefixEnd_5122263 2630182957741197856155647 := by
  unfold tailWord_5122263
  simp only [CollatzResearch.WordTrace]
  refine ⟨186824279841923438718099443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124549519894615625812066295 186824279841923438718099443)
  ·
    refine ⟨280236419762885158077149165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186824279841923438718099443 280236419762885158077149165)
    ·
      refine ⟨105088657411081934278930937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 280236419762885158077149165 105088657411081934278930937)
      ·
        refine ⟨78816493058311450709198203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105088657411081934278930937 78816493058311450709198203)
        ·
          refine ⟨118224739587467176063797305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78816493058311450709198203 118224739587467176063797305)
          ·
            refine ⟨88668554690600382047847979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118224739587467176063797305 88668554690600382047847979)
            ·
              refine ⟨133002832035900573071771969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88668554690600382047847979 133002832035900573071771969)
              ·
                refine ⟨99752124026925429803828977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133002832035900573071771969 99752124026925429803828977)
                ·
                  refine ⟨74814093020194072352871733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99752124026925429803828977 74814093020194072352871733)
                  ·
                    refine ⟨7013821220643194283081725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 74814093020194072352871733 7013821220643194283081725)
                    ·
                      refine ⟨2630182957741197856155647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7013821220643194283081725 2630182957741197856155647)
                      ·
                        rfl

theorem cell23_5122263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 5, 3].length) (baseStart_5122263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5122263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5122263 prefixEnd_5122263 := by exact prefixLift 5122263
  have htrace : WordTrace (prefixWord ++ tailWord_5122263) baseStart_5122263 baseEnd_5122263 := by
    simpa [prefixWord, tailWord_5122263, baseEnd_5122263] using wordTrace_append hprefix tailTrace_5122263
  have hstable : (prefixWord ++ tailWord_5122263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5122263).length < 2 ^ (prefixWord ++ tailWord_5122263).sum := by decide
  have hdescent : baseEnd_5122263 < baseStart_5122263 := by decide
  rcases family_descends (prefixWord ++ tailWord_5122263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5122283 : List Nat := [1, 1, 1, 1, 2, 5, 1, 3, 3, 5]
def baseStart_5122283 : Nat := 118140960795 + 5122283 * 2 ^ 59
def prefixEnd_5122283 : Nat := 4983230072969 + 3 ^ 40 * 5122283 * 2
def baseEnd_5122283 : Nat := 876731075784762592635185

theorem tailTrace_5122283 : CollatzResearch.WordTrace tailWord_5122283 prefixEnd_5122283 876731075784762592635185 := by
  unfold tailWord_5122283
  simp only [CollatzResearch.WordTrace]
  refine ⟨186825009301850982133827503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124550006201233988089218335 186825009301850982133827503)
  ·
    refine ⟨280237513952776473200741255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186825009301850982133827503 280237513952776473200741255)
    ·
      refine ⟨420356270929164709801111883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280237513952776473200741255 420356270929164709801111883)
      ·
        refine ⟨630534406393747064701667825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 420356270929164709801111883 630534406393747064701667825)
        ·
          refine ⟨472900804795310298526250869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 630534406393747064701667825 472900804795310298526250869)
          ·
            refine ⟨44334450449560340486836019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 472900804795310298526250869 44334450449560340486836019)
            ·
              refine ⟨66501675674340510730254029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44334450449560340486836019 66501675674340510730254029)
              ·
                refine ⟨24938128377877691523845261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66501675674340510730254029 24938128377877691523845261)
                ·
                  refine ⟨9351798141704134321441973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24938128377877691523845261 9351798141704134321441973)
                  ·
                    refine ⟨876731075784762592635185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9351798141704134321441973 876731075784762592635185)
                    ·
                      rfl

theorem cell23_5122283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 3, 5].length) (baseStart_5122283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5122283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5122283 prefixEnd_5122283 := by exact prefixLift 5122283
  have htrace : WordTrace (prefixWord ++ tailWord_5122283) baseStart_5122283 baseEnd_5122283 := by
    simpa [prefixWord, tailWord_5122283, baseEnd_5122283] using wordTrace_append hprefix tailTrace_5122283
  have hstable : (prefixWord ++ tailWord_5122283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5122283).length < 2 ^ (prefixWord ++ tailWord_5122283).sum := by decide
  have hdescent : baseEnd_5122283 < baseStart_5122283 := by decide
  rcases family_descends (prefixWord ++ tailWord_5122283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5122314 : List Nat := [3, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3]
def baseStart_5122314 : Nat := 118140960795 + 5122314 * 2 ^ 59
def prefixEnd_5122314 : Nat := 4983230072969 + 3 ^ 40 * 5122314 * 2
def baseEnd_5122314 : Nat := 2630209145254577156617913

theorem tailTrace_5122314 : CollatzResearch.WordTrace tailWord_5122314 prefixEnd_5122314 2630209145254577156617913 := by
  unfold tailWord_5122314
  simp only [CollatzResearch.WordTrace]
  refine ⟨46706534991184668607051499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124550759976492449618803997 46706534991184668607051499)
  ·
    refine ⟨70059802486777002910577249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46706534991184668607051499 70059802486777002910577249)
    ·
      refine ⟨52544851865082752182932937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70059802486777002910577249 52544851865082752182932937)
      ·
        refine ⟨39408638898812064137199703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52544851865082752182932937 39408638898812064137199703)
        ·
          refine ⟨59112958348218096205799555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39408638898812064137199703 59112958348218096205799555)
          ·
            refine ⟨88669437522327144308699333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59112958348218096205799555 88669437522327144308699333)
            ·
              refine ⟨16625519535436339557881125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88669437522327144308699333 16625519535436339557881125)
              ·
                refine ⟨3117284912894313667102711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16625519535436339557881125 3117284912894313667102711)
                ·
                  refine ⟨4675927369341470500654067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3117284912894313667102711 4675927369341470500654067)
                  ·
                    refine ⟨7013891054012205750981101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4675927369341470500654067 7013891054012205750981101)
                    ·
                      refine ⟨2630209145254577156617913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7013891054012205750981101 2630209145254577156617913)
                      ·
                        rfl

theorem cell23_5122314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3].length) (baseStart_5122314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5122314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5122314 prefixEnd_5122314 := by exact prefixLift 5122314
  have htrace : WordTrace (prefixWord ++ tailWord_5122314) baseStart_5122314 baseEnd_5122314 := by
    simpa [prefixWord, tailWord_5122314, baseEnd_5122314] using wordTrace_append hprefix tailTrace_5122314
  have hstable : (prefixWord ++ tailWord_5122314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5122314).length < 2 ^ (prefixWord ++ tailWord_5122314).sum := by decide
  have hdescent : baseEnd_5122314 < baseStart_5122314 := by decide
  rcases family_descends (prefixWord ++ tailWord_5122314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5122334 : List Nat := [4, 3, 2, 1, 1, 1, 1, 4, 1, 5]
def baseStart_5122334 : Nat := 118140960795 + 5122334 * 2 ^ 59
def prefixEnd_5122334 : Nat := 4983230072969 + 3 ^ 40 * 5122334 * 2
def baseEnd_5122334 : Nat := 876739804955889026122607

theorem tailTrace_5122334 : CollatzResearch.WordTrace tailWord_5122334 prefixEnd_5122334 876739804955889026122607 := by
  unfold tailWord_5122334
  simp only [CollatzResearch.WordTrace]
  refine ⟨23353358678083277230491757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124551246283110811895956037 23353358678083277230491757)
  ·
    refine ⟨8757509504281228961434409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23353358678083277230491757 8757509504281228961434409)
    ·
      refine ⟨6568132128210921721075807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8757509504281228961434409 6568132128210921721075807)
      ·
        refine ⟨9852198192316382581613711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6568132128210921721075807 9852198192316382581613711)
        ·
          refine ⟨14778297288474573872420567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9852198192316382581613711 14778297288474573872420567)
          ·
            refine ⟨22167445932711860808630851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14778297288474573872420567 22167445932711860808630851)
            ·
              refine ⟨33251168899067791212946277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22167445932711860808630851 33251168899067791212946277)
              ·
                refine ⟨6234594168575210852427427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33251168899067791212946277 6234594168575210852427427)
                ·
                  refine ⟨9351891252862816278641141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6234594168575210852427427 9351891252862816278641141)
                  ·
                    refine ⟨876739804955889026122607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9351891252862816278641141 876739804955889026122607)
                    ·
                      rfl

theorem cell23_5122334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_5122334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5122334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5122334 prefixEnd_5122334 := by exact prefixLift 5122334
  have htrace : WordTrace (prefixWord ++ tailWord_5122334) baseStart_5122334 baseEnd_5122334 := by
    simpa [prefixWord, tailWord_5122334, baseEnd_5122334] using wordTrace_append hprefix tailTrace_5122334
  have hstable : (prefixWord ++ tailWord_5122334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5122334).length < 2 ^ (prefixWord ++ tailWord_5122334).sum := by decide
  have hdescent : baseEnd_5122334 < baseStart_5122334 := by decide
  rcases family_descends (prefixWord ++ tailWord_5122334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5122357 : List Nat := [1, 3, 3, 1, 2, 1, 1, 5, 1, 2, 3]
def baseStart_5122357 : Nat := 118140960795 + 5122357 * 2 ^ 59
def prefixEnd_5122357 : Nat := 4983230072969 + 3 ^ 40 * 5122357 * 2
def baseEnd_5122357 : Nat := 2630231224922720488380215

theorem tailTrace_5122357 : CollatzResearch.WordTrace tailWord_5122357 prefixEnd_5122357 2630231224922720488380215 := by
  unfold tailWord_5122357
  simp only [CollatzResearch.WordTrace]
  refine ⟨186827708303582892772021325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124551805535721928514680883 186827708303582892772021325)
  ·
    refine ⟨70060390613843584789507997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186827708303582892772021325 70060390613843584789507997)
    ·
      refine ⟨26272646480191344296065499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70060390613843584789507997 26272646480191344296065499)
      ·
        refine ⟨39408969720287016444098249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26272646480191344296065499 39408969720287016444098249)
        ·
          refine ⟨29556727290215262333073687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39408969720287016444098249 29556727290215262333073687)
          ·
            refine ⟨44335090935322893499610531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29556727290215262333073687 44335090935322893499610531)
            ·
              refine ⟨66502636402984340249415797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44335090935322893499610531 66502636402984340249415797)
              ·
                refine ⟨6234622162779781898382731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66502636402984340249415797 6234622162779781898382731)
                ·
                  refine ⟨9351933244169672847574097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6234622162779781898382731 9351933244169672847574097)
                  ·
                    refine ⟨7013949933127254635680573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9351933244169672847574097 7013949933127254635680573)
                    ·
                      refine ⟨2630231224922720488380215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7013949933127254635680573 2630231224922720488380215)
                      ·
                        rfl

theorem cell23_5122357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 5, 1, 2, 3].length) (baseStart_5122357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5122357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5122357 prefixEnd_5122357 := by exact prefixLift 5122357
  have htrace : WordTrace (prefixWord ++ tailWord_5122357) baseStart_5122357 baseEnd_5122357 := by
    simpa [prefixWord, tailWord_5122357, baseEnd_5122357] using wordTrace_append hprefix tailTrace_5122357
  have hstable : (prefixWord ++ tailWord_5122357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5122357).length < 2 ^ (prefixWord ++ tailWord_5122357).sum := by decide
  have hdescent : baseEnd_5122357 < baseStart_5122357 := by decide
  rcases family_descends (prefixWord ++ tailWord_5122357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5122383 : List Nat := [1, 1, 2, 1, 1, 2, 1, 4, 1, 4, 5]
def baseStart_5122383 : Nat := 118140960795 + 5122383 * 2 ^ 59
def prefixEnd_5122383 : Nat := 4983230072969 + 3 ^ 40 * 5122383 * 2
def baseEnd_5122383 : Nat := 2630244575419737386655095

theorem tailTrace_5122383 : CollatzResearch.WordTrace tailWord_5122383 prefixEnd_5122383 2630244575419737386655095 := by
  unfold tailWord_5122383
  simp only [CollatzResearch.WordTrace]
  refine ⟨186828656601488699212467803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124552437734325799474978535 186828656601488699212467803)
  ·
    refine ⟨280242984902233048818701705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186828656601488699212467803 280242984902233048818701705)
    ·
      refine ⟨210182238676674786614026279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 280242984902233048818701705 210182238676674786614026279)
      ·
        refine ⟨315273358015012179921039419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210182238676674786614026279 315273358015012179921039419)
        ·
          refine ⟨472910037022518269881559129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315273358015012179921039419 472910037022518269881559129)
          ·
            refine ⟨354682527766888702411169347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 472910037022518269881559129 354682527766888702411169347)
            ·
              refine ⟨532023791650333053616754021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 354682527766888702411169347 532023791650333053616754021)
              ·
                refine ⟨99754460934437447553141379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 532023791650333053616754021 99754460934437447553141379)
                ·
                  refine ⟨149631691401656171329712069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99754460934437447553141379 149631691401656171329712069)
                  ·
                    refine ⟨28055942137810532124321013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 149631691401656171329712069 28055942137810532124321013)
                    ·
                      refine ⟨2630244575419737386655095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28055942137810532124321013 2630244575419737386655095)
                      ·
                        rfl

theorem cell23_5122383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 4, 5].length) (baseStart_5122383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5122383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5122383 prefixEnd_5122383 := by exact prefixLift 5122383
  have htrace : WordTrace (prefixWord ++ tailWord_5122383) baseStart_5122383 baseEnd_5122383 := by
    simpa [prefixWord, tailWord_5122383, baseEnd_5122383] using wordTrace_append hprefix tailTrace_5122383
  have hstable : (prefixWord ++ tailWord_5122383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5122383).length < 2 ^ (prefixWord ++ tailWord_5122383).sum := by decide
  have hdescent : baseEnd_5122383 < baseStart_5122383 := by decide
  rcases family_descends (prefixWord ++ tailWord_5122383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5122393 : List Nat := [1, 2, 1, 2, 2, 2, 1, 1, 1, 2, 8]
def baseStart_5122393 : Nat := 118140960795 + 5122393 * 2 ^ 59
def prefixEnd_5122393 : Nat := 4983230072969 + 3 ^ 40 * 5122393 * 2
def baseEnd_5122393 : Nat := 2630249710226282347530049

theorem tailTrace_5122393 : CollatzResearch.WordTrace tailWord_5122393 prefixEnd_5122393 2630249710226282347530049 := by
  unfold tailWord_5122393
  simp only [CollatzResearch.WordTrace]
  refine ⟨186829021331452470920331833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124552680887634980613554555 186829021331452470920331833)
  ·
    refine ⟨140121765998589353190248875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186829021331452470920331833 140121765998589353190248875)
    ·
      refine ⟨210182648997884029785373313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140121765998589353190248875 210182648997884029785373313)
      ·
        refine ⟨157636986748413022339029985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210182648997884029785373313 157636986748413022339029985)
        ·
          refine ⟨118227740061309766754272489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157636986748413022339029985 118227740061309766754272489)
          ·
            refine ⟨88670805045982325065704367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118227740061309766754272489 88670805045982325065704367)
            ·
              refine ⟨133006207568973487598556551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88670805045982325065704367 133006207568973487598556551)
              ·
                refine ⟨199509311353460231397834827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133006207568973487598556551 199509311353460231397834827)
                ·
                  refine ⟨299263967030190347096752241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 199509311353460231397834827 299263967030190347096752241)
                  ·
                    refine ⟨224447975272642760322564181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 299263967030190347096752241 224447975272642760322564181)
                    ·
                      refine ⟨2630249710226282347530049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 224447975272642760322564181 2630249710226282347530049)
                      ·
                        rfl

theorem cell23_5122393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 2, 8].length) (baseStart_5122393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5122393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5122393 prefixEnd_5122393 := by exact prefixLift 5122393
  have htrace : WordTrace (prefixWord ++ tailWord_5122393) baseStart_5122393 baseEnd_5122393 := by
    simpa [prefixWord, tailWord_5122393, baseEnd_5122393] using wordTrace_append hprefix tailTrace_5122393
  have hstable : (prefixWord ++ tailWord_5122393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5122393).length < 2 ^ (prefixWord ++ tailWord_5122393).sum := by decide
  have hdescent : baseEnd_5122393 < baseStart_5122393 := by decide
  rcases family_descends (prefixWord ++ tailWord_5122393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5122398 : List Nat := [4, 4, 2, 1, 1, 1, 1, 2, 1, 6]
def baseStart_5122398 : Nat := 118140960795 + 5122398 * 2 ^ 59
def prefixEnd_5122398 : Nat := 4983230072969 + 3 ^ 40 * 5122398 * 2
def baseEnd_5122398 : Nat := 876750759209851609322509

theorem tailTrace_5122398 : CollatzResearch.WordTrace tailWord_5122398 prefixEnd_5122398 876750759209851609322509 := by
  unfold tailWord_5122398
  simp only [CollatzResearch.WordTrace]
  refine ⟨23353650462054294596782981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124552802464289571182842565 23353650462054294596782981)
  ·
    refine ⟨4378809461635180236896809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23353650462054294596782981 4378809461635180236896809)
    ·
      refine ⟨3284107096226385177672607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4378809461635180236896809 3284107096226385177672607)
      ·
        refine ⟨4926160644339577766508911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3284107096226385177672607 4926160644339577766508911)
        ·
          refine ⟨7389240966509366649763367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4926160644339577766508911 7389240966509366649763367)
          ·
            refine ⟨11083861449764049974645051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7389240966509366649763367 11083861449764049974645051)
            ·
              refine ⟨16625792174646074961967577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11083861449764049974645051 16625792174646074961967577)
              ·
                refine ⟨12469344130984556221475683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16625792174646074961967577 12469344130984556221475683)
                ·
                  refine ⟨18704016196476834332213525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12469344130984556221475683 18704016196476834332213525)
                  ·
                    refine ⟨876750759209851609322509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18704016196476834332213525 876750759209851609322509)
                    ·
                      rfl

theorem cell23_5122398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_5122398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5122398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5122398 prefixEnd_5122398 := by exact prefixLift 5122398
  have htrace : WordTrace (prefixWord ++ tailWord_5122398) baseStart_5122398 baseEnd_5122398 := by
    simpa [prefixWord, tailWord_5122398, baseEnd_5122398] using wordTrace_append hprefix tailTrace_5122398
  have hstable : (prefixWord ++ tailWord_5122398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5122398).length < 2 ^ (prefixWord ++ tailWord_5122398).sum := by decide
  have hdescent : baseEnd_5122398 < baseStart_5122398 := by decide
  rcases family_descends (prefixWord ++ tailWord_5122398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5122421 : List Nat := [1, 3, 4, 1, 2, 2, 2, 2, 2, 1, 3]
def baseStart_5122421 : Nat := 118140960795 + 5122421 * 2 ^ 59
def prefixEnd_5122421 : Nat := 4983230072969 + 3 ^ 40 * 5122421 * 2
def baseEnd_5122421 : Nat := 2630264087684608237979921

theorem tailTrace_5122421 : CollatzResearch.WordTrace tailWord_5122421 prefixEnd_5122421 2630264087684608237979921 := by
  unfold tailWord_5122421
  simp only [CollatzResearch.WordTrace]
  refine ⟨186830042575351031702351117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124553361716900687801567411 186830042575351031702351117)
  ·
    refine ⟨70061265965756636888381669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186830042575351031702351117 70061265965756636888381669)
    ·
      refine ⟨13136487368579369416571563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70061265965756636888381669 13136487368579369416571563)
      ·
        refine ⟨19704731052869054124857345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13136487368579369416571563 19704731052869054124857345)
        ·
          refine ⟨14778548289651790593643009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19704731052869054124857345 14778548289651790593643009)
          ·
            refine ⟨11083911217238842945232257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14778548289651790593643009 11083911217238842945232257)
            ·
              refine ⟨8312933412929132208924193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11083911217238842945232257 8312933412929132208924193)
              ·
                refine ⟨6234700059696849156693145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8312933412929132208924193 6234700059696849156693145)
                ·
                  refine ⟨4676025044772636867519859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6234700059696849156693145 4676025044772636867519859)
                  ·
                    refine ⟨7014037567158955301279789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4676025044772636867519859 7014037567158955301279789)
                    ·
                      refine ⟨2630264087684608237979921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7014037567158955301279789 2630264087684608237979921)
                      ·
                        rfl

theorem cell23_5122421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_5122421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5122421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5122421 prefixEnd_5122421 := by exact prefixLift 5122421
  have htrace : WordTrace (prefixWord ++ tailWord_5122421) baseStart_5122421 baseEnd_5122421 := by
    simpa [prefixWord, tailWord_5122421, baseEnd_5122421] using wordTrace_append hprefix tailTrace_5122421
  have hstable : (prefixWord ++ tailWord_5122421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5122421).length < 2 ^ (prefixWord ++ tailWord_5122421).sum := by decide
  have hdescent : baseEnd_5122421 < baseStart_5122421 := by decide
  rcases family_descends (prefixWord ++ tailWord_5122421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5122444 : List Nat := [2, 2, 1, 2, 1, 5, 2, 1, 1, 4, 2]
def baseStart_5122444 : Nat := 118140960795 + 5122444 * 2 ^ 59
def prefixEnd_5122444 : Nat := 4983230072969 + 3 ^ 40 * 5122444 * 2
def baseEnd_5122444 : Nat := 2630275897739661647992315

theorem tailTrace_5122444 : CollatzResearch.WordTrace tailWord_5122444 prefixEnd_5122444 2630275897739661647992315 := by
  unfold tailWord_5122444
  simp only [CollatzResearch.WordTrace]
  refine ⟨93415440727133853315219193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124553920969511804420292257 93415440727133853315219193)
  ·
    refine ⟨70061580545350389986414395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93415440727133853315219193 70061580545350389986414395)
    ·
      refine ⟨105092370818025584979621593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70061580545350389986414395 105092370818025584979621593)
      ·
        refine ⟨78819278113519188734716195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105092370818025584979621593 78819278113519188734716195)
        ·
          refine ⟨118228917170278783102074293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78819278113519188734716195 118228917170278783102074293)
          ·
            refine ⟨11083960984713635915819465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 118228917170278783102074293 11083960984713635915819465)
            ·
              refine ⟨8312970738535226936864599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11083960984713635915819465 8312970738535226936864599)
              ·
                refine ⟨12469456107802840405296899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8312970738535226936864599 12469456107802840405296899)
                ·
                  refine ⟨18704184161704260607945349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12469456107802840405296899 18704184161704260607945349)
                  ·
                    refine ⟨3507034530319548863989753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18704184161704260607945349 3507034530319548863989753)
                    ·
                      refine ⟨2630275897739661647992315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3507034530319548863989753 2630275897739661647992315)
                      ·
                        rfl

theorem cell23_5122444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 1, 1, 4, 2].length) (baseStart_5122444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5122444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5122444 prefixEnd_5122444 := by exact prefixLift 5122444
  have htrace : WordTrace (prefixWord ++ tailWord_5122444) baseStart_5122444 baseEnd_5122444 := by
    simpa [prefixWord, tailWord_5122444, baseEnd_5122444] using wordTrace_append hprefix tailTrace_5122444
  have hstable : (prefixWord ++ tailWord_5122444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5122444).length < 2 ^ (prefixWord ++ tailWord_5122444).sum := by decide
  have hdescent : baseEnd_5122444 < baseStart_5122444 := by decide
  rcases family_descends (prefixWord ++ tailWord_5122444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5122465 : List Nat := [1, 2, 3, 5, 1, 2, 2, 1, 1, 3, 2]
def baseStart_5122465 : Nat := 118140960795 + 5122465 * 2 ^ 59
def prefixEnd_5122465 : Nat := 4983230072969 + 3 ^ 40 * 5122465 * 2
def baseEnd_5122465 : Nat := 2630286680833406065829719

theorem tailTrace_5122465 : CollatzResearch.WordTrace tailWord_5122465 prefixEnd_5122465 2630286680833406065829719 := by
  unfold tailWord_5122465
  simp only [CollatzResearch.WordTrace]
  refine ⟨186831647387191627216952849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124554431591461084811301899 186831647387191627216952849)
  ·
    refine ⟨140123735540393720412714637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186831647387191627216952849 140123735540393720412714637)
    ·
      refine ⟨52546400827647645154767989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140123735540393720412714637 52546400827647645154767989)
      ·
        refine ⟨4926225077591966733259499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52546400827647645154767989 4926225077591966733259499)
        ·
          refine ⟨7389337616387950099889249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4926225077591966733259499 7389337616387950099889249)
          ·
            refine ⟨5542003212290962574916937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7389337616387950099889249 5542003212290962574916937)
            ·
              refine ⟨4156502409218221931187703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5542003212290962574916937 4156502409218221931187703)
              ·
                refine ⟨6234753613827332896781555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4156502409218221931187703 6234753613827332896781555)
                ·
                  refine ⟨9352130420740999345172333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6234753613827332896781555 9352130420740999345172333)
                  ·
                    refine ⟨3507048907777874754439625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9352130420740999345172333 3507048907777874754439625)
                    ·
                      refine ⟨2630286680833406065829719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3507048907777874754439625 2630286680833406065829719)
                      ·
                        rfl

theorem cell23_5122465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_5122465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5122465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5122465 prefixEnd_5122465 := by exact prefixLift 5122465
  have htrace : WordTrace (prefixWord ++ tailWord_5122465) baseStart_5122465 baseEnd_5122465 := by
    simpa [prefixWord, tailWord_5122465, baseEnd_5122465] using wordTrace_append hprefix tailTrace_5122465
  have hstable : (prefixWord ++ tailWord_5122465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5122465).length < 2 ^ (prefixWord ++ tailWord_5122465).sum := by decide
  have hdescent : baseEnd_5122465 < baseStart_5122465 := by decide
  rcases family_descends (prefixWord ++ tailWord_5122465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5122467 : List Nat := [1, 1, 1, 4, 1, 4, 1, 5, 5]
def baseStart_5122467 : Nat := 118140960795 + 5122467 * 2 ^ 59
def prefixEnd_5122467 : Nat := 4983230072969 + 3 ^ 40 * 5122467 * 2
def baseEnd_5122467 : Nat := 292254189754968339778301

theorem tailTrace_5122467 : CollatzResearch.WordTrace tailWord_5122467 prefixEnd_5122467 292254189754968339778301 := by
  unfold tailWord_5122467
  simp only [CollatzResearch.WordTrace]
  refine ⟨186831720333184381558525655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124554480222122921039017103 186831720333184381558525655)
  ·
    refine ⟨280247580499776572337788483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186831720333184381558525655 280247580499776572337788483)
    ·
      refine ⟨420371370749664858506682725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280247580499776572337788483 420371370749664858506682725)
      ·
        refine ⟨78819632015562160970003011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 420371370749664858506682725 78819632015562160970003011)
        ·
          refine ⟨118229448023343241455004517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78819632015562160970003011 118229448023343241455004517)
          ·
            refine ⟨22168021504376857772813347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 118229448023343241455004517 22168021504376857772813347)
            ·
              refine ⟨33252032256565286659220021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22168021504376857772813347 33252032256565286659220021)
              ·
                refine ⟨3117378024052995624301877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33252032256565286659220021 3117378024052995624301877)
                ·
                  refine ⟨292254189754968339778301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3117378024052995624301877 292254189754968339778301)
                  ·
                    rfl

theorem cell23_5122467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 5, 5].length) (baseStart_5122467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5122467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5122467 prefixEnd_5122467 := by exact prefixLift 5122467
  have htrace : WordTrace (prefixWord ++ tailWord_5122467) baseStart_5122467 baseEnd_5122467 := by
    simpa [prefixWord, tailWord_5122467, baseEnd_5122467] using wordTrace_append hprefix tailTrace_5122467
  have hstable : (prefixWord ++ tailWord_5122467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5122467).length < 2 ^ (prefixWord ++ tailWord_5122467).sum := by decide
  have hdescent : baseEnd_5122467 < baseStart_5122467 := by decide
  rcases family_descends (prefixWord ++ tailWord_5122467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5122490 : List Nat := [3, 1, 1, 1, 2, 1, 1, 5, 1, 2, 5]
def baseStart_5122490 : Nat := 118140960795 + 5122490 * 2 ^ 59
def prefixEnd_5122490 : Nat := 4983230072969 + 3 ^ 40 * 5122490 * 2
def baseEnd_5122490 : Nat := 2630299517849768468017103

theorem tailTrace_5122490 : CollatzResearch.WordTrace tailWord_5122490 prefixEnd_5122490 2630299517849768468017103 := by
  unfold tailWord_5122490
  simp only [CollatzResearch.WordTrace]
  refine ⟨46708139803025264121653231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124555039474734037657741949 46708139803025264121653231)
  ·
    refine ⟨70062209704537896182479847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46708139803025264121653231 70062209704537896182479847)
    ·
      refine ⟨105093314556806844273719771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70062209704537896182479847 105093314556806844273719771)
      ·
        refine ⟨157639971835210266410579657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105093314556806844273719771 157639971835210266410579657)
        ·
          refine ⟨118229978876407699807934743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157639971835210266410579657 118229978876407699807934743)
          ·
            refine ⟨177344968314611549711902115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118229978876407699807934743 177344968314611549711902115)
            ·
              refine ⟨266017452471917324567853173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177344968314611549711902115 266017452471917324567853173)
              ·
                refine ⟨24939136169242249178236235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 266017452471917324567853173 24939136169242249178236235)
                ·
                  refine ⟨37408704253863373767354353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24939136169242249178236235 37408704253863373767354353)
                  ·
                    refine ⟨28056528190397530325515765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37408704253863373767354353 28056528190397530325515765)
                    ·
                      refine ⟨2630299517849768468017103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28056528190397530325515765 2630299517849768468017103)
                      ·
                        rfl

theorem cell23_5122490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 1, 2, 5].length) (baseStart_5122490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5122490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5122490 prefixEnd_5122490 := by exact prefixLift 5122490
  have htrace : WordTrace (prefixWord ++ tailWord_5122490) baseStart_5122490 baseEnd_5122490 := by
    simpa [prefixWord, tailWord_5122490, baseEnd_5122490] using wordTrace_append hprefix tailTrace_5122490
  have hstable : (prefixWord ++ tailWord_5122490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5122490).length < 2 ^ (prefixWord ++ tailWord_5122490).sum := by decide
  have hdescent : baseEnd_5122490 < baseStart_5122490 := by decide
  rcases family_descends (prefixWord ++ tailWord_5122490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5122510 : List Nat := [4, 1, 1, 1, 2, 1, 1, 1, 1, 10]
def baseStart_5122510 : Nat := 118140960795 + 5122510 * 2 ^ 59
def prefixEnd_5122510 : Nat := 4983230072969 + 3 ^ 40 * 5122510 * 2
def baseEnd_5122510 : Nat := 876769929154286129922337

theorem tailTrace_5122510 : CollatzResearch.WordTrace tailWord_5122510 prefixEnd_5122510 876769929154286129922337 := by
  unfold tailWord_5122510
  simp only [CollatzResearch.WordTrace]
  refine ⟨23354161084003574987792623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124555525781352399934893989 23354161084003574987792623)
  ·
    refine ⟨35031241626005362481688935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23354161084003574987792623 35031241626005362481688935)
    ·
      refine ⟨52546862439008043722533403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35031241626005362481688935 52546862439008043722533403)
      ·
        refine ⟨78820293658512065583800105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52546862439008043722533403 78820293658512065583800105)
        ·
          refine ⟨59115220243884049187850079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78820293658512065583800105 59115220243884049187850079)
          ·
            refine ⟨88672830365826073781775119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59115220243884049187850079 88672830365826073781775119)
            ·
              refine ⟨133009245548739110672662679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88672830365826073781775119 133009245548739110672662679)
              ·
                refine ⟨199513868323108666008994019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133009245548739110672662679 199513868323108666008994019)
                ·
                  refine ⟨299270802484662999013491029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 199513868323108666008994019 299270802484662999013491029)
                  ·
                    refine ⟨876769929154286129922337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 299270802484662999013491029 876769929154286129922337)
                    ·
                      rfl

theorem cell23_5122510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 1, 10].length) (baseStart_5122510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5122510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5122510 prefixEnd_5122510 := by exact prefixLift 5122510
  have htrace : WordTrace (prefixWord ++ tailWord_5122510) baseStart_5122510 baseEnd_5122510 := by
    simpa [prefixWord, tailWord_5122510, baseEnd_5122510] using wordTrace_append hprefix tailTrace_5122510
  have hstable : (prefixWord ++ tailWord_5122510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5122510).length < 2 ^ (prefixWord ++ tailWord_5122510).sum := by decide
  have hdescent : baseEnd_5122510 < baseStart_5122510 := by decide
  rcases family_descends (prefixWord ++ tailWord_5122510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5122517 : List Nat := [1, 3, 2, 3, 1, 2, 2, 1, 1, 3, 4]
def baseStart_5122517 : Nat := 118140960795 + 5122517 * 2 ^ 59
def prefixEnd_5122517 : Nat := 4983230072969 + 3 ^ 40 * 5122517 * 2
def baseEnd_5122517 : Nat := 2630313381827439862379479

theorem tailTrace_5122517 : CollatzResearch.WordTrace tailWord_5122517 prefixEnd_5122517 2630313381827439862379479 := by
  unfold tailWord_5122517
  simp only [CollatzResearch.WordTrace]
  refine ⟨186833543983003240097845805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124555695988668826731897203 186833543983003240097845805)
  ·
    refine ⟨70062578993626215036692177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186833543983003240097845805 70062578993626215036692177)
    ·
      refine ⟨52546934245219661277519133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70062578993626215036692177 52546934245219661277519133)
      ·
        refine ⟨19705100341957372979069675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52546934245219661277519133 19705100341957372979069675)
        ·
          refine ⟨29557650512936059468604513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19705100341957372979069675 29557650512936059468604513)
          ·
            refine ⟨22168237884702044601453385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29557650512936059468604513 22168237884702044601453385)
            ·
              refine ⟨16626178413526533451090039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22168237884702044601453385 16626178413526533451090039)
              ·
                refine ⟨24939267620289800176635059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16626178413526533451090039 24939267620289800176635059)
                ·
                  refine ⟨37408901430434700264952589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24939267620289800176635059 37408901430434700264952589)
                  ·
                    refine ⟨14028338036413012599357221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37408901430434700264952589 14028338036413012599357221)
                    ·
                      refine ⟨2630313381827439862379479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14028338036413012599357221 2630313381827439862379479)
                      ·
                        rfl

theorem cell23_5122517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_5122517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5122517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5122517 prefixEnd_5122517 := by exact prefixLift 5122517
  have htrace : WordTrace (prefixWord ++ tailWord_5122517) baseStart_5122517 baseEnd_5122517 := by
    simpa [prefixWord, tailWord_5122517, baseEnd_5122517] using wordTrace_append hprefix tailTrace_5122517
  have hstable : (prefixWord ++ tailWord_5122517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5122517).length < 2 ^ (prefixWord ++ tailWord_5122517).sum := by decide
  have hdescent : baseEnd_5122517 < baseStart_5122517 := by decide
  rcases family_descends (prefixWord ++ tailWord_5122517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5122520 : List Nat := [2, 1, 2, 2, 2, 1, 1, 2, 2, 3, 5]
def baseStart_5122520 : Nat := 118140960795 + 5122520 * 2 ^ 59
def prefixEnd_5122520 : Nat := 4983230072969 + 3 ^ 40 * 5122520 * 2
def baseEnd_5122520 : Nat := 2630314922269403350641965

theorem tailTrace_5122520 : CollatzResearch.WordTrace tailWord_5122520 prefixEnd_5122520 2630314922269403350641965 := by
  unfold tailWord_5122520
  simp only [CollatzResearch.WordTrace]
  refine ⟨93416826700996185805102507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124555768934661581073470009 93416826700996185805102507)
  ·
    refine ⟨140125240051494278707653761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93416826700996185805102507 140125240051494278707653761)
    ·
      refine ⟨105093930038620709030740321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140125240051494278707653761 105093930038620709030740321)
      ·
        refine ⟨78820447528965531773055241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105093930038620709030740321 78820447528965531773055241)
        ·
          refine ⟨59115335646724148829791431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78820447528965531773055241 59115335646724148829791431)
          ·
            refine ⟨88673003470086223244687147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59115335646724148829791431 88673003470086223244687147)
            ·
              refine ⟨133009505205129334867030721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88673003470086223244687147 133009505205129334867030721)
              ·
                refine ⟨99757128903847001150273041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133009505205129334867030721 99757128903847001150273041)
                ·
                  refine ⟨74817846677885250862704781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99757128903847001150273041 74817846677885250862704781)
                  ·
                    refine ⟨28056692504206969073514293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 74817846677885250862704781 28056692504206969073514293)
                    ·
                      refine ⟨2630314922269403350641965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28056692504206969073514293 2630314922269403350641965)
                      ·
                        rfl

theorem cell23_5122520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_5122520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5122520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5122520 prefixEnd_5122520 := by exact prefixLift 5122520
  have htrace : WordTrace (prefixWord ++ tailWord_5122520) baseStart_5122520 baseEnd_5122520 := by
    simpa [prefixWord, tailWord_5122520, baseEnd_5122520] using wordTrace_append hprefix tailTrace_5122520
  have hstable : (prefixWord ++ tailWord_5122520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5122520).length < 2 ^ (prefixWord ++ tailWord_5122520).sum := by decide
  have hdescent : baseEnd_5122520 < baseStart_5122520 := by decide
  rcases family_descends (prefixWord ++ tailWord_5122520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5122540 : List Nat := [2, 2, 1, 1, 2, 1, 3, 3, 8]
def baseStart_5122540 : Nat := 118140960795 + 5122540 * 2 ^ 59
def prefixEnd_5122540 : Nat := 4983230072969 + 3 ^ 40 * 5122540 * 2
def baseEnd_5122540 : Nat := 292258354653610363599097

theorem tailTrace_5122540 : CollatzResearch.WordTrace tailWord_5122540 prefixEnd_5122540 292258354653610363599097 := by
  unfold tailWord_5122540
  simp only [CollatzResearch.WordTrace]
  refine ⟨93417191430959957512966537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124556255241279943350622049 93417191430959957512966537)
  ·
    refine ⟨70062893573219968134724903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93417191430959957512966537 70062893573219968134724903)
    ·
      refine ⟨105094340359829952202087355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70062893573219968134724903 105094340359829952202087355)
      ·
        refine ⟨157641510539744928303131033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105094340359829952202087355 157641510539744928303131033)
        ·
          refine ⟨118231132904808696227348275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157641510539744928303131033 118231132904808696227348275)
          ·
            refine ⟨177346699357213044341022413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118231132904808696227348275 177346699357213044341022413)
            ·
              refine ⟨66505012258954891627883405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 177346699357213044341022413 66505012258954891627883405)
              ·
                refine ⟨24939379597108084360456277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66505012258954891627883405 24939379597108084360456277)
                ·
                  refine ⟨292258354653610363599097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24939379597108084360456277 292258354653610363599097)
                  ·
                    rfl

theorem cell23_5122540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 8].length) (baseStart_5122540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5122540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5122540 prefixEnd_5122540 := by exact prefixLift 5122540
  have htrace : WordTrace (prefixWord ++ tailWord_5122540) baseStart_5122540 baseEnd_5122540 := by
    simpa [prefixWord, tailWord_5122540, baseEnd_5122540] using wordTrace_append hprefix tailTrace_5122540
  have hstable : (prefixWord ++ tailWord_5122540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5122540).length < 2 ^ (prefixWord ++ tailWord_5122540).sum := by decide
  have hdescent : baseEnd_5122540 < baseStart_5122540 := by decide
  rcases family_descends (prefixWord ++ tailWord_5122540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5122557 : List Nat := [1, 4, 1, 1, 1, 3, 3, 3, 6]
def baseStart_5122557 : Nat := 118140960795 + 5122557 * 2 ^ 59
def prefixEnd_5122557 : Nat := 4983230072969 + 3 ^ 40 * 5122557 * 2
def baseEnd_5122557 : Nat := 292259324561513300653255

theorem tailTrace_5122557 : CollatzResearch.WordTrace tailWord_5122557 prefixEnd_5122557 292259324561513300653255 := by
  unfold tailWord_5122557
  simp only [CollatzResearch.WordTrace]
  refine ⟨186835002902858326929301925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124556668601905551286201283 186835002902858326929301925)
  ·
    refine ⟨35031563044285936299244111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 186835002902858326929301925 35031563044285936299244111)
    ·
      refine ⟨52547344566428904448866167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35031563044285936299244111 52547344566428904448866167)
      ·
        refine ⟨78821016849643356673299251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52547344566428904448866167 78821016849643356673299251)
        ·
          refine ⟨118231525274465035009948877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78821016849643356673299251 118231525274465035009948877)
          ·
            refine ⟨44336821977924388128730829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118231525274465035009948877 44336821977924388128730829)
            ·
              refine ⟨16626308241721645548274061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44336821977924388128730829 16626308241721645548274061)
              ·
                refine ⟨6234865590645617080602773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16626308241721645548274061 6234865590645617080602773)
                ·
                  refine ⟨292259324561513300653255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6234865590645617080602773 292259324561513300653255)
                  ·
                    rfl

theorem cell23_5122557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 3, 6].length) (baseStart_5122557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5122557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5122557 prefixEnd_5122557 := by exact prefixLift 5122557
  have htrace : WordTrace (prefixWord ++ tailWord_5122557) baseStart_5122557 baseEnd_5122557 := by
    simpa [prefixWord, tailWord_5122557, baseEnd_5122557] using wordTrace_append hprefix tailTrace_5122557
  have hstable : (prefixWord ++ tailWord_5122557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5122557).length < 2 ^ (prefixWord ++ tailWord_5122557).sum := by decide
  have hdescent : baseEnd_5122557 < baseStart_5122557 := by decide
  rcases family_descends (prefixWord ++ tailWord_5122557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5122594 : List Nat := [3, 3, 1, 1, 1, 1, 1, 2, 3, 5, 2]
def baseStart_5122594 : Nat := 118140960795 + 5122594 * 2 ^ 59
def prefixEnd_5122594 : Nat := 4983230072969 + 3 ^ 40 * 5122594 * 2
def baseEnd_5122594 : Nat := 2630352919837836061116625

theorem tailTrace_5122594 : CollatzResearch.WordTrace tailWord_5122594 prefixEnd_5122594 2630352919837836061116625 := by
  unfold tailWord_5122594
  simp only [CollatzResearch.WordTrace]
  refine ⟨46709088100931070562099709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124557568269149521498932557 46709088100931070562099709)
  ·
    refine ⟨17515908037849151460787391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46709088100931070562099709 17515908037849151460787391)
    ·
      refine ⟨26273862056773727191181087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17515908037849151460787391 26273862056773727191181087)
      ·
        refine ⟨39410793085160590786771631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26273862056773727191181087 39410793085160590786771631)
        ·
          refine ⟨59116189627740886180157447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39410793085160590786771631 59116189627740886180157447)
          ·
            refine ⟨88674284441611329270236171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59116189627740886180157447 88674284441611329270236171)
            ·
              refine ⟨133011426662416993905354257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88674284441611329270236171 133011426662416993905354257)
              ·
                refine ⟨99758569996812745429015693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133011426662416993905354257 99758569996812745429015693)
                ·
                  refine ⟨37409463748804779535880885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 99758569996812745429015693 37409463748804779535880885)
                  ·
                    refine ⟨3507137226450448081488833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37409463748804779535880885 3507137226450448081488833)
                    ·
                      refine ⟨2630352919837836061116625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3507137226450448081488833 2630352919837836061116625)
                      ·
                        rfl

theorem cell23_5122594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 3, 5, 2].length) (baseStart_5122594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5122594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5122594 prefixEnd_5122594 := by exact prefixLift 5122594
  have htrace : WordTrace (prefixWord ++ tailWord_5122594) baseStart_5122594 baseEnd_5122594 := by
    simpa [prefixWord, tailWord_5122594, baseEnd_5122594] using wordTrace_append hprefix tailTrace_5122594
  have hstable : (prefixWord ++ tailWord_5122594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5122594).length < 2 ^ (prefixWord ++ tailWord_5122594).sum := by decide
  have hdescent : baseEnd_5122594 < baseStart_5122594 := by decide
  rcases family_descends (prefixWord ++ tailWord_5122594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5122641 : List Nat := [1, 2, 2, 1, 3, 3, 4, 1, 1, 1, 4]
def baseStart_5122641 : Nat := 118140960795 + 5122641 * 2 ^ 59
def prefixEnd_5122641 : Nat := 4983230072969 + 3 ^ 40 * 5122641 * 2
def baseEnd_5122641 : Nat := 2630377053428597377228909

theorem tailTrace_5122641 : CollatzResearch.WordTrace tailWord_5122641 prefixEnd_5122641 2630377053428597377228909 := by
  unfold tailWord_5122641
  simp only [CollatzResearch.WordTrace]
  refine ⟨186838066634554009275359777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124558711089702672850239851 186838066634554009275359777)
  ·
    refine ⟨140128549975915506956519833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186838066634554009275359777 140128549975915506956519833)
    ·
      refine ⟨105096412481936630217389875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140128549975915506956519833 105096412481936630217389875)
      ·
        refine ⟨157644618722904945326084813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105096412481936630217389875 157644618722904945326084813)
        ·
          refine ⟨59116732021089354497281805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 157644618722904945326084813 59116732021089354497281805)
          ·
            refine ⟨22168774507908507936480677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59116732021089354497281805 22168774507908507936480677)
            ·
              refine ⟨4156645220232845238090127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22168774507908507936480677 4156645220232845238090127)
              ·
                refine ⟨6234967830349267857135191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4156645220232845238090127 6234967830349267857135191)
                ·
                  refine ⟨9352451745523901785702787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6234967830349267857135191 9352451745523901785702787)
                  ·
                    refine ⟨14028677618285852678554181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9352451745523901785702787 14028677618285852678554181)
                    ·
                      refine ⟨2630377053428597377228909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14028677618285852678554181 2630377053428597377228909)
                      ·
                        rfl

theorem cell23_5122641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 4, 1, 1, 1, 4].length) (baseStart_5122641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5122641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5122641 prefixEnd_5122641 := by exact prefixLift 5122641
  have htrace : WordTrace (prefixWord ++ tailWord_5122641) baseStart_5122641 baseEnd_5122641 := by
    simpa [prefixWord, tailWord_5122641, baseEnd_5122641] using wordTrace_append hprefix tailTrace_5122641
  have hstable : (prefixWord ++ tailWord_5122641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5122641).length < 2 ^ (prefixWord ++ tailWord_5122641).sum := by decide
  have hdescent : baseEnd_5122641 < baseStart_5122641 := by decide
  rcases family_descends (prefixWord ++ tailWord_5122641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5122692 : List Nat := [2, 3, 2, 1, 3, 3, 1, 3, 1, 2, 2]
def baseStart_5122692 : Nat := 118140960795 + 5122692 * 2 ^ 59
def prefixEnd_5122692 : Nat := 4983230072969 + 3 ^ 40 * 5122692 * 2
def baseEnd_5122692 : Nat := 2630403240941976677691175

theorem tailTrace_5122692 : CollatzResearch.WordTrace tailWord_5122692 prefixEnd_5122692 2630403240941976677691175 := by
  unfold tailWord_5122692
  simp only [CollatzResearch.WordTrace]
  refine ⟨93419963378684622492733165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124559951171579496656977553 93419963378684622492733165)
  ·
    refine ⟨35032486267006733434774937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93419963378684622492733165 35032486267006733434774937)
    ·
      refine ⟨26274364700255050076081203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35032486267006733434774937 26274364700255050076081203)
      ·
        refine ⟨39411547050382575114121805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26274364700255050076081203 39411547050382575114121805)
        ·
          refine ⟨14779330143893465667795677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39411547050382575114121805 14779330143893465667795677)
          ·
            refine ⟨5542248803960049625423379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14779330143893465667795677 5542248803960049625423379)
            ·
              refine ⟨8313373205940074438135069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5542248803960049625423379 8313373205940074438135069)
              ·
                refine ⟨3117514952227527914300651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8313373205940074438135069 3117514952227527914300651)
                ·
                  refine ⟨4676272428341291871450977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3117514952227527914300651 4676272428341291871450977)
                  ·
                    refine ⟨3507204321255968903588233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4676272428341291871450977 3507204321255968903588233)
                    ·
                      refine ⟨2630403240941976677691175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3507204321255968903588233 2630403240941976677691175)
                      ·
                        rfl

theorem cell23_5122692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 3, 1, 2, 2].length) (baseStart_5122692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5122692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5122692 prefixEnd_5122692 := by exact prefixLift 5122692
  have htrace : WordTrace (prefixWord ++ tailWord_5122692) baseStart_5122692 baseEnd_5122692 := by
    simpa [prefixWord, tailWord_5122692, baseEnd_5122692] using wordTrace_append hprefix tailTrace_5122692
  have hstable : (prefixWord ++ tailWord_5122692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5122692).length < 2 ^ (prefixWord ++ tailWord_5122692).sum := by decide
  have hdescent : baseEnd_5122692 < baseStart_5122692 := by decide
  rcases family_descends (prefixWord ++ tailWord_5122692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5122697 : List Nat := [1, 2, 1, 1, 4, 1, 1, 2, 1, 5, 4]
def baseStart_5122697 : Nat := 118140960795 + 5122697 * 2 ^ 59
def prefixEnd_5122697 : Nat := 4983230072969 + 3 ^ 40 * 5122697 * 2
def baseEnd_5122697 : Nat := 2630405808345249158128651

theorem tailTrace_5122697 : CollatzResearch.WordTrace tailWord_5122697 prefixEnd_5122697 2630405808345249158128651 := by
  unfold tailWord_5122697
  simp only [CollatzResearch.WordTrace]
  refine ⟨186840109122351130839398345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124560072748234087226265563 186840109122351130839398345)
  ·
    refine ⟨140130081841763348129548759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186840109122351130839398345 140130081841763348129548759)
    ·
      refine ⟨210195122762645022194323139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140130081841763348129548759 210195122762645022194323139)
      ·
        refine ⟨315292684143967533291484709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210195122762645022194323139 315292684143967533291484709)
        ·
          refine ⟨59117378276993912492153383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 315292684143967533291484709 59117378276993912492153383)
          ·
            refine ⟨88676067415490868738230075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59117378276993912492153383 88676067415490868738230075)
            ·
              refine ⟨133014101123236303107345113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88676067415490868738230075 133014101123236303107345113)
              ·
                refine ⟨99760575842427227330508835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133014101123236303107345113 99760575842427227330508835)
                ·
                  refine ⟨149640863763640840995763253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99760575842427227330508835 149640863763640840995763253)
                  ·
                    refine ⟨14028830977841328843352805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 149640863763640840995763253 14028830977841328843352805)
                    ·
                      refine ⟨2630405808345249158128651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14028830977841328843352805 2630405808345249158128651)
                      ·
                        rfl

theorem cell23_5122697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 5, 4].length) (baseStart_5122697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5122697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5122697 prefixEnd_5122697 := by exact prefixLift 5122697
  have htrace : WordTrace (prefixWord ++ tailWord_5122697) baseStart_5122697 baseEnd_5122697 := by
    simpa [prefixWord, tailWord_5122697, baseEnd_5122697] using wordTrace_append hprefix tailTrace_5122697
  have hstable : (prefixWord ++ tailWord_5122697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5122697).length < 2 ^ (prefixWord ++ tailWord_5122697).sum := by decide
  have hdescent : baseEnd_5122697 < baseStart_5122697 := by decide
  rcases family_descends (prefixWord ++ tailWord_5122697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5122708 : List Nat := [2, 4, 2, 2, 1, 1, 2, 1, 4, 1, 3]
def baseStart_5122708 : Nat := 118140960795 + 5122708 * 2 ^ 59
def prefixEnd_5122708 : Nat := 4983230072969 + 3 ^ 40 * 5122708 * 2
def baseEnd_5122708 : Nat := 2630411456632448615091101

theorem tailTrace_5122708 : CollatzResearch.WordTrace tailWord_5122708 prefixEnd_5122708 2630411456632448615091101 := by
  unfold tailWord_5122708
  simp only [CollatzResearch.WordTrace]
  refine ⟨93420255162655639859024389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124560340216874186478699185 93420255162655639859024389)
  ·
    refine ⟨17516297842997932473567073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93420255162655639859024389 17516297842997932473567073)
    ·
      refine ⟨13137223382248449355175305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17516297842997932473567073 13137223382248449355175305)
      ·
        refine ⟨9852917536686337016381479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13137223382248449355175305 9852917536686337016381479)
        ·
          refine ⟨14779376305029505524572219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9852917536686337016381479 14779376305029505524572219)
          ·
            refine ⟨22169064457544258286858329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14779376305029505524572219 22169064457544258286858329)
            ·
              refine ⟨16626798343158193715143747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22169064457544258286858329 16626798343158193715143747)
              ·
                refine ⟨24940197514737290572715621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16626798343158193715143747 24940197514737290572715621)
                ·
                  refine ⟨4676287034013241982384179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24940197514737290572715621 4676287034013241982384179)
                  ·
                    refine ⟨7014430551019862973576269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4676287034013241982384179 7014430551019862973576269)
                    ·
                      refine ⟨2630411456632448615091101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7014430551019862973576269 2630411456632448615091101)
                      ·
                        rfl

theorem cell23_5122708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_5122708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5122708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5122708 prefixEnd_5122708 := by exact prefixLift 5122708
  have htrace : WordTrace (prefixWord ++ tailWord_5122708) baseStart_5122708 baseEnd_5122708 := by
    simpa [prefixWord, tailWord_5122708, baseEnd_5122708] using wordTrace_append hprefix tailTrace_5122708
  have hstable : (prefixWord ++ tailWord_5122708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5122708).length < 2 ^ (prefixWord ++ tailWord_5122708).sum := by decide
  have hdescent : baseEnd_5122708 < baseStart_5122708 := by decide
  rcases family_descends (prefixWord ++ tailWord_5122708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5122718 : List Nat := [4, 3, 1, 1, 1, 1, 2, 2, 3, 3, 2]
def baseStart_5122718 : Nat := 118140960795 + 5122718 * 2 ^ 59
def prefixEnd_5122718 : Nat := 4983230072969 + 3 ^ 40 * 5122718 * 2
def baseEnd_5122718 : Nat := 2630416591438993575966055

theorem tailTrace_5122718 : CollatzResearch.WordTrace tailWord_5122718 prefixEnd_5122718 2630416591438993575966055 := by
  unfold tailWord_5122718
  simp only [CollatzResearch.WordTrace]
  refine ⟨23355109381909381428239101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124560583370183367617275205 23355109381909381428239101)
  ·
    refine ⟨8758166018216018035589663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23355109381909381428239101 8758166018216018035589663)
    ·
      refine ⟨13137249027324027053384495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8758166018216018035589663 13137249027324027053384495)
      ·
        refine ⟨19705873540986040580076743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13137249027324027053384495 19705873540986040580076743)
        ·
          refine ⟨29558810311479060870115115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19705873540986040580076743 29558810311479060870115115)
          ·
            refine ⟨44338215467218591305172673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29558810311479060870115115 44338215467218591305172673)
            ·
              refine ⟨33253661600413943478879505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44338215467218591305172673 33253661600413943478879505)
              ·
                refine ⟨24940246200310457609159629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33253661600413943478879505 24940246200310457609159629)
                ·
                  refine ⟨9352592325116421603434861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24940246200310457609159629 9352592325116421603434861)
                  ·
                    refine ⟨3507222121918658101288073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9352592325116421603434861 3507222121918658101288073)
                    ·
                      refine ⟨2630416591438993575966055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3507222121918658101288073 2630416591438993575966055)
                      ·
                        rfl

theorem cell23_5122718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 3, 3, 2].length) (baseStart_5122718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5122718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5122718 prefixEnd_5122718 := by exact prefixLift 5122718
  have htrace : WordTrace (prefixWord ++ tailWord_5122718) baseStart_5122718 baseEnd_5122718 := by
    simpa [prefixWord, tailWord_5122718, baseEnd_5122718] using wordTrace_append hprefix tailTrace_5122718
  have hstable : (prefixWord ++ tailWord_5122718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5122718).length < 2 ^ (prefixWord ++ tailWord_5122718).sum := by decide
  have hdescent : baseEnd_5122718 < baseStart_5122718 := by decide
  rcases family_descends (prefixWord ++ tailWord_5122718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5122757 : List Nat := [1, 3, 1, 1, 1, 1, 2, 1, 2, 4, 6]
def baseStart_5122757 : Nat := 118140960795 + 5122757 * 2 ^ 59
def prefixEnd_5122757 : Nat := 4983230072969 + 3 ^ 40 * 5122757 * 2
def baseEnd_5122757 : Nat := 2630436617184518923378375

theorem tailTrace_5122757 : CollatzResearch.WordTrace tailWord_5122757 prefixEnd_5122757 2630436617184518923378375 := by
  unfold tailWord_5122757
  simp only [CollatzResearch.WordTrace]
  refine ⟨186842297502133761086582525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124561531668089174057721683 186842297502133761086582525)
  ·
    refine ⟨70065861563300160407468447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186842297502133761086582525 70065861563300160407468447)
    ·
      refine ⟨105098792344950240611202671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70065861563300160407468447 105098792344950240611202671)
      ·
        refine ⟨157648188517425360916804007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105098792344950240611202671 157648188517425360916804007)
        ·
          refine ⟨236472282776138041375206011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157648188517425360916804007 236472282776138041375206011)
          ·
            refine ⟨354708424164207062062809017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236472282776138041375206011 354708424164207062062809017)
            ·
              refine ⟨266031318123155296547106763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 354708424164207062062809017 266031318123155296547106763)
              ·
                refine ⟨399046977184732944820660145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 266031318123155296547106763 399046977184732944820660145)
                ·
                  refine ⟨299285232888549708615495109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 399046977184732944820660145 299285232888549708615495109)
                  ·
                    refine ⟨56115981166603070365405333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 299285232888549708615495109 56115981166603070365405333)
                    ·
                      refine ⟨2630436617184518923378375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56115981166603070365405333 2630436617184518923378375)
                      ·
                        rfl

theorem cell23_5122757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 4, 6].length) (baseStart_5122757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5122757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5122757 prefixEnd_5122757 := by exact prefixLift 5122757
  have htrace : WordTrace (prefixWord ++ tailWord_5122757) baseStart_5122757 baseEnd_5122757 := by
    simpa [prefixWord, tailWord_5122757, baseEnd_5122757] using wordTrace_append hprefix tailTrace_5122757
  have hstable : (prefixWord ++ tailWord_5122757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5122757).length < 2 ^ (prefixWord ++ tailWord_5122757).sum := by decide
  have hdescent : baseEnd_5122757 < baseStart_5122757 := by decide
  rcases family_descends (prefixWord ++ tailWord_5122757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5122767 : List Nat := [1, 1, 2, 1, 1, 3, 1, 1, 5, 7]
def baseStart_5122767 : Nat := 118140960795 + 5122767 * 2 ^ 59
def prefixEnd_5122767 : Nat := 4983230072969 + 3 ^ 40 * 5122767 * 2
def baseEnd_5122767 : Nat := 876813917330354628084443

theorem tailTrace_5122767 : CollatzResearch.WordTrace tailWord_5122767 prefixEnd_5122767 876813917330354628084443 := by
  unfold tailWord_5122767
  simp only [CollatzResearch.WordTrace]
  refine ⟨186842662232097532794446555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124561774821398355196297703 186842662232097532794446555)
  ·
    refine ⟨280263993348146299191669833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186842662232097532794446555 280263993348146299191669833)
    ·
      refine ⟨210197995011109724393752375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 280263993348146299191669833 210197995011109724393752375)
      ·
        refine ⟨315296992516664586590628563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210197995011109724393752375 315296992516664586590628563)
        ·
          refine ⟨472945488774996879885942845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315296992516664586590628563 472945488774996879885942845)
          ·
            refine ⟨177354558290623829957228567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 472945488774996879885942845 177354558290623829957228567)
            ·
              refine ⟨266031837435935744935842851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177354558290623829957228567 266031837435935744935842851)
              ·
                refine ⟨399047756153903617403764277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 266031837435935744935842851 399047756153903617403764277)
                ·
                  refine ⟨37410727139428464131602901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 399047756153903617403764277 37410727139428464131602901)
                  ·
                    refine ⟨876813917330354628084443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37410727139428464131602901 876813917330354628084443)
                    ·
                      rfl

theorem cell23_5122767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 7].length) (baseStart_5122767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5122767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5122767 prefixEnd_5122767 := by exact prefixLift 5122767
  have htrace : WordTrace (prefixWord ++ tailWord_5122767) baseStart_5122767 baseEnd_5122767 := by
    simpa [prefixWord, tailWord_5122767, baseEnd_5122767] using wordTrace_append hprefix tailTrace_5122767
  have hstable : (prefixWord ++ tailWord_5122767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5122767).length < 2 ^ (prefixWord ++ tailWord_5122767).sum := by decide
  have hdescent : baseEnd_5122767 < baseStart_5122767 := by decide
  rcases family_descends (prefixWord ++ tailWord_5122767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5122831 : List Nat := [1, 1, 2, 1, 1, 1, 8, 1, 3, 4]
def baseStart_5122831 : Nat := 118140960795 + 5122831 * 2 ^ 59
def prefixEnd_5122831 : Nat := 4983230072969 + 3 ^ 40 * 5122831 * 2
def baseEnd_5122831 : Nat := 876824871584317211284345

theorem tailTrace_5122831 : CollatzResearch.WordTrace tailWord_5122831 prefixEnd_5122831 876824871584317211284345 := by
  unfold tailWord_5122831
  simp only [CollatzResearch.WordTrace]
  refine ⟨186844996503865671724776347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124563331002577114483184231 186844996503865671724776347)
  ·
    refine ⟨280267494755798507587164521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186844996503865671724776347 280267494755798507587164521)
    ·
      refine ⟨210200621066848880690373391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 280267494755798507587164521 210200621066848880690373391)
      ·
        refine ⟨315300931600273321035560087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210200621066848880690373391 315300931600273321035560087)
        ·
          refine ⟨472951397400409981553340131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315300931600273321035560087 472951397400409981553340131)
          ·
            refine ⟨709427096100614972330010197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 472951397400409981553340131 709427096100614972330010197)
            ·
              refine ⟨8313598782429081706992307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 709427096100614972330010197 8313598782429081706992307)
              ·
                refine ⟨12470398173643622560488461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8313598782429081706992307 12470398173643622560488461)
                ·
                  refine ⟨4676399315116358460183173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12470398173643622560488461 4676399315116358460183173)
                  ·
                    refine ⟨876824871584317211284345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4676399315116358460183173 876824871584317211284345)
                    ·
                      rfl

theorem cell23_5122831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 1, 3, 4].length) (baseStart_5122831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5122831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5122831 prefixEnd_5122831 := by exact prefixLift 5122831
  have htrace : WordTrace (prefixWord ++ tailWord_5122831) baseStart_5122831 baseEnd_5122831 := by
    simpa [prefixWord, tailWord_5122831, baseEnd_5122831] using wordTrace_append hprefix tailTrace_5122831
  have hstable : (prefixWord ++ tailWord_5122831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5122831).length < 2 ^ (prefixWord ++ tailWord_5122831).sum := by decide
  have hdescent : baseEnd_5122831 < baseStart_5122831 := by decide
  rcases family_descends (prefixWord ++ tailWord_5122831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5122898 : List Nat := [3, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2]
def baseStart_5122898 : Nat := 118140960795 + 5122898 * 2 ^ 59
def prefixEnd_5122898 : Nat := 4983230072969 + 3 ^ 40 * 5122898 * 2
def baseEnd_5122898 : Nat := 2630509017956802871715227

theorem tailTrace_5122898 : CollatzResearch.WordTrace tailWord_5122898 prefixEnd_5122898 2630509017956802871715227 := by
  unfold tailWord_5122898
  simp only [CollatzResearch.WordTrace]
  refine ⟨46711860048655735541866337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124564960129748628111643565 46711860048655735541866337)
  ·
    refine ⟨35033895036491801656399753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46711860048655735541866337 35033895036491801656399753)
    ·
      refine ⟨26275421277368851242299815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35033895036491801656399753 26275421277368851242299815)
      ·
        refine ⟨39413131916053276863449723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26275421277368851242299815 39413131916053276863449723)
        ·
          refine ⟨59119697874079915295174585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39413131916053276863449723 59119697874079915295174585)
          ·
            refine ⟨44339773405559936471380939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59119697874079915295174585 44339773405559936471380939)
            ·
              refine ⟨66509660108339904707071409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44339773405559936471380939 66509660108339904707071409)
              ·
                refine ⟨49882245081254928530303557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66509660108339904707071409 49882245081254928530303557)
                ·
                  refine ⟨9352920952735299099431917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49882245081254928530303557 9352920952735299099431917)
                  ·
                    refine ⟨3507345357275737162286969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9352920952735299099431917 3507345357275737162286969)
                    ·
                      refine ⟨2630509017956802871715227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3507345357275737162286969 2630509017956802871715227)
                      ·
                        rfl

theorem cell23_5122898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2].length) (baseStart_5122898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5122898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5122898 prefixEnd_5122898 := by exact prefixLift 5122898
  have htrace : WordTrace (prefixWord ++ tailWord_5122898) baseStart_5122898 baseEnd_5122898 := by
    simpa [prefixWord, tailWord_5122898, baseEnd_5122898] using wordTrace_append hprefix tailTrace_5122898
  have hstable : (prefixWord ++ tailWord_5122898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5122898).length < 2 ^ (prefixWord ++ tailWord_5122898).sum := by decide
  have hdescent : baseEnd_5122898 < baseStart_5122898 := by decide
  rcases family_descends (prefixWord ++ tailWord_5122898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5122904 : List Nat := [2, 1, 2, 2, 1, 1, 1, 2, 5, 6]
def baseStart_5122904 : Nat := 118140960795 + 5122904 * 2 ^ 59
def prefixEnd_5122904 : Nat := 4983230072969 + 3 ^ 40 * 5122904 * 2
def baseEnd_5122904 : Nat := 876837366280243282746733

theorem tailTrace_5122904 : CollatzResearch.WordTrace tailWord_5122904 prefixEnd_5122904 876837366280243282746733 := by
  unfold tailWord_5122904
  simp only [CollatzResearch.WordTrace]
  refine ⟨93423829516300602596091883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124565106021734136794789177 93423829516300602596091883)
  ·
    refine ⟨140135744274450903894137825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93423829516300602596091883 140135744274450903894137825)
    ·
      refine ⟨105101808205838177920603369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140135744274450903894137825 105101808205838177920603369)
      ·
        refine ⟨78826356154378633440452527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105101808205838177920603369 78826356154378633440452527)
        ·
          refine ⟨118239534231567950160678791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78826356154378633440452527 118239534231567950160678791)
          ·
            refine ⟨177359301347351925241018187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118239534231567950160678791 177359301347351925241018187)
            ·
              refine ⟨266038952021027887861527281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177359301347351925241018187 266038952021027887861527281)
              ·
                refine ⟨199529214015770915896145461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 266038952021027887861527281 199529214015770915896145461)
                ·
                  refine ⟨18705863813978523365263637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 199529214015770915896145461 18705863813978523365263637)
                  ·
                    refine ⟨876837366280243282746733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18705863813978523365263637 876837366280243282746733)
                    ·
                      rfl

theorem cell23_5122904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 5, 6].length) (baseStart_5122904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5122904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5122904 prefixEnd_5122904 := by exact prefixLift 5122904
  have htrace : WordTrace (prefixWord ++ tailWord_5122904) baseStart_5122904 baseEnd_5122904 := by
    simpa [prefixWord, tailWord_5122904, baseEnd_5122904] using wordTrace_append hprefix tailTrace_5122904
  have hstable : (prefixWord ++ tailWord_5122904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5122904).length < 2 ^ (prefixWord ++ tailWord_5122904).sum := by decide
  have hdescent : baseEnd_5122904 < baseStart_5122904 := by decide
  rcases family_descends (prefixWord ++ tailWord_5122904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5122908 : List Nat := [2, 2, 4, 2, 1, 2, 1, 1, 3, 5]
def baseStart_5122908 : Nat := 118140960795 + 5122908 * 2 ^ 59
def prefixEnd_5122908 : Nat := 4983230072969 + 3 ^ 40 * 5122908 * 2
def baseEnd_5122908 : Nat := 876838050921115944196727

theorem tailTrace_5122908 : CollatzResearch.WordTrace tailWord_5122908 prefixEnd_5122908 876838050921115944196727 := by
  unfold tailWord_5122908
  simp only [CollatzResearch.WordTrace]
  refine ⟨93423902462293356937664689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124565203283057809250219585 93423902462293356937664689)
  ·
    refine ⟨70067926846720017703248517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93423902462293356937664689 70067926846720017703248517)
    ·
      refine ⟨13137736283760003319359097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70067926846720017703248517 13137736283760003319359097)
      ·
        refine ⟨9853302212820002489519323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13137736283760003319359097 9853302212820002489519323)
        ·
          refine ⟨14779953319230003734278985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9853302212820002489519323 14779953319230003734278985)
          ·
            refine ⟨11084964989422502800709239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14779953319230003734278985 11084964989422502800709239)
            ·
              refine ⟨16627447484133754201063859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11084964989422502800709239 16627447484133754201063859)
              ·
                refine ⟨24941171226200631301595789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16627447484133754201063859 24941171226200631301595789)
                ·
                  refine ⟨9352939209825236738098421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24941171226200631301595789 9352939209825236738098421)
                  ·
                    refine ⟨876838050921115944196727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9352939209825236738098421 876838050921115944196727)
                    ·
                      rfl

theorem cell23_5122908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_5122908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5122908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5122908 prefixEnd_5122908 := by exact prefixLift 5122908
  have htrace : WordTrace (prefixWord ++ tailWord_5122908) baseStart_5122908 baseEnd_5122908 := by
    simpa [prefixWord, tailWord_5122908, baseEnd_5122908] using wordTrace_append hprefix tailTrace_5122908
  have hstable : (prefixWord ++ tailWord_5122908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5122908).length < 2 ^ (prefixWord ++ tailWord_5122908).sum := by decide
  have hdescent : baseEnd_5122908 < baseStart_5122908 := by decide
  rcases family_descends (prefixWord ++ tailWord_5122908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5122911 : List Nat := [1, 1, 2, 3, 1, 3, 3, 1, 3, 1, 4]
def baseStart_5122911 : Nat := 118140960795 + 5122911 * 2 ^ 59
def prefixEnd_5122911 : Nat := 4983230072969 + 3 ^ 40 * 5122911 * 2
def baseEnd_5122911 : Nat := 2630515693205311320852667

theorem tailTrace_5122911 : CollatzResearch.WordTrace tailWord_5122911 prefixEnd_5122911 2630515693205311320852667 := by
  unfold tailWord_5122911
  simp only [CollatzResearch.WordTrace]
  refine ⟨186847914343575845387688587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124565276229050563591792391 186847914343575845387688587)
  ·
    refine ⟨280271871515363768081532881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186847914343575845387688587 280271871515363768081532881)
    ·
      refine ⟨210203903636522826061149661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 280271871515363768081532881 210203903636522826061149661)
      ·
        refine ⟨78826463863696059772931123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 210203903636522826061149661 78826463863696059772931123)
        ·
          refine ⟨118239695795544089659396685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78826463863696059772931123 118239695795544089659396685)
          ·
            refine ⟨44339885923329033622273757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118239695795544089659396685 44339885923329033622273757)
            ·
              refine ⟨16627457221248387608352659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44339885923329033622273757 16627457221248387608352659)
              ·
                refine ⟨24941185831872581412528989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16627457221248387608352659 24941185831872581412528989)
                ·
                  refine ⟨9352944686952218029698371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24941185831872581412528989 9352944686952218029698371)
                  ·
                    refine ⟨14029417030428327044547557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9352944686952218029698371 14029417030428327044547557)
                    ·
                      refine ⟨2630515693205311320852667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14029417030428327044547557 2630515693205311320852667)
                      ·
                        rfl

theorem cell23_5122911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 3, 1, 4].length) (baseStart_5122911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5122911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5122911 prefixEnd_5122911 := by exact prefixLift 5122911
  have htrace : WordTrace (prefixWord ++ tailWord_5122911) baseStart_5122911 baseEnd_5122911 := by
    simpa [prefixWord, tailWord_5122911, baseEnd_5122911] using wordTrace_append hprefix tailTrace_5122911
  have hstable : (prefixWord ++ tailWord_5122911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5122911).length < 2 ^ (prefixWord ++ tailWord_5122911).sum := by decide
  have hdescent : baseEnd_5122911 < baseStart_5122911 := by decide
  rcases family_descends (prefixWord ++ tailWord_5122911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5122915 : List Nat := [1, 1, 1, 5, 3, 2, 2, 1, 2, 3, 2]
def baseStart_5122915 : Nat := 118140960795 + 5122915 * 2 ^ 59
def prefixEnd_5122915 : Nat := 4983230072969 + 3 ^ 40 * 5122915 * 2
def baseEnd_5122915 : Nat := 2630517747127929305202649

theorem tailTrace_5122915 : CollatzResearch.WordTrace tailWord_5122915 prefixEnd_5122915 2630517747127929305202649 := by
  unfold tailWord_5122915
  simp only [CollatzResearch.WordTrace]
  refine ⟨186848060235561354070834199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124565373490374236047222799 186848060235561354070834199)
  ·
    refine ⟨280272090353342031106251299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186848060235561354070834199 280272090353342031106251299)
    ·
      refine ⟨420408135530013046659376949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280272090353342031106251299 420408135530013046659376949)
      ·
        refine ⟨39413262705938723124316589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 420408135530013046659376949 39413262705938723124316589)
        ·
          refine ⟨14779973514727021171618721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39413262705938723124316589 14779973514727021171618721)
          ·
            refine ⟨11084980136045265878714041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14779973514727021171618721 11084980136045265878714041)
            ·
              refine ⟨8313735102033949409035531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11084980136045265878714041 8313735102033949409035531)
              ·
                refine ⟨12470602653050924113553297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8313735102033949409035531 12470602653050924113553297)
                ·
                  refine ⟨9352951989788193085164973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12470602653050924113553297 9352951989788193085164973)
                  ·
                    refine ⟨3507356996170572406936865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9352951989788193085164973 3507356996170572406936865)
                    ·
                      refine ⟨2630517747127929305202649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3507356996170572406936865 2630517747127929305202649)
                      ·
                        rfl

theorem cell23_5122915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 1, 2, 3, 2].length) (baseStart_5122915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5122915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5122915 prefixEnd_5122915 := by exact prefixLift 5122915
  have htrace : WordTrace (prefixWord ++ tailWord_5122915) baseStart_5122915 baseEnd_5122915 := by
    simpa [prefixWord, tailWord_5122915, baseEnd_5122915] using wordTrace_append hprefix tailTrace_5122915
  have hstable : (prefixWord ++ tailWord_5122915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5122915).length < 2 ^ (prefixWord ++ tailWord_5122915).sum := by decide
  have hdescent : baseEnd_5122915 < baseStart_5122915 := by decide
  rcases family_descends (prefixWord ++ tailWord_5122915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5122931 : List Nat := [1, 1, 1, 2, 2, 1, 7, 1, 1, 1, 5]
def baseStart_5122931 : Nat := 118140960795 + 5122931 * 2 ^ 59
def prefixEnd_5122931 : Nat := 4983230072969 + 3 ^ 40 * 5122931 * 2
def baseEnd_5122931 : Nat := 2630525962818401242602575

theorem tailTrace_5122931 : CollatzResearch.WordTrace tailWord_5122931 prefixEnd_5122931 2630525962818401242602575 := by
  unfold tailWord_5122931
  simp only [CollatzResearch.WordTrace]
  refine ⟨186848643803503388803416647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124565762535668925868944431 186848643803503388803416647)
  ·
    refine ⟨280272965705255083205124971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186848643803503388803416647 280272965705255083205124971)
    ·
      refine ⟨420409448557882624807687457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280272965705255083205124971 420409448557882624807687457)
      ·
        refine ⟨315307086418411968605765593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 420409448557882624807687457 315307086418411968605765593)
        ·
          refine ⟨236480314813808976454324195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 315307086418411968605765593 236480314813808976454324195)
          ·
            refine ⟨354720472220713464681486293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236480314813808976454324195 354720472220713464681486293)
            ·
              refine ⟨8313761067672971828472335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 354720472220713464681486293 8313761067672971828472335)
              ·
                refine ⟨12470641601509457742708503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8313761067672971828472335 12470641601509457742708503)
                ·
                  refine ⟨18705962402264186614062755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12470641601509457742708503 18705962402264186614062755)
                  ·
                    refine ⟨28058943603396279921094133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18705962402264186614062755 28058943603396279921094133)
                    ·
                      refine ⟨2630525962818401242602575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28058943603396279921094133 2630525962818401242602575)
                      ·
                        rfl

theorem cell23_5122931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 1, 1, 1, 5].length) (baseStart_5122931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5122931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5122931 prefixEnd_5122931 := by exact prefixLift 5122931
  have htrace : WordTrace (prefixWord ++ tailWord_5122931) baseStart_5122931 baseEnd_5122931 := by
    simpa [prefixWord, tailWord_5122931, baseEnd_5122931] using wordTrace_append hprefix tailTrace_5122931
  have hstable : (prefixWord ++ tailWord_5122931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5122931).length < 2 ^ (prefixWord ++ tailWord_5122931).sum := by decide
  have hdescent : baseEnd_5122931 < baseStart_5122931 := by decide
  rcases family_descends (prefixWord ++ tailWord_5122931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5122944 : List Nat := [2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 7]
def baseStart_5122944 : Nat := 118140960795 + 5122944 * 2 ^ 59
def prefixEnd_5122944 : Nat := 4983230072969 + 3 ^ 40 * 5122944 * 2
def baseEnd_5122944 : Nat := 2630532638066909691740015

theorem tailTrace_5122944 : CollatzResearch.WordTrace tailWord_5122944 prefixEnd_5122944 2630532638066909691740015 := by
  unfold tailWord_5122944
  simp only [CollatzResearch.WordTrace]
  refine ⟨93424558976228146011819943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124566078634970861349093257 93424558976228146011819943)
  ·
    refine ⟨140136838464342219017729915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93424558976228146011819943 140136838464342219017729915)
    ·
      refine ⟨210205257696513328526594873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140136838464342219017729915 210205257696513328526594873)
      ·
        refine ⟨157653943272384996394946155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210205257696513328526594873 157653943272384996394946155)
        ·
          refine ⟨236480914908577494592419233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157653943272384996394946155 236480914908577494592419233)
          ·
            refine ⟨177360686181433120944314425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 236480914908577494592419233 177360686181433120944314425)
            ·
              refine ⟨133020514636074840708235819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 177360686181433120944314425 133020514636074840708235819)
              ·
                refine ⟨199530771954112261062353729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133020514636074840708235819 199530771954112261062353729)
                ·
                  refine ⟨149648078965584195796765297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 199530771954112261062353729 149648078965584195796765297)
                  ·
                    refine ⟨112236059224188146847573973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 149648078965584195796765297 112236059224188146847573973)
                    ·
                      refine ⟨2630532638066909691740015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 112236059224188146847573973 2630532638066909691740015)
                      ·
                        rfl

theorem cell23_5122944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 7].length) (baseStart_5122944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5122944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5122944 prefixEnd_5122944 := by exact prefixLift 5122944
  have htrace : WordTrace (prefixWord ++ tailWord_5122944) baseStart_5122944 baseEnd_5122944 := by
    simpa [prefixWord, tailWord_5122944, baseEnd_5122944] using wordTrace_append hprefix tailTrace_5122944
  have hstable : (prefixWord ++ tailWord_5122944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5122944).length < 2 ^ (prefixWord ++ tailWord_5122944).sum := by decide
  have hdescent : baseEnd_5122944 < baseStart_5122944 := by decide
  rcases family_descends (prefixWord ++ tailWord_5122944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5122951 : List Nat := [1, 1, 4, 2, 3, 1, 3, 8]
def baseStart_5122951 : Nat := 118140960795 + 5122951 * 2 ^ 59
def prefixEnd_5122951 : Nat := 4983230072969 + 3 ^ 40 * 5122951 * 2
def baseEnd_5122951 : Nat := 97427267867833006087129

theorem tailTrace_5122951 : CollatzResearch.WordTrace tailWord_5122951 prefixEnd_5122951 97427267867833006087129 := by
  unfold tailWord_5122951
  simp only [CollatzResearch.WordTrace]
  refine ⟨186849373263430932219144707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124566248842287288146096471 186849373263430932219144707)
  ·
    refine ⟨280274059895146398328717061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186849373263430932219144707 280274059895146398328717061)
    ·
      refine ⟨52551386230339949686634449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 280274059895146398328717061 52551386230339949686634449)
      ·
        refine ⟨39413539672754962264975837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52551386230339949686634449 39413539672754962264975837)
        ·
          refine ⟨14780077377283110849365939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39413539672754962264975837 14780077377283110849365939)
          ·
            refine ⟨22170116065924666274048909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14780077377283110849365939 22170116065924666274048909)
            ·
              refine ⟨8313793524721749852768341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22170116065924666274048909 8313793524721749852768341)
              ·
                refine ⟨97427267867833006087129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8313793524721749852768341 97427267867833006087129)
                ·
                  rfl

theorem cell23_5122951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 8].length) (baseStart_5122951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5122951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5122951 prefixEnd_5122951 := by exact prefixLift 5122951
  have htrace : WordTrace (prefixWord ++ tailWord_5122951) baseStart_5122951 baseEnd_5122951 := by
    simpa [prefixWord, tailWord_5122951, baseEnd_5122951] using wordTrace_append hprefix tailTrace_5122951
  have hstable : (prefixWord ++ tailWord_5122951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5122951).length < 2 ^ (prefixWord ++ tailWord_5122951).sum := by decide
  have hdescent : baseEnd_5122951 < baseStart_5122951 := by decide
  rcases family_descends (prefixWord ++ tailWord_5122951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5122966 : List Nat := [5, 3, 1, 1, 1, 3, 1, 1, 2, 3, 2]
def baseStart_5122966 : Nat := 118140960795 + 5122966 * 2 ^ 59
def prefixEnd_5122966 : Nat := 4983230072969 + 3 ^ 40 * 5122966 * 2
def baseEnd_5122966 : Nat := 2630543934641308605664915

theorem tailTrace_5122966 : CollatzResearch.WordTrace tailWord_5122966 prefixEnd_5122966 2630543934641308605664915 := by
  unfold tailWord_5122966
  simp only [CollatzResearch.WordTrace]
  refine ⟨11678120022398536861308797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 124566613572251059853960501 11678120022398536861308797)
  ·
    refine ⟨4379295008399451322990799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11678120022398536861308797 4379295008399451322990799)
    ·
      refine ⟨6568942512599176984486199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4379295008399451322990799 6568942512599176984486199)
      ·
        refine ⟨9853413768898765476729299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6568942512599176984486199 9853413768898765476729299)
        ·
          refine ⟨14780120653348148215093949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9853413768898765476729299 14780120653348148215093949)
          ·
            refine ⟨5542545245005555580660231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14780120653348148215093949 5542545245005555580660231)
            ·
              refine ⟨8313817867508333370990347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5542545245005555580660231 8313817867508333370990347)
              ·
                refine ⟨12470726801262500056485521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8313817867508333370990347 12470726801262500056485521)
                ·
                  refine ⟨9353045100946875042364141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12470726801262500056485521 9353045100946875042364141)
                  ·
                    refine ⟨3507391912855078140886553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9353045100946875042364141 3507391912855078140886553)
                    ·
                      refine ⟨2630543934641308605664915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3507391912855078140886553 2630543934641308605664915)
                      ·
                        rfl

theorem cell23_5122966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_5122966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5122966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5122966 prefixEnd_5122966 := by exact prefixLift 5122966
  have htrace : WordTrace (prefixWord ++ tailWord_5122966) baseStart_5122966 baseEnd_5122966 := by
    simpa [prefixWord, tailWord_5122966, baseEnd_5122966] using wordTrace_append hprefix tailTrace_5122966
  have hstable : (prefixWord ++ tailWord_5122966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5122966).length < 2 ^ (prefixWord ++ tailWord_5122966).sum := by decide
  have hdescent : baseEnd_5122966 < baseStart_5122966 := by decide
  rcases family_descends (prefixWord ++ tailWord_5122966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5122989 : List Nat := [1, 5, 2, 3, 1, 2, 1, 2, 2, 4]
def baseStart_5122989 : Nat := 118140960795 + 5122989 * 2 ^ 59
def prefixEnd_5122989 : Nat := 4983230072969 + 3 ^ 40 * 5122989 * 2
def baseEnd_5122989 : Nat := 876851914898787338559103

theorem tailTrace_5122989 : CollatzResearch.WordTrace tailWord_5122989 prefixEnd_5122989 876851914898787338559103 := by
  unfold tailWord_5122989
  simp only [CollatzResearch.WordTrace]
  refine ⟨186850759237293264709028021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124567172824862176472685347 186850759237293264709028021)
  ·
    refine ⟨17517258678496243566471377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 186850759237293264709028021 17517258678496243566471377)
    ·
      refine ⟨13137944008872182674853533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17517258678496243566471377 13137944008872182674853533)
      ·
        refine ⟨4926729003327068503070075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13137944008872182674853533 4926729003327068503070075)
        ·
          refine ⟨7390093504990602754605113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4926729003327068503070075 7390093504990602754605113)
          ·
            refine ⟨5542570128742952065953835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7390093504990602754605113 5542570128742952065953835)
            ·
              refine ⟨8313855193114428098930753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5542570128742952065953835 8313855193114428098930753)
              ·
                refine ⟨6235391394835821074198065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8313855193114428098930753 6235391394835821074198065)
                ·
                  refine ⟨4676543546126865805648549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6235391394835821074198065 4676543546126865805648549)
                  ·
                    refine ⟨876851914898787338559103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4676543546126865805648549 876851914898787338559103)
                    ·
                      rfl

theorem cell23_5122989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_5122989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5122989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5122989 prefixEnd_5122989 := by exact prefixLift 5122989
  have htrace : WordTrace (prefixWord ++ tailWord_5122989) baseStart_5122989 baseEnd_5122989 := by
    simpa [prefixWord, tailWord_5122989, baseEnd_5122989] using wordTrace_append hprefix tailTrace_5122989
  have hstable : (prefixWord ++ tailWord_5122989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5122989).length < 2 ^ (prefixWord ++ tailWord_5122989).sum := by decide
  have hdescent : baseEnd_5122989 < baseStart_5122989 := by decide
  rcases family_descends (prefixWord ++ tailWord_5122989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5122996 : List Nat := [2, 5, 2, 1, 1, 1, 2, 4, 1, 2, 2]
def baseStart_5122996 : Nat := 118140960795 + 5122996 * 2 ^ 59
def prefixEnd_5122996 : Nat := 4983230072969 + 3 ^ 40 * 5122996 * 2
def baseEnd_5122996 : Nat := 2630559339060943488289777

theorem tailTrace_5122996 : CollatzResearch.WordTrace tailWord_5122996 prefixEnd_5122996 2630559339060943488289777 := by
  unfold tailWord_5122996
  simp only [CollatzResearch.WordTrace]
  refine ⟨93425507274133952452266421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124567343032178603269688561 93425507274133952452266421)
  ·
    refine ⟨8758641306950058042399977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 93425507274133952452266421 8758641306950058042399977)
    ·
      refine ⟨6568980980212543531799983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8758641306950058042399977 6568980980212543531799983)
      ·
        refine ⟨9853471470318815297699975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6568980980212543531799983 9853471470318815297699975)
        ·
          refine ⟨14780207205478222946549963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9853471470318815297699975 14780207205478222946549963)
          ·
            refine ⟨22170310808217334419824945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14780207205478222946549963 22170310808217334419824945)
            ·
              refine ⟨16627733106163000814868709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22170310808217334419824945 16627733106163000814868709)
              ·
                refine ⟨3117699957405562652787883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16627733106163000814868709 3117699957405562652787883)
                ·
                  refine ⟨4676549936108343979181825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3117699957405562652787883 4676549936108343979181825)
                  ·
                    refine ⟨3507412452081257984386369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4676549936108343979181825 3507412452081257984386369)
                    ·
                      refine ⟨2630559339060943488289777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3507412452081257984386369 2630559339060943488289777)
                      ·
                        rfl

theorem cell23_5122996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_5122996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5122996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5122996 prefixEnd_5122996 := by exact prefixLift 5122996
  have htrace : WordTrace (prefixWord ++ tailWord_5122996) baseStart_5122996 baseEnd_5122996 := by
    simpa [prefixWord, tailWord_5122996, baseEnd_5122996] using wordTrace_append hprefix tailTrace_5122996
  have hstable : (prefixWord ++ tailWord_5122996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5122996).length < 2 ^ (prefixWord ++ tailWord_5122996).sum := by decide
  have hdescent : baseEnd_5122996 < baseStart_5122996 := by decide
  rcases family_descends (prefixWord ++ tailWord_5122996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5123022 : List Nat := [4, 1, 1, 1, 2, 4, 2, 2, 1, 3, 2]
def baseStart_5123022 : Nat := 118140960795 + 5123022 * 2 ^ 59
def prefixEnd_5123022 : Nat := 4983230072969 + 3 ^ 40 * 5123022 * 2
def baseEnd_5123022 : Nat := 2630572689557960386564657

theorem tailTrace_5123022 : CollatzResearch.WordTrace tailWord_5123022 prefixEnd_5123022 2630572689557960386564657 := by
  unfold tailWord_5123022
  simp only [CollatzResearch.WordTrace]
  refine ⟨23356495355771713918122415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124567975230782474229986213 23356495355771713918122415)
  ·
    refine ⟨35034743033657570877183623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23356495355771713918122415 35034743033657570877183623)
    ·
      refine ⟨52552114550486356315775435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35034743033657570877183623 52552114550486356315775435)
      ·
        refine ⟨78828171825729534473663153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52552114550486356315775435 78828171825729534473663153)
        ·
          refine ⟨59121128869297150855247365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78828171825729534473663153 59121128869297150855247365)
          ·
            refine ⟨11085211662993215785358881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59121128869297150855247365 11085211662993215785358881)
            ·
              refine ⟨8313908747244911839019161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11085211662993215785358881 8313908747244911839019161)
              ·
                refine ⟨6235431560433683879264371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8313908747244911839019161 6235431560433683879264371)
                ·
                  refine ⟨9353147340650525818896557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6235431560433683879264371 9353147340650525818896557)
                  ·
                    refine ⟨3507430252743947182086209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9353147340650525818896557 3507430252743947182086209)
                    ·
                      refine ⟨2630572689557960386564657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3507430252743947182086209 2630572689557960386564657)
                      ·
                        rfl

theorem cell23_5123022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 2, 1, 3, 2].length) (baseStart_5123022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5123022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5123022 prefixEnd_5123022 := by exact prefixLift 5123022
  have htrace : WordTrace (prefixWord ++ tailWord_5123022) baseStart_5123022 baseEnd_5123022 := by
    simpa [prefixWord, tailWord_5123022, baseEnd_5123022] using wordTrace_append hprefix tailTrace_5123022
  have hstable : (prefixWord ++ tailWord_5123022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5123022).length < 2 ^ (prefixWord ++ tailWord_5123022).sum := by decide
  have hdescent : baseEnd_5123022 < baseStart_5123022 := by decide
  rcases family_descends (prefixWord ++ tailWord_5123022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5123031 : List Nat := [1, 1, 3, 2, 1, 1, 2, 2, 4, 2, 4]
def baseStart_5123031 : Nat := 118140960795 + 5123031 * 2 ^ 59
def prefixEnd_5123031 : Nat := 4983230072969 + 3 ^ 40 * 5123031 * 2
def baseEnd_5123031 : Nat := 2630577310883850851352115

theorem tailTrace_5123031 : CollatzResearch.WordTrace tailWord_5123031 prefixEnd_5123031 2630577310883850851352115 := by
  unfold tailWord_5123031
  simp only [CollatzResearch.WordTrace]
  refine ⟨186852291103141105882056947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124568194068760737254704631 186852291103141105882056947)
  ·
    refine ⟨280278436654711658823085421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186852291103141105882056947 280278436654711658823085421)
    ·
      refine ⟨105104413745516872058657033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 280278436654711658823085421 105104413745516872058657033)
      ·
        refine ⟨78828310309137654043992775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105104413745516872058657033 78828310309137654043992775)
        ·
          refine ⟨118242465463706481065989163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78828310309137654043992775 118242465463706481065989163)
          ·
            refine ⟨177363698195559721598983745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118242465463706481065989163 177363698195559721598983745)
            ·
              refine ⟨133022773646669791199237809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 177363698195559721598983745 133022773646669791199237809)
              ·
                refine ⟨99767080235002343399428357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133022773646669791199237809 99767080235002343399428357)
                ·
                  refine ⟨18706327544062939387392817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 99767080235002343399428357 18706327544062939387392817)
                  ·
                    refine ⟨14029745658047204540544613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18706327544062939387392817 14029745658047204540544613)
                    ·
                      refine ⟨2630577310883850851352115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14029745658047204540544613 2630577310883850851352115)
                      ·
                        rfl

theorem cell23_5123031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 4, 2, 4].length) (baseStart_5123031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5123031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5123031 prefixEnd_5123031 := by exact prefixLift 5123031
  have htrace : WordTrace (prefixWord ++ tailWord_5123031) baseStart_5123031 baseEnd_5123031 := by
    simpa [prefixWord, tailWord_5123031, baseEnd_5123031] using wordTrace_append hprefix tailTrace_5123031
  have hstable : (prefixWord ++ tailWord_5123031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5123031).length < 2 ^ (prefixWord ++ tailWord_5123031).sum := by decide
  have hdescent : baseEnd_5123031 < baseStart_5123031 := by decide
  rcases family_descends (prefixWord ++ tailWord_5123031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5123142 : List Nat := [6, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4]
def baseStart_5123142 : Nat := 118140960795 + 5123142 * 2 ^ 59
def prefixEnd_5123142 : Nat := 4983230072969 + 3 ^ 40 * 5123142 * 2
def baseEnd_5123142 : Nat := 2630634307236499917064105

theorem tailTrace_5123142 : CollatzResearch.WordTrace tailWord_5123142 prefixEnd_5123142 2630634307236499917064105 := by
  unfold tailWord_5123142
  simp only [CollatzResearch.WordTrace]
  refine ⟨5839260612679342869979615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 124570893070492647892898453 5839260612679342869979615)
  ·
    refine ⟨8758890919019014304969423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5839260612679342869979615 8758890919019014304969423)
    ·
      refine ⟨13138336378528521457454135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8758890919019014304969423 13138336378528521457454135)
      ·
        refine ⟨19707504567792782186181203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13138336378528521457454135 19707504567792782186181203)
        ·
          refine ⟨29561256851689173279271805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19707504567792782186181203 29561256851689173279271805)
          ·
            refine ⟨11085471319383439979726927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29561256851689173279271805 11085471319383439979726927)
            ·
              refine ⟨16628206979075159969590391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11085471319383439979726927 16628206979075159969590391)
              ·
                refine ⟨24942310468612739954385587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16628206979075159969590391 24942310468612739954385587)
                ·
                  refine ⟨37413465702919109931578381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24942310468612739954385587 37413465702919109931578381)
                  ·
                    refine ⟨14030049638594666224341893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37413465702919109931578381 14030049638594666224341893)
                    ·
                      refine ⟨2630634307236499917064105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14030049638594666224341893 2630634307236499917064105)
                      ·
                        rfl

theorem cell23_5123142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_5123142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5123142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5123142 prefixEnd_5123142 := by exact prefixLift 5123142
  have htrace : WordTrace (prefixWord ++ tailWord_5123142) baseStart_5123142 baseEnd_5123142 := by
    simpa [prefixWord, tailWord_5123142, baseEnd_5123142] using wordTrace_append hprefix tailTrace_5123142
  have hstable : (prefixWord ++ tailWord_5123142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5123142).length < 2 ^ (prefixWord ++ tailWord_5123142).sum := by decide
  have hdescent : baseEnd_5123142 < baseStart_5123142 := by decide
  rcases family_descends (prefixWord ++ tailWord_5123142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5123151 : List Nat := [1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 8]
def baseStart_5123151 : Nat := 118140960795 + 5123151 * 2 ^ 59
def prefixEnd_5123151 : Nat := 4983230072969 + 3 ^ 40 * 5123151 * 2
def baseEnd_5123151 : Nat := 2630638928562390381851563

theorem tailTrace_5123151 : CollatzResearch.WordTrace tailWord_5123151 prefixEnd_5123151 2630638928562390381851563 := by
  unfold tailWord_5123151
  simp only [CollatzResearch.WordTrace]
  refine ⟨186856667862706366376425307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124571111908470910917616871 186856667862706366376425307)
  ·
    refine ⟨280285001794059549564637961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186856667862706366376425307 280285001794059549564637961)
    ·
      refine ⟨210213751345544662173478471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 280285001794059549564637961 210213751345544662173478471)
      ·
        refine ⟨315320627018316993260217707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210213751345544662173478471 315320627018316993260217707)
        ·
          refine ⟨472980940527475489890326561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315320627018316993260217707 472980940527475489890326561)
          ·
            refine ⟨354735705395606617417744921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 472980940527475489890326561 354735705395606617417744921)
            ·
              refine ⟨266051779046704963063308691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 354735705395606617417744921 266051779046704963063308691)
              ·
                refine ⟨399077668570057444594963037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 266051779046704963063308691 399077668570057444594963037)
                ·
                  refine ⟨149654125713771541723111139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 399077668570057444594963037 149654125713771541723111139)
                  ·
                    refine ⟨224481188570657312584666709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 149654125713771541723111139 224481188570657312584666709)
                    ·
                      refine ⟨2630638928562390381851563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 224481188570657312584666709 2630638928562390381851563)
                      ·
                        rfl

theorem cell23_5123151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 8].length) (baseStart_5123151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5123151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5123151 prefixEnd_5123151 := by exact prefixLift 5123151
  have htrace : WordTrace (prefixWord ++ tailWord_5123151) baseStart_5123151 baseEnd_5123151 := by
    simpa [prefixWord, tailWord_5123151, baseEnd_5123151] using wordTrace_append hprefix tailTrace_5123151
  have hstable : (prefixWord ++ tailWord_5123151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5123151).length < 2 ^ (prefixWord ++ tailWord_5123151).sum := by decide
  have hdescent : baseEnd_5123151 < baseStart_5123151 := by decide
  rcases family_descends (prefixWord ++ tailWord_5123151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5123182 : List Nat := [4, 1, 2, 2, 1, 3, 3, 1, 6]
def baseStart_5123182 : Nat := 118140960795 + 5123182 * 2 ^ 59
def prefixEnd_5123182 : Nat := 4983230072969 + 3 ^ 40 * 5123182 * 2
def baseEnd_5123182 : Nat := 292294982940297751173769

theorem tailTrace_5123182 : CollatzResearch.WordTrace tailWord_5123182 prefixEnd_5123182 292294982940297751173769 := by
  unfold tailWord_5123182
  simp only [CollatzResearch.WordTrace]
  refine ⟨23357224815699257333850475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124571865683729372447202533 23357224815699257333850475)
  ·
    refine ⟨35035837223548886000775713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23357224815699257333850475 35035837223548886000775713)
    ·
      refine ⟨26276877917661664500581785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35035837223548886000775713 26276877917661664500581785)
      ·
        refine ⟨19707658438246248375436339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26276877917661664500581785 19707658438246248375436339)
        ·
          refine ⟨29561487657369372563154509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19707658438246248375436339 29561487657369372563154509)
          ·
            refine ⟨11085557871513514711182941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29561487657369372563154509 11085557871513514711182941)
            ·
              refine ⟨4157084201817568016693603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11085557871513514711182941 4157084201817568016693603)
              ·
                refine ⟨6235626302726352025040405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4157084201817568016693603 6235626302726352025040405)
                ·
                  refine ⟨292294982940297751173769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6235626302726352025040405 292294982940297751173769)
                  ·
                    rfl

theorem cell23_5123182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 3, 1, 6].length) (baseStart_5123182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5123182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5123182 prefixEnd_5123182 := by exact prefixLift 5123182
  have htrace : WordTrace (prefixWord ++ tailWord_5123182) baseStart_5123182 baseEnd_5123182 := by
    simpa [prefixWord, tailWord_5123182, baseEnd_5123182] using wordTrace_append hprefix tailTrace_5123182
  have hstable : (prefixWord ++ tailWord_5123182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5123182).length < 2 ^ (prefixWord ++ tailWord_5123182).sum := by decide
  have hdescent : baseEnd_5123182 < baseStart_5123182 := by decide
  rcases family_descends (prefixWord ++ tailWord_5123182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5123185 : List Nat := [1, 2, 2, 2, 1, 1, 2, 1, 6, 3, 2]
def baseStart_5123185 : Nat := 118140960795 + 5123185 * 2 ^ 59
def prefixEnd_5123185 : Nat := 4983230072969 + 3 ^ 40 * 5123185 * 2
def baseEnd_5123185 : Nat := 2630656386904643248826407

theorem tailTrace_5123185 : CollatzResearch.WordTrace tailWord_5123185 prefixEnd_5123185 2630656386904643248826407 := by
  unfold tailWord_5123185
  simp only [CollatzResearch.WordTrace]
  refine ⟨186857907944583190183163009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124571938629722126788775339 186857907944583190183163009)
  ·
    refine ⟨140143430958437392637372257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186857907944583190183163009 140143430958437392637372257)
    ·
      refine ⟨105107573218828044478029193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140143430958437392637372257 105107573218828044478029193)
      ·
        refine ⟨78830679914121033358521895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105107573218828044478029193 78830679914121033358521895)
        ·
          refine ⟨118246019871181550037782843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78830679914121033358521895 118246019871181550037782843)
          ·
            refine ⟨177369029806772325056674265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118246019871181550037782843 177369029806772325056674265)
            ·
              refine ⟨133026772355079243792505699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 177369029806772325056674265 133026772355079243792505699)
              ·
                refine ⟨199540158532618865688758549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133026772355079243792505699 199540158532618865688758549)
                ·
                  refine ⟨9353444931216509329160557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 199540158532618865688758549 9353444931216509329160557)
                  ·
                    refine ⟨3507541849206190998435209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9353444931216509329160557 3507541849206190998435209)
                    ·
                      refine ⟨2630656386904643248826407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3507541849206190998435209 2630656386904643248826407)
                      ·
                        rfl

theorem cell23_5123185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 6, 3, 2].length) (baseStart_5123185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5123185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5123185 prefixEnd_5123185 := by exact prefixLift 5123185
  have htrace : WordTrace (prefixWord ++ tailWord_5123185) baseStart_5123185 baseEnd_5123185 := by
    simpa [prefixWord, tailWord_5123185, baseEnd_5123185] using wordTrace_append hprefix tailTrace_5123185
  have hstable : (prefixWord ++ tailWord_5123185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5123185).length < 2 ^ (prefixWord ++ tailWord_5123185).sum := by decide
  have hdescent : baseEnd_5123185 < baseStart_5123185 := by decide
  rcases family_descends (prefixWord ++ tailWord_5123185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5123209 : List Nat := [1, 2, 1, 1, 4, 3, 3, 3, 1, 1, 3]
def baseStart_5123209 : Nat := 118140960795 + 5123209 * 2 ^ 59
def prefixEnd_5123209 : Nat := 4983230072969 + 3 ^ 40 * 5123209 * 2
def baseEnd_5123209 : Nat := 2630668710440351154926297

theorem tailTrace_5123209 : CollatzResearch.WordTrace tailWord_5123209 prefixEnd_5123209 2630668710440351154926297 := by
  unfold tailWord_5123209
  simp only [CollatzResearch.WordTrace]
  refine ⟨186858783296496242282036681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124572522197664161521357787 186858783296496242282036681)
  ·
    refine ⟨140144087472372181711527511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186858783296496242282036681 140144087472372181711527511)
    ·
      refine ⟨210216131208558272567291267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140144087472372181711527511 210216131208558272567291267)
      ·
        refine ⟨315324196812837408850936901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210216131208558272567291267 315324196812837408850936901)
        ·
          refine ⟨59123286902407014159550669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 315324196812837408850936901 59123286902407014159550669)
          ·
            refine ⟨22171232588402630309831501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59123286902407014159550669 22171232588402630309831501)
            ·
              refine ⟨8314212220650986366186813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22171232588402630309831501 8314212220650986366186813)
              ·
                refine ⟨3117829582744119887320055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8314212220650986366186813 3117829582744119887320055)
                ·
                  refine ⟨4676744374116179830980083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3117829582744119887320055 4676744374116179830980083)
                  ·
                    refine ⟨7015116561174269746470125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4676744374116179830980083 7015116561174269746470125)
                    ·
                      refine ⟨2630668710440351154926297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7015116561174269746470125 2630668710440351154926297)
                      ·
                        rfl

theorem cell23_5123209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 3, 1, 1, 3].length) (baseStart_5123209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5123209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5123209 prefixEnd_5123209 := by exact prefixLift 5123209
  have htrace : WordTrace (prefixWord ++ tailWord_5123209) baseStart_5123209 baseEnd_5123209 := by
    simpa [prefixWord, tailWord_5123209, baseEnd_5123209] using wordTrace_append hprefix tailTrace_5123209
  have hstable : (prefixWord ++ tailWord_5123209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5123209).length < 2 ^ (prefixWord ++ tailWord_5123209).sum := by decide
  have hdescent : baseEnd_5123209 < baseStart_5123209 := by decide
  rcases family_descends (prefixWord ++ tailWord_5123209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5123249 : List Nat := [1, 2, 2, 5, 1, 3, 1, 2, 1, 1, 4]
def baseStart_5123249 : Nat := 118140960795 + 5123249 * 2 ^ 59
def prefixEnd_5123249 : Nat := 4983230072969 + 3 ^ 40 * 5123249 * 2
def baseEnd_5123249 : Nat := 2630689249666530998426113

theorem tailTrace_5123249 : CollatzResearch.WordTrace tailWord_5123249 prefixEnd_5123249 2630689249666530998426113 := by
  unfold tailWord_5123249
  simp only [CollatzResearch.WordTrace]
  refine ⟨186860242216351329113492801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124573494810900886075661867 186860242216351329113492801)
  ·
    refine ⟨140145181662263496835119601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186860242216351329113492801 140145181662263496835119601)
    ·
      refine ⟨105108886246697622626339701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140145181662263496835119601 105108886246697622626339701)
      ·
        refine ⟨9853958085627902121219347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 105108886246697622626339701 9853958085627902121219347)
        ·
          refine ⟨14780937128441853181829021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9853958085627902121219347 14780937128441853181829021)
          ·
            refine ⟨5542851423165694943185883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14780937128441853181829021 5542851423165694943185883)
            ·
              refine ⟨8314277134748542414778825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5542851423165694943185883 8314277134748542414778825)
              ·
                refine ⟨6235707851061406811084119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8314277134748542414778825 6235707851061406811084119)
                ·
                  refine ⟨9353561776592110216626179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6235707851061406811084119 9353561776592110216626179)
                  ·
                    refine ⟨14030342664888165324939269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9353561776592110216626179 14030342664888165324939269)
                    ·
                      refine ⟨2630689249666530998426113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14030342664888165324939269 2630689249666530998426113)
                      ·
                        rfl

theorem cell23_5123249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_5123249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5123249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5123249 prefixEnd_5123249 := by exact prefixLift 5123249
  have htrace : WordTrace (prefixWord ++ tailWord_5123249) baseStart_5123249 baseEnd_5123249 := by
    simpa [prefixWord, tailWord_5123249, baseEnd_5123249] using wordTrace_append hprefix tailTrace_5123249
  have hstable : (prefixWord ++ tailWord_5123249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5123249).length < 2 ^ (prefixWord ++ tailWord_5123249).sum := by decide
  have hdescent : baseEnd_5123249 < baseStart_5123249 := by decide
  rcases family_descends (prefixWord ++ tailWord_5123249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5123262 : List Nat := [4, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4]
def baseStart_5123262 : Nat := 118140960795 + 5123262 * 2 ^ 59
def prefixEnd_5123262 : Nat := 4983230072969 + 3 ^ 40 * 5123262 * 2
def baseEnd_5123262 : Nat := 2630695924915039447563553

theorem tailTrace_5123262 : CollatzResearch.WordTrace tailWord_5123262 prefixEnd_5123262 2630695924915039447563553 := by
  unfold tailWord_5123262
  simp only [CollatzResearch.WordTrace]
  refine ⟨23357589545663029041714505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124573810910202821555810693 23357589545663029041714505)
  ·
    refine ⟨17518192159247271781285879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23357589545663029041714505 17518192159247271781285879)
    ·
      refine ⟨26277288238870907671928819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17518192159247271781285879 26277288238870907671928819)
      ·
        refine ⟨39415932358306361507893229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26277288238870907671928819 39415932358306361507893229)
        ·
          refine ⟨14780974634364885565459961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39415932358306361507893229 14780974634364885565459961)
          ·
            refine ⟨11085730975773664174094971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14780974634364885565459961 11085730975773664174094971)
            ·
              refine ⟨16628596463660496261142457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11085730975773664174094971 16628596463660496261142457)
              ·
                refine ⟨12471447347745372195856843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16628596463660496261142457 12471447347745372195856843)
                ·
                  refine ⟨18707171021618058293785265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12471447347745372195856843 18707171021618058293785265)
                  ·
                    refine ⟨14030378266213543720338949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18707171021618058293785265 14030378266213543720338949)
                    ·
                      refine ⟨2630695924915039447563553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14030378266213543720338949 2630695924915039447563553)
                      ·
                        rfl

theorem cell23_5123262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_5123262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5123262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5123262 prefixEnd_5123262 := by exact prefixLift 5123262
  have htrace : WordTrace (prefixWord ++ tailWord_5123262) baseStart_5123262 baseEnd_5123262 := by
    simpa [prefixWord, tailWord_5123262, baseEnd_5123262] using wordTrace_append hprefix tailTrace_5123262
  have hstable : (prefixWord ++ tailWord_5123262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5123262).length < 2 ^ (prefixWord ++ tailWord_5123262).sum := by decide
  have hdescent : baseEnd_5123262 < baseStart_5123262 := by decide
  rcases family_descends (prefixWord ++ tailWord_5123262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5123277 : List Nat := [1, 6, 2, 2, 1, 2, 2, 2, 1, 1, 3]
def baseStart_5123277 : Nat := 118140960795 + 5123277 * 2 ^ 59
def prefixEnd_5123277 : Nat := 4983230072969 + 3 ^ 40 * 5123277 * 2
def baseEnd_5123277 : Nat := 2630703627124856888875985

theorem tailTrace_5123277 : CollatzResearch.WordTrace tailWord_5123277 prefixEnd_5123277 2630703627124856888875985 := by
  unfold tailWord_5123277
  simp only [CollatzResearch.WordTrace]
  refine ⟨186861263460249889895512085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124574175640166593263674723 186861263460249889895512085)
  ·
    refine ⟨8759121724699213588852129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 186861263460249889895512085 8759121724699213588852129)
    ·
      refine ⟨6569341293524410191639097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8759121724699213588852129 6569341293524410191639097)
      ·
        refine ⟨4927005970143307643729323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6569341293524410191639097 4927005970143307643729323)
        ·
          refine ⟨7390508955214961465593985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4927005970143307643729323 7390508955214961465593985)
          ·
            refine ⟨5542881716411221099195489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7390508955214961465593985 5542881716411221099195489)
            ·
              refine ⟨4157161287308415824396617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5542881716411221099195489 4157161287308415824396617)
              ·
                refine ⟨3117870965481311868297463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4157161287308415824396617 3117870965481311868297463)
                ·
                  refine ⟨4676806448221967802446195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3117870965481311868297463 4676806448221967802446195)
                  ·
                    refine ⟨7015209672332951703669293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4676806448221967802446195 7015209672332951703669293)
                    ·
                      refine ⟨2630703627124856888875985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7015209672332951703669293 2630703627124856888875985)
                      ·
                        rfl

theorem cell23_5123277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_5123277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5123277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5123277 prefixEnd_5123277 := by exact prefixLift 5123277
  have htrace : WordTrace (prefixWord ++ tailWord_5123277) baseStart_5123277 baseEnd_5123277 := by
    simpa [prefixWord, tailWord_5123277, baseEnd_5123277] using wordTrace_append hprefix tailTrace_5123277
  have hstable : (prefixWord ++ tailWord_5123277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5123277).length < 2 ^ (prefixWord ++ tailWord_5123277).sum := by decide
  have hdescent : baseEnd_5123277 < baseStart_5123277 := by decide
  rcases family_descends (prefixWord ++ tailWord_5123277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5123285 : List Nat := [1, 3, 2, 4, 1, 1, 1, 1, 2, 7]
def baseStart_5123285 : Nat := 118140960795 + 5123285 * 2 ^ 59
def prefixEnd_5123285 : Nat := 4983230072969 + 3 ^ 40 * 5123285 * 2
def baseEnd_5123285 : Nat := 876902578323364285858649

theorem tailTrace_5123285 : CollatzResearch.WordTrace tailWord_5123285 prefixEnd_5123285 876902578323364285858649 := by
  unfold tailWord_5123285
  simp only [CollatzResearch.WordTrace]
  refine ⟨186861555244220907261803309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124574370162813938174535539 186861555244220907261803309)
  ·
    refine ⟨70073083216582840223176241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186861555244220907261803309 70073083216582840223176241)
    ·
      refine ⟨52554812412437130167382181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70073083216582840223176241 52554812412437130167382181)
      ·
        refine ⟨9854027327331961906384159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52554812412437130167382181 9854027327331961906384159)
        ·
          refine ⟨14781040990997942859576239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9854027327331961906384159 14781040990997942859576239)
          ·
            refine ⟨22171561486496914289364359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14781040990997942859576239 22171561486496914289364359)
            ·
              refine ⟨33257342229745371434046539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22171561486496914289364359 33257342229745371434046539)
              ·
                refine ⟨49886013344618057151069809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33257342229745371434046539 49886013344618057151069809)
                ·
                  refine ⟨37414510008463542863302357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49886013344618057151069809 37414510008463542863302357)
                  ·
                    refine ⟨876902578323364285858649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37414510008463542863302357 876902578323364285858649)
                    ·
                      rfl

theorem cell23_5123285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 7].length) (baseStart_5123285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5123285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5123285 prefixEnd_5123285 := by exact prefixLift 5123285
  have htrace : WordTrace (prefixWord ++ tailWord_5123285) baseStart_5123285 baseEnd_5123285 := by
    simpa [prefixWord, tailWord_5123285, baseEnd_5123285] using wordTrace_append hprefix tailTrace_5123285
  have hstable : (prefixWord ++ tailWord_5123285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5123285).length < 2 ^ (prefixWord ++ tailWord_5123285).sum := by decide
  have hdescent : baseEnd_5123285 < baseStart_5123285 := by decide
  rcases family_descends (prefixWord ++ tailWord_5123285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5123309 : List Nat := [1, 5, 1, 2, 2, 1, 2, 1, 3, 3, 2]
def baseStart_5123309 : Nat := 118140960795 + 5123309 * 2 ^ 59
def prefixEnd_5123309 : Nat := 4983230072969 + 3 ^ 40 * 5123309 * 2
def baseEnd_5123309 : Nat := 2630720058505800763675837

theorem tailTrace_5123309 : CollatzResearch.WordTrace tailWord_5123309 prefixEnd_5123309 2630720058505800763675837 := by
  unfold tailWord_5123309
  simp only [CollatzResearch.WordTrace]
  refine ⟨186862430596133959360676981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124574953730755972907117987 186862430596133959360676981)
  ·
    refine ⟨17518352868387558690063467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 186862430596133959360676981 17518352868387558690063467)
    ·
      refine ⟨26277529302581338035095201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17518352868387558690063467 26277529302581338035095201)
      ·
        refine ⟨19708146976936003526321401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26277529302581338035095201 19708146976936003526321401)
        ·
          refine ⟨14781110232702002644741051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19708146976936003526321401 14781110232702002644741051)
          ·
            refine ⟨22171665349053003967111577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14781110232702002644741051 22171665349053003967111577)
            ·
              refine ⟨16628749011789752975333683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22171665349053003967111577 16628749011789752975333683)
              ·
                refine ⟨24943123517684629463000525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16628749011789752975333683 24943123517684629463000525)
                ·
                  refine ⟨9353671319131736048625197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24943123517684629463000525 9353671319131736048625197)
                  ·
                    refine ⟨3507626744674401018234449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9353671319131736048625197 3507626744674401018234449)
                    ·
                      refine ⟨2630720058505800763675837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3507626744674401018234449 2630720058505800763675837)
                      ·
                        rfl

theorem cell23_5123309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 3, 3, 2].length) (baseStart_5123309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5123309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5123309 prefixEnd_5123309 := by exact prefixLift 5123309
  have htrace : WordTrace (prefixWord ++ tailWord_5123309) baseStart_5123309 baseEnd_5123309 := by
    simpa [prefixWord, tailWord_5123309, baseEnd_5123309] using wordTrace_append hprefix tailTrace_5123309
  have hstable : (prefixWord ++ tailWord_5123309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5123309).length < 2 ^ (prefixWord ++ tailWord_5123309).sum := by decide
  have hdescent : baseEnd_5123309 < baseStart_5123309 := by decide
  rcases family_descends (prefixWord ++ tailWord_5123309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5123322 : List Nat := [3, 1, 1, 1, 1, 4, 1, 4, 1, 4, 2]
def baseStart_5123322 : Nat := 118140960795 + 5123322 * 2 ^ 59
def prefixEnd_5123322 : Nat := 4983230072969 + 3 ^ 40 * 5123322 * 2
def baseEnd_5123322 : Nat := 2630726733754309212813277

theorem tailTrace_5123322 : CollatzResearch.WordTrace tailWord_5123322 prefixEnd_5123322 2630726733754309212813277 := by
  unfold tailWord_5123322
  simp only [CollatzResearch.WordTrace]
  refine ⟨46715726186271715645225055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124575269830057908387266813 46715726186271715645225055)
  ·
    refine ⟨70073589279407573467837583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46715726186271715645225055 70073589279407573467837583)
    ·
      refine ⟨105110383919111360201756375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70073589279407573467837583 105110383919111360201756375)
      ·
        refine ⟨157665575878667040302634563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105110383919111360201756375 157665575878667040302634563)
        ·
          refine ⟨236498363818000560453951845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157665575878667040302634563 236498363818000560453951845)
          ·
            refine ⟨44343443215875105085115971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 236498363818000560453951845 44343443215875105085115971)
            ·
              refine ⟨66515164823812657627673957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44343443215875105085115971 66515164823812657627673957)
              ·
                refine ⟨12471593404464873305188867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66515164823812657627673957 12471593404464873305188867)
                ·
                  refine ⟨18707390106697309957783301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12471593404464873305188867 18707390106697309957783301)
                  ·
                    refine ⟨3507635645005745617084369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18707390106697309957783301 3507635645005745617084369)
                    ·
                      refine ⟨2630726733754309212813277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3507635645005745617084369 2630726733754309212813277)
                      ·
                        rfl

theorem cell23_5123322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 4, 1, 4, 2].length) (baseStart_5123322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5123322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5123322 prefixEnd_5123322 := by exact prefixLift 5123322
  have htrace : WordTrace (prefixWord ++ tailWord_5123322) baseStart_5123322 baseEnd_5123322 := by
    simpa [prefixWord, tailWord_5123322, baseEnd_5123322] using wordTrace_append hprefix tailTrace_5123322
  have hstable : (prefixWord ++ tailWord_5123322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5123322).length < 2 ^ (prefixWord ++ tailWord_5123322).sum := by decide
  have hdescent : baseEnd_5123322 < baseStart_5123322 := by decide
  rcases family_descends (prefixWord ++ tailWord_5123322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5123326 : List Nat := [4, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2]
def baseStart_5123326 : Nat := 118140960795 + 5123326 * 2 ^ 59
def prefixEnd_5123326 : Nat := 4983230072969 + 3 ^ 40 * 5123326 * 2
def baseEnd_5123326 : Nat := 2630728787676927197163259

theorem tailTrace_5123326 : CollatzResearch.WordTrace tailWord_5123326 prefixEnd_5123326 2630728787676927197163259 := by
  unfold tailWord_5123326
  simp only [CollatzResearch.WordTrace]
  refine ⟨23357881329634046408005729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124575367091381580842697221 23357881329634046408005729)
  ·
    refine ⟨17518410997225534806004297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23357881329634046408005729 17518410997225534806004297)
    ·
      refine ⟨13138808247919151104503223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17518410997225534806004297 13138808247919151104503223)
      ·
        refine ⟨19708212371878726656754835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13138808247919151104503223 19708212371878726656754835)
        ·
          refine ⟨29562318557818089985132253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19708212371878726656754835 29562318557818089985132253)
          ·
            refine ⟨11085869459181783744424595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29562318557818089985132253 11085869459181783744424595)
            ·
              refine ⟨16628804188772675616636893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11085869459181783744424595 16628804188772675616636893)
              ·
                refine ⟨6235801570789753356238835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16628804188772675616636893 6235801570789753356238835)
                ·
                  refine ⟨9353702356184630034358253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6235801570789753356238835 9353702356184630034358253)
                  ·
                    refine ⟨3507638383569236262884345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9353702356184630034358253 3507638383569236262884345)
                    ·
                      refine ⟨2630728787676927197163259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3507638383569236262884345 2630728787676927197163259)
                      ·
                        rfl

theorem cell23_5123326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2].length) (baseStart_5123326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5123326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5123326 prefixEnd_5123326 := by exact prefixLift 5123326
  have htrace : WordTrace (prefixWord ++ tailWord_5123326) baseStart_5123326 baseEnd_5123326 := by
    simpa [prefixWord, tailWord_5123326, baseEnd_5123326] using wordTrace_append hprefix tailTrace_5123326
  have hstable : (prefixWord ++ tailWord_5123326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5123326).length < 2 ^ (prefixWord ++ tailWord_5123326).sum := by decide
  have hdescent : baseEnd_5123326 < baseStart_5123326 := by decide
  rcases family_descends (prefixWord ++ tailWord_5123326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5123328 : List Nat := [2, 1, 1, 2, 1, 1, 3, 1, 11]
def baseStart_5123328 : Nat := 118140960795 + 5123328 * 2 ^ 59
def prefixEnd_5123328 : Nat := 4983230072969 + 3 ^ 40 * 5123328 * 2
def baseEnd_5123328 : Nat := 292303312737581798815361

theorem tailTrace_5123328 : CollatzResearch.WordTrace tailWord_5123328 prefixEnd_5123328 292303312737581798815361 := by
  unfold tailWord_5123328
  simp only [CollatzResearch.WordTrace]
  refine ⟨93431561791532562802809319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124575415722043417070412425 93431561791532562802809319)
  ·
    refine ⟨140147342687298844204213979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93431561791532562802809319 140147342687298844204213979)
    ·
      refine ⟨210221014030948266306320969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140147342687298844204213979 210221014030948266306320969)
      ·
        refine ⟨157665760523211199729740727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210221014030948266306320969 157665760523211199729740727)
        ·
          refine ⟨236498640784816799594611091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157665760523211199729740727 236498640784816799594611091)
          ·
            refine ⟨354747961177225199391916637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236498640784816799594611091 354747961177225199391916637)
            ·
              refine ⟨133030485441459449771968739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 354747961177225199391916637 133030485441459449771968739)
              ·
                refine ⟨199545728162189174657953109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133030485441459449771968739 199545728162189174657953109)
                ·
                  refine ⟨292303312737581798815361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 199545728162189174657953109 292303312737581798815361)
                  ·
                    rfl

theorem cell23_5123328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 11].length) (baseStart_5123328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5123328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5123328 prefixEnd_5123328 := by exact prefixLift 5123328
  have htrace : WordTrace (prefixWord ++ tailWord_5123328) baseStart_5123328 baseEnd_5123328 := by
    simpa [prefixWord, tailWord_5123328, baseEnd_5123328] using wordTrace_append hprefix tailTrace_5123328
  have hstable : (prefixWord ++ tailWord_5123328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5123328).length < 2 ^ (prefixWord ++ tailWord_5123328).sum := by decide
  have hdescent : baseEnd_5123328 < baseStart_5123328 := by decide
  rcases family_descends (prefixWord ++ tailWord_5123328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5123339 : List Nat := [1, 1, 1, 1, 5, 4, 1, 1, 4, 2, 2]
def baseStart_5123339 : Nat := 118140960795 + 5123339 * 2 ^ 59
def prefixEnd_5123339 : Nat := 4983230072969 + 3 ^ 40 * 5123339 * 2
def baseEnd_5123339 : Nat := 2630735462925435646300699

theorem tailTrace_5123339 : CollatzResearch.WordTrace tailWord_5123339 prefixEnd_5123339 2630735462925435646300699 := by
  unfold tailWord_5123339
  simp only [CollatzResearch.WordTrace]
  refine ⟨186863524786025274484269071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124575683190683516322846047 186863524786025274484269071)
  ·
    refine ⟨280295287179037911726403607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186863524786025274484269071 280295287179037911726403607)
    ·
      refine ⟨420442930768556867589605411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280295287179037911726403607 420442930768556867589605411)
      ·
        refine ⟨630664396152835301384408117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 420442930768556867589605411 630664396152835301384408117)
        ·
          refine ⟨59124787139328309504788261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 630664396152835301384408117 59124787139328309504788261)
          ·
            refine ⟨11085897588624058032147799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59124787139328309504788261 11085897588624058032147799)
            ·
              refine ⟨16628846382936087048221699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11085897588624058032147799 16628846382936087048221699)
              ·
                refine ⟨24943269574404130572332549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16628846382936087048221699 24943269574404130572332549)
                ·
                  refine ⟨4676863045200774482312353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24943269574404130572332549 4676863045200774482312353)
                  ·
                    refine ⟨3507647283900580861734265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4676863045200774482312353 3507647283900580861734265)
                    ·
                      refine ⟨2630735462925435646300699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3507647283900580861734265 2630735462925435646300699)
                      ·
                        rfl

theorem cell23_5123339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 4, 2, 2].length) (baseStart_5123339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5123339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5123339 prefixEnd_5123339 := by exact prefixLift 5123339
  have htrace : WordTrace (prefixWord ++ tailWord_5123339) baseStart_5123339 baseEnd_5123339 := by
    simpa [prefixWord, tailWord_5123339, baseEnd_5123339] using wordTrace_append hprefix tailTrace_5123339
  have hstable : (prefixWord ++ tailWord_5123339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5123339).length < 2 ^ (prefixWord ++ tailWord_5123339).sum := by decide
  have hdescent : baseEnd_5123339 < baseStart_5123339 := by decide
  rcases family_descends (prefixWord ++ tailWord_5123339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5123345 : List Nat := [1, 2, 2, 1, 1, 4, 4, 1, 7]
def baseStart_5123345 : Nat := 118140960795 + 5123345 * 2 ^ 59
def prefixEnd_5123345 : Nat := 4983230072969 + 3 ^ 40 * 5123345 * 2
def baseEnd_5123345 : Nat := 292304282645484735869519

theorem tailTrace_5123345 : CollatzResearch.WordTrace tailWord_5123345 prefixEnd_5123345 292304282645484735869519 := by
  unfold tailWord_5123345
  simp only [CollatzResearch.WordTrace]
  refine ⟨186863743624003537508987489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124575829082669025005991659 186863743624003537508987489)
  ·
    refine ⟨140147807718002653131740617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186863743624003537508987489 140147807718002653131740617)
    ·
      refine ⟨105110855788501989848805463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140147807718002653131740617 105110855788501989848805463)
      ·
        refine ⟨157666283682752984773208195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105110855788501989848805463 157666283682752984773208195)
        ·
          refine ⟨236499425524129477159812293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157666283682752984773208195 236499425524129477159812293)
          ·
            refine ⟨44343642285774276967464805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 236499425524129477159812293 44343642285774276967464805)
            ·
              refine ⟨8314432928582676931399651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44343642285774276967464805 8314432928582676931399651)
              ·
                refine ⟨12471649392874015397099477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8314432928582676931399651 12471649392874015397099477)
                ·
                  refine ⟨292304282645484735869519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12471649392874015397099477 292304282645484735869519)
                  ·
                    rfl

theorem cell23_5123345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 1, 7].length) (baseStart_5123345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5123345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5123345 prefixEnd_5123345 := by exact prefixLift 5123345
  have htrace : WordTrace (prefixWord ++ tailWord_5123345) baseStart_5123345 baseEnd_5123345 := by
    simpa [prefixWord, tailWord_5123345, baseEnd_5123345] using wordTrace_append hprefix tailTrace_5123345
  have hstable : (prefixWord ++ tailWord_5123345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5123345).length < 2 ^ (prefixWord ++ tailWord_5123345).sum := by decide
  have hdescent : baseEnd_5123345 < baseStart_5123345 := by decide
  rcases family_descends (prefixWord ++ tailWord_5123345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5123375 : List Nat := [1, 1, 2, 1, 2, 1, 3, 5, 2, 5]
def baseStart_5123375 : Nat := 118140960795 + 5123375 * 2 ^ 59
def prefixEnd_5123375 : Nat := 4983230072969 + 3 ^ 40 * 5123375 * 2
def baseEnd_5123375 : Nat := 876917982742999168483511

theorem tailTrace_5123375 : CollatzResearch.WordTrace tailWord_5123375 prefixEnd_5123375 876917982742999168483511 := by
  unfold tailWord_5123375
  simp only [CollatzResearch.WordTrace]
  refine ⟨186864837813894852632579579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124576558542596568421719719 186864837813894852632579579)
  ·
    refine ⟨280297256720842278948869369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186864837813894852632579579 280297256720842278948869369)
    ·
      refine ⟨210222942540631709211652027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 280297256720842278948869369 210222942540631709211652027)
      ·
        refine ⟨315334413810947563817478041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210222942540631709211652027 315334413810947563817478041)
        ·
          refine ⟨236500810358210672863108531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 315334413810947563817478041 236500810358210672863108531)
          ·
            refine ⟨354751215537316009294662797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236500810358210672863108531 354751215537316009294662797)
            ·
              refine ⟨133031705826493503485498549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 354751215537316009294662797 133031705826493503485498549)
              ·
                refine ⟨12471722421233765951765489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 133031705826493503485498549 12471722421233765951765489)
                ·
                  refine ⟨9353791815925324463824117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12471722421233765951765489 9353791815925324463824117)
                  ·
                    refine ⟨876917982742999168483511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9353791815925324463824117 876917982742999168483511)
                    ·
                      rfl

theorem cell23_5123375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 5, 2, 5].length) (baseStart_5123375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5123375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5123375 prefixEnd_5123375 := by exact prefixLift 5123375
  have htrace : WordTrace (prefixWord ++ tailWord_5123375) baseStart_5123375 baseEnd_5123375 := by
    simpa [prefixWord, tailWord_5123375, baseEnd_5123375] using wordTrace_append hprefix tailTrace_5123375
  have hstable : (prefixWord ++ tailWord_5123375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5123375).length < 2 ^ (prefixWord ++ tailWord_5123375).sum := by decide
  have hdescent : baseEnd_5123375 < baseStart_5123375 := by decide
  rcases family_descends (prefixWord ++ tailWord_5123375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5123379 : List Nat := [1, 1, 1, 2, 5, 4, 1, 3, 5]
def baseStart_5123379 : Nat := 118140960795 + 5123379 * 2 ^ 59
def prefixEnd_5123379 : Nat := 4983230072969 + 3 ^ 40 * 5123379 * 2
def baseEnd_5123379 : Nat := 292306222461290609977835

theorem tailTrace_5123379 : CollatzResearch.WordTrace tailWord_5123379 prefixEnd_5123379 292306222461290609977835 := by
  unfold tailWord_5123379
  simp only [CollatzResearch.WordTrace]
  refine ⟨186864983705880361315725191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124576655803920240877150127 186864983705880361315725191)
  ·
    refine ⟨280297475558820541973587787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186864983705880361315725191 280297475558820541973587787)
    ·
      refine ⟨420446213338230812960381681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280297475558820541973587787 420446213338230812960381681)
      ·
        refine ⟨315334660003673109720286261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 420446213338230812960381681 315334660003673109720286261)
        ·
          refine ⟨29562624375344354036276837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 315334660003673109720286261 29562624375344354036276837)
          ·
            refine ⟨5542992070377066381801907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29562624375344354036276837 5542992070377066381801907)
            ·
              refine ⟨8314488105565599572702861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5542992070377066381801907 8314488105565599572702861)
              ·
                refine ⟨3117933039587099839763573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8314488105565599572702861 3117933039587099839763573)
                ·
                  refine ⟨292306222461290609977835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3117933039587099839763573 292306222461290609977835)
                  ·
                    rfl

theorem cell23_5123379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 3, 5].length) (baseStart_5123379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5123379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5123379 prefixEnd_5123379 := by exact prefixLift 5123379
  have htrace : WordTrace (prefixWord ++ tailWord_5123379) baseStart_5123379 baseEnd_5123379 := by
    simpa [prefixWord, tailWord_5123379, baseEnd_5123379] using wordTrace_append hprefix tailTrace_5123379
  have hstable : (prefixWord ++ tailWord_5123379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5123379).length < 2 ^ (prefixWord ++ tailWord_5123379).sum := by decide
  have hdescent : baseEnd_5123379 < baseStart_5123379 := by decide
  rcases family_descends (prefixWord ++ tailWord_5123379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5123412 : List Nat := [2, 4, 1, 1, 2, 1, 1, 2, 4, 1, 4]
def baseStart_5123412 : Nat := 118140960795 + 5123412 * 2 ^ 59
def prefixEnd_5123412 : Nat := 4983230072969 + 3 ^ 40 * 5123412 * 2
def baseEnd_5123412 : Nat := 2630772947013213860687863

theorem tailTrace_5123412 : CollatzResearch.WordTrace tailWord_5123412 prefixEnd_5123412 2630772947013213860687863 := by
  unfold tailWord_5123412
  simp only [CollatzResearch.WordTrace]
  refine ⟨93433093657380403975838245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124577458209840538634450993 93433093657380403975838245)
  ·
    refine ⟨17518705060758825745469671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93433093657380403975838245 17518705060758825745469671)
    ·
      refine ⟨26278057591138238618204507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17518705060758825745469671 26278057591138238618204507)
      ·
        refine ⟨39417086386707357927306761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26278057591138238618204507 39417086386707357927306761)
        ·
          refine ⟨29562814790030518445480071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39417086386707357927306761 29562814790030518445480071)
          ·
            refine ⟨44344222185045777668220107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29562814790030518445480071 44344222185045777668220107)
            ·
              refine ⟨66516333277568666502330161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44344222185045777668220107 66516333277568666502330161)
              ·
                refine ⟨49887249958176499876747621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66516333277568666502330161 49887249958176499876747621)
                ·
                  refine ⟨9353859367158093726890179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49887249958176499876747621 9353859367158093726890179)
                  ·
                    refine ⟨14030789050737140590335269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9353859367158093726890179 14030789050737140590335269)
                    ·
                      refine ⟨2630772947013213860687863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14030789050737140590335269 2630772947013213860687863)
                      ·
                        rfl

theorem cell23_5123412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_5123412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5123412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5123412 prefixEnd_5123412 := by exact prefixLift 5123412
  have htrace : WordTrace (prefixWord ++ tailWord_5123412) baseStart_5123412 baseEnd_5123412 := by
    simpa [prefixWord, tailWord_5123412, baseEnd_5123412] using wordTrace_append hprefix tailTrace_5123412
  have hstable : (prefixWord ++ tailWord_5123412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5123412).length < 2 ^ (prefixWord ++ tailWord_5123412).sum := by decide
  have hdescent : baseEnd_5123412 < baseStart_5123412 := by decide
  rcases family_descends (prefixWord ++ tailWord_5123412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5123425 : List Nat := [1, 2, 3, 1, 1, 1, 1, 3, 2, 4, 4]
def baseStart_5123425 : Nat := 118140960795 + 5123425 * 2 ^ 59
def prefixEnd_5123425 : Nat := 4983230072969 + 3 ^ 40 * 5123425 * 2
def baseEnd_5123425 : Nat := 2630779622261722309825303

theorem tailTrace_5123425 : CollatzResearch.WordTrace tailWord_5123425 prefixEnd_5123425 2630779622261722309825303 := by
  unfold tailWord_5123425
  simp only [CollatzResearch.WordTrace]
  refine ⟨186866661463713711171899729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124577774309142474114599819 186866661463713711171899729)
  ·
    refine ⟨140149996097785283378924797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186866661463713711171899729 140149996097785283378924797)
    ·
      refine ⟨52556248536669481267096799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140149996097785283378924797 52556248536669481267096799)
      ·
        refine ⟨78834372805004221900645199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52556248536669481267096799 78834372805004221900645199)
        ·
          refine ⟨118251559207506332850967799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78834372805004221900645199 118251559207506332850967799)
          ·
            refine ⟨177377338811259499276451699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118251559207506332850967799 177377338811259499276451699)
            ·
              refine ⟨266066008216889248914677549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177377338811259499276451699 266066008216889248914677549)
              ·
                refine ⟨99774753081333468343004081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 266066008216889248914677549 99774753081333468343004081)
                ·
                  refine ⟨74831064811000101257253061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99774753081333468343004081 74831064811000101257253061)
                  ·
                    refine ⟨14030824652062518985734949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 74831064811000101257253061 14030824652062518985734949)
                    ·
                      refine ⟨2630779622261722309825303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14030824652062518985734949 2630779622261722309825303)
                      ·
                        rfl

theorem cell23_5123425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 4, 4].length) (baseStart_5123425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5123425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5123425 prefixEnd_5123425 := by exact prefixLift 5123425
  have htrace : WordTrace (prefixWord ++ tailWord_5123425) baseStart_5123425 baseEnd_5123425 := by
    simpa [prefixWord, tailWord_5123425, baseEnd_5123425] using wordTrace_append hprefix tailTrace_5123425
  have hstable : (prefixWord ++ tailWord_5123425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5123425).length < 2 ^ (prefixWord ++ tailWord_5123425).sum := by decide
  have hdescent : baseEnd_5123425 < baseStart_5123425 := by decide
  rcases family_descends (prefixWord ++ tailWord_5123425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5123439 : List Nat := [1, 1, 2, 1, 3, 1, 4, 5, 1, 4]
def baseStart_5123439 : Nat := 118140960795 + 5123439 * 2 ^ 59
def prefixEnd_5123439 : Nat := 4983230072969 + 3 ^ 40 * 5123439 * 2
def baseEnd_5123439 : Nat := 876928936996961751683413

theorem tailTrace_5123439 : CollatzResearch.WordTrace tailWord_5123439 prefixEnd_5123439 876928936996961751683413 := by
  unfold tailWord_5123439
  simp only [CollatzResearch.WordTrace]
  refine ⟨186867172085662991562909371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124578114723775327708606247 186867172085662991562909371)
  ·
    refine ⟨280300758128494487344364057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186867172085662991562909371 280300758128494487344364057)
    ·
      refine ⟨210225568596370865508273043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 280300758128494487344364057 210225568596370865508273043)
      ·
        refine ⟨315338352894556298262409565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210225568596370865508273043 315338352894556298262409565)
        ·
          refine ⟨118251882335458611848403587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 315338352894556298262409565 118251882335458611848403587)
          ·
            refine ⟨177377823503187917772605381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118251882335458611848403587 177377823503187917772605381)
            ·
              refine ⟨33258341906847734582363509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 177377823503187917772605381 33258341906847734582363509)
              ·
                refine ⟨3117969553766975117096579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33258341906847734582363509 3117969553766975117096579)
                ·
                  refine ⟨4676954330650462675644869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3117969553766975117096579 4676954330650462675644869)
                  ·
                    refine ⟨876928936996961751683413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4676954330650462675644869 876928936996961751683413)
                    ·
                      rfl

theorem cell23_5123439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 5, 1, 4].length) (baseStart_5123439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5123439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5123439 prefixEnd_5123439 := by exact prefixLift 5123439
  have htrace : WordTrace (prefixWord ++ tailWord_5123439) baseStart_5123439 baseEnd_5123439 := by
    simpa [prefixWord, tailWord_5123439, baseEnd_5123439] using wordTrace_append hprefix tailTrace_5123439
  have hstable : (prefixWord ++ tailWord_5123439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5123439).length < 2 ^ (prefixWord ++ tailWord_5123439).sum := by decide
  have hdescent : baseEnd_5123439 < baseStart_5123439 := by decide
  rcases family_descends (prefixWord ++ tailWord_5123439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5123452 : List Nat := [2, 2, 2, 1, 1, 1, 6, 2, 6]
def baseStart_5123452 : Nat := 118140960795 + 5123452 * 2 ^ 59
def prefixEnd_5123452 : Nat := 4983230072969 + 3 ^ 40 * 5123452 * 2
def baseEnd_5123452 : Nat := 292310387359932633798631

theorem tailTrace_5123452 : CollatzResearch.WordTrace tailWord_5123452 prefixEnd_5123452 292310387359932633798631 := by
  unfold tailWord_5123452
  simp only [CollatzResearch.WordTrace]
  refine ⟨93433823117307947391566305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124578430823077263188755073 93433823117307947391566305)
  ·
    refine ⟨70075367337980960543674729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93433823117307947391566305 70075367337980960543674729)
    ·
      refine ⟨52556525503485720407756047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70075367337980960543674729 52556525503485720407756047)
      ·
        refine ⟨78834788255228580611634071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52556525503485720407756047 78834788255228580611634071)
        ·
          refine ⟨118252182382842870917451107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78834788255228580611634071 118252182382842870917451107)
          ·
            refine ⟨177378273574264306376176661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118252182382842870917451107 177378273574264306376176661)
            ·
              refine ⟨8314606573793639361383281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 177378273574264306376176661 8314606573793639361383281)
              ·
                refine ⟨6235954930345229521037461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8314606573793639361383281 6235954930345229521037461)
                ·
                  refine ⟨292310387359932633798631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6235954930345229521037461 292310387359932633798631)
                  ·
                    rfl

theorem cell23_5123452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 2, 6].length) (baseStart_5123452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5123452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5123452 prefixEnd_5123452 := by exact prefixLift 5123452
  have htrace : WordTrace (prefixWord ++ tailWord_5123452) baseStart_5123452 baseEnd_5123452 := by
    simpa [prefixWord, tailWord_5123452, baseEnd_5123452] using wordTrace_append hprefix tailTrace_5123452
  have hstable : (prefixWord ++ tailWord_5123452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5123452).length < 2 ^ (prefixWord ++ tailWord_5123452).sum := by decide
  have hdescent : baseEnd_5123452 < baseStart_5123452 := by decide
  rcases family_descends (prefixWord ++ tailWord_5123452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5123482 : List Nat := [3, 1, 1, 4, 1, 1, 1, 3, 3, 5]
def baseStart_5123482 : Nat := 118140960795 + 5123482 * 2 ^ 59
def prefixEnd_5123482 : Nat := 4983230072969 + 3 ^ 40 * 5123482 * 2
def baseEnd_5123482 : Nat := 876936296886342862270847

theorem tailTrace_5123482 : CollatzResearch.WordTrace tailWord_5123482 prefixEnd_5123482 876936296886342862270847 := by
  unfold tailWord_5123482
  simp only [CollatzResearch.WordTrace]
  refine ⟨46717185106126802476681175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124579160283004806604483133 46717185106126802476681175)
  ·
    refine ⟨70075777659190203715021763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46717185106126802476681175 70075777659190203715021763)
    ·
      refine ⟨105113666488785305572532645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70075777659190203715021763 105113666488785305572532645)
      ·
        refine ⟨19708812466647244794849871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105113666488785305572532645 19708812466647244794849871)
        ·
          refine ⟨29563218699970867192274807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19708812466647244794849871 29563218699970867192274807)
          ·
            refine ⟨44344828049956300788412211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29563218699970867192274807 44344828049956300788412211)
            ·
              refine ⟨66517242074934451182618317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44344828049956300788412211 66517242074934451182618317)
              ·
                refine ⟨24943965778100419193481869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66517242074934451182618317 24943965778100419193481869)
                ·
                  refine ⟨9353987166787657197555701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24943965778100419193481869 9353987166787657197555701)
                  ·
                    refine ⟨876936296886342862270847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9353987166787657197555701 876936296886342862270847)
                    ·
                      rfl

theorem cell23_5123482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 3, 5].length) (baseStart_5123482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5123482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5123482 prefixEnd_5123482 := by exact prefixLift 5123482
  have htrace : WordTrace (prefixWord ++ tailWord_5123482) baseStart_5123482 baseEnd_5123482 := by
    simpa [prefixWord, tailWord_5123482, baseEnd_5123482] using wordTrace_append hprefix tailTrace_5123482
  have hstable : (prefixWord ++ tailWord_5123482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5123482).length < 2 ^ (prefixWord ++ tailWord_5123482).sum := by decide
  have hdescent : baseEnd_5123482 < baseStart_5123482 := by decide
  rcases family_descends (prefixWord ++ tailWord_5123482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5123570 : List Nat := [3, 2, 1, 4, 1, 3, 1, 1, 3, 2, 2]
def baseStart_5123570 : Nat := 118140960795 + 5123570 * 2 ^ 59
def prefixEnd_5123570 : Nat := 4983230072969 + 3 ^ 40 * 5123570 * 2
def baseEnd_5123570 : Nat := 2630854076956624242512137

theorem tailTrace_5123570 : CollatzResearch.WordTrace tailWord_5123570 prefixEnd_5123570 2630854076956624242512137 := by
  unfold tailWord_5123570
  simp only [CollatzResearch.WordTrace]
  refine ⟨46717987512047100233982041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124581300032125600623952109 46717987512047100233982041)
  ·
    refine ⟨35038490634035325175486531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46717987512047100233982041 35038490634035325175486531)
    ·
      refine ⟨52557735951052987763229797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35038490634035325175486531 52557735951052987763229797)
      ·
        refine ⟨9854575490822435205605587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52557735951052987763229797 9854575490822435205605587)
        ·
          refine ⟨14781863236233652808408381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9854575490822435205605587 14781863236233652808408381)
          ·
            refine ⟨5543198713587619803153143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14781863236233652808408381 5543198713587619803153143)
            ·
              refine ⟨8314798070381429704729715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5543198713587619803153143 8314798070381429704729715)
              ·
                refine ⟨12472197105572144557094573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8314798070381429704729715 12472197105572144557094573)
                ·
                  refine ⟨4677073914589554208910465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12472197105572144557094573 4677073914589554208910465)
                  ·
                    refine ⟨3507805435942165656682849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4677073914589554208910465 3507805435942165656682849)
                    ·
                      refine ⟨2630854076956624242512137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3507805435942165656682849 2630854076956624242512137)
                      ·
                        rfl

theorem cell23_5123570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_5123570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5123570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5123570 prefixEnd_5123570 := by exact prefixLift 5123570
  have htrace : WordTrace (prefixWord ++ tailWord_5123570) baseStart_5123570 baseEnd_5123570 := by
    simpa [prefixWord, tailWord_5123570, baseEnd_5123570] using wordTrace_append hprefix tailTrace_5123570
  have hstable : (prefixWord ++ tailWord_5123570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5123570).length < 2 ^ (prefixWord ++ tailWord_5123570).sum := by decide
  have hdescent : baseEnd_5123570 < baseStart_5123570 := by decide
  rcases family_descends (prefixWord ++ tailWord_5123570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5123579 : List Nat := [1, 1, 1, 1, 1, 3, 2, 3, 5, 3, 2]
def baseStart_5123579 : Nat := 118140960795 + 5123579 * 2 ^ 59
def prefixEnd_5123579 : Nat := 4983230072969 + 3 ^ 40 * 5123579 * 2
def baseEnd_5123579 : Nat := 2630858698282514707299595

theorem tailTrace_5123579 : CollatzResearch.WordTrace tailWord_5123579 prefixEnd_5123579 2630858698282514707299595 := by
  unfold tailWord_5123579
  simp only [CollatzResearch.WordTrace]
  refine ⟨186872278305155795473005791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124581518870103863648670527 186872278305155795473005791)
  ·
    refine ⟨280308417457733693209508687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186872278305155795473005791 280308417457733693209508687)
    ·
      refine ⟨420462626186600539814263031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280308417457733693209508687 420462626186600539814263031)
      ·
        refine ⟨630693939279900809721394547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 420462626186600539814263031 630693939279900809721394547)
        ·
          refine ⟨946040908919851214582091821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 630693939279900809721394547 946040908919851214582091821)
          ·
            refine ⟨354765340844944205468284433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 946040908919851214582091821 354765340844944205468284433)
            ·
              refine ⟨266074005633708154101213325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 354765340844944205468284433 266074005633708154101213325)
              ·
                refine ⟨99777752112640557787954997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 266074005633708154101213325 99777752112640557787954997)
                ·
                  refine ⟨9354164260560052292620781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 99777752112640557787954997 9354164260560052292620781)
                  ·
                    refine ⟨3507811597710019609732793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9354164260560052292620781 3507811597710019609732793)
                    ·
                      refine ⟨2630858698282514707299595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3507811597710019609732793 2630858698282514707299595)
                      ·
                        rfl

theorem cell23_5123579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 5, 3, 2].length) (baseStart_5123579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5123579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5123579 prefixEnd_5123579 := by exact prefixLift 5123579
  have htrace : WordTrace (prefixWord ++ tailWord_5123579) baseStart_5123579 baseEnd_5123579 := by
    simpa [prefixWord, tailWord_5123579, baseEnd_5123579] using wordTrace_append hprefix tailTrace_5123579
  have hstable : (prefixWord ++ tailWord_5123579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5123579).length < 2 ^ (prefixWord ++ tailWord_5123579).sum := by decide
  have hdescent : baseEnd_5123579 < baseStart_5123579 := by decide
  rcases family_descends (prefixWord ++ tailWord_5123579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5123626 : List Nat := [3, 1, 4, 1, 1, 1, 1, 2, 3, 4, 2]
def baseStart_5123626 : Nat := 118140960795 + 5123626 * 2 ^ 59
def prefixEnd_5123626 : Nat := 4983230072969 + 3 ^ 40 * 5123626 * 2
def baseEnd_5123626 : Nat := 2630882831873276023411879

theorem tailTrace_5123626 : CollatzResearch.WordTrace tailWord_5123626 prefixEnd_5123626 2630882831873276023411879 := by
  unfold tailWord_5123626
  simp only [CollatzResearch.WordTrace]
  refine ⟨46718498133996380624991683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124582661690657014999977821 46718498133996380624991683)
  ·
    refine ⟨70077747200994570937487525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46718498133996380624991683 70077747200994570937487525)
    ·
      refine ⟨13139577600186482050778911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70077747200994570937487525 13139577600186482050778911)
      ·
        refine ⟨19709366400279723076168367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13139577600186482050778911 19709366400279723076168367)
        ·
          refine ⟨29564049600419584614252551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19709366400279723076168367 29564049600419584614252551)
          ·
            refine ⟨44346074400629376921378827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29564049600419584614252551 44346074400629376921378827)
            ·
              refine ⟨66519111600944065382068241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44346074400629376921378827 66519111600944065382068241)
              ·
                refine ⟨49889333700708049036551181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66519111600944065382068241 49889333700708049036551181)
                ·
                  refine ⟨18708500137765518388706693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49889333700708049036551181 18708500137765518388706693)
                  ·
                    refine ⟨3507843775831034697882505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18708500137765518388706693 3507843775831034697882505)
                    ·
                      refine ⟨2630882831873276023411879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3507843775831034697882505 2630882831873276023411879)
                      ·
                        rfl

theorem cell23_5123626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 3, 4, 2].length) (baseStart_5123626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5123626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5123626 prefixEnd_5123626 := by exact prefixLift 5123626
  have htrace : WordTrace (prefixWord ++ tailWord_5123626) baseStart_5123626 baseEnd_5123626 := by
    simpa [prefixWord, tailWord_5123626, baseEnd_5123626] using wordTrace_append hprefix tailTrace_5123626
  have hstable : (prefixWord ++ tailWord_5123626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5123626).length < 2 ^ (prefixWord ++ tailWord_5123626).sum := by decide
  have hdescent : baseEnd_5123626 < baseStart_5123626 := by decide
  rcases family_descends (prefixWord ++ tailWord_5123626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5123632 : List Nat := [2, 1, 1, 1, 2, 3, 1, 5, 7]
def baseStart_5123632 : Nat := 118140960795 + 5123632 * 2 ^ 59
def prefixEnd_5123632 : Nat := 4983230072969 + 3 ^ 40 * 5123632 * 2
def baseEnd_5123632 : Nat := 292320656973022555548539

theorem tailTrace_5123632 : CollatzResearch.WordTrace tailWord_5123632 prefixEnd_5123632 292320656973022555548539 := by
  unfold tailWord_5123632
  simp only [CollatzResearch.WordTrace]
  refine ⟨93437105686981892762342575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124582807582642523683123433 93437105686981892762342575)
  ·
    refine ⟨140155658530472839143513863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93437105686981892762342575 140155658530472839143513863)
    ·
      refine ⟨210233487795709258715270795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140155658530472839143513863 210233487795709258715270795)
      ·
        refine ⟨315350231693563888072906193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210233487795709258715270795 315350231693563888072906193)
        ·
          refine ⟨236512673770172916054679645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 315350231693563888072906193 236512673770172916054679645)
          ·
            refine ⟨88692252663814843520504867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 236512673770172916054679645 88692252663814843520504867)
            ·
              refine ⟨133038378995722265280757301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88692252663814843520504867 133038378995722265280757301)
              ·
                refine ⟨12472348030848962370070997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 133038378995722265280757301 12472348030848962370070997)
                ·
                  refine ⟨292320656973022555548539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12472348030848962370070997 292320656973022555548539)
                  ·
                    rfl

theorem cell23_5123632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 5, 7].length) (baseStart_5123632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5123632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5123632 prefixEnd_5123632 := by exact prefixLift 5123632
  have htrace : WordTrace (prefixWord ++ tailWord_5123632) baseStart_5123632 baseEnd_5123632 := by
    simpa [prefixWord, tailWord_5123632, baseEnd_5123632] using wordTrace_append hprefix tailTrace_5123632
  have hstable : (prefixWord ++ tailWord_5123632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5123632).length < 2 ^ (prefixWord ++ tailWord_5123632).sum := by decide
  have hdescent : baseEnd_5123632 < baseStart_5123632 := by decide
  rcases family_descends (prefixWord ++ tailWord_5123632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5123639 : List Nat := [1, 1, 3, 1, 2, 5, 1, 1, 2, 2, 4]
def baseStart_5123639 : Nat := 118140960795 + 5123639 * 2 ^ 59
def prefixEnd_5123639 : Nat := 4983230072969 + 3 ^ 40 * 5123639 * 2
def baseEnd_5123639 : Nat := 2630889507121784472549319

theorem tailTrace_5123639 : CollatzResearch.WordTrace tailWord_5123639 prefixEnd_5123639 2630889507121784472549319 := by
  unfold tailWord_5123639
  simp only [CollatzResearch.WordTrace]
  refine ⟨186874466684938425720189971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124582977789958950480126647 186874466684938425720189971)
  ·
    refine ⟨280311700027407638580284957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186874466684938425720189971 280311700027407638580284957)
    ·
      refine ⟨105116887510277864467606859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 280311700027407638580284957 105116887510277864467606859)
      ·
        refine ⟨157675331265416796701410289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105116887510277864467606859 157675331265416796701410289)
        ·
          refine ⟨118256498449062597526057717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157675331265416796701410289 118256498449062597526057717)
          ·
            refine ⟨11086546729599618518067911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 118256498449062597526057717 11086546729599618518067911)
            ·
              refine ⟨16629820094399427777101867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11086546729599618518067911 16629820094399427777101867)
              ·
                refine ⟨24944730141599141665652801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16629820094399427777101867 24944730141599141665652801)
                ·
                  refine ⟨18708547606199356249239601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24944730141599141665652801 18708547606199356249239601)
                  ·
                    refine ⟨14031410704649517186929701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18708547606199356249239601 14031410704649517186929701)
                    ·
                      refine ⟨2630889507121784472549319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14031410704649517186929701 2630889507121784472549319)
                      ·
                        rfl

theorem cell23_5123639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 2, 2, 4].length) (baseStart_5123639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5123639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5123639 prefixEnd_5123639 := by exact prefixLift 5123639
  have htrace : WordTrace (prefixWord ++ tailWord_5123639) baseStart_5123639 baseEnd_5123639 := by
    simpa [prefixWord, tailWord_5123639, baseEnd_5123639] using wordTrace_append hprefix tailTrace_5123639
  have hstable : (prefixWord ++ tailWord_5123639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5123639).length < 2 ^ (prefixWord ++ tailWord_5123639).sum := by decide
  have hdescent : baseEnd_5123639 < baseStart_5123639 := by decide
  rcases family_descends (prefixWord ++ tailWord_5123639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5123649 : List Nat := [1, 2, 5, 1, 1, 1, 3, 2, 7]
def baseStart_5123649 : Nat := 118140960795 + 5123649 * 2 ^ 59
def prefixEnd_5123649 : Nat := 4983230072969 + 3 ^ 40 * 5123649 * 2
def baseEnd_5123649 : Nat := 292321626880925492602697

theorem tailTrace_5123649 : CollatzResearch.WordTrace tailWord_5123649 prefixEnd_5123649 292321626880925492602697 := by
  unfold tailWord_5123649
  simp only [CollatzResearch.WordTrace]
  refine ⟨186874831414902197428054001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124583220943268131618702667 186874831414902197428054001)
  ·
    refine ⟨140156123561176648071040501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186874831414902197428054001 140156123561176648071040501)
    ·
      refine ⟨13139636583860310756660047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 140156123561176648071040501 13139636583860310756660047)
      ·
        refine ⟨19709454875790466134990071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13139636583860310756660047 19709454875790466134990071)
        ·
          refine ⟨29564182313685699202485107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19709454875790466134990071 29564182313685699202485107)
          ·
            refine ⟨44346273470528548803727661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29564182313685699202485107 44346273470528548803727661)
            ·
              refine ⟨16629852551448205801397873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44346273470528548803727661 16629852551448205801397873)
              ·
                refine ⟨12472389413586154351048405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16629852551448205801397873 12472389413586154351048405)
                ·
                  refine ⟨292321626880925492602697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12472389413586154351048405 292321626880925492602697)
                  ·
                    rfl

theorem cell23_5123649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 2, 7].length) (baseStart_5123649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5123649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5123649 prefixEnd_5123649 := by exact prefixLift 5123649
  have htrace : WordTrace (prefixWord ++ tailWord_5123649) baseStart_5123649 baseEnd_5123649 := by
    simpa [prefixWord, tailWord_5123649, baseEnd_5123649] using wordTrace_append hprefix tailTrace_5123649
  have hstable : (prefixWord ++ tailWord_5123649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5123649).length < 2 ^ (prefixWord ++ tailWord_5123649).sum := by decide
  have hdescent : baseEnd_5123649 < baseStart_5123649 := by decide
  rcases family_descends (prefixWord ++ tailWord_5123649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5123666 : List Nat := [3, 2, 2, 1, 2, 2, 1, 5, 5]
def baseStart_5123666 : Nat := 118140960795 + 5123666 * 2 ^ 59
def prefixEnd_5123666 : Nat := 4983230072969 + 3 ^ 40 * 5123666 * 2
def baseEnd_5123666 : Nat := 292322596788828429656855

theorem tailTrace_5123666 : CollatzResearch.WordTrace tailWord_5123666 prefixEnd_5123666 292322596788828429656855 := by
  unfold tailWord_5123666
  simp only [CollatzResearch.WordTrace]
  refine ⟨46718862863960152332855713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124583634303893739554281901 46718862863960152332855713)
  ·
    refine ⟨35039147147970114249641785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46718862863960152332855713 35039147147970114249641785)
    ·
      refine ⟨26279360360977585687231339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35039147147970114249641785 26279360360977585687231339)
      ·
        refine ⟨39419040541466378530847009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26279360360977585687231339 39419040541466378530847009)
        ·
          refine ⟨29564280406099783898135257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39419040541466378530847009 29564280406099783898135257)
          ·
            refine ⟨22173210304574837923601443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29564280406099783898135257 22173210304574837923601443)
            ·
              refine ⟨33259815456862256885402165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22173210304574837923601443 33259815456862256885402165)
              ·
                refine ⟨3118107699080836583006453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33259815456862256885402165 3118107699080836583006453)
                ·
                  refine ⟨292322596788828429656855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3118107699080836583006453 292322596788828429656855)
                  ·
                    rfl

theorem cell23_5123666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 5, 5].length) (baseStart_5123666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5123666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5123666 prefixEnd_5123666 := by exact prefixLift 5123666
  have htrace : WordTrace (prefixWord ++ tailWord_5123666) baseStart_5123666 baseEnd_5123666 := by
    simpa [prefixWord, tailWord_5123666, baseEnd_5123666] using wordTrace_append hprefix tailTrace_5123666
  have hstable : (prefixWord ++ tailWord_5123666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5123666).length < 2 ^ (prefixWord ++ tailWord_5123666).sum := by decide
  have hdescent : baseEnd_5123666 < baseStart_5123666 := by decide
  rcases family_descends (prefixWord ++ tailWord_5123666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5123676 : List Nat := [2, 2, 4, 1, 2, 1, 1, 2, 2, 3, 3]
def baseStart_5123676 : Nat := 118140960795 + 5123676 * 2 ^ 59
def prefixEnd_5123676 : Nat := 4983230072969 + 3 ^ 40 * 5123676 * 2
def baseEnd_5123676 : Nat := 2630908505906000827786649

theorem tailTrace_5123676 : CollatzResearch.WordTrace tailWord_5123676 prefixEnd_5123676 2630908505906000827786649 := by
  unfold tailWord_5123676
  simp only [CollatzResearch.WordTrace]
  refine ⟨93437908092902190519643441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124583877457202920692857921 93437908092902190519643441)
  ·
    refine ⟨70078431069676642889732581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93437908092902190519643441 70078431069676642889732581)
    ·
      refine ⟨13139705825564370541824859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70078431069676642889732581 13139705825564370541824859)
      ·
        refine ⟨19709558738346555812737289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13139705825564370541824859 19709558738346555812737289)
        ·
          refine ⟨14782169053759916859552967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19709558738346555812737289 14782169053759916859552967)
          ·
            refine ⟨22173253580639875289329451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14782169053759916859552967 22173253580639875289329451)
            ·
              refine ⟨33259880370959812933994177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22173253580639875289329451 33259880370959812933994177)
              ·
                refine ⟨24944910278219859700495633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33259880370959812933994177 24944910278219859700495633)
                ·
                  refine ⟨18708682708664894775371725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24944910278219859700495633 18708682708664894775371725)
                  ·
                    refine ⟨7015756015749335540764397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18708682708664894775371725 7015756015749335540764397)
                    ·
                      refine ⟨2630908505906000827786649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7015756015749335540764397 2630908505906000827786649)
                      ·
                        rfl

theorem cell23_5123676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_5123676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5123676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5123676 prefixEnd_5123676 := by exact prefixLift 5123676
  have htrace : WordTrace (prefixWord ++ tailWord_5123676) baseStart_5123676 baseEnd_5123676 := by
    simpa [prefixWord, tailWord_5123676, baseEnd_5123676] using wordTrace_append hprefix tailTrace_5123676
  have hstable : (prefixWord ++ tailWord_5123676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5123676).length < 2 ^ (prefixWord ++ tailWord_5123676).sum := by decide
  have hdescent : baseEnd_5123676 < baseStart_5123676 := by decide
  rcases family_descends (prefixWord ++ tailWord_5123676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5123677 : List Nat := [1, 4, 4, 2, 1, 1, 1, 1, 4, 2, 2]
def baseStart_5123677 : Nat := 118140960795 + 5123677 * 2 ^ 59
def prefixEnd_5123677 : Nat := 4983230072969 + 3 ^ 40 * 5123677 * 2
def baseEnd_5123677 : Nat := 2630909019386655323874145

theorem tailTrace_5123677 : CollatzResearch.WordTrace tailWord_5123677 prefixEnd_5123677 2630909019386655323874145 := by
  unfold tailWord_5123677
  simp only [CollatzResearch.WordTrace]
  refine ⟨186875852658800758210073285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124583901772533838806715523 186875852658800758210073285)
  ·
    refine ⟨35039222373525142164388741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 186875852658800758210073285 35039222373525142164388741)
    ·
      refine ⟨6569854195035964155822889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35039222373525142164388741 6569854195035964155822889)
      ·
        refine ⟨4927390646276973116867167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6569854195035964155822889 4927390646276973116867167)
        ·
          refine ⟨7391085969415459675300751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4927390646276973116867167 7391085969415459675300751)
          ·
            refine ⟨11086628954123189512951127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7391085969415459675300751 11086628954123189512951127)
            ·
              refine ⟨16629943431184784269426691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11086628954123189512951127 16629943431184784269426691)
              ·
                refine ⟨24944915146777176404140037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16629943431184784269426691 24944915146777176404140037)
                ·
                  refine ⟨4677171590020720575776257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24944915146777176404140037 4677171590020720575776257)
                  ·
                    refine ⟨3507878692515540431832193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4677171590020720575776257 3507878692515540431832193)
                    ·
                      refine ⟨2630909019386655323874145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3507878692515540431832193 2630909019386655323874145)
                      ·
                        rfl

theorem cell23_5123677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_5123677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5123677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5123677 prefixEnd_5123677 := by exact prefixLift 5123677
  have htrace : WordTrace (prefixWord ++ tailWord_5123677) baseStart_5123677 baseEnd_5123677 := by
    simpa [prefixWord, tailWord_5123677, baseEnd_5123677] using wordTrace_append hprefix tailTrace_5123677
  have hstable : (prefixWord ++ tailWord_5123677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5123677).length < 2 ^ (prefixWord ++ tailWord_5123677).sum := by decide
  have hdescent : baseEnd_5123677 < baseStart_5123677 := by decide
  rcases family_descends (prefixWord ++ tailWord_5123677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5123736 : List Nat := [2, 1, 2, 4, 1, 2, 1, 1, 4, 2, 3]
def baseStart_5123736 : Nat := 118140960795 + 5123736 * 2 ^ 59
def prefixEnd_5123736 : Nat := 4983230072969 + 3 ^ 40 * 5123736 * 2
def baseEnd_5123736 : Nat := 2630939314745270593036373

theorem tailTrace_5123736 : CollatzResearch.WordTrace tailWord_5123736 prefixEnd_5123736 2630939314745270593036373 := by
  unfold tailWord_5123736
  simp only [CollatzResearch.WordTrace]
  refine ⟨93439002282793505643235531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124585336377058007524314041 93439002282793505643235531)
  ·
    refine ⟨140158503424190258464853297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93439002282793505643235531 140158503424190258464853297)
    ·
      refine ⟨105118877568142693848639973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140158503424190258464853297 105118877568142693848639973)
      ·
        refine ⟨19709789544026755096619995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105118877568142693848639973 19709789544026755096619995)
        ·
          refine ⟨29564684316040132644929993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19709789544026755096619995 29564684316040132644929993)
          ·
            refine ⟨22173513237030099483697495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29564684316040132644929993 22173513237030099483697495)
            ·
              refine ⟨33260269855545149225546243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22173513237030099483697495 33260269855545149225546243)
              ·
                refine ⟨49890404783317723838319365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33260269855545149225546243 49890404783317723838319365)
                ·
                  refine ⟨9354450896872073219684881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49890404783317723838319365 9354450896872073219684881)
                  ·
                    refine ⟨7015838172654054914763661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9354450896872073219684881 7015838172654054914763661)
                    ·
                      refine ⟨2630939314745270593036373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7015838172654054914763661 2630939314745270593036373)
                      ·
                        rfl

theorem cell23_5123736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_5123736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5123736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5123736 prefixEnd_5123736 := by exact prefixLift 5123736
  have htrace : WordTrace (prefixWord ++ tailWord_5123736) baseStart_5123736 baseEnd_5123736 := by
    simpa [prefixWord, tailWord_5123736, baseEnd_5123736] using wordTrace_append hprefix tailTrace_5123736
  have hstable : (prefixWord ++ tailWord_5123736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5123736).length < 2 ^ (prefixWord ++ tailWord_5123736).sum := by decide
  have hdescent : baseEnd_5123736 < baseStart_5123736 := by decide
  rcases family_descends (prefixWord ++ tailWord_5123736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5123793 : List Nat := [1, 2, 2, 1, 2, 4, 2, 2, 2, 3, 2]
def baseStart_5123793 : Nat := 118140960795 + 5123793 * 2 ^ 59
def prefixEnd_5123793 : Nat := 4983230072969 + 3 ^ 40 * 5123793 * 2
def baseEnd_5123793 : Nat := 2630968583142576870023611

theorem tailTrace_5123793 : CollatzResearch.WordTrace tailWord_5123793 prefixEnd_5123793 2630968583142576870023611 := by
  unfold tailWord_5123793
  simp only [CollatzResearch.WordTrace]
  refine ⟨186880083526380510021296033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124586722350920340014197355 186880083526380510021296033)
  ·
    refine ⟨140160062644785382515972025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186880083526380510021296033 140160062644785382515972025)
    ·
      refine ⟨105120046983589036886979019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140160062644785382515972025 105120046983589036886979019)
      ·
        refine ⟨157680070475383555330468529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105120046983589036886979019 157680070475383555330468529)
        ·
          refine ⟨118260052856537666497851397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157680070475383555330468529 118260052856537666497851397)
          ·
            refine ⟨22173759910600812468347137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 118260052856537666497851397 22173759910600812468347137)
            ·
              refine ⟨16630319932950609351260353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22173759910600812468347137 16630319932950609351260353)
              ·
                refine ⟨12472739949712957013445265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16630319932950609351260353 12472739949712957013445265)
                ·
                  refine ⟨9354554962284717760083949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12472739949712957013445265 9354554962284717760083949)
                  ·
                    refine ⟨3507958110856769160031481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9354554962284717760083949 3507958110856769160031481)
                    ·
                      refine ⟨2630968583142576870023611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3507958110856769160031481 2630968583142576870023611)
                      ·
                        rfl

theorem cell23_5123793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 2, 2, 3, 2].length) (baseStart_5123793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5123793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5123793 prefixEnd_5123793 := by exact prefixLift 5123793
  have htrace : WordTrace (prefixWord ++ tailWord_5123793) baseStart_5123793 baseEnd_5123793 := by
    simpa [prefixWord, tailWord_5123793, baseEnd_5123793] using wordTrace_append hprefix tailTrace_5123793
  have hstable : (prefixWord ++ tailWord_5123793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5123793).length < 2 ^ (prefixWord ++ tailWord_5123793).sum := by decide
  have hdescent : baseEnd_5123793 < baseStart_5123793 := by decide
  rcases family_descends (prefixWord ++ tailWord_5123793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5123799 : List Nat := [1, 1, 3, 2, 1, 3, 1, 2, 3, 6]
def baseStart_5123799 : Nat := 118140960795 + 5123799 * 2 ^ 59
def prefixEnd_5123799 : Nat := 4983230072969 + 3 ^ 40 * 5123799 * 2
def baseEnd_5123799 : Nat := 876990554675501282182861

theorem tailTrace_5123799 : CollatzResearch.WordTrace tailWord_5123799 prefixEnd_5123799 876990554675501282182861 := by
  unfold tailWord_5123799
  simp only [CollatzResearch.WordTrace]
  refine ⟨186880302364358773046014451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124586868242905848697342967 186880302364358773046014451)
  ·
    refine ⟨280320453546538159569021677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186880302364358773046014451 280320453546538159569021677)
    ·
      refine ⟨105120170079951809838383129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 280320453546538159569021677 105120170079951809838383129)
      ·
        refine ⟨78840127559963857378787347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105120170079951809838383129 78840127559963857378787347)
        ·
          refine ⟨118260191339945786068181021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78840127559963857378787347 118260191339945786068181021)
          ·
            refine ⟨44347571752479669775567883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118260191339945786068181021 44347571752479669775567883)
            ·
              refine ⟨66521357628719504663351825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44347571752479669775567883 66521357628719504663351825)
              ·
                refine ⟨49891018221539628497513869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66521357628719504663351825 49891018221539628497513869)
                ·
                  refine ⟨18709131833077360686567701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49891018221539628497513869 18709131833077360686567701)
                  ·
                    refine ⟨876990554675501282182861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18709131833077360686567701 876990554675501282182861)
                    ·
                      rfl

theorem cell23_5123799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 3, 6].length) (baseStart_5123799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5123799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5123799 prefixEnd_5123799 := by exact prefixLift 5123799
  have htrace : WordTrace (prefixWord ++ tailWord_5123799) baseStart_5123799 baseEnd_5123799 := by
    simpa [prefixWord, tailWord_5123799, baseEnd_5123799] using wordTrace_append hprefix tailTrace_5123799
  have hstable : (prefixWord ++ tailWord_5123799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5123799).length < 2 ^ (prefixWord ++ tailWord_5123799).sum := by decide
  have hdescent : baseEnd_5123799 < baseStart_5123799 := by decide
  rcases family_descends (prefixWord ++ tailWord_5123799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5123800 : List Nat := [2, 1, 2, 2, 3, 1, 3, 4, 1, 1, 3]
def baseStart_5123800 : Nat := 118140960795 + 5123800 * 2 ^ 59
def prefixEnd_5123800 : Nat := 4983230072969 + 3 ^ 40 * 5123800 * 2
def baseEnd_5123800 : Nat := 2630972177507158342636079

theorem tailTrace_5123800 : CollatzResearch.WordTrace tailWord_5123800 prefixEnd_5123800 2630972177507158342636079 := by
  unfold tailWord_5123800
  simp only [CollatzResearch.WordTrace]
  refine ⟨93440169418677575108400427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124586892558236766811200569 93440169418677575108400427)
  ·
    refine ⟨140160254128016362662600641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93440169418677575108400427 140160254128016362662600641)
    ·
      refine ⟨105120190596012271996950481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140160254128016362662600641 105120190596012271996950481)
      ·
        refine ⟨78840142947009203997712861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105120190596012271996950481 78840142947009203997712861)
        ·
          refine ⟨29565053605128451499142323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78840142947009203997712861 29565053605128451499142323)
          ·
            refine ⟨44347580407692677248713485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29565053605128451499142323 44347580407692677248713485)
            ·
              refine ⟨16630342652884753968267557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44347580407692677248713485 16630342652884753968267557)
              ·
                refine ⟨3118189247415891369050167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16630342652884753968267557 3118189247415891369050167)
                ·
                  refine ⟨4677283871123837053575251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3118189247415891369050167 4677283871123837053575251)
                  ·
                    refine ⟨7015925806685755580362877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4677283871123837053575251 7015925806685755580362877)
                    ·
                      refine ⟨2630972177507158342636079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7015925806685755580362877 2630972177507158342636079)
                      ·
                        rfl

theorem cell23_5123800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 4, 1, 1, 3].length) (baseStart_5123800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5123800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5123800 prefixEnd_5123800 := by exact prefixLift 5123800
  have htrace : WordTrace (prefixWord ++ tailWord_5123800) baseStart_5123800 baseEnd_5123800 := by
    simpa [prefixWord, tailWord_5123800, baseEnd_5123800] using wordTrace_append hprefix tailTrace_5123800
  have hstable : (prefixWord ++ tailWord_5123800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5123800).length < 2 ^ (prefixWord ++ tailWord_5123800).sum := by decide
  have hdescent : baseEnd_5123800 < baseStart_5123800 := by decide
  rcases family_descends (prefixWord ++ tailWord_5123800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5123816 : List Nat := [2, 1, 4, 1, 3, 1, 1, 3, 1, 6]
def baseStart_5123816 : Nat := 118140960795 + 5123816 * 2 ^ 59
def prefixEnd_5123816 : Nat := 4983230072969 + 3 ^ 40 * 5123816 * 2
def baseEnd_5123816 : Nat := 876993464399210093345335

theorem tailTrace_5123816 : CollatzResearch.WordTrace tailWord_5123816 prefixEnd_5123816 876993464399210093345335 := by
  unfold tailWord_5123816
  simp only [CollatzResearch.WordTrace]
  refine ⟨93440461202648592474691651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124587281603531456632922201 93440461202648592474691651)
  ·
    refine ⟨140160691803972888712037477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93440461202648592474691651 140160691803972888712037477)
    ·
      refine ⟨26280129713244916633507027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 140160691803972888712037477 26280129713244916633507027)
      ·
        refine ⟨39420194569867374950260541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26280129713244916633507027 39420194569867374950260541)
        ·
          refine ⟨14782572963700265606347703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39420194569867374950260541 14782572963700265606347703)
          ·
            refine ⟨22173859445550398409521555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14782572963700265606347703 22173859445550398409521555)
            ·
              refine ⟨33260789168325597614282333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22173859445550398409521555 33260789168325597614282333)
              ·
                refine ⟨12472795938122099105355875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33260789168325597614282333 12472795938122099105355875)
                ·
                  refine ⟨18709193907183148658033813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12472795938122099105355875 18709193907183148658033813)
                  ·
                    refine ⟨876993464399210093345335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18709193907183148658033813 876993464399210093345335)
                    ·
                      rfl

theorem cell23_5123816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 3, 1, 6].length) (baseStart_5123816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5123816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5123816 prefixEnd_5123816 := by exact prefixLift 5123816
  have htrace : WordTrace (prefixWord ++ tailWord_5123816) baseStart_5123816 baseEnd_5123816 := by
    simpa [prefixWord, tailWord_5123816, baseEnd_5123816] using wordTrace_append hprefix tailTrace_5123816
  have hstable : (prefixWord ++ tailWord_5123816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5123816).length < 2 ^ (prefixWord ++ tailWord_5123816).sum := by decide
  have hdescent : baseEnd_5123816 < baseStart_5123816 := by decide
  rcases family_descends (prefixWord ++ tailWord_5123816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5123819 : List Nat := [1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 6]
def baseStart_5123819 : Nat := 118140960795 + 5123819 * 2 ^ 59
def prefixEnd_5123819 : Nat := 4983230072969 + 3 ^ 40 * 5123819 * 2
def baseEnd_5123819 : Nat := 2630981933639593768298491

theorem tailTrace_5123819 : CollatzResearch.WordTrace tailWord_5123819 prefixEnd_5123819 2630981933639593768298491 := by
  unfold tailWord_5123819
  simp only [CollatzResearch.WordTrace]
  refine ⟨186881031824286316461742511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124587354549524210974495007 186881031824286316461742511)
  ·
    refine ⟨280321547736429474692613767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186881031824286316461742511 280321547736429474692613767)
    ·
      refine ⟨420482321604644212038920651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280321547736429474692613767 420482321604644212038920651)
      ·
        refine ⟨630723482406966318058380977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 420482321604644212038920651 630723482406966318058380977)
        ·
          refine ⟨473042611805224738543785733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 630723482406966318058380977 473042611805224738543785733)
          ·
            refine ⟨88695489713479638476959825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 473042611805224738543785733 88695489713479638476959825)
            ·
              refine ⟨66521617285109728857719869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88695489713479638476959825 66521617285109728857719869)
              ·
                refine ⟨24945606481916148321644951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66521617285109728857719869 24945606481916148321644951)
                ·
                  refine ⟨37418409722874222482467427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24945606481916148321644951 37418409722874222482467427)
                  ·
                    refine ⟨56127614584311333723701141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37418409722874222482467427 56127614584311333723701141)
                    ·
                      refine ⟨2630981933639593768298491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56127614584311333723701141 2630981933639593768298491)
                      ·
                        rfl

theorem cell23_5123819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 6].length) (baseStart_5123819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5123819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5123819 prefixEnd_5123819 := by exact prefixLift 5123819
  have htrace : WordTrace (prefixWord ++ tailWord_5123819) baseStart_5123819 baseEnd_5123819 := by
    simpa [prefixWord, tailWord_5123819, baseEnd_5123819] using wordTrace_append hprefix tailTrace_5123819
  have hstable : (prefixWord ++ tailWord_5123819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5123819).length < 2 ^ (prefixWord ++ tailWord_5123819).sum := by decide
  have hdescent : baseEnd_5123819 < baseStart_5123819 := by decide
  rcases family_descends (prefixWord ++ tailWord_5123819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5123836 : List Nat := [2, 2, 2, 1, 3, 1, 1, 4, 1, 2, 4]
def baseStart_5123836 : Nat := 118140960795 + 5123836 * 2 ^ 59
def prefixEnd_5123836 : Nat := 4983230072969 + 3 ^ 40 * 5123836 * 2
def baseEnd_5123836 : Nat := 2630990662810720201785913

theorem tailTrace_5123836 : CollatzResearch.WordTrace tailWord_5123836 prefixEnd_5123836 2630990662810720201785913 := by
  unfold tailWord_5123836
  simp only [CollatzResearch.WordTrace]
  refine ⟨93440825932612364182555681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124587767910149818910074241 93440825932612364182555681)
  ·
    refine ⟨70080619449459273136916761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93440825932612364182555681 70080619449459273136916761)
    ·
      refine ⟨52560464587094454852687571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70080619449459273136916761 52560464587094454852687571)
      ·
        refine ⟨78840696880641682279031357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52560464587094454852687571 78840696880641682279031357)
        ·
          refine ⟨29565261330240630854636759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78840696880641682279031357 29565261330240630854636759)
          ·
            refine ⟨44347891995360946281955139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29565261330240630854636759 44347891995360946281955139)
            ·
              refine ⟨66521837993041419422932709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44347891995360946281955139 66521837993041419422932709)
              ·
                refine ⟨12472844623695266141799883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66521837993041419422932709 12472844623695266141799883)
                ·
                  refine ⟨18709266935542899212699825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12472844623695266141799883 18709266935542899212699825)
                  ·
                    refine ⟨14031950201657174409524869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18709266935542899212699825 14031950201657174409524869)
                    ·
                      refine ⟨2630990662810720201785913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14031950201657174409524869 2630990662810720201785913)
                      ·
                        rfl

theorem cell23_5123836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 4, 1, 2, 4].length) (baseStart_5123836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5123836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5123836 prefixEnd_5123836 := by exact prefixLift 5123836
  have htrace : WordTrace (prefixWord ++ tailWord_5123836) baseStart_5123836 baseEnd_5123836 := by
    simpa [prefixWord, tailWord_5123836, baseEnd_5123836] using wordTrace_append hprefix tailTrace_5123836
  have hstable : (prefixWord ++ tailWord_5123836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5123836).length < 2 ^ (prefixWord ++ tailWord_5123836).sum := by decide
  have hdescent : baseEnd_5123836 < baseStart_5123836 := by decide
  rcases family_descends (prefixWord ++ tailWord_5123836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5123849 : List Nat := [1, 2, 1, 1, 3, 2, 1, 2, 2, 2, 6]
def baseStart_5123849 : Nat := 118140960795 + 5123849 * 2 ^ 59
def prefixEnd_5123849 : Nat := 4983230072969 + 3 ^ 40 * 5123849 * 2
def baseEnd_5123849 : Nat := 2630997338059228650923353

theorem tailTrace_5123849 : CollatzResearch.WordTrace tailWord_5123849 prefixEnd_5123849 2630997338059228650923353 := by
  unfold tailWord_5123849
  simp only [CollatzResearch.WordTrace]
  refine ⟨186882126014177631585334601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124588084009451754390223067 186882126014177631585334601)
  ·
    refine ⟨140161594510633223689000951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186882126014177631585334601 140161594510633223689000951)
    ·
      refine ⟨210242391765949835533501427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140161594510633223689000951 210242391765949835533501427)
      ·
        refine ⟨315363587648924753300252141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210242391765949835533501427 315363587648924753300252141)
        ·
          refine ⟨118261345368346782487594553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 315363587648924753300252141 118261345368346782487594553)
          ·
            refine ⟨88696009026260086865695915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118261345368346782487594553 88696009026260086865695915)
            ·
              refine ⟨133044013539390130298543873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88696009026260086865695915 133044013539390130298543873)
              ·
                refine ⟨99783010154542597723907905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133044013539390130298543873 99783010154542597723907905)
                ·
                  refine ⟨74837257615906948292930929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99783010154542597723907905 74837257615906948292930929)
                  ·
                    refine ⟨56127943211930211219698197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 74837257615906948292930929 56127943211930211219698197)
                    ·
                      refine ⟨2630997338059228650923353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56127943211930211219698197 2630997338059228650923353)
                      ·
                        rfl

theorem cell23_5123849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 2, 6].length) (baseStart_5123849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5123849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5123849 prefixEnd_5123849 := by exact prefixLift 5123849
  have htrace : WordTrace (prefixWord ++ tailWord_5123849) baseStart_5123849 baseEnd_5123849 := by
    simpa [prefixWord, tailWord_5123849, baseEnd_5123849] using wordTrace_append hprefix tailTrace_5123849
  have hstable : (prefixWord ++ tailWord_5123849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5123849).length < 2 ^ (prefixWord ++ tailWord_5123849).sum := by decide
  have hdescent : baseEnd_5123849 < baseStart_5123849 := by decide
  rcases family_descends (prefixWord ++ tailWord_5123849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5123850 : List Nat := [3, 1, 2, 2, 1, 5, 1, 2, 2, 4]
def baseStart_5123850 : Nat := 118140960795 + 5123850 * 2 ^ 59
def prefixEnd_5123850 : Nat := 4983230072969 + 3 ^ 40 * 5123850 * 2
def baseEnd_5123850 : Nat := 876999283846627715670283

theorem tailTrace_5123850 : CollatzResearch.WordTrace tailWord_5123850 prefixEnd_5123850 876999283846627715670283 := by
  unfold tailWord_5123850
  simp only [CollatzResearch.WordTrace]
  refine ⟨46720540621793502189030251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124588108324782672504080669 46720540621793502189030251)
  ·
    refine ⟨70080810932690253283545377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46720540621793502189030251 70080810932690253283545377)
    ·
      refine ⟨52560608199517689962659033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70080810932690253283545377 52560608199517689962659033)
      ·
        refine ⟨39420456149638267471994275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52560608199517689962659033 39420456149638267471994275)
        ·
          refine ⟨59130684224457401207991413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39420456149638267471994275 59130684224457401207991413)
          ·
            refine ⟨5543501646042881363249195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59130684224457401207991413 5543501646042881363249195)
            ·
              refine ⟨8315252469064322044873793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5543501646042881363249195 8315252469064322044873793)
              ·
                refine ⟨6236439351798241533655345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8315252469064322044873793 6236439351798241533655345)
                ·
                  refine ⟨4677329513848681150241509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6236439351798241533655345 4677329513848681150241509)
                  ·
                    refine ⟨876999283846627715670283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4677329513848681150241509 876999283846627715670283)
                    ·
                      rfl

theorem cell23_5123850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 2, 2, 4].length) (baseStart_5123850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5123850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5123850 prefixEnd_5123850 := by exact prefixLift 5123850
  have htrace : WordTrace (prefixWord ++ tailWord_5123850) baseStart_5123850 baseEnd_5123850 := by
    simpa [prefixWord, tailWord_5123850, baseEnd_5123850] using wordTrace_append hprefix tailTrace_5123850
  have hstable : (prefixWord ++ tailWord_5123850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5123850).length < 2 ^ (prefixWord ++ tailWord_5123850).sum := by decide
  have hdescent : baseEnd_5123850 < baseStart_5123850 := by decide
  rcases family_descends (prefixWord ++ tailWord_5123850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5123859 : List Nat := [1, 1, 1, 2, 1, 3, 2, 3, 2, 7]
def baseStart_5123859 : Nat := 118140960795 + 5123859 * 2 ^ 59
def prefixEnd_5123859 : Nat := 4983230072969 + 3 ^ 40 * 5123859 * 2
def baseEnd_5123859 : Nat := 877000824288591203932769

theorem tailTrace_5123859 : CollatzResearch.WordTrace tailWord_5123859 prefixEnd_5123859 877000824288591203932769 := by
  unfold tailWord_5123859
  simp only [CollatzResearch.WordTrace]
  refine ⟨186882490744141403293198631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124588327162760935528799087 186882490744141403293198631)
  ·
    refine ⟨280323736116212104939797947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186882490744141403293198631 280323736116212104939797947)
    ·
      refine ⟨420485604174318157409696921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280323736116212104939797947 420485604174318157409696921)
      ·
        refine ⟨315364203130738618057272691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 420485604174318157409696921 315364203130738618057272691)
        ·
          refine ⟨473046304696107927085909037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315364203130738618057272691 473046304696107927085909037)
          ·
            refine ⟨177392364261040472657215889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 473046304696107927085909037 177392364261040472657215889)
            ·
              refine ⟨133044273195780354492911917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 177392364261040472657215889 133044273195780354492911917)
              ·
                refine ⟨49891602448417632934841969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 133044273195780354492911917 49891602448417632934841969)
                ·
                  refine ⟨37418701836313224701131477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49891602448417632934841969 37418701836313224701131477)
                  ·
                    refine ⟨877000824288591203932769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37418701836313224701131477 877000824288591203932769)
                    ·
                      rfl

theorem cell23_5123859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 7].length) (baseStart_5123859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5123859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5123859 prefixEnd_5123859 := by exact prefixLift 5123859
  have htrace : WordTrace (prefixWord ++ tailWord_5123859) baseStart_5123859 baseEnd_5123859 := by
    simpa [prefixWord, tailWord_5123859, baseEnd_5123859] using wordTrace_append hprefix tailTrace_5123859
  have hstable : (prefixWord ++ tailWord_5123859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5123859).length < 2 ^ (prefixWord ++ tailWord_5123859).sum := by decide
  have hdescent : baseEnd_5123859 < baseStart_5123859 := by decide
  rcases family_descends (prefixWord ++ tailWord_5123859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5123873 : List Nat := [1, 2, 3, 2, 1, 3, 3, 1, 1, 3, 3]
def baseStart_5123873 : Nat := 118140960795 + 5123873 * 2 ^ 59
def prefixEnd_5123873 : Nat := 4983230072969 + 3 ^ 40 * 5123873 * 2
def baseEnd_5123873 : Nat := 2631009661594936557023243

theorem tailTrace_5123873 : CollatzResearch.WordTrace tailWord_5123873 prefixEnd_5123873 2631009661594936557023243 := by
  unfold tailWord_5123873
  simp only [CollatzResearch.WordTrace]
  refine ⟨186883001366090683684208273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124588667577393789122805515 186883001366090683684208273)
  ·
    refine ⟨140162251024568012763156205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186883001366090683684208273 140162251024568012763156205)
    ·
      refine ⟨52560844134213004786183577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140162251024568012763156205 52560844134213004786183577)
      ·
        refine ⟨39420633100659753589637683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52560844134213004786183577 39420633100659753589637683)
        ·
          refine ⟨59130949650989630384456525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39420633100659753589637683 59130949650989630384456525)
          ·
            refine ⟨22174106119121111394171197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59130949650989630384456525 22174106119121111394171197)
            ·
              refine ⟨8315289794670416772814199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22174106119121111394171197 8315289794670416772814199)
              ·
                refine ⟨12472934692005625159221299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8315289794670416772814199 12472934692005625159221299)
                ·
                  refine ⟨18709402038008437738831949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12472934692005625159221299 18709402038008437738831949)
                  ·
                    refine ⟨7016025764253164152061981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18709402038008437738831949 7016025764253164152061981)
                    ·
                      refine ⟨2631009661594936557023243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7016025764253164152061981 2631009661594936557023243)
                      ·
                        rfl

theorem cell23_5123873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 1, 1, 3, 3].length) (baseStart_5123873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5123873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5123873 prefixEnd_5123873 := by exact prefixLift 5123873
  have htrace : WordTrace (prefixWord ++ tailWord_5123873) baseStart_5123873 baseEnd_5123873 := by
    simpa [prefixWord, tailWord_5123873, baseEnd_5123873] using wordTrace_append hprefix tailTrace_5123873
  have hstable : (prefixWord ++ tailWord_5123873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5123873).length < 2 ^ (prefixWord ++ tailWord_5123873).sum := by decide
  have hdescent : baseEnd_5123873 < baseStart_5123873 := by decide
  rcases family_descends (prefixWord ++ tailWord_5123873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5123891 : List Nat := [1, 1, 1, 2, 8, 1, 1, 3, 1, 2, 2]
def baseStart_5123891 : Nat := 118140960795 + 5123891 * 2 ^ 59
def prefixEnd_5123891 : Nat := 4983230072969 + 3 ^ 40 * 5123891 * 2
def baseEnd_5123891 : Nat := 2631018904246717486598161

theorem tailTrace_5123891 : CollatzResearch.WordTrace tailWord_5123891 prefixEnd_5123891 2631018904246717486598161 := by
  unfold tailWord_5123891
  simp only [CollatzResearch.WordTrace]
  refine ⟨186883657880025472758363527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124589105253350315172242351 186883657880025472758363527)
  ·
    refine ⟨280325486820038209137545291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186883657880025472758363527 280325486820038209137545291)
    ·
      refine ⟨420488230230057313706317937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280325486820038209137545291 420488230230057313706317937)
      ·
        refine ⟨315366172672542985279738453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 420488230230057313706317937 315366172672542985279738453)
        ·
          refine ⟨3695697336006363108746935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 315366172672542985279738453 3695697336006363108746935)
          ·
            refine ⟨5543546004009544663120403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3695697336006363108746935 5543546004009544663120403)
            ·
              refine ⟨8315319006014316994680605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5543546004009544663120403 8315319006014316994680605)
              ·
                refine ⟨3118244627255368873005227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8315319006014316994680605 3118244627255368873005227)
                ·
                  refine ⟨4677366940883053309507841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3118244627255368873005227 4677366940883053309507841)
                  ·
                    refine ⟨3508025205662289982130881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4677366940883053309507841 3508025205662289982130881)
                    ·
                      refine ⟨2631018904246717486598161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3508025205662289982130881 2631018904246717486598161)
                      ·
                        rfl

theorem cell23_5123891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 3, 1, 2, 2].length) (baseStart_5123891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5123891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5123891 prefixEnd_5123891 := by exact prefixLift 5123891
  have htrace : WordTrace (prefixWord ++ tailWord_5123891) baseStart_5123891 baseEnd_5123891 := by
    simpa [prefixWord, tailWord_5123891, baseEnd_5123891] using wordTrace_append hprefix tailTrace_5123891
  have hstable : (prefixWord ++ tailWord_5123891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5123891).length < 2 ^ (prefixWord ++ tailWord_5123891).sum := by decide
  have hdescent : baseEnd_5123891 < baseStart_5123891 := by decide
  rcases family_descends (prefixWord ++ tailWord_5123891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5123900 : List Nat := [2, 2, 2, 2, 1, 1, 4, 3, 1, 3, 2]
def baseStart_5123900 : Nat := 118140960795 + 5123900 * 2 ^ 59
def prefixEnd_5123900 : Nat := 4983230072969 + 3 ^ 40 * 5123900 * 2
def baseEnd_5123900 : Nat := 2631023525572607951385619

theorem tailTrace_5123900 : CollatzResearch.WordTrace tailWord_5123900 prefixEnd_5123900 2631023525572607951385619 := by
  unfold tailWord_5123900
  simp only [CollatzResearch.WordTrace]
  refine ⟨93441993068496433647720577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124589324091328578196960769 93441993068496433647720577)
  ·
    refine ⟨70081494801372325235790433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93441993068496433647720577 70081494801372325235790433)
    ·
      refine ⟨52561121101029243926842825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70081494801372325235790433 52561121101029243926842825)
      ·
        refine ⟨39420840825771932945132119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52561121101029243926842825 39420840825771932945132119)
        ·
          refine ⟨59131261238657899417698179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39420840825771932945132119 59131261238657899417698179)
          ·
            refine ⟨88696891857986849126547269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59131261238657899417698179 88696891857986849126547269)
            ·
              refine ⟨16630667223372534211227613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88696891857986849126547269 16630667223372534211227613)
              ·
                refine ⟨6236500208764700329210355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16630667223372534211227613 6236500208764700329210355)
                ·
                  refine ⟨9354750313147050493815533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6236500208764700329210355 9354750313147050493815533)
                  ·
                    refine ⟨3508031367430143935180825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9354750313147050493815533 3508031367430143935180825)
                    ·
                      refine ⟨2631023525572607951385619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3508031367430143935180825 2631023525572607951385619)
                      ·
                        rfl

theorem cell23_5123900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 3, 1, 3, 2].length) (baseStart_5123900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5123900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5123900 prefixEnd_5123900 := by exact prefixLift 5123900
  have htrace : WordTrace (prefixWord ++ tailWord_5123900) baseStart_5123900 baseEnd_5123900 := by
    simpa [prefixWord, tailWord_5123900, baseEnd_5123900] using wordTrace_append hprefix tailTrace_5123900
  have hstable : (prefixWord ++ tailWord_5123900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5123900).length < 2 ^ (prefixWord ++ tailWord_5123900).sum := by decide
  have hdescent : baseEnd_5123900 < baseStart_5123900 := by decide
  rcases family_descends (prefixWord ++ tailWord_5123900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5123924 : List Nat := [2, 4, 1, 1, 3, 3, 2, 1, 2, 1, 3]
def baseStart_5123924 : Nat := 118140960795 + 5123924 * 2 ^ 59
def prefixEnd_5123924 : Nat := 4983230072969 + 3 ^ 40 * 5123924 * 2
def baseEnd_5123924 : Nat := 2631035849108315857485509

theorem tailTrace_5123924 : CollatzResearch.WordTrace tailWord_5123924 prefixEnd_5123924 2631035849108315857485509 := by
  unfold tailWord_5123924
  simp only [CollatzResearch.WordTrace]
  refine ⟨93442430744452959697157413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124589907659270612929543217 93442430744452959697157413)
  ·
    refine ⟨17520455764584929943217015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93442430744452959697157413 17520455764584929943217015)
    ·
      refine ⟨26280683646877394914825523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17520455764584929943217015 26280683646877394914825523)
      ·
        refine ⟨39421025470316092372238285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26280683646877394914825523 39421025470316092372238285)
        ·
          refine ⟨14782884551368534639589357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39421025470316092372238285 14782884551368534639589357)
          ·
            refine ⟨5543581706763200489846009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14782884551368534639589357 5543581706763200489846009)
            ·
              refine ⟨4157686280072400367384507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5543581706763200489846009 4157686280072400367384507)
              ·
                refine ⟨6236529420108600551076761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4157686280072400367384507 6236529420108600551076761)
                ·
                  refine ⟨4677397065081450413307571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6236529420108600551076761 4677397065081450413307571)
                  ·
                    refine ⟨7016095597622175619961357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4677397065081450413307571 7016095597622175619961357)
                    ·
                      refine ⟨2631035849108315857485509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7016095597622175619961357 2631035849108315857485509)
                      ·
                        rfl

theorem cell23_5123924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 2, 1, 2, 1, 3].length) (baseStart_5123924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5123924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5123924 prefixEnd_5123924 := by exact prefixLift 5123924
  have htrace : WordTrace (prefixWord ++ tailWord_5123924) baseStart_5123924 baseEnd_5123924 := by
    simpa [prefixWord, tailWord_5123924, baseEnd_5123924] using wordTrace_append hprefix tailTrace_5123924
  have hstable : (prefixWord ++ tailWord_5123924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5123924).length < 2 ^ (prefixWord ++ tailWord_5123924).sum := by decide
  have hdescent : baseEnd_5123924 < baseStart_5123924 := by decide
  rcases family_descends (prefixWord ++ tailWord_5123924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5123953 : List Nat := [1, 2, 2, 2, 1, 3, 2, 5, 5]
def baseStart_5123953 : Nat := 118140960795 + 5123953 * 2 ^ 59
def prefixEnd_5123953 : Nat := 4983230072969 + 3 ^ 40 * 5123953 * 2
def baseEnd_5123953 : Nat := 292338971116366249335875

theorem tailTrace_5123953 : CollatzResearch.WordTrace tailWord_5123953 prefixEnd_5123953 292338971116366249335875 := by
  unfold tailWord_5123953
  simp only [CollatzResearch.WordTrace]
  refine ⟨186885919205800857347120513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124590612803867238231413675 186885919205800857347120513)
  ·
    refine ⟨140164439404350643010340385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186885919205800857347120513 140164439404350643010340385)
    ·
      refine ⟨105123329553262982257755289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140164439404350643010340385 105123329553262982257755289)
      ·
        refine ⟨78842497164947236693316467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105123329553262982257755289 78842497164947236693316467)
        ·
          refine ⟨118263745747420855039974701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78842497164947236693316467 118263745747420855039974701)
          ·
            refine ⟨44348904655282820639990513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118263745747420855039974701 44348904655282820639990513)
            ·
              refine ⟨33261678491462115479992885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44348904655282820639990513 33261678491462115479992885)
              ·
                refine ⟨3118282358574573326249333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33261678491462115479992885 3118282358574573326249333)
                ·
                  refine ⟨292338971116366249335875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3118282358574573326249333 292338971116366249335875)
                  ·
                    rfl

theorem cell23_5123953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 5, 5].length) (baseStart_5123953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5123953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5123953 prefixEnd_5123953 := by exact prefixLift 5123953
  have htrace : WordTrace (prefixWord ++ tailWord_5123953) baseStart_5123953 baseEnd_5123953 := by
    simpa [prefixWord, tailWord_5123953, baseEnd_5123953] using wordTrace_append hprefix tailTrace_5123953
  have hstable : (prefixWord ++ tailWord_5123953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5123953).length < 2 ^ (prefixWord ++ tailWord_5123953).sum := by decide
  have hdescent : baseEnd_5123953 < baseStart_5123953 := by decide
  rcases family_descends (prefixWord ++ tailWord_5123953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5123973 : List Nat := [1, 3, 1, 1, 3, 2, 1, 1, 1, 7, 2]
def baseStart_5123973 : Nat := 118140960795 + 5123973 * 2 ^ 59
def prefixEnd_5123973 : Nat := 4983230072969 + 3 ^ 40 * 5123973 * 2
def baseEnd_5123973 : Nat := 2631061009660386165772783

theorem tailTrace_5123973 : CollatzResearch.WordTrace tailWord_5123973 prefixEnd_5123973 2631061009660386165772783 := by
  unfold tailWord_5123973
  simp only [CollatzResearch.WordTrace]
  refine ⟨186886648665728400762848573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124591099110485600508565715 186886648665728400762848573)
  ·
    refine ⟨70082493249648150286068215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186886648665728400762848573 70082493249648150286068215)
    ·
      refine ⟨105123739874472225429102323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70082493249648150286068215 105123739874472225429102323)
      ·
        refine ⟨157685609811708338143653485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105123739874472225429102323 157685609811708338143653485)
        ·
          refine ⟨59132103679390626803870057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 157685609811708338143653485 59132103679390626803870057)
          ·
            refine ⟨44349077759542970102902543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59132103679390626803870057 44349077759542970102902543)
            ·
              refine ⟨66523616639314455154353815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44349077759542970102902543 66523616639314455154353815)
              ·
                refine ⟨99785424958971682731530723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66523616639314455154353815 99785424958971682731530723)
                ·
                  refine ⟨149678137438457524097296085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99785424958971682731530723 149678137438457524097296085)
                  ·
                    refine ⟨3508081346213848221030377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 149678137438457524097296085 3508081346213848221030377)
                    ·
                      refine ⟨2631061009660386165772783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3508081346213848221030377 2631061009660386165772783)
                      ·
                        rfl

theorem cell23_5123973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 7, 2].length) (baseStart_5123973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5123973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5123973 prefixEnd_5123973 := by exact prefixLift 5123973
  have htrace : WordTrace (prefixWord ++ tailWord_5123973) baseStart_5123973 baseEnd_5123973 := by
    simpa [prefixWord, tailWord_5123973, baseEnd_5123973] using wordTrace_append hprefix tailTrace_5123973
  have hstable : (prefixWord ++ tailWord_5123973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5123973).length < 2 ^ (prefixWord ++ tailWord_5123973).sum := by decide
  have hdescent : baseEnd_5123973 < baseStart_5123973 := by decide
  rcases family_descends (prefixWord ++ tailWord_5123973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5124003 : List Nat := [1, 1, 1, 4, 1, 2, 1, 1, 3, 6, 2]
def baseStart_5124003 : Nat := 118140960795 + 5124003 * 2 ^ 59
def prefixEnd_5124003 : Nat := 4983230072969 + 3 ^ 40 * 5124003 * 2
def baseEnd_5124003 : Nat := 2631076414080021048397645

theorem tailTrace_5124003 : CollatzResearch.WordTrace tailWord_5124003 prefixEnd_5124003 2631076414080021048397645 := by
  unfold tailWord_5124003
  simp only [CollatzResearch.WordTrace]
  refine ⟨186887742855619715886440663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124591828570413143924293775 186887742855619715886440663)
  ·
    refine ⟨280331614283429573829660995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186887742855619715886440663 280331614283429573829660995)
    ·
      refine ⟨420497421425144360744491493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280331614283429573829660995 420497421425144360744491493)
      ·
        refine ⟨78843266517214567639592155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 420497421425144360744491493 78843266517214567639592155)
        ·
          refine ⟨118264899775821851459388233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78843266517214567639592155 118264899775821851459388233)
          ·
            refine ⟨88698674831866388594541175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118264899775821851459388233 88698674831866388594541175)
            ·
              refine ⟨133048012247799582891811763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88698674831866388594541175 133048012247799582891811763)
              ·
                refine ⟨199572018371699374337717645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133048012247799582891811763 199572018371699374337717645)
                ·
                  refine ⟨74839506889387265376644117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 199572018371699374337717645 74839506889387265376644117)
                  ·
                    refine ⟨3508101885440028064530193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 74839506889387265376644117 3508101885440028064530193)
                    ·
                      refine ⟨2631076414080021048397645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3508101885440028064530193 2631076414080021048397645)
                      ·
                        rfl

theorem cell23_5124003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 6, 2].length) (baseStart_5124003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5124003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5124003 prefixEnd_5124003 := by exact prefixLift 5124003
  have htrace : WordTrace (prefixWord ++ tailWord_5124003) baseStart_5124003 baseEnd_5124003 := by
    simpa [prefixWord, tailWord_5124003, baseEnd_5124003] using wordTrace_append hprefix tailTrace_5124003
  have hstable : (prefixWord ++ tailWord_5124003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5124003).length < 2 ^ (prefixWord ++ tailWord_5124003).sum := by decide
  have hdescent : baseEnd_5124003 < baseStart_5124003 := by decide
  rcases family_descends (prefixWord ++ tailWord_5124003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5124016 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 4]
def baseStart_5124016 : Nat := 118140960795 + 5124016 * 2 ^ 59
def prefixEnd_5124016 : Nat := 4983230072969 + 3 ^ 40 * 5124016 * 2
def baseEnd_5124016 : Nat := 2631083089328529497535085

theorem tailTrace_5124016 : CollatzResearch.WordTrace tailWord_5124016 prefixEnd_5124016 2631083089328529497535085 := by
  unfold tailWord_5124016
  simp only [CollatzResearch.WordTrace]
  refine ⟨93444108502286309553331951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124592144669715079404442601 93444108502286309553331951)
  ·
    refine ⟨140166162753429464329997927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93444108502286309553331951 140166162753429464329997927)
    ·
      refine ⟨210249244130144196494996891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140166162753429464329997927 210249244130144196494996891)
      ·
        refine ⟨315373866195216294742495337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210249244130144196494996891 315373866195216294742495337)
        ·
          refine ⟨236530399646412221056871503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 315373866195216294742495337 236530399646412221056871503)
          ·
            refine ⟨354795599469618331585307255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236530399646412221056871503 354795599469618331585307255)
            ·
              refine ⟨532193399204427497377960883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 354795599469618331585307255 532193399204427497377960883)
              ·
                refine ⟨798290098806641246066941325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 532193399204427497377960883 798290098806641246066941325)
                ·
                  refine ⟨299358787052490467275102997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 798290098806641246066941325 299358787052490467275102997)
                  ·
                    refine ⟨14032443143085490653520453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 299358787052490467275102997 14032443143085490653520453)
                    ·
                      refine ⟨2631083089328529497535085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14032443143085490653520453 2631083089328529497535085)
                      ·
                        rfl

theorem cell23_5124016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 4].length) (baseStart_5124016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5124016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5124016 prefixEnd_5124016 := by exact prefixLift 5124016
  have htrace : WordTrace (prefixWord ++ tailWord_5124016) baseStart_5124016 baseEnd_5124016 := by
    simpa [prefixWord, tailWord_5124016, baseEnd_5124016] using wordTrace_append hprefix tailTrace_5124016
  have hstable : (prefixWord ++ tailWord_5124016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5124016).length < 2 ^ (prefixWord ++ tailWord_5124016).sum := by decide
  have hdescent : baseEnd_5124016 < baseStart_5124016 := by decide
  rcases family_descends (prefixWord ++ tailWord_5124016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5124023 : List Nat := [1, 1, 3, 1, 3, 1, 1, 3, 4, 2, 3]
def baseStart_5124023 : Nat := 118140960795 + 5124023 * 2 ^ 59
def prefixEnd_5124023 : Nat := 4983230072969 + 3 ^ 40 * 5124023 * 2
def baseEnd_5124023 : Nat := 2631086683693110970147553

theorem tailTrace_5124023 : CollatzResearch.WordTrace tailWord_5124023 prefixEnd_5124023 2631086683693110970147553 := by
  unfold tailWord_5124023
  simp only [CollatzResearch.WordTrace]
  refine ⟨186888472315547259302168723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124592314877031506201445815 186888472315547259302168723)
  ·
    refine ⟨280332708473320888953253085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186888472315547259302168723 280332708473320888953253085)
    ·
      refine ⟨105124765677495333357469907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 280332708473320888953253085 105124765677495333357469907)
      ·
        refine ⟨157687148516243000036204861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105124765677495333357469907 157687148516243000036204861)
        ·
          refine ⟨59132680693591125013576823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 157687148516243000036204861 59132680693591125013576823)
          ·
            refine ⟨88699021040386687520365235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59132680693591125013576823 88699021040386687520365235)
            ·
              refine ⟨133048531560580031280547853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88699021040386687520365235 133048531560580031280547853)
              ·
                refine ⟨49893199335217511730205445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 133048531560580031280547853 49893199335217511730205445)
                ·
                  refine ⟨9354974875353283449413521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49893199335217511730205445 9354974875353283449413521)
                  ·
                    refine ⟨7016231156514962587060141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9354974875353283449413521 7016231156514962587060141)
                    ·
                      refine ⟨2631086683693110970147553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7016231156514962587060141 2631086683693110970147553)
                      ·
                        rfl

theorem cell23_5124023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 4, 2, 3].length) (baseStart_5124023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5124023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5124023 prefixEnd_5124023 := by exact prefixLift 5124023
  have htrace : WordTrace (prefixWord ++ tailWord_5124023) baseStart_5124023 baseEnd_5124023 := by
    simpa [prefixWord, tailWord_5124023, baseEnd_5124023] using wordTrace_append hprefix tailTrace_5124023
  have hstable : (prefixWord ++ tailWord_5124023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5124023).length < 2 ^ (prefixWord ++ tailWord_5124023).sum := by decide
  have hdescent : baseEnd_5124023 < baseStart_5124023 := by decide
  rcases family_descends (prefixWord ++ tailWord_5124023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5124030 : List Nat := [4, 2, 1, 1, 1, 3, 1, 3, 3, 4]
def baseStart_5124030 : Nat := 118140960795 + 5124030 * 2 ^ 59
def prefixEnd_5124030 : Nat := 4983230072969 + 3 ^ 40 * 5124030 * 2
def baseEnd_5124030 : Nat := 877030092685897480920007

theorem tailTrace_5124030 : CollatzResearch.WordTrace tailWord_5124030 prefixEnd_5124030 877030092685897480920007 := by
  unfold tailWord_5124030
  simp only [CollatzResearch.WordTrace]
  refine ⟨23361090953315237437209193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124592485084347932998449029 23361090953315237437209193)
  ·
    refine ⟨17520818214986428077906895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23361090953315237437209193 17520818214986428077906895)
    ·
      refine ⟨26281227322479642116860343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17520818214986428077906895 26281227322479642116860343)
      ·
        refine ⟨39421840983719463175290515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26281227322479642116860343 39421840983719463175290515)
        ·
          refine ⟨59132761475579194762935773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39421840983719463175290515 59132761475579194762935773)
          ·
            refine ⟨22174785553342198036100915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59132761475579194762935773 22174785553342198036100915)
            ·
              refine ⟨33262178330013297054151373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22174785553342198036100915 33262178330013297054151373)
              ·
                refine ⟨12473316873754986395306765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33262178330013297054151373 12473316873754986395306765)
                ·
                  refine ⟨4677493827658119898240037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12473316873754986395306765 4677493827658119898240037)
                  ·
                    refine ⟨877030092685897480920007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4677493827658119898240037 877030092685897480920007)
                    ·
                      rfl

theorem cell23_5124030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 3, 3, 4].length) (baseStart_5124030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5124030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5124030 prefixEnd_5124030 := by exact prefixLift 5124030
  have htrace : WordTrace (prefixWord ++ tailWord_5124030) baseStart_5124030 baseEnd_5124030 := by
    simpa [prefixWord, tailWord_5124030, baseEnd_5124030] using wordTrace_append hprefix tailTrace_5124030
  have hstable : (prefixWord ++ tailWord_5124030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5124030).length < 2 ^ (prefixWord ++ tailWord_5124030).sum := by decide
  have hdescent : baseEnd_5124030 < baseStart_5124030 := by decide
  rcases family_descends (prefixWord ++ tailWord_5124030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5124080 : List Nat := [2, 1, 1, 1, 3, 2, 3, 1, 4, 3, 2]
def baseStart_5124080 : Nat := 118140960795 + 5124080 * 2 ^ 59
def prefixEnd_5124080 : Nat := 4983230072969 + 3 ^ 40 * 5124080 * 2
def baseEnd_5124080 : Nat := 2631115952090417247134791

theorem tailTrace_5124080 : CollatzResearch.WordTrace tailWord_5124080 prefixEnd_5124080 2631115952090417247134791 := by
  unfold tailWord_5124080
  simp only [CollatzResearch.WordTrace]
  refine ⟨93445275638170379018496847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124593700850893838691329129 93445275638170379018496847)
  ·
    refine ⟨140167913457255568527745271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93445275638170379018496847 140167913457255568527745271)
    ·
      refine ⟨210251870185883352791617907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140167913457255568527745271 210251870185883352791617907)
      ·
        refine ⟨315377805278825029187426861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210251870185883352791617907 315377805278825029187426861)
        ·
          refine ⟨118266676979559385945285073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 315377805278825029187426861 118266676979559385945285073)
          ·
            refine ⟨88700007734669539458963805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118266676979559385945285073 88700007734669539458963805)
            ·
              refine ⟨33262502900501077297111427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88700007734669539458963805 33262502900501077297111427)
              ·
                refine ⟨49893754350751615945667141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33262502900501077297111427 49893754350751615945667141)
                ·
                  refine ⟨9355078940765927989812589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49893754350751615945667141 9355078940765927989812589)
                  ·
                    refine ⟨3508154602787222996179721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9355078940765927989812589 3508154602787222996179721)
                    ·
                      refine ⟨2631115952090417247134791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3508154602787222996179721 2631115952090417247134791)
                      ·
                        rfl

theorem cell23_5124080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 4, 3, 2].length) (baseStart_5124080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5124080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5124080 prefixEnd_5124080 := by exact prefixLift 5124080
  have htrace : WordTrace (prefixWord ++ tailWord_5124080) baseStart_5124080 baseEnd_5124080 := by
    simpa [prefixWord, tailWord_5124080, baseEnd_5124080] using wordTrace_append hprefix tailTrace_5124080
  have hstable : (prefixWord ++ tailWord_5124080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5124080).length < 2 ^ (prefixWord ++ tailWord_5124080).sum := by decide
  have hdescent : baseEnd_5124080 < baseStart_5124080 := by decide
  rcases family_descends (prefixWord ++ tailWord_5124080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5124094 : List Nat := [4, 2, 2, 2, 1, 3, 2, 1, 6]
def baseStart_5124094 : Nat := 118140960795 + 5124094 * 2 ^ 59
def prefixEnd_5124094 : Nat := 4983230072969 + 3 ^ 40 * 5124094 * 2
def baseEnd_5124094 : Nat := 292347015646620021373303

theorem tailTrace_5124094 : CollatzResearch.WordTrace tailWord_5124094 prefixEnd_5124094 292347015646620021373303 := by
  unfold tailWord_5124094
  simp only [CollatzResearch.WordTrace]
  refine ⟨23361382737286254803500417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124594041265526692285335557 23361382737286254803500417)
  ·
    refine ⟨17521037052964691102625313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23361382737286254803500417 17521037052964691102625313)
    ·
      refine ⟨13140777789723518326968985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17521037052964691102625313 13140777789723518326968985)
      ·
        refine ⟨9855583342292638745226739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13140777789723518326968985 9855583342292638745226739)
        ·
          refine ⟨14783375013438958117840109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9855583342292638745226739 14783375013438958117840109)
          ·
            refine ⟨5543765630039609294190041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14783375013438958117840109 5543765630039609294190041)
            ·
              refine ⟨4157824222529706970642531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5543765630039609294190041 4157824222529706970642531)
              ·
                refine ⟨6236736333794560455963797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4157824222529706970642531 6236736333794560455963797)
                ·
                  refine ⟨292347015646620021373303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6236736333794560455963797 292347015646620021373303)
                  ·
                    rfl

theorem cell23_5124094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 2, 1, 6].length) (baseStart_5124094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5124094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5124094 prefixEnd_5124094 := by exact prefixLift 5124094
  have htrace : WordTrace (prefixWord ++ tailWord_5124094) baseStart_5124094 baseEnd_5124094 := by
    simpa [prefixWord, tailWord_5124094, baseEnd_5124094] using wordTrace_append hprefix tailTrace_5124094
  have hstable : (prefixWord ++ tailWord_5124094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5124094).length < 2 ^ (prefixWord ++ tailWord_5124094).sum := by decide
  have hdescent : baseEnd_5124094 < baseStart_5124094 := by decide
  rcases family_descends (prefixWord ++ tailWord_5124094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5124110 : List Nat := [4, 1, 1, 2, 2, 1, 3, 1, 3, 1, 4]
def baseStart_5124110 : Nat := 118140960795 + 5124110 * 2 ^ 59
def prefixEnd_5124110 : Nat := 4983230072969 + 3 ^ 40 * 5124110 * 2
def baseEnd_5124110 : Nat := 2631131356510052129759653

theorem tailTrace_5124110 : CollatzResearch.WordTrace tailWord_5124110 prefixEnd_5124110 2631131356510052129759653 := by
  unfold tailWord_5124110
  simp only [CollatzResearch.WordTrace]
  refine ⟨23361455683279009145073223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124594430310821382107057189 23361455683279009145073223)
  ·
    refine ⟨35042183524918513717609835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23361455683279009145073223 35042183524918513717609835)
    ·
      refine ⟨52563275287377770576414753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35042183524918513717609835 52563275287377770576414753)
      ·
        refine ⟨39422456465533327932311065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52563275287377770576414753 39422456465533327932311065)
        ·
          refine ⟨29566842349149995949233299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39422456465533327932311065 29566842349149995949233299)
          ·
            refine ⟨44350263523724993923849949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29566842349149995949233299 44350263523724993923849949)
            ·
              refine ⟨16631348821396872721443731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44350263523724993923849949 16631348821396872721443731)
              ·
                refine ⟨24947023232095309082165597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16631348821396872721443731 24947023232095309082165597)
                ·
                  refine ⟨9355133712035740905812099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24947023232095309082165597 9355133712035740905812099)
                  ·
                    refine ⟨14032700568053611358718149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9355133712035740905812099 14032700568053611358718149)
                    ·
                      refine ⟨2631131356510052129759653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14032700568053611358718149 2631131356510052129759653)
                      ·
                        rfl

theorem cell23_5124110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_5124110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5124110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5124110 prefixEnd_5124110 := by exact prefixLift 5124110
  have htrace : WordTrace (prefixWord ++ tailWord_5124110) baseStart_5124110 baseEnd_5124110 := by
    simpa [prefixWord, tailWord_5124110, baseEnd_5124110] using wordTrace_append hprefix tailTrace_5124110
  have hstable : (prefixWord ++ tailWord_5124110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5124110).length < 2 ^ (prefixWord ++ tailWord_5124110).sum := by decide
  have hdescent : baseEnd_5124110 < baseStart_5124110 := by decide
  rcases family_descends (prefixWord ++ tailWord_5124110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5124127 : List Nat := [1, 1, 2, 4, 1, 2, 5, 1, 1, 1, 4]
def baseStart_5124127 : Nat := 118140960795 + 5124127 * 2 ^ 59
def prefixEnd_5124127 : Nat := 4983230072969 + 3 ^ 40 * 5124127 * 2
def baseEnd_5124127 : Nat := 2631140085681178563247075

theorem tailTrace_5124127 : CollatzResearch.WordTrace tailWord_5124127 prefixEnd_5124127 2631140085681178563247075 := by
  unfold tailWord_5124127
  simp only [CollatzResearch.WordTrace]
  refine ⟨186892265507170485063954635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124594843671446990042636423 186892265507170485063954635)
  ·
    refine ⟨280338398260755727595931953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186892265507170485063954635 280338398260755727595931953)
    ·
      refine ⟨210253798695566795696948965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 280338398260755727595931953 210253798695566795696948965)
      ·
        refine ⟨39422587255418774193177931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 210253798695566795696948965 39422587255418774193177931)
        ·
          refine ⟨59133880883128161289766897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39422587255418774193177931 59133880883128161289766897)
          ·
            refine ⟨44350410662346120967325173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59133880883128161289766897 44350410662346120967325173)
            ·
              refine ⟨4157850999594948840686735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44350410662346120967325173 4157850999594948840686735)
              ·
                refine ⟨6236776499392423261030103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4157850999594948840686735 6236776499392423261030103)
                ·
                  refine ⟨9355164749088634891545155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6236776499392423261030103 9355164749088634891545155)
                  ·
                    refine ⟨14032747123632952337317733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9355164749088634891545155 14032747123632952337317733)
                    ·
                      refine ⟨2631140085681178563247075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14032747123632952337317733 2631140085681178563247075)
                      ·
                        rfl

theorem cell23_5124127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 5, 1, 1, 1, 4].length) (baseStart_5124127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5124127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5124127 prefixEnd_5124127 := by exact prefixLift 5124127
  have htrace : WordTrace (prefixWord ++ tailWord_5124127) baseStart_5124127 baseEnd_5124127 := by
    simpa [prefixWord, tailWord_5124127, baseEnd_5124127] using wordTrace_append hprefix tailTrace_5124127
  have hstable : (prefixWord ++ tailWord_5124127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5124127).length < 2 ^ (prefixWord ++ tailWord_5124127).sum := by decide
  have hdescent : baseEnd_5124127 < baseStart_5124127 := by decide
  rcases family_descends (prefixWord ++ tailWord_5124127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5124138 : List Nat := [3, 1, 4, 1, 2, 3, 2, 2, 1, 1, 3]
def baseStart_5124138 : Nat := 118140960795 + 5124138 * 2 ^ 59
def prefixEnd_5124138 : Nat := 4983230072969 + 3 ^ 40 * 5124138 * 2
def baseEnd_5124138 : Nat := 2631145733968378020209525

theorem tailTrace_5124138 : CollatzResearch.WordTrace tailWord_5124138 prefixEnd_5124138 2631145733968378020209525 := by
  unfold tailWord_5124138
  simp only [CollatzResearch.WordTrace]
  refine ⟨46723166677532658485651267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124595111140087089295070045 46723166677532658485651267)
  ·
    refine ⟨70084750016298987728476901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46723166677532658485651267 70084750016298987728476901)
    ·
      refine ⟨13140890628056060199089419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70084750016298987728476901 13140890628056060199089419)
      ·
        refine ⟨19711335942084090298634129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13140890628056060199089419 19711335942084090298634129)
        ·
          refine ⟨14783501956563067723975597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19711335942084090298634129 14783501956563067723975597)
          ·
            refine ⟨5543813233711150396490849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14783501956563067723975597 5543813233711150396490849)
            ·
              refine ⟨4157859925283362797368137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5543813233711150396490849 4157859925283362797368137)
              ·
                refine ⟨3118394943962522098026103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4157859925283362797368137 3118394943962522098026103)
                ·
                  refine ⟨4677592415943783147039155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3118394943962522098026103 4677592415943783147039155)
                  ·
                    refine ⟨7016388623915674720558733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4677592415943783147039155 7016388623915674720558733)
                    ·
                      refine ⟨2631145733968378020209525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7016388623915674720558733 2631145733968378020209525)
                      ·
                        rfl

theorem cell23_5124138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 2, 2, 1, 1, 3].length) (baseStart_5124138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5124138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5124138 prefixEnd_5124138 := by exact prefixLift 5124138
  have htrace : WordTrace (prefixWord ++ tailWord_5124138) baseStart_5124138 baseEnd_5124138 := by
    simpa [prefixWord, tailWord_5124138, baseEnd_5124138] using wordTrace_append hprefix tailTrace_5124138
  have hstable : (prefixWord ++ tailWord_5124138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5124138).length < 2 ^ (prefixWord ++ tailWord_5124138).sum := by decide
  have hdescent : baseEnd_5124138 < baseStart_5124138 := by decide
  rcases family_descends (prefixWord ++ tailWord_5124138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5124160 : List Nat := [2, 1, 1, 2, 2, 4, 1, 3, 1, 3, 3]
def baseStart_5124160 : Nat := 118140960795 + 5124160 * 2 ^ 59
def prefixEnd_5124160 : Nat := 4983230072969 + 3 ^ 40 * 5124160 * 2
def baseEnd_5124160 : Nat := 2631157030542776934134423

theorem tailTrace_5124160 : CollatzResearch.WordTrace tailWord_5124160 prefixEnd_5124160 2631157030542776934134423 := by
  unfold tailWord_5124160
  simp only [CollatzResearch.WordTrace]
  refine ⟨93446734558025465849952967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124595646077367287799937289 93446734558025465849952967)
  ·
    refine ⟨140170101837038198774929451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93446734558025465849952967 140170101837038198774929451)
    ·
      refine ⟨210255152755557298162394177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140170101837038198774929451 210255152755557298162394177)
      ·
        refine ⟨157691364566667973621795633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210255152755557298162394177 157691364566667973621795633)
        ·
          refine ⟨118268523425000980216346725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157691364566667973621795633 118268523425000980216346725)
          ·
            refine ⟨22175348142187683790565011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 118268523425000980216346725 22175348142187683790565011)
            ·
              refine ⟨33263022213281525685847517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22175348142187683790565011 33263022213281525685847517)
              ·
                refine ⟨12473633329980572132192819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33263022213281525685847517 12473633329980572132192819)
                ·
                  refine ⟨18710449994970858198289229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12473633329980572132192819 18710449994970858198289229)
                  ·
                    refine ⟨7016418748114071824358461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18710449994970858198289229 7016418748114071824358461)
                    ·
                      refine ⟨2631157030542776934134423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7016418748114071824358461 2631157030542776934134423)
                      ·
                        rfl

theorem cell23_5124160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 3, 1, 3, 3].length) (baseStart_5124160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5124160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5124160 prefixEnd_5124160 := by exact prefixLift 5124160
  have htrace : WordTrace (prefixWord ++ tailWord_5124160) baseStart_5124160 baseEnd_5124160 := by
    simpa [prefixWord, tailWord_5124160, baseEnd_5124160] using wordTrace_append hprefix tailTrace_5124160
  have hstable : (prefixWord ++ tailWord_5124160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5124160).length < 2 ^ (prefixWord ++ tailWord_5124160).sum := by decide
  have hdescent : baseEnd_5124160 < baseStart_5124160 := by decide
  rcases family_descends (prefixWord ++ tailWord_5124160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5124178 : List Nat := [3, 2, 2, 1, 4, 1, 2, 3, 1, 2, 2]
def baseStart_5124178 : Nat := 118140960795 + 5124178 * 2 ^ 59
def prefixEnd_5124178 : Nat := 4983230072969 + 3 ^ 40 * 5124178 * 2
def baseEnd_5124178 : Nat := 2631166273194557863709341

theorem tailTrace_5124178 : CollatzResearch.WordTrace tailWord_5124178 prefixEnd_5124178 2631166273194557863709341 := by
  unfold tailWord_5124178
  simp only [CollatzResearch.WordTrace]
  refine ⟨46723531407496430193515297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124596083753323813849374125 46723531407496430193515297)
  ·
    refine ⟨35042648555622322645136473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46723531407496430193515297 35042648555622322645136473)
    ·
      refine ⟨26281986416716741983852355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35042648555622322645136473 26281986416716741983852355)
      ·
        refine ⟨39422979625075112975778533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26281986416716741983852355 39422979625075112975778533)
        ·
          refine ⟨7391808679701583682958475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39422979625075112975778533 7391808679701583682958475)
          ·
            refine ⟨11087713019552375524437713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7391808679701583682958475 11087713019552375524437713)
            ·
              refine ⟨8315784764664281643328285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11087713019552375524437713 8315784764664281643328285)
              ·
                refine ⟨3118419286749105616248107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8315784764664281643328285 3118419286749105616248107)
                ·
                  refine ⟨4677628930123658424372161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3118419286749105616248107 4677628930123658424372161)
                  ·
                    refine ⟨3508221697592743818279121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4677628930123658424372161 3508221697592743818279121)
                    ·
                      refine ⟨2631166273194557863709341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3508221697592743818279121 2631166273194557863709341)
                      ·
                        rfl

theorem cell23_5124178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 3, 1, 2, 2].length) (baseStart_5124178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5124178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5124178 prefixEnd_5124178 := by exact prefixLift 5124178
  have htrace : WordTrace (prefixWord ++ tailWord_5124178) baseStart_5124178 baseEnd_5124178 := by
    simpa [prefixWord, tailWord_5124178, baseEnd_5124178] using wordTrace_append hprefix tailTrace_5124178
  have hstable : (prefixWord ++ tailWord_5124178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5124178).length < 2 ^ (prefixWord ++ tailWord_5124178).sum := by decide
  have hdescent : baseEnd_5124178 < baseStart_5124178 := by decide
  rcases family_descends (prefixWord ++ tailWord_5124178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5124210 : List Nat := [3, 2, 1, 2, 2, 2, 2, 1, 2, 6]
def baseStart_5124210 : Nat := 118140960795 + 5124210 * 2 ^ 59
def prefixEnd_5124210 : Nat := 4983230072969 + 3 ^ 40 * 5124210 * 2
def baseEnd_5124210 : Nat := 877060901525167246169731

theorem tailTrace_5124210 : CollatzResearch.WordTrace tailWord_5124210 prefixEnd_5124210 877060901525167246169731 := by
  unfold tailWord_5124210
  simp only [CollatzResearch.WordTrace]
  refine ⟨46723823191467447559806521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124596861843913193492817389 46723823191467447559806521)
  ·
    refine ⟨35042867393600585669854891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46723823191467447559806521 35042867393600585669854891)
    ·
      refine ⟨52564301090400878504782337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35042867393600585669854891 52564301090400878504782337)
      ·
        refine ⟨39423225817800658878586753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52564301090400878504782337 39423225817800658878586753)
        ·
          refine ⟨29567419363350494158940065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39423225817800658878586753 29567419363350494158940065)
          ·
            refine ⟨22175564522512870619205049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29567419363350494158940065 22175564522512870619205049)
            ·
              refine ⟨16631673391884652964403787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22175564522512870619205049 16631673391884652964403787)
              ·
                refine ⟨24947510087826979446605681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16631673391884652964403787 24947510087826979446605681)
                ·
                  refine ⟨18710632565870234584954261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24947510087826979446605681 18710632565870234584954261)
                  ·
                    refine ⟨877060901525167246169731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18710632565870234584954261 877060901525167246169731)
                    ·
                      rfl

theorem cell23_5124210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 2, 6].length) (baseStart_5124210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5124210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5124210 prefixEnd_5124210 := by exact prefixLift 5124210
  have htrace : WordTrace (prefixWord ++ tailWord_5124210) baseStart_5124210 baseEnd_5124210 := by
    simpa [prefixWord, tailWord_5124210, baseEnd_5124210] using wordTrace_append hprefix tailTrace_5124210
  have hstable : (prefixWord ++ tailWord_5124210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5124210).length < 2 ^ (prefixWord ++ tailWord_5124210).sum := by decide
  have hdescent : baseEnd_5124210 < baseStart_5124210 := by decide
  rcases family_descends (prefixWord ++ tailWord_5124210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5124234 : List Nat := [3, 1, 2, 3, 1, 2, 1, 2, 4, 2, 2]
def baseStart_5124234 : Nat := 118140960795 + 5124234 * 2 ^ 59
def prefixEnd_5124234 : Nat := 4983230072969 + 3 ^ 40 * 5124234 * 2
def baseEnd_5124234 : Nat := 2631195028111209644609083

theorem tailTrace_5124234 : CollatzResearch.WordTrace tailWord_5124234 prefixEnd_5124234 2631195028111209644609083 := by
  unfold tailWord_5124234
  simp only [CollatzResearch.WordTrace]
  refine ⟨46724042029445710584524939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124597445411855228225399837 46724042029445710584524939)
  ·
    refine ⟨70086063044168565876787409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46724042029445710584524939 70086063044168565876787409)
    ·
      refine ⟨52564547283126424407590557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70086063044168565876787409 52564547283126424407590557)
      ·
        refine ⟨19711705231172409152846459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52564547283126424407590557 19711705231172409152846459)
        ·
          refine ⟨29567557846758613729269689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19711705231172409152846459 29567557846758613729269689)
          ·
            refine ⟨22175668385068960296952267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29567557846758613729269689 22175668385068960296952267)
            ·
              refine ⟨33263502577603440445428401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22175668385068960296952267 33263502577603440445428401)
              ·
                refine ⟨24947626933202580334071301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33263502577603440445428401 24947626933202580334071301)
                ·
                  refine ⟨4677680049975483812638369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24947626933202580334071301 4677680049975483812638369)
                  ·
                    refine ⟨3508260037481612859478777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4677680049975483812638369 3508260037481612859478777)
                    ·
                      refine ⟨2631195028111209644609083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3508260037481612859478777 2631195028111209644609083)
                      ·
                        rfl

theorem cell23_5124234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 4, 2, 2].length) (baseStart_5124234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5124234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5124234 prefixEnd_5124234 := by exact prefixLift 5124234
  have htrace : WordTrace (prefixWord ++ tailWord_5124234) baseStart_5124234 baseEnd_5124234 := by
    simpa [prefixWord, tailWord_5124234, baseEnd_5124234] using wordTrace_append hprefix tailTrace_5124234
  have hstable : (prefixWord ++ tailWord_5124234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5124234).length < 2 ^ (prefixWord ++ tailWord_5124234).sum := by decide
  have hdescent : baseEnd_5124234 < baseStart_5124234 := by decide
  rcases family_descends (prefixWord ++ tailWord_5124234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5124246 : List Nat := [5, 3, 2, 1, 1, 1, 3, 2, 1, 2, 2]
def baseStart_5124246 : Nat := 118140960795 + 5124246 * 2 ^ 59
def prefixEnd_5124246 : Nat := 4983230072969 + 3 ^ 40 * 5124246 * 2
def baseEnd_5124246 : Nat := 2631201189879063597659029

theorem tailTrace_5124246 : CollatzResearch.WordTrace tailWord_5124246 prefixEnd_5124246 2631201189879063597659029 := by
  unfold tailWord_5124246
  simp only [CollatzResearch.WordTrace]
  refine ⟨11681037862108710524221037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 124597737195826245591691061 11681037862108710524221037)
  ·
    refine ⟨4380389198290766446582889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11681037862108710524221037 4380389198290766446582889)
    ·
      refine ⟨3285291898718074834937167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4380389198290766446582889 3285291898718074834937167)
      ·
        refine ⟨4927937848077112252405751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3285291898718074834937167 4927937848077112252405751)
        ·
          refine ⟨7391906772115668378608627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4927937848077112252405751 7391906772115668378608627)
          ·
            refine ⟨11087860158173502567912941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7391906772115668378608627 11087860158173502567912941)
            ·
              refine ⟨4157947559315063462967353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11087860158173502567912941 4157947559315063462967353)
              ·
                refine ⟨3118460669486297597225515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4157947559315063462967353 3118460669486297597225515)
                ·
                  refine ⟨4677691004229446395838273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3118460669486297597225515 4677691004229446395838273)
                  ·
                    refine ⟨3508268253172084796878705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4677691004229446395838273 3508268253172084796878705)
                    ·
                      refine ⟨2631201189879063597659029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3508268253172084796878705 2631201189879063597659029)
                      ·
                        rfl

theorem cell23_5124246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_5124246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5124246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5124246 prefixEnd_5124246 := by exact prefixLift 5124246
  have htrace : WordTrace (prefixWord ++ tailWord_5124246) baseStart_5124246 baseEnd_5124246 := by
    simpa [prefixWord, tailWord_5124246, baseEnd_5124246] using wordTrace_append hprefix tailTrace_5124246
  have hstable : (prefixWord ++ tailWord_5124246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5124246).length < 2 ^ (prefixWord ++ tailWord_5124246).sum := by decide
  have hdescent : baseEnd_5124246 < baseStart_5124246 := by decide
  rcases family_descends (prefixWord ++ tailWord_5124246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5124257 : List Nat := [1, 2, 3, 3, 1, 4, 1, 1, 7]
def baseStart_5124257 : Nat := 118140960795 + 5124257 * 2 ^ 59
def prefixEnd_5124257 : Nat := 4983230072969 + 3 ^ 40 * 5124257 * 2
def baseEnd_5124257 : Nat := 292356315351807006069053

theorem tailTrace_5124257 : CollatzResearch.WordTrace tailWord_5124257 prefixEnd_5124257 292356315351807006069053 := by
  unfold tailWord_5124257
  simp only [CollatzResearch.WordTrace]
  refine ⟨186897006996699517266187025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124598004664466344844124683 186897006996699517266187025)
  ·
    refine ⟨140172755247524637949640269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186897006996699517266187025 140172755247524637949640269)
    ·
      refine ⟨52564783217821739231115101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140172755247524637949640269 52564783217821739231115101)
      ·
        refine ⟨19711793706683152211668163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52564783217821739231115101 19711793706683152211668163)
        ·
          refine ⟨29567690560024728317502245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19711793706683152211668163 29567690560024728317502245)
          ·
            refine ⟨5543941980004636559531671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29567690560024728317502245 5543941980004636559531671)
            ·
              refine ⟨8315912970006954839297507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5543941980004636559531671 8315912970006954839297507)
              ·
                refine ⟨12473869455010432258946261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8315912970006954839297507 12473869455010432258946261)
                ·
                  refine ⟨292356315351807006069053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12473869455010432258946261 292356315351807006069053)
                  ·
                    rfl

theorem cell23_5124257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 1, 7].length) (baseStart_5124257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5124257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5124257 prefixEnd_5124257 := by exact prefixLift 5124257
  have htrace : WordTrace (prefixWord ++ tailWord_5124257) baseStart_5124257 baseEnd_5124257 := by
    simpa [prefixWord, tailWord_5124257, baseEnd_5124257] using wordTrace_append hprefix tailTrace_5124257
  have hstable : (prefixWord ++ tailWord_5124257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5124257).length < 2 ^ (prefixWord ++ tailWord_5124257).sum := by decide
  have hdescent : baseEnd_5124257 < baseStart_5124257 := by decide
  rcases family_descends (prefixWord ++ tailWord_5124257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5124381 : List Nat := [1, 4, 2, 3, 2, 1, 3, 1, 6]
def baseStart_5124381 : Nat := 118140960795 + 5124381 * 2 ^ 59
def prefixEnd_5124381 : Nat := 4983230072969 + 3 ^ 40 * 5124381 * 2
def baseEnd_5124381 : Nat := 292363389974157841052323

theorem tailTrace_5124381 : CollatzResearch.WordTrace tailWord_5124381 prefixEnd_5124381 292363389974157841052323 := by
  unfold tailWord_5124381
  simp only [CollatzResearch.WordTrace]
  refine ⟨186901529648250286443700997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124601019765500190962467331 186901529648250286443700997)
  ·
    refine ⟨35044036809046928708193937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 186901529648250286443700997 35044036809046928708193937)
    ·
      refine ⟨26283027606785196531145453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35044036809046928708193937 26283027606785196531145453)
      ·
        refine ⟨9856135352544448699179545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26283027606785196531145453 9856135352544448699179545)
        ·
          refine ⟨7392101514408336524384659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9856135352544448699179545 7392101514408336524384659)
          ·
            refine ⟨11088152271612504786576989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7392101514408336524384659 11088152271612504786576989)
            ·
              refine ⟨4158057101854689294966371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11088152271612504786576989 4158057101854689294966371)
              ·
                refine ⟨6237085652782033942449557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4158057101854689294966371 6237085652782033942449557)
                ·
                  refine ⟨292363389974157841052323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6237085652782033942449557 292363389974157841052323)
                  ·
                    rfl

theorem cell23_5124381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 3, 1, 6].length) (baseStart_5124381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5124381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5124381 prefixEnd_5124381 := by exact prefixLift 5124381
  have htrace : WordTrace (prefixWord ++ tailWord_5124381) baseStart_5124381 baseEnd_5124381 := by
    simpa [prefixWord, tailWord_5124381, baseEnd_5124381] using wordTrace_append hprefix tailTrace_5124381
  have hstable : (prefixWord ++ tailWord_5124381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5124381).length < 2 ^ (prefixWord ++ tailWord_5124381).sum := by decide
  have hdescent : baseEnd_5124381 < baseStart_5124381 := by decide
  rcases family_descends (prefixWord ++ tailWord_5124381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5124384 : List Nat := [2, 1, 1, 5, 2, 1, 1, 2, 1, 5, 2]
def baseStart_5124384 : Nat := 118140960795 + 5124384 * 2 ^ 59
def prefixEnd_5124384 : Nat := 4983230072969 + 3 ^ 40 * 5124384 * 2
def baseEnd_5124384 : Nat := 2631272050209384057733393

theorem tailTrace_5124384 : CollatzResearch.WordTrace tailWord_5124384 prefixEnd_5124384 2631272050209384057733393 := by
  unfold tailWord_5124384
  simp only [CollatzResearch.WordTrace]
  refine ⟨93450819533619708978030103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124601092711492945304040137 93450819533619708978030103)
  ·
    refine ⟨140176229300429563467045155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93450819533619708978030103 140176229300429563467045155)
    ·
      refine ⟨210264343950644345200567733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140176229300429563467045155 210264343950644345200567733)
      ·
        refine ⟨19712282245372907362553225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 210264343950644345200567733 19712282245372907362553225)
        ·
          refine ⟨14784211684029680521914919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19712282245372907362553225 14784211684029680521914919)
          ·
            refine ⟨22176317526044520782872379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14784211684029680521914919 22176317526044520782872379)
            ·
              refine ⟨33264476289066781174308569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22176317526044520782872379 33264476289066781174308569)
              ·
                refine ⟨24948357216800085880731427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33264476289066781174308569 24948357216800085880731427)
                ·
                  refine ⟨37422535825200128821097141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24948357216800085880731427 37422535825200128821097141)
                  ·
                    refine ⟨3508362733612512076977857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37422535825200128821097141 3508362733612512076977857)
                    ·
                      refine ⟨2631272050209384057733393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3508362733612512076977857 2631272050209384057733393)
                      ·
                        rfl

theorem cell23_5124384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 1, 5, 2].length) (baseStart_5124384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5124384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5124384 prefixEnd_5124384 := by exact prefixLift 5124384
  have htrace : WordTrace (prefixWord ++ tailWord_5124384) baseStart_5124384 baseEnd_5124384 := by
    simpa [prefixWord, tailWord_5124384, baseEnd_5124384] using wordTrace_append hprefix tailTrace_5124384
  have hstable : (prefixWord ++ tailWord_5124384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5124384).length < 2 ^ (prefixWord ++ tailWord_5124384).sum := by decide
  have hdescent : baseEnd_5124384 < baseStart_5124384 := by decide
  rcases family_descends (prefixWord ++ tailWord_5124384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5124448 : List Nat := [2, 1, 1, 3, 6, 1, 1, 2, 1, 1, 4]
def baseStart_5124448 : Nat := 118140960795 + 5124448 * 2 ^ 59
def prefixEnd_5124448 : Nat := 4983230072969 + 3 ^ 40 * 5124448 * 2
def baseEnd_5124448 : Nat := 2631304912971271807333099

theorem tailTrace_5124448 : CollatzResearch.WordTrace tailWord_5124448 prefixEnd_5124448 2631304912971271807333099 := by
  unfold tailWord_5124448
  simp only [CollatzResearch.WordTrace]
  refine ⟨93451986669503778443194999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124602648892671704590926665 93451986669503778443194999)
  ·
    refine ⟨140177980004255667664792499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93451986669503778443194999 140177980004255667664792499)
    ·
      refine ⟨210266970006383501497188749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140177980004255667664792499 210266970006383501497188749)
      ·
        refine ⟨78850113752393813061445781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 210266970006383501497188749 78850113752393813061445781)
        ·
          refine ⟨3696099082143459987255271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 78850113752393813061445781 3696099082143459987255271)
          ·
            refine ⟨5544148623215189980882907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3696099082143459987255271 5544148623215189980882907)
            ·
              refine ⟨8316222934822784971324361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5544148623215189980882907 8316222934822784971324361)
              ·
                refine ⟨6237167201117088728493271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8316222934822784971324361 6237167201117088728493271)
                ·
                  refine ⟨9355750801675633092739907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6237167201117088728493271 9355750801675633092739907)
                  ·
                    refine ⟨14033626202513449639109861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9355750801675633092739907 14033626202513449639109861)
                    ·
                      refine ⟨2631304912971271807333099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14033626202513449639109861 2631304912971271807333099)
                      ·
                        rfl

theorem cell23_5124448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 2, 1, 1, 4].length) (baseStart_5124448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5124448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5124448 prefixEnd_5124448 := by exact prefixLift 5124448
  have htrace : WordTrace (prefixWord ++ tailWord_5124448) baseStart_5124448 baseEnd_5124448 := by
    simpa [prefixWord, tailWord_5124448, baseEnd_5124448] using wordTrace_append hprefix tailTrace_5124448
  have hstable : (prefixWord ++ tailWord_5124448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5124448).length < 2 ^ (prefixWord ++ tailWord_5124448).sum := by decide
  have hdescent : baseEnd_5124448 < baseStart_5124448 := by decide
  rcases family_descends (prefixWord ++ tailWord_5124448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5124464 : List Nat := [2, 1, 1, 1, 4, 4, 1, 2, 1, 3, 3]
def baseStart_5124464 : Nat := 118140960795 + 5124464 * 2 ^ 59
def prefixEnd_5124464 : Nat := 4983230072969 + 3 ^ 40 * 5124464 * 2
def baseEnd_5124464 : Nat := 2631313128661743744733025

theorem tailTrace_5124464 : CollatzResearch.WordTrace tailWord_5124464 prefixEnd_5124464 2631313128661743744733025 := by
  unfold tailWord_5124464
  simp only [CollatzResearch.WordTrace]
  refine ⟨93452278453474795809486223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124603037937966394412648297 93452278453474795809486223)
  ·
    refine ⟨140178417680212193714229335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93452278453474795809486223 140178417680212193714229335)
    ·
      refine ⟨210267626520318290571344003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140178417680212193714229335 210267626520318290571344003)
      ·
        refine ⟨315401439780477435857016005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210267626520318290571344003 315401439780477435857016005)
        ·
          refine ⟨59137769958839519223190501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 315401439780477435857016005 59137769958839519223190501)
          ·
            refine ⟨11088331867282409854348219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59137769958839519223190501 11088331867282409854348219)
            ·
              refine ⟨16632497800923614781522329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11088331867282409854348219 16632497800923614781522329)
              ·
                refine ⟨12474373350692711086141747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16632497800923614781522329 12474373350692711086141747)
                ·
                  refine ⟨18711560026039066629212621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12474373350692711086141747 18711560026039066629212621)
                  ·
                    refine ⟨7016835009764649985954733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18711560026039066629212621 7016835009764649985954733)
                    ·
                      refine ⟨2631313128661743744733025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7016835009764649985954733 2631313128661743744733025)
                      ·
                        rfl

theorem cell23_5124464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 2, 1, 3, 3].length) (baseStart_5124464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5124464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5124464 prefixEnd_5124464 := by exact prefixLift 5124464
  have htrace : WordTrace (prefixWord ++ tailWord_5124464) baseStart_5124464 baseEnd_5124464 := by
    simpa [prefixWord, tailWord_5124464, baseEnd_5124464] using wordTrace_append hprefix tailTrace_5124464
  have hstable : (prefixWord ++ tailWord_5124464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5124464).length < 2 ^ (prefixWord ++ tailWord_5124464).sum := by decide
  have hdescent : baseEnd_5124464 < baseStart_5124464 := by decide
  rcases family_descends (prefixWord ++ tailWord_5124464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5124474 : List Nat := [3, 1, 1, 1, 1, 1, 2, 1, 7, 3, 2]
def baseStart_5124474 : Nat := 118140960795 + 5124474 * 2 ^ 59
def prefixEnd_5124474 : Nat := 4983230072969 + 3 ^ 40 * 5124474 * 2
def baseEnd_5124474 : Nat := 2631318263468288705607979

theorem tailTrace_5124474 : CollatzResearch.WordTrace tailWord_5124474 prefixEnd_5124474 2631318263468288705607979 := by
  unfold tailWord_5124474
  simp only [CollatzResearch.WordTrace]
  refine ⟨46726230409228340831709119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124603281091275575551224317 46726230409228340831709119)
  ·
    refine ⟨70089345613842511247563679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46726230409228340831709119 70089345613842511247563679)
    ·
      refine ⟨105134018420763766871345519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70089345613842511247563679 105134018420763766871345519)
      ·
        refine ⟨157701027631145650307018279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105134018420763766871345519 157701027631145650307018279)
        ·
          refine ⟨236551541446718475460527419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157701027631145650307018279 236551541446718475460527419)
          ·
            refine ⟨354827312170077713190791129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236551541446718475460527419 354827312170077713190791129)
            ·
              refine ⟨266120484127558284893093347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 354827312170077713190791129 266120484127558284893093347)
              ·
                refine ⟨399180726191337427339640021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 266120484127558284893093347 399180726191337427339640021)
                ·
                  refine ⟨9355798270109470953272813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 399180726191337427339640021 9355798270109470953272813)
                  ·
                    refine ⟨3508424351291051607477305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9355798270109470953272813 3508424351291051607477305)
                    ·
                      refine ⟨2631318263468288705607979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3508424351291051607477305 2631318263468288705607979)
                      ·
                        rfl

theorem cell23_5124474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 7, 3, 2].length) (baseStart_5124474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5124474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5124474 prefixEnd_5124474 := by exact prefixLift 5124474
  have htrace : WordTrace (prefixWord ++ tailWord_5124474) baseStart_5124474 baseEnd_5124474 := by
    simpa [prefixWord, tailWord_5124474, baseEnd_5124474] using wordTrace_append hprefix tailTrace_5124474
  have hstable : (prefixWord ++ tailWord_5124474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5124474).length < 2 ^ (prefixWord ++ tailWord_5124474).sum := by decide
  have hdescent : baseEnd_5124474 < baseStart_5124474 := by decide
  rcases family_descends (prefixWord ++ tailWord_5124474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5124487 : List Nat := [1, 1, 4, 2, 2, 1, 1, 1, 1, 5, 4]
def baseStart_5124487 : Nat := 118140960795 + 5124487 * 2 ^ 59
def prefixEnd_5124487 : Nat := 4983230072969 + 3 ^ 40 * 5124487 * 2
def baseEnd_5124487 : Nat := 2631324938716797154745419

theorem tailTrace_5124487 : CollatzResearch.WordTrace tailWord_5124487 prefixEnd_5124487 2631324938716797154745419 := by
  unfold tailWord_5124487
  simp only [CollatzResearch.WordTrace]
  refine ⟨186905395785866266547059715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124603597190577511031373143 186905395785866266547059715)
  ·
    refine ⟨280358093678799399820589573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186905395785866266547059715 280358093678799399820589573)
    ·
      refine ⟨52567142564774887466360545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 280358093678799399820589573 52567142564774887466360545)
      ·
        refine ⟨39425356923581165599770409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52567142564774887466360545 39425356923581165599770409)
        ·
          refine ⟨29569017692685874199827807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39425356923581165599770409 29569017692685874199827807)
          ·
            refine ⟨44353526539028811299741711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29569017692685874199827807 44353526539028811299741711)
            ·
              refine ⟨66530289808543216949612567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44353526539028811299741711 66530289808543216949612567)
              ·
                refine ⟨99795434712814825424418851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66530289808543216949612567 99795434712814825424418851)
                ·
                  refine ⟨149693152069222238136628277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99795434712814825424418851 149693152069222238136628277)
                  ·
                    refine ⟨14033733006489584825308901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 149693152069222238136628277 14033733006489584825308901)
                    ·
                      refine ⟨2631324938716797154745419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14033733006489584825308901 2631324938716797154745419)
                      ·
                        rfl

theorem cell23_5124487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_5124487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5124487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5124487 prefixEnd_5124487 := by exact prefixLift 5124487
  have htrace : WordTrace (prefixWord ++ tailWord_5124487) baseStart_5124487 baseEnd_5124487 := by
    simpa [prefixWord, tailWord_5124487, baseEnd_5124487] using wordTrace_append hprefix tailTrace_5124487
  have hstable : (prefixWord ++ tailWord_5124487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5124487).length < 2 ^ (prefixWord ++ tailWord_5124487).sum := by decide
  have hdescent : baseEnd_5124487 < baseStart_5124487 := by decide
  rcases family_descends (prefixWord ++ tailWord_5124487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5124517 : List Nat := [1, 3, 1, 2, 1, 1, 3, 2, 1, 4, 4]
def baseStart_5124517 : Nat := 118140960795 + 5124517 * 2 ^ 59
def prefixEnd_5124517 : Nat := 4983230072969 + 3 ^ 40 * 5124517 * 2
def baseEnd_5124517 : Nat := 2631340343136432037370281

theorem tailTrace_5124517 : CollatzResearch.WordTrace tailWord_5124517 prefixEnd_5124517 2631340343136432037370281 := by
  unfold tailWord_5124517
  simp only [CollatzResearch.WordTrace]
  refine ⟨186906489975757581670651805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124604326650505054447101203 186906489975757581670651805)
  ·
    refine ⟨70089933740909093126494427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186906489975757581670651805 70089933740909093126494427)
    ·
      refine ⟨105134900611363639689741641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70089933740909093126494427 105134900611363639689741641)
      ·
        refine ⟨78851175458522729767306231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105134900611363639689741641 78851175458522729767306231)
        ·
          refine ⟨118276763187784094650959347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78851175458522729767306231 118276763187784094650959347)
          ·
            refine ⟨177415144781676141976439021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118276763187784094650959347 177415144781676141976439021)
            ·
              refine ⟨66530679293128553241164633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 177415144781676141976439021 66530679293128553241164633)
              ·
                refine ⟨49898009469846414930873475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66530679293128553241164633 49898009469846414930873475)
                ·
                  refine ⟨74847014204769622396310213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49898009469846414930873475 74847014204769622396310213)
                  ·
                    refine ⟨14033815163394304199308165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 74847014204769622396310213 14033815163394304199308165)
                    ·
                      refine ⟨2631340343136432037370281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14033815163394304199308165 2631340343136432037370281)
                      ·
                        rfl

theorem cell23_5124517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 4, 4].length) (baseStart_5124517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5124517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5124517 prefixEnd_5124517 := by exact prefixLift 5124517
  have htrace : WordTrace (prefixWord ++ tailWord_5124517) baseStart_5124517 baseEnd_5124517 := by
    simpa [prefixWord, tailWord_5124517, baseEnd_5124517] using wordTrace_append hprefix tailTrace_5124517
  have hstable : (prefixWord ++ tailWord_5124517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5124517).length < 2 ^ (prefixWord ++ tailWord_5124517).sum := by decide
  have hdescent : baseEnd_5124517 < baseStart_5124517 := by decide
  rcases family_descends (prefixWord ++ tailWord_5124517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5124525 : List Nat := [1, 5, 2, 2, 2, 1, 1, 3, 1, 3, 2]
def baseStart_5124525 : Nat := 118140960795 + 5124525 * 2 ^ 59
def prefixEnd_5124525 : Nat := 4983230072969 + 3 ^ 40 * 5124525 * 2
def baseEnd_5124525 : Nat := 2631344450981668006070245

theorem tailTrace_5124525 : CollatzResearch.WordTrace tailWord_5124525 prefixEnd_5124525 2631344450981668006070245 := by
  unfold tailWord_5124525
  simp only [CollatzResearch.WordTrace]
  refine ⟨186906781759728599036943029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124604521173152399357962019 186906781759728599036943029)
  ·
    refine ⟨17522510789974556159713409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 186906781759728599036943029 17522510789974556159713409)
    ·
      refine ⟨13141883092480917119785057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17522510789974556159713409 13141883092480917119785057)
      ·
        refine ⟨9856412319360687839838793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13141883092480917119785057 9856412319360687839838793)
        ·
          refine ⟨7392309239520515879879095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9856412319360687839838793 7392309239520515879879095)
          ·
            refine ⟨11088463859280773819818643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7392309239520515879879095 11088463859280773819818643)
            ·
              refine ⟨16632695788921160729727965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11088463859280773819818643 16632695788921160729727965)
              ·
                refine ⟨6237260920845435273647987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16632695788921160729727965 6237260920845435273647987)
                ·
                  refine ⟨9355891381268152910471981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6237260920845435273647987 9355891381268152910471981)
                  ·
                    refine ⟨3508459267975557341426993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9355891381268152910471981 3508459267975557341426993)
                    ·
                      refine ⟨2631344450981668006070245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3508459267975557341426993 2631344450981668006070245)
                      ·
                        rfl

theorem cell23_5124525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_5124525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5124525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5124525 prefixEnd_5124525 := by exact prefixLift 5124525
  have htrace : WordTrace (prefixWord ++ tailWord_5124525) baseStart_5124525 baseEnd_5124525 := by
    simpa [prefixWord, tailWord_5124525, baseEnd_5124525] using wordTrace_append hprefix tailTrace_5124525
  have hstable : (prefixWord ++ tailWord_5124525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5124525).length < 2 ^ (prefixWord ++ tailWord_5124525).sum := by decide
  have hdescent : baseEnd_5124525 < baseStart_5124525 := by decide
  rcases family_descends (prefixWord ++ tailWord_5124525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5124554 : List Nat := [3, 1, 2, 1, 2, 2, 1, 3, 2, 3, 3]
def baseStart_5124554 : Nat := 118140960795 + 5124554 * 2 ^ 59
def prefixEnd_5124554 : Nat := 4983230072969 + 3 ^ 40 * 5124554 * 2
def baseEnd_5124554 : Nat := 2631359341920648392607611

theorem tailTrace_5124554 : CollatzResearch.WordTrace tailWord_5124554 prefixEnd_5124554 2631359341920648392607611 := by
  unfold tailWord_5124554
  simp only [CollatzResearch.WordTrace]
  refine ⟨46726959869155884247437179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124605226317749024659832477 46726959869155884247437179)
  ·
    refine ⟨70090439803733826371155769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46726959869155884247437179 70090439803733826371155769)
    ·
      refine ⟨52567829852800369778366827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70090439803733826371155769 52567829852800369778366827)
      ·
        refine ⟨78851744779200554667550241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52567829852800369778366827 78851744779200554667550241)
        ·
          refine ⟨59138808584400416000662681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78851744779200554667550241 59138808584400416000662681)
          ·
            refine ⟨44354106438300312000497011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59138808584400416000662681 44354106438300312000497011)
            ·
              refine ⟨66531159657450468000745517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44354106438300312000497011 66531159657450468000745517)
              ·
                refine ⟨24949184871543925500279569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66531159657450468000745517 24949184871543925500279569)
                ·
                  refine ⟨18711888653657944125209677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24949184871543925500279569 18711888653657944125209677)
                  ·
                    refine ⟨7016958245121729046953629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18711888653657944125209677 7016958245121729046953629)
                    ·
                      refine ⟨2631359341920648392607611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7016958245121729046953629 2631359341920648392607611)
                      ·
                        rfl

theorem cell23_5124554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 2, 3, 3].length) (baseStart_5124554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5124554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5124554 prefixEnd_5124554 := by exact prefixLift 5124554
  have htrace : WordTrace (prefixWord ++ tailWord_5124554) baseStart_5124554 baseEnd_5124554 := by
    simpa [prefixWord, tailWord_5124554, baseEnd_5124554] using wordTrace_append hprefix tailTrace_5124554
  have hstable : (prefixWord ++ tailWord_5124554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5124554).length < 2 ^ (prefixWord ++ tailWord_5124554).sum := by decide
  have hdescent : baseEnd_5124554 < baseStart_5124554 := by decide
  rcases family_descends (prefixWord ++ tailWord_5124554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5124567 : List Nat := [1, 1, 3, 2, 1, 1, 1, 1, 5, 2, 5]
def baseStart_5124567 : Nat := 118140960795 + 5124567 * 2 ^ 59
def prefixEnd_5124567 : Nat := 4983230072969 + 3 ^ 40 * 5124567 * 2
def baseEnd_5124567 : Nat := 2631366017169156841745051

theorem tailTrace_5124567 : CollatzResearch.WordTrace tailWord_5124567 prefixEnd_5124567 2631366017169156841745051 := by
  unfold tailWord_5124567
  simp only [CollatzResearch.WordTrace]
  refine ⟨186908313625576440209971955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124605542417050960139981303 186908313625576440209971955)
  ·
    refine ⟨280362470438364660314957933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186908313625576440209971955 280362470438364660314957933)
    ·
      refine ⟨105135926414386747618109225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 280362470438364660314957933 105135926414386747618109225)
      ·
        refine ⟨78851944810790060713581919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105135926414386747618109225 78851944810790060713581919)
        ·
          refine ⟨118277917216185091070372879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78851944810790060713581919 118277917216185091070372879)
          ·
            refine ⟨177416875824277636605559319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118277917216185091070372879 177416875824277636605559319)
            ·
              refine ⟨266125313736416454908338979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177416875824277636605559319 266125313736416454908338979)
              ·
                refine ⟨399187970604624682362508469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 266125313736416454908338979 399187970604624682362508469)
                ·
                  refine ⟨37423872244183563971485169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 399187970604624682362508469 37423872244183563971485169)
                  ·
                    refine ⟨28067904183137672978613877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37423872244183563971485169 28067904183137672978613877)
                    ·
                      refine ⟨2631366017169156841745051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28067904183137672978613877 2631366017169156841745051)
                      ·
                        rfl

theorem cell23_5124567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 2, 5].length) (baseStart_5124567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5124567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5124567 prefixEnd_5124567 := by exact prefixLift 5124567
  have htrace : WordTrace (prefixWord ++ tailWord_5124567) baseStart_5124567 baseEnd_5124567 := by
    simpa [prefixWord, tailWord_5124567, baseEnd_5124567] using wordTrace_append hprefix tailTrace_5124567
  have hstable : (prefixWord ++ tailWord_5124567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5124567).length < 2 ^ (prefixWord ++ tailWord_5124567).sum := by decide
  have hdescent : baseEnd_5124567 < baseStart_5124567 := by decide
  rcases family_descends (prefixWord ++ tailWord_5124567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5124617 : List Nat := [1, 2, 1, 1, 3, 1, 2, 2, 10]
def baseStart_5124617 : Nat := 118140960795 + 5124617 * 2 ^ 59
def prefixEnd_5124617 : Nat := 4983230072969 + 3 ^ 40 * 5124617 * 2
def baseEnd_5124617 : Nat := 292376854577986849568869

theorem tailTrace_5124617 : CollatzResearch.WordTrace tailWord_5124617 prefixEnd_5124617 292376854577986849568869 := by
  unfold tailWord_5124617
  simp only [CollatzResearch.WordTrace]
  refine ⟨186910137275395298749292105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124606758183596865832861403 186910137275395298749292105)
  ·
    refine ⟨140182602956546474061969079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186910137275395298749292105 140182602956546474061969079)
    ·
      refine ⟨210273904434819711092953619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140182602956546474061969079 210273904434819711092953619)
      ·
        refine ⟨315410856652229566639430429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210273904434819711092953619 315410856652229566639430429)
        ·
          refine ⟨118279071244586087489786411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 315410856652229566639430429 118279071244586087489786411)
          ·
            refine ⟨177418606866879131234679617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118279071244586087489786411 177418606866879131234679617)
            ·
              refine ⟨133063955150159348426009713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 177418606866879131234679617 133063955150159348426009713)
              ·
                refine ⟨99797966362619511319507285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133063955150159348426009713 99797966362619511319507285)
                ·
                  refine ⟨292376854577986849568869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 99797966362619511319507285 292376854577986849568869)
                  ·
                    rfl

theorem cell23_5124617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 10].length) (baseStart_5124617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5124617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5124617 prefixEnd_5124617 := by exact prefixLift 5124617
  have htrace : WordTrace (prefixWord ++ tailWord_5124617) baseStart_5124617 baseEnd_5124617 := by
    simpa [prefixWord, tailWord_5124617, baseEnd_5124617] using wordTrace_append hprefix tailTrace_5124617
  have hstable : (prefixWord ++ tailWord_5124617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5124617).length < 2 ^ (prefixWord ++ tailWord_5124617).sum := by decide
  have hdescent : baseEnd_5124617 < baseStart_5124617 := by decide
  rcases family_descends (prefixWord ++ tailWord_5124617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5124628 : List Nat := [2, 4, 3, 1, 1, 1, 1, 3, 2, 1, 4]
def baseStart_5124628 : Nat := 118140960795 + 5124628 * 2 ^ 59
def prefixEnd_5124628 : Nat := 4983230072969 + 3 ^ 40 * 5124628 * 2
def baseEnd_5124628 : Nat := 2631397339489081103082271

theorem tailTrace_5124628 : CollatzResearch.WordTrace tailWord_5124628 prefixEnd_5124628 2631397339489081103082271 := by
  unfold tailWord_5124628
  simp only [CollatzResearch.WordTrace]
  refine ⟨93455269239177723813971269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124607025652236965085295025 93455269239177723813971269)
  ·
    refine ⟨17522862982345823215119613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93455269239177723813971269 17522862982345823215119613)
    ·
      refine ⟨6571073618379683705669855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17522862982345823215119613 6571073618379683705669855)
      ·
        refine ⟨9856610427569525558504783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6571073618379683705669855 9856610427569525558504783)
        ·
          refine ⟨14784915641354288337757175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9856610427569525558504783 14784915641354288337757175)
          ·
            refine ⟨22177373462031432506635763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14784915641354288337757175 22177373462031432506635763)
            ·
              refine ⟨33266060193047148759953645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22177373462031432506635763 33266060193047148759953645)
              ·
                refine ⟨12474772572392680784982617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33266060193047148759953645 12474772572392680784982617)
                ·
                  refine ⟨9356079429294510588736963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12474772572392680784982617 9356079429294510588736963)
                  ·
                    refine ⟨14034119143941765883105445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9356079429294510588736963 14034119143941765883105445)
                    ·
                      refine ⟨2631397339489081103082271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14034119143941765883105445 2631397339489081103082271)
                      ·
                        rfl

theorem cell23_5124628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_5124628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5124628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5124628 prefixEnd_5124628 := by exact prefixLift 5124628
  have htrace : WordTrace (prefixWord ++ tailWord_5124628) baseStart_5124628 baseEnd_5124628 := by
    simpa [prefixWord, tailWord_5124628, baseEnd_5124628] using wordTrace_append hprefix tailTrace_5124628
  have hstable : (prefixWord ++ tailWord_5124628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5124628).length < 2 ^ (prefixWord ++ tailWord_5124628).sum := by decide
  have hdescent : baseEnd_5124628 < baseStart_5124628 := by decide
  rcases family_descends (prefixWord ++ tailWord_5124628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5124648 : List Nat := [2, 1, 5, 2, 1, 1, 2, 2, 2, 2, 3]
def baseStart_5124648 : Nat := 118140960795 + 5124648 * 2 ^ 59
def prefixEnd_5124648 : Nat := 4983230072969 + 3 ^ 40 * 5124648 * 2
def baseEnd_5124648 : Nat := 2631407609102171024832179

theorem tailTrace_5124648 : CollatzResearch.WordTrace tailWord_5124648 prefixEnd_5124648 2631407609102171024832179 := by
  unfold tailWord_5124648
  simp only [CollatzResearch.WordTrace]
  refine ⟨93455633969141495521835299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124607511958855327362447065 93455633969141495521835299)
  ·
    refine ⟨140183450953712243282752949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93455633969141495521835299 140183450953712243282752949)
    ·
      refine ⟨13142198526910522807758089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 140183450953712243282752949 13142198526910522807758089)
      ·
        refine ⟨9856648895182892105818567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13142198526910522807758089 9856648895182892105818567)
        ·
          refine ⟨14784973342774338158727851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9856648895182892105818567 14784973342774338158727851)
          ·
            refine ⟨22177460014161507238091777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14784973342774338158727851 22177460014161507238091777)
            ·
              refine ⟨16633095010621130428568833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22177460014161507238091777 16633095010621130428568833)
              ·
                refine ⟨12474821257965847821426625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16633095010621130428568833 12474821257965847821426625)
                ·
                  refine ⟨9356115943474385866069969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12474821257965847821426625 9356115943474385866069969)
                  ·
                    refine ⟨7017086957605789399552477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9356115943474385866069969 7017086957605789399552477)
                    ·
                      refine ⟨2631407609102171024832179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7017086957605789399552477 2631407609102171024832179)
                      ·
                        rfl

theorem cell23_5124648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_5124648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5124648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5124648 prefixEnd_5124648 := by exact prefixLift 5124648
  have htrace : WordTrace (prefixWord ++ tailWord_5124648) baseStart_5124648 baseEnd_5124648 := by
    simpa [prefixWord, tailWord_5124648, baseEnd_5124648] using wordTrace_append hprefix tailTrace_5124648
  have hstable : (prefixWord ++ tailWord_5124648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5124648).length < 2 ^ (prefixWord ++ tailWord_5124648).sum := by decide
  have hdescent : baseEnd_5124648 < baseStart_5124648 := by decide
  rcases family_descends (prefixWord ++ tailWord_5124648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5124664 : List Nat := [2, 1, 2, 1, 4, 1, 1, 1, 5, 5]
def baseStart_5124664 : Nat := 118140960795 + 5124664 * 2 ^ 59
def prefixEnd_5124664 : Nat := 4983230072969 + 3 ^ 40 * 5124664 * 2
def baseEnd_5124664 : Nat := 877138608264214320744035

theorem tailTrace_5124664 : CollatzResearch.WordTrace tailWord_5124664 prefixEnd_5124664 877138608264214320744035 := by
  unfold tailWord_5124664
  simp only [CollatzResearch.WordTrace]
  refine ⟨93455925753112512888126523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124607901004150017184168697 93455925753112512888126523)
  ·
    refine ⟨140183888629668769332189785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93455925753112512888126523 140183888629668769332189785)
    ·
      refine ⟨105137916472251576999142339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140183888629668769332189785 105137916472251576999142339)
      ·
        refine ⟨157706874708377365498713509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105137916472251576999142339 157706874708377365498713509)
        ·
          refine ⟨29570039007820756031008783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 157706874708377365498713509 29570039007820756031008783)
          ·
            refine ⟨44355058511731134046513175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29570039007820756031008783 44355058511731134046513175)
            ·
              refine ⟨66532587767596701069769763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44355058511731134046513175 66532587767596701069769763)
              ·
                refine ⟨99798881651395051604654645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66532587767596701069769763 99798881651395051604654645)
                ·
                  refine ⟨9356145154818286087936373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 99798881651395051604654645 9356145154818286087936373)
                  ·
                    refine ⟨877138608264214320744035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9356145154818286087936373 877138608264214320744035)
                    ·
                      rfl

theorem cell23_5124664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 5, 5].length) (baseStart_5124664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5124664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5124664 prefixEnd_5124664 := by exact prefixLift 5124664
  have htrace : WordTrace (prefixWord ++ tailWord_5124664) baseStart_5124664 baseEnd_5124664 := by
    simpa [prefixWord, tailWord_5124664, baseEnd_5124664] using wordTrace_append hprefix tailTrace_5124664
  have hstable : (prefixWord ++ tailWord_5124664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5124664).length < 2 ^ (prefixWord ++ tailWord_5124664).sum := by decide
  have hdescent : baseEnd_5124664 < baseStart_5124664 := by decide
  rcases family_descends (prefixWord ++ tailWord_5124664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5124671 : List Nat := [1, 1, 2, 2, 3, 2, 2, 2, 1, 5, 2]
def baseStart_5124671 : Nat := 118140960795 + 5124671 * 2 ^ 59
def prefixEnd_5124671 : Nat := 4983230072969 + 3 ^ 40 * 5124671 * 2
def baseEnd_5124671 : Nat := 2631419419157224434844573

theorem tailTrace_5124671 : CollatzResearch.WordTrace tailWord_5124671 prefixEnd_5124671 2631419419157224434844573 := by
  unfold tailWord_5124671
  simp only [CollatzResearch.WordTrace]
  refine ⟨186912106817199665971757867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124608071211466443981171911 186912106817199665971757867)
  ·
    refine ⟨280368160225799498957636801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186912106817199665971757867 280368160225799498957636801)
    ·
      refine ⟨210276120169349624218227601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 280368160225799498957636801 210276120169349624218227601)
      ·
        refine ⟨157707090127012218163670701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210276120169349624218227601 157707090127012218163670701)
        ·
          refine ⟨59140158797629581811376513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 157707090127012218163670701 59140158797629581811376513)
          ·
            refine ⟨44355119098222186358532385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59140158797629581811376513 44355119098222186358532385)
            ·
              refine ⟨33266339323666639768899289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44355119098222186358532385 33266339323666639768899289)
              ·
                refine ⟨24949754492749979826674467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33266339323666639768899289 24949754492749979826674467)
                ·
                  refine ⟨37424631739124969740011701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24949754492749979826674467 37424631739124969740011701)
                  ·
                    refine ⟨3508559225542965913126097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37424631739124969740011701 3508559225542965913126097)
                    ·
                      refine ⟨2631419419157224434844573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3508559225542965913126097 2631419419157224434844573)
                      ·
                        rfl

theorem cell23_5124671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 5, 2].length) (baseStart_5124671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5124671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5124671 prefixEnd_5124671 := by exact prefixLift 5124671
  have htrace : WordTrace (prefixWord ++ tailWord_5124671) baseStart_5124671 baseEnd_5124671 := by
    simpa [prefixWord, tailWord_5124671, baseEnd_5124671] using wordTrace_append hprefix tailTrace_5124671
  have hstable : (prefixWord ++ tailWord_5124671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5124671).length < 2 ^ (prefixWord ++ tailWord_5124671).sum := by decide
  have hdescent : baseEnd_5124671 < baseStart_5124671 := by decide
  rcases family_descends (prefixWord ++ tailWord_5124671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5124695 : List Nat := [1, 1, 3, 2, 2, 2, 4, 3, 1, 1, 3]
def baseStart_5124695 : Nat := 118140960795 + 5124695 * 2 ^ 59
def prefixEnd_5124695 : Nat := 4983230072969 + 3 ^ 40 * 5124695 * 2
def baseEnd_5124695 : Nat := 2631431742692932340944463

theorem tailTrace_5124695 : CollatzResearch.WordTrace tailWord_5124695 prefixEnd_5124695 2631431742692932340944463 := by
  unfold tailWord_5124695
  simp only [CollatzResearch.WordTrace]
  refine ⟨186912982169112718070631539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124608654779408478713754359 186912982169112718070631539)
  ·
    refine ⟨280369473253669077105947309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186912982169112718070631539 280369473253669077105947309)
    ·
      refine ⟨105138552470125903914730241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 280369473253669077105947309 105138552470125903914730241)
      ·
        refine ⟨78853914352594427936047681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105138552470125903914730241 78853914352594427936047681)
        ·
          refine ⟨59140435764445820952035761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78853914352594427936047681 59140435764445820952035761)
          ·
            refine ⟨44355326823334365714026821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59140435764445820952035761 44355326823334365714026821)
            ·
              refine ⟨8316623779375193571380029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44355326823334365714026821 8316623779375193571380029)
              ·
                refine ⟨3118733917265697589267511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8316623779375193571380029 3118733917265697589267511)
                ·
                  refine ⟨4678100875898546383901267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3118733917265697589267511 4678100875898546383901267)
                  ·
                    refine ⟨7017151313847819575851901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4678100875898546383901267 7017151313847819575851901)
                    ·
                      refine ⟨2631431742692932340944463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7017151313847819575851901 2631431742692932340944463)
                      ·
                        rfl

theorem cell23_5124695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 3, 1, 1, 3].length) (baseStart_5124695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5124695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5124695 prefixEnd_5124695 := by exact prefixLift 5124695
  have htrace : WordTrace (prefixWord ++ tailWord_5124695) baseStart_5124695 baseEnd_5124695 := by
    simpa [prefixWord, tailWord_5124695, baseEnd_5124695] using wordTrace_append hprefix tailTrace_5124695
  have hstable : (prefixWord ++ tailWord_5124695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5124695).length < 2 ^ (prefixWord ++ tailWord_5124695).sum := by decide
  have hdescent : baseEnd_5124695 < baseStart_5124695 := by decide
  rcases family_descends (prefixWord ++ tailWord_5124695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5124741 : List Nat := [1, 3, 1, 1, 4, 2, 4, 7]
def baseStart_5124741 : Nat := 118140960795 + 5124741 * 2 ^ 59
def prefixEnd_5124741 : Nat := 4983230072969 + 3 ^ 40 * 5124741 * 2
def baseEnd_5124741 : Nat := 97461309733445894850713

theorem tailTrace_5124741 : CollatzResearch.WordTrace tailWord_5124741 prefixEnd_5124741 97461309733445894850713 := by
  unfold tailWord_5124741
  simp only [CollatzResearch.WordTrace]
  refine ⟨186914659926946067926806077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124609773284630711951204051 186914659926946067926806077)
  ·
    refine ⟨70092997472604775472552279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186914659926946067926806077 70092997472604775472552279)
    ·
      refine ⟨105139496208907163208828419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70092997472604775472552279 105139496208907163208828419)
      ·
        refine ⟨157709244313360744813242629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105139496208907163208828419 157709244313360744813242629)
        ·
          refine ⟨29570483308755139652482993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 157709244313360744813242629 29570483308755139652482993)
          ·
            refine ⟨22177862481566354739362245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29570483308755139652482993 22177862481566354739362245)
            ·
              refine ⟨4158349215293691513630421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22177862481566354739362245 4158349215293691513630421)
              ·
                refine ⟨97461309733445894850713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4158349215293691513630421 97461309733445894850713)
                ·
                  rfl

theorem cell23_5124741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 4, 7].length) (baseStart_5124741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5124741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5124741 prefixEnd_5124741 := by exact prefixLift 5124741
  have htrace : WordTrace (prefixWord ++ tailWord_5124741) baseStart_5124741 baseEnd_5124741 := by
    simpa [prefixWord, tailWord_5124741, baseEnd_5124741] using wordTrace_append hprefix tailTrace_5124741
  have hstable : (prefixWord ++ tailWord_5124741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5124741).length < 2 ^ (prefixWord ++ tailWord_5124741).sum := by decide
  have hdescent : baseEnd_5124741 < baseStart_5124741 := by decide
  rcases family_descends (prefixWord ++ tailWord_5124741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5124769 : List Nat := [1, 2, 3, 3, 4, 1, 1, 1, 3, 2, 2]
def baseStart_5124769 : Nat := 118140960795 + 5124769 * 2 ^ 59
def prefixEnd_5124769 : Nat := 4983230072969 + 3 ^ 40 * 5124769 * 2
def baseEnd_5124769 : Nat := 2631469740261365051419123

theorem tailTrace_5124769 : CollatzResearch.WordTrace tailWord_5124769 prefixEnd_5124769 2631469740261365051419123 := by
  unfold tailWord_5124769
  simp only [CollatzResearch.WordTrace]
  refine ⟨186915681170844628708825361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124610454113896419139216907 186915681170844628708825361)
  ·
    refine ⟨140186760878133471531619021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186915681170844628708825361 140186760878133471531619021)
    ·
      refine ⟨52570035329300051824357133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140186760878133471531619021 52570035329300051824357133)
      ·
        refine ⟨19713763248487519434133925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52570035329300051824357133 19713763248487519434133925)
        ·
          refine ⟨3696330609091409893900111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19713763248487519434133925 3696330609091409893900111)
          ·
            refine ⟨5544495913637114840850167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3696330609091409893900111 5544495913637114840850167)
            ·
              refine ⟨8316743870455672261275251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5544495913637114840850167 8316743870455672261275251)
              ·
                refine ⟨12475115805683508391912877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8316743870455672261275251 12475115805683508391912877)
                ·
                  refine ⟨4678168427131315646967329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12475115805683508391912877 4678168427131315646967329)
                  ·
                    refine ⟨3508626320348486735225497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4678168427131315646967329 3508626320348486735225497)
                    ·
                      refine ⟨2631469740261365051419123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3508626320348486735225497 2631469740261365051419123)
                      ·
                        rfl

theorem cell23_5124769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 1, 3, 2, 2].length) (baseStart_5124769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5124769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5124769 prefixEnd_5124769 := by exact prefixLift 5124769
  have htrace : WordTrace (prefixWord ++ tailWord_5124769) baseStart_5124769 baseEnd_5124769 := by
    simpa [prefixWord, tailWord_5124769, baseEnd_5124769] using wordTrace_append hprefix tailTrace_5124769
  have hstable : (prefixWord ++ tailWord_5124769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5124769).length < 2 ^ (prefixWord ++ tailWord_5124769).sum := by decide
  have hdescent : baseEnd_5124769 < baseStart_5124769 := by decide
  rcases family_descends (prefixWord ++ tailWord_5124769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5124784 : List Nat := [2, 1, 1, 1, 2, 1, 3, 3, 1, 8]
def baseStart_5124784 : Nat := 118140960795 + 5124784 * 2 ^ 59
def prefixEnd_5124784 : Nat := 4983230072969 + 3 ^ 40 * 5124784 * 2
def baseEnd_5124784 : Nat := 877159147490394164243851

theorem tailTrace_5124784 : CollatzResearch.WordTrace tailWord_5124784 prefixEnd_5124784 877159147490394164243851 := by
  unfold tailWord_5124784
  simp only [CollatzResearch.WordTrace]
  refine ⟨93458114132895143135310703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124610818843860190847080937 93458114132895143135310703)
  ·
    refine ⟨140187171199342714702966055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93458114132895143135310703 140187171199342714702966055)
    ·
      refine ⟨210280756799014072054449083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140187171199342714702966055 210280756799014072054449083)
      ·
        refine ⟨315421135198521108081673625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210280756799014072054449083 315421135198521108081673625)
        ·
          refine ⟨236565851398890831061255219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 315421135198521108081673625 236565851398890831061255219)
          ·
            refine ⟨354848777098336246591882829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236565851398890831061255219 354848777098336246591882829)
            ·
              refine ⟨133068291411876092471956061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 354848777098336246591882829 133068291411876092471956061)
              ·
                refine ⟨49900609279453534676983523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 133068291411876092471956061 49900609279453534676983523)
                ·
                  refine ⟨74850913919180302015475285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49900609279453534676983523 74850913919180302015475285)
                  ·
                    refine ⟨877159147490394164243851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 74850913919180302015475285 877159147490394164243851)
                    ·
                      rfl

theorem cell23_5124784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 1, 8].length) (baseStart_5124784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5124784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5124784 prefixEnd_5124784 := by exact prefixLift 5124784
  have htrace : WordTrace (prefixWord ++ tailWord_5124784) baseStart_5124784 baseEnd_5124784 := by
    simpa [prefixWord, tailWord_5124784, baseEnd_5124784] using wordTrace_append hprefix tailTrace_5124784
  have hstable : (prefixWord ++ tailWord_5124784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5124784).length < 2 ^ (prefixWord ++ tailWord_5124784).sum := by decide
  have hdescent : baseEnd_5124784 < baseStart_5124784 := by decide
  rcases family_descends (prefixWord ++ tailWord_5124784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5124806 : List Nat := [6, 1, 2, 1, 2, 1, 3, 1, 1, 2, 3]
def baseStart_5124806 : Nat := 118140960795 + 5124806 * 2 ^ 59
def prefixEnd_5124806 : Nat := 4983230072969 + 3 ^ 40 * 5124806 * 2
def baseEnd_5124806 : Nat := 2631488739045581406656453

theorem tailTrace_5124806 : CollatzResearch.WordTrace tailWord_5124806 prefixEnd_5124806 2631488739045581406656453 := by
  unfold tailWord_5124806
  simp only [CollatzResearch.WordTrace]
  refine ⟨5841157208490955750872571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 124611353781140389351948181 5841157208490955750872571)
  ·
    refine ⟨8761735812736433626308857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5841157208490955750872571 8761735812736433626308857)
    ·
      refine ⟨6571301859552325219731643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8761735812736433626308857 6571301859552325219731643)
      ·
        refine ⟨9856952789328487829597465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6571301859552325219731643 9856952789328487829597465)
        ·
          refine ⟨7392714591996365872198099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9856952789328487829597465 7392714591996365872198099)
          ·
            refine ⟨11089071887994548808297149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7392714591996365872198099 11089071887994548808297149)
            ·
              refine ⟨4158401957997955803111431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11089071887994548808297149 4158401957997955803111431)
              ·
                refine ⟨6237602936996933704667147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4158401957997955803111431 6237602936996933704667147)
                ·
                  refine ⟨9356404405495400557000721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6237602936996933704667147 9356404405495400557000721)
                  ·
                    refine ⟨7017303304121550417750541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9356404405495400557000721 7017303304121550417750541)
                    ·
                      refine ⟨2631488739045581406656453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7017303304121550417750541 2631488739045581406656453)
                      ·
                        rfl

theorem cell23_5124806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_5124806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5124806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5124806 prefixEnd_5124806 := by exact prefixLift 5124806
  have htrace : WordTrace (prefixWord ++ tailWord_5124806) baseStart_5124806 baseEnd_5124806 := by
    simpa [prefixWord, tailWord_5124806, baseEnd_5124806] using wordTrace_append hprefix tailTrace_5124806
  have hstable : (prefixWord ++ tailWord_5124806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5124806).length < 2 ^ (prefixWord ++ tailWord_5124806).sum := by decide
  have hdescent : baseEnd_5124806 < baseStart_5124806 := by decide
  rcases family_descends (prefixWord ++ tailWord_5124806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5124808 : List Nat := [2, 1, 3, 1, 2, 3, 1, 1, 3, 4, 2]
def baseStart_5124808 : Nat := 118140960795 + 5124808 * 2 ^ 59
def prefixEnd_5124808 : Nat := 4983230072969 + 3 ^ 40 * 5124808 * 2
def baseEnd_5124808 : Nat := 2631489766006890398831443

theorem tailTrace_5124808 : CollatzResearch.WordTrace tailWord_5124808 prefixEnd_5124808 2631489766006890398831443 := by
  unfold tailWord_5124808
  simp only [CollatzResearch.WordTrace]
  refine ⟨93458551808851669184747539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124611402411802225579663385 93458551808851669184747539)
  ·
    refine ⟨140187827713277503777121309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93458551808851669184747539 140187827713277503777121309)
    ·
      refine ⟨52570435392479063916420491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140187827713277503777121309 52570435392479063916420491)
      ·
        refine ⟨78855653088718595874630737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52570435392479063916420491 78855653088718595874630737)
        ·
          refine ⟨59141739816538946905973053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78855653088718595874630737 59141739816538946905973053)
          ·
            refine ⟨22178152431202105089739895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59141739816538946905973053 22178152431202105089739895)
            ·
              refine ⟨33267228646803157634609843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22178152431202105089739895 33267228646803157634609843)
              ·
                refine ⟨49900842970204736451914765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33267228646803157634609843 49900842970204736451914765)
                ·
                  refine ⟨18712816113826776169468037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49900842970204736451914765 18712816113826776169468037)
                  ·
                    refine ⟨3508653021342520531775257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18712816113826776169468037 3508653021342520531775257)
                    ·
                      refine ⟨2631489766006890398831443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3508653021342520531775257 2631489766006890398831443)
                      ·
                        rfl

theorem cell23_5124808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 3, 4, 2].length) (baseStart_5124808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5124808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5124808 prefixEnd_5124808 := by exact prefixLift 5124808
  have htrace : WordTrace (prefixWord ++ tailWord_5124808) baseStart_5124808 baseEnd_5124808 := by
    simpa [prefixWord, tailWord_5124808, baseEnd_5124808] using wordTrace_append hprefix tailTrace_5124808
  have hstable : (prefixWord ++ tailWord_5124808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5124808).length < 2 ^ (prefixWord ++ tailWord_5124808).sum := by decide
  have hdescent : baseEnd_5124808 < baseStart_5124808 := by decide
  rcases family_descends (prefixWord ++ tailWord_5124808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5124841 : List Nat := [1, 2, 1, 1, 1, 2, 5, 1, 1, 5, 3]
def baseStart_5124841 : Nat := 118140960795 + 5124841 * 2 ^ 59
def prefixEnd_5124841 : Nat := 4983230072969 + 3 ^ 40 * 5124841 * 2
def baseEnd_5124841 : Nat := 2631506710868488769718791

theorem tailTrace_5124841 : CollatzResearch.WordTrace tailWord_5124841 prefixEnd_5124841 2631506710868488769718791 := by
  unfold tailWord_5124841
  simp only [CollatzResearch.WordTrace]
  refine ⟨186918307226583785005446377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124612204817722523336964251 186918307226583785005446377)
  ·
    refine ⟨140188730419937838754084783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186918307226583785005446377 140188730419937838754084783)
    ·
      refine ⟨210283095629906758131127175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140188730419937838754084783 210283095629906758131127175)
      ·
        refine ⟨315424643444860137196690763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210283095629906758131127175 315424643444860137196690763)
        ·
          refine ⟨473136965167290205795036145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315424643444860137196690763 473136965167290205795036145)
          ·
            refine ⟨354852723875467654346277109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 473136965167290205795036145 354852723875467654346277109)
            ·
              refine ⟨33267442863325092594963479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 354852723875467654346277109 33267442863325092594963479)
              ·
                refine ⟨49901164294987638892445219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33267442863325092594963479 49901164294987638892445219)
                ·
                  refine ⟨74851746442481458338667829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49901164294987638892445219 74851746442481458338667829)
                  ·
                    refine ⟨7017351228982636719250109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 74851746442481458338667829 7017351228982636719250109)
                    ·
                      refine ⟨2631506710868488769718791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7017351228982636719250109 2631506710868488769718791)
                      ·
                        rfl

theorem cell23_5124841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 5, 3].length) (baseStart_5124841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5124841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5124841 prefixEnd_5124841 := by exact prefixLift 5124841
  have htrace : WordTrace (prefixWord ++ tailWord_5124841) baseStart_5124841 baseEnd_5124841 := by
    simpa [prefixWord, tailWord_5124841, baseEnd_5124841] using wordTrace_append hprefix tailTrace_5124841
  have hstable : (prefixWord ++ tailWord_5124841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5124841).length < 2 ^ (prefixWord ++ tailWord_5124841).sum := by decide
  have hdescent : baseEnd_5124841 < baseStart_5124841 := by decide
  rcases family_descends (prefixWord ++ tailWord_5124841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5124861 : List Nat := [1, 4, 1, 1, 1, 1, 5, 1, 1, 7]
def baseStart_5124861 : Nat := 118140960795 + 5124861 * 2 ^ 59
def prefixEnd_5124861 : Nat := 4983230072969 + 3 ^ 40 * 5124861 * 2
def baseEnd_5124861 : Nat := 877172326827192897156233

theorem tailTrace_5124861 : CollatzResearch.WordTrace tailWord_5124861 prefixEnd_5124861 877172326827192897156233 := by
  unfold tailWord_5124861
  simp only [CollatzResearch.WordTrace]
  refine ⟨186919036686511328421174437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124612691124340885614116291 186919036686511328421174437)
  ·
    refine ⟨35047319378720874078970207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 186919036686511328421174437 35047319378720874078970207)
    ·
      refine ⟨52570979068081311118455311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35047319378720874078970207 52570979068081311118455311)
      ·
        refine ⟨78856468602121966677682967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52570979068081311118455311 78856468602121966677682967)
        ·
          refine ⟨118284702903182950016524451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78856468602121966677682967 118284702903182950016524451)
          ·
            refine ⟨177427054354774425024786677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118284702903182950016524451 177427054354774425024786677)
            ·
              refine ⟨16633786345760102346073751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 177427054354774425024786677 16633786345760102346073751)
              ·
                refine ⟨24950679518640153519110627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16633786345760102346073751 24950679518640153519110627)
                ·
                  refine ⟨37426019277960230278665941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24950679518640153519110627 37426019277960230278665941)
                  ·
                    refine ⟨877172326827192897156233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37426019277960230278665941 877172326827192897156233)
                    ·
                      rfl

theorem cell23_5124861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 7].length) (baseStart_5124861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5124861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5124861 prefixEnd_5124861 := by exact prefixLift 5124861
  have htrace : WordTrace (prefixWord ++ tailWord_5124861) baseStart_5124861 baseEnd_5124861 := by
    simpa [prefixWord, tailWord_5124861, baseEnd_5124861] using wordTrace_append hprefix tailTrace_5124861
  have hstable : (prefixWord ++ tailWord_5124861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5124861).length < 2 ^ (prefixWord ++ tailWord_5124861).sum := by decide
  have hdescent : baseEnd_5124861 < baseStart_5124861 := by decide
  rcases family_descends (prefixWord ++ tailWord_5124861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5124898 : List Nat := [3, 3, 1, 1, 2, 2, 1, 2, 1, 3, 4]
def baseStart_5124898 : Nat := 118140960795 + 5124898 * 2 ^ 59
def prefixEnd_5124898 : Nat := 4983230072969 + 3 ^ 40 * 5124898 * 2
def baseEnd_5124898 : Nat := 2631535979265795046706029

theorem tailTrace_5124898 : CollatzResearch.WordTrace tailWord_5124898 prefixEnd_5124898 2631535979265795046706029 := by
  unfold tailWord_5124898
  simp only [CollatzResearch.WordTrace]
  refine ⟨46730096546844320935067837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124613590791584855826847565 46730096546844320935067837)
  ·
    refine ⟨17523786205066620350650439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46730096546844320935067837 17523786205066620350650439)
    ·
      refine ⟨26285679307599930525975659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17523786205066620350650439 26285679307599930525975659)
      ·
        refine ⟨39428518961399895788963489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26285679307599930525975659 39428518961399895788963489)
        ·
          refine ⟨29571389221049921841722617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39428518961399895788963489 29571389221049921841722617)
          ·
            refine ⟨22178541915787441381291963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29571389221049921841722617 22178541915787441381291963)
            ·
              refine ⟨33267812873681162071937945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22178541915787441381291963 33267812873681162071937945)
              ·
                refine ⟨24950859655260871553953459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33267812873681162071937945 24950859655260871553953459)
                ·
                  refine ⟨37426289482891307330930189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24950859655260871553953459 37426289482891307330930189)
                  ·
                    refine ⟨14034858556084240249098821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37426289482891307330930189 14034858556084240249098821)
                    ·
                      refine ⟨2631535979265795046706029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14034858556084240249098821 2631535979265795046706029)
                      ·
                        rfl

theorem cell23_5124898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_5124898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5124898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5124898 prefixEnd_5124898 := by exact prefixLift 5124898
  have htrace : WordTrace (prefixWord ++ tailWord_5124898) baseStart_5124898 baseEnd_5124898 := by
    simpa [prefixWord, tailWord_5124898, baseEnd_5124898] using wordTrace_append hprefix tailTrace_5124898
  have hstable : (prefixWord ++ tailWord_5124898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5124898).length < 2 ^ (prefixWord ++ tailWord_5124898).sum := by decide
  have hdescent : baseEnd_5124898 < baseStart_5124898 := by decide
  rcases family_descends (prefixWord ++ tailWord_5124898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5124908 : List Nat := [2, 2, 1, 1, 1, 4, 1, 4, 3, 4]
def baseStart_5124908 : Nat := 118140960795 + 5124908 * 2 ^ 59
def prefixEnd_5124908 : Nat := 4983230072969 + 3 ^ 40 * 5124908 * 2
def baseEnd_5124908 : Nat := 877180371357446669193661

theorem tailTrace_5124908 : CollatzResearch.WordTrace tailWord_5124908 prefixEnd_5124908 877180371357446669193661 := by
  unfold tailWord_5124908
  simp only [CollatzResearch.WordTrace]
  refine ⟨93460375458670527724067689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124613833944894036965423585 93460375458670527724067689)
  ·
    refine ⟨70095281594002895793050767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93460375458670527724067689 70095281594002895793050767)
    ·
      refine ⟨105142922391004343689576151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70095281594002895793050767 105142922391004343689576151)
      ·
        refine ⟨157714383586506515534364227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105142922391004343689576151 157714383586506515534364227)
        ·
          refine ⟨236571575379759773301546341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157714383586506515534364227 236571575379759773301546341)
          ·
            refine ⟨44357170383704957494039939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 236571575379759773301546341 44357170383704957494039939)
            ·
              refine ⟨66535755575557436241059909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44357170383704957494039939 66535755575557436241059909)
              ·
                refine ⟨12475454170417019295198733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66535755575557436241059909 12475454170417019295198733)
                ·
                  refine ⟨4678295313906382235699525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12475454170417019295198733 4678295313906382235699525)
                  ·
                    refine ⟨877180371357446669193661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4678295313906382235699525 877180371357446669193661)
                    ·
                      rfl

theorem cell23_5124908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 4].length) (baseStart_5124908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5124908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5124908 prefixEnd_5124908 := by exact prefixLift 5124908
  have htrace : WordTrace (prefixWord ++ tailWord_5124908) baseStart_5124908 baseEnd_5124908 := by
    simpa [prefixWord, tailWord_5124908, baseEnd_5124908] using wordTrace_append hprefix tailTrace_5124908
  have hstable : (prefixWord ++ tailWord_5124908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5124908).length < 2 ^ (prefixWord ++ tailWord_5124908).sum := by decide
  have hdescent : baseEnd_5124908 < baseStart_5124908 := by decide
  rcases family_descends (prefixWord ++ tailWord_5124908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5124961 : List Nat := [1, 2, 3, 1, 1, 1, 2, 1, 1, 3, 7]
def baseStart_5124961 : Nat := 118140960795 + 5124961 * 2 ^ 59
def prefixEnd_5124961 : Nat := 4983230072969 + 3 ^ 40 * 5124961 * 2
def baseEnd_5124961 : Nat := 2631568328547028300218239

theorem tailTrace_5124961 : CollatzResearch.WordTrace tailWord_5124961 prefixEnd_5124961 2631568328547028300218239 := by
  unfold tailWord_5124961
  simp only [CollatzResearch.WordTrace]
  refine ⟨186922683986149045499814737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124615122657432696999876491 186922683986149045499814737)
  ·
    refine ⟨140192012989611784124861053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186922683986149045499814737 140192012989611784124861053)
    ·
      refine ⟨52572004871104419046822895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140192012989611784124861053 52572004871104419046822895)
      ·
        refine ⟨78858007306656628570234343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52572004871104419046822895 78858007306656628570234343)
        ·
          refine ⟨118287010959984942855351515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78858007306656628570234343 118287010959984942855351515)
          ·
            refine ⟨177430516439977414283027273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118287010959984942855351515 177430516439977414283027273)
            ·
              refine ⟨133072887329983060712270455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 177430516439977414283027273 133072887329983060712270455)
              ·
                refine ⟨199609330994974591068405683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133072887329983060712270455 199609330994974591068405683)
                ·
                  refine ⟨299413996492461886602608525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 199609330994974591068405683 299413996492461886602608525)
                  ·
                    refine ⟨112280248684673207475978197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 299413996492461886602608525 112280248684673207475978197)
                    ·
                      refine ⟨2631568328547028300218239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 112280248684673207475978197 2631568328547028300218239)
                      ·
                        rfl

theorem cell23_5124961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_5124961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5124961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5124961 prefixEnd_5124961 := by exact prefixLift 5124961
  have htrace : WordTrace (prefixWord ++ tailWord_5124961) baseStart_5124961 baseEnd_5124961 := by
    simpa [prefixWord, tailWord_5124961, baseEnd_5124961] using wordTrace_append hprefix tailTrace_5124961
  have hstable : (prefixWord ++ tailWord_5124961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5124961).length < 2 ^ (prefixWord ++ tailWord_5124961).sum := by decide
  have hdescent : baseEnd_5124961 < baseStart_5124961 := by decide
  rcases family_descends (prefixWord ++ tailWord_5124961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5124965 : List Nat := [1, 3, 1, 3, 1, 1, 2, 4, 3, 1, 3]
def baseStart_5124965 : Nat := 118140960795 + 5124965 * 2 ^ 59
def prefixEnd_5124965 : Nat := 4983230072969 + 3 ^ 40 * 5124965 * 2
def baseEnd_5124965 : Nat := 2631570382469646284568221

theorem tailTrace_5124965 : CollatzResearch.WordTrace tailWord_5124965 prefixEnd_5124965 2631570382469646284568221 := by
  unfold tailWord_5124965
  simp only [CollatzResearch.WordTrace]
  refine ⟨186922829878134554182960349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124615219918756369455306899 186922829878134554182960349)
  ·
    refine ⟨70096061204300457818610131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186922829878134554182960349 70096061204300457818610131)
    ·
      refine ⟨105144091806450686727915197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70096061204300457818610131 105144091806450686727915197)
      ·
        refine ⟨39429034427419007522968199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105144091806450686727915197 39429034427419007522968199)
        ·
          refine ⟨59143551641128511284452299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39429034427419007522968199 59143551641128511284452299)
          ·
            refine ⟨88715327461692766926678449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59143551641128511284452299 88715327461692766926678449)
            ·
              refine ⟨66536495596269575195008837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88715327461692766926678449 66536495596269575195008837)
              ·
                refine ⟨12475592924300545349064157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66536495596269575195008837 12475592924300545349064157)
                ·
                  refine ⟨4678347346612704505899059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12475592924300545349064157 4678347346612704505899059)
                  ·
                    refine ⟨7017521019919056758848589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4678347346612704505899059 7017521019919056758848589)
                    ·
                      refine ⟨2631570382469646284568221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7017521019919056758848589 2631570382469646284568221)
                      ·
                        rfl

theorem cell23_5124965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 4, 3, 1, 3].length) (baseStart_5124965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5124965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5124965 prefixEnd_5124965 := by exact prefixLift 5124965
  have htrace : WordTrace (prefixWord ++ tailWord_5124965) baseStart_5124965 baseEnd_5124965 := by
    simpa [prefixWord, tailWord_5124965, baseEnd_5124965] using wordTrace_append hprefix tailTrace_5124965
  have hstable : (prefixWord ++ tailWord_5124965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5124965).length < 2 ^ (prefixWord ++ tailWord_5124965).sum := by decide
  have hdescent : baseEnd_5124965 < baseStart_5124965 := by decide
  rcases family_descends (prefixWord ++ tailWord_5124965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5124999 : List Nat := [1, 1, 4, 2, 3, 2, 1, 4, 1, 1, 3]
def baseStart_5124999 : Nat := 118140960795 + 5124999 * 2 ^ 59
def prefixEnd_5124999 : Nat := 4983230072969 + 3 ^ 40 * 5124999 * 2
def baseEnd_5124999 : Nat := 2631587840811899151543065

theorem tailTrace_5124999 : CollatzResearch.WordTrace tailWord_5124999 prefixEnd_5124999 2631587840811899151543065 := by
  unfold tailWord_5124999
  simp only [CollatzResearch.WordTrace]
  refine ⟨186924069960011377989698051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124616046640007585326465367 186924069960011377989698051)
  ·
    refine ⟨280386104940017066984547077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186924069960011377989698051 280386104940017066984547077)
    ·
      refine ⟨52572394676253200059602577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 280386104940017066984547077 52572394676253200059602577)
      ·
        refine ⟨39429296007189900044701933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52572394676253200059602577 39429296007189900044701933)
        ·
          refine ⟨14785986002696212516763225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39429296007189900044701933 14785986002696212516763225)
          ·
            refine ⟨11089489502022159387572419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14785986002696212516763225 11089489502022159387572419)
            ·
              refine ⟨16634234253033239081358629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11089489502022159387572419 16634234253033239081358629)
              ·
                refine ⟨3118918922443732327754743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16634234253033239081358629 3118918922443732327754743)
                ·
                  refine ⟨4678378383665598491632115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3118918922443732327754743 4678378383665598491632115)
                  ·
                    refine ⟨7017567575498397737448173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4678378383665598491632115 7017567575498397737448173)
                    ·
                      refine ⟨2631587840811899151543065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7017567575498397737448173 2631587840811899151543065)
                      ·
                        rfl

theorem cell23_5124999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 4, 1, 1, 3].length) (baseStart_5124999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5124999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5124999 prefixEnd_5124999 := by exact prefixLift 5124999
  have htrace : WordTrace (prefixWord ++ tailWord_5124999) baseStart_5124999 baseEnd_5124999 := by
    simpa [prefixWord, tailWord_5124999, baseEnd_5124999] using wordTrace_append hprefix tailTrace_5124999
  have hstable : (prefixWord ++ tailWord_5124999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5124999).length < 2 ^ (prefixWord ++ tailWord_5124999).sum := by decide
  have hdescent : baseEnd_5124999 < baseStart_5124999 := by decide
  rcases family_descends (prefixWord ++ tailWord_5124999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5125011 : List Nat := [1, 1, 1, 2, 1, 2, 1, 14]
def baseStart_5125011 : Nat := 118140960795 + 5125011 * 2 ^ 59
def prefixEnd_5125011 : Nat := 4983230072969 + 3 ^ 40 * 5125011 * 2
def baseEnd_5125011 : Nat := 97466444539990855725667

theorem tailTrace_5125011 : CollatzResearch.WordTrace tailWord_5125011 prefixEnd_5125011 97466444539990855725667 := by
  unfold tailWord_5125011
  simp only [CollatzResearch.WordTrace]
  refine ⟨186924507635967904039134887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124616338423978602692756591 186924507635967904039134887)
  ·
    refine ⟨280386761453951856058702331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186924507635967904039134887 280386761453951856058702331)
    ·
      refine ⟨420580142180927784088053497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280386761453951856058702331 420580142180927784088053497)
      ·
        refine ⟨315435106635695838066040123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 420580142180927784088053497 315435106635695838066040123)
        ·
          refine ⟨473152659953543757099060185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315435106635695838066040123 473152659953543757099060185)
          ·
            refine ⟨354864494965157817824295139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 473152659953543757099060185 354864494965157817824295139)
            ·
              refine ⟨532296742447736726736442709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 354864494965157817824295139 532296742447736726736442709)
              ·
                refine ⟨97466444539990855725667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 14 532296742447736726736442709 97466444539990855725667)
                ·
                  rfl

theorem cell23_5125011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 14].length) (baseStart_5125011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5125011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5125011 prefixEnd_5125011 := by exact prefixLift 5125011
  have htrace : WordTrace (prefixWord ++ tailWord_5125011) baseStart_5125011 baseEnd_5125011 := by
    simpa [prefixWord, tailWord_5125011, baseEnd_5125011] using wordTrace_append hprefix tailTrace_5125011
  have hstable : (prefixWord ++ tailWord_5125011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5125011).length < 2 ^ (prefixWord ++ tailWord_5125011).sum := by decide
  have hdescent : baseEnd_5125011 < baseStart_5125011 := by decide
  rcases family_descends (prefixWord ++ tailWord_5125011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5125015 : List Nat := [1, 1, 3, 3, 1, 2, 1, 5, 2, 4]
def baseStart_5125015 : Nat := 118140960795 + 5125015 * 2 ^ 59
def prefixEnd_5125015 : Nat := 4983230072969 + 3 ^ 40 * 5125015 * 2
def baseEnd_5125015 : Nat := 877198685500790362980997

theorem tailTrace_5125015 : CollatzResearch.WordTrace tailWord_5125015 prefixEnd_5125015 877198685500790362980997 := by
  unfold tailWord_5125015
  simp only [CollatzResearch.WordTrace]
  refine ⟨186924653527953412722280499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124616435685302275148186999 186924653527953412722280499)
  ·
    refine ⟨280386980291930119083420749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186924653527953412722280499 280386980291930119083420749)
    ·
      refine ⟨105145117609473794656282781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 280386980291930119083420749 105145117609473794656282781)
      ·
        refine ⟨39429419103552672996106043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105145117609473794656282781 39429419103552672996106043)
        ·
          refine ⟨59144128655329009494159065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39429419103552672996106043 59144128655329009494159065)
          ·
            refine ⟨44358096491496757120619299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59144128655329009494159065 44358096491496757120619299)
            ·
              refine ⟨66537144737245135680928949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44358096491496757120619299 66537144737245135680928949)
              ·
                refine ⟨6237857319116731470087089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66537144737245135680928949 6237857319116731470087089)
                ·
                  refine ⟨4678392989337548602565317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6237857319116731470087089 4678392989337548602565317)
                  ·
                    refine ⟨877198685500790362980997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4678392989337548602565317 877198685500790362980997)
                    ·
                      rfl

theorem cell23_5125015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 5, 2, 4].length) (baseStart_5125015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5125015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5125015 prefixEnd_5125015 := by exact prefixLift 5125015
  have htrace : WordTrace (prefixWord ++ tailWord_5125015) baseStart_5125015 baseEnd_5125015 := by
    simpa [prefixWord, tailWord_5125015, baseEnd_5125015] using wordTrace_append hprefix tailTrace_5125015
  have hstable : (prefixWord ++ tailWord_5125015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5125015).length < 2 ^ (prefixWord ++ tailWord_5125015).sum := by decide
  have hdescent : baseEnd_5125015 < baseStart_5125015 := by decide
  rcases family_descends (prefixWord ++ tailWord_5125015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5125085 : List Nat := [1, 4, 3, 1, 2, 1, 1, 1, 2, 2, 5]
def baseStart_5125085 : Nat := 118140960795 + 5125085 * 2 ^ 59
def prefixEnd_5125085 : Nat := 4983230072969 + 3 ^ 40 * 5125085 * 2
def baseEnd_5125085 : Nat := 2631632000148185815067669

theorem tailTrace_5125085 : CollatzResearch.WordTrace tailWord_5125085 prefixEnd_5125085 2631632000148185815067669 := by
  unfold tailWord_5125085
  simp only [CollatzResearch.WordTrace]
  refine ⟨186927206637699814677328709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124618137758466543118219139 186927206637699814677328709)
  ·
    refine ⟨35048851244568715251999133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 186927206637699814677328709 35048851244568715251999133)
    ·
      refine ⟨13143319216713268219499675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35048851244568715251999133 13143319216713268219499675)
      ·
        refine ⟨19714978825069902329249513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13143319216713268219499675 19714978825069902329249513)
        ·
          refine ⟨14786234118802426746937135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19714978825069902329249513 14786234118802426746937135)
          ·
            refine ⟨22179351178203640120405703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14786234118802426746937135 22179351178203640120405703)
            ·
              refine ⟨33269026767305460180608555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22179351178203640120405703 33269026767305460180608555)
              ·
                refine ⟨49903540150958190270912833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33269026767305460180608555 49903540150958190270912833)
                ·
                  refine ⟨37427655113218642703184625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49903540150958190270912833 37427655113218642703184625)
                  ·
                    refine ⟨28070741334913982027388469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37427655113218642703184625 28070741334913982027388469)
                    ·
                      refine ⟨2631632000148185815067669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28070741334913982027388469 2631632000148185815067669)
                      ·
                        rfl

theorem cell23_5125085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_5125085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5125085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5125085 prefixEnd_5125085 := by exact prefixLift 5125085
  have htrace : WordTrace (prefixWord ++ tailWord_5125085) baseStart_5125085 baseEnd_5125085 := by
    simpa [prefixWord, tailWord_5125085, baseEnd_5125085] using wordTrace_append hprefix tailTrace_5125085
  have hstable : (prefixWord ++ tailWord_5125085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5125085).length < 2 ^ (prefixWord ++ tailWord_5125085).sum := by decide
  have hdescent : baseEnd_5125085 < baseStart_5125085 := by decide
  rcases family_descends (prefixWord ++ tailWord_5125085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5125090 : List Nat := [3, 3, 3, 1, 1, 3, 1, 3, 1, 2, 2]
def baseStart_5125090 : Nat := 118140960795 + 5125090 * 2 ^ 59
def prefixEnd_5125090 : Nat := 4983230072969 + 3 ^ 40 * 5125090 * 2
def baseEnd_5125090 : Nat := 2631634567551458295505147

theorem tailTrace_5125090 : CollatzResearch.WordTrace tailWord_5125090 prefixEnd_5125090 2631634567551458295505147 := by
  unfold tailWord_5125090
  simp only [CollatzResearch.WordTrace]
  refine ⟨46731847250670425132815181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124618259335121133687507149 46731847250670425132815181)
  ·
    refine ⟨17524442719001409424805693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46731847250670425132815181 17524442719001409424805693)
    ·
      refine ⟨6571666019625528534302135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17524442719001409424805693 6571666019625528534302135)
      ·
        refine ⟨9857499029438292801453203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6571666019625528534302135 9857499029438292801453203)
        ·
          refine ⟨14786248544157439202179805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9857499029438292801453203 14786248544157439202179805)
          ·
            refine ⟨5544843204059039700817427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14786248544157439202179805 5544843204059039700817427)
            ·
              refine ⟨8317264806088559551226141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5544843204059039700817427 8317264806088559551226141)
              ·
                refine ⟨3118974302283209831709803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8317264806088559551226141 3118974302283209831709803)
                ·
                  refine ⟨4678461453424814747564705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3118974302283209831709803 4678461453424814747564705)
                  ·
                    refine ⟨3508846090068611060673529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4678461453424814747564705 3508846090068611060673529)
                    ·
                      refine ⟨2631634567551458295505147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3508846090068611060673529 2631634567551458295505147)
                      ·
                        rfl

theorem cell23_5125090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_5125090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5125090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5125090 prefixEnd_5125090 := by exact prefixLift 5125090
  have htrace : WordTrace (prefixWord ++ tailWord_5125090) baseStart_5125090 baseEnd_5125090 := by
    simpa [prefixWord, tailWord_5125090, baseEnd_5125090] using wordTrace_append hprefix tailTrace_5125090
  have hstable : (prefixWord ++ tailWord_5125090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5125090).length < 2 ^ (prefixWord ++ tailWord_5125090).sum := by decide
  have hdescent : baseEnd_5125090 < baseStart_5125090 := by decide
  rcases family_descends (prefixWord ++ tailWord_5125090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
