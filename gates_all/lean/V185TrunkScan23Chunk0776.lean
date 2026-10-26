import V185TrunkScan23Chunk0775

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4589868 : List Nat := [2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 4]
def baseStart_4589868 : Nat := 118140960795 + 4589868 * 2 ^ 59
def prefixEnd_4589868 : Nat := 4983230072969 + 3 ^ 40 * 4589868 * 2
def baseEnd_4589868 : Nat := 2356808424690753354041587

theorem tailTrace_4589868 : CollatzResearch.WordTrace tailWord_4589868 prefixEnd_4589868 2356808424690753354041587 := by
  unfold tailWord_4589868
  simp only [CollatzResearch.WordTrace]
  refine ⟨83703119467849798945537129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111604159290466398594049505 83703119467849798945537129)
  ·
    refine ⟨62777339600887349209152847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83703119467849798945537129 62777339600887349209152847)
    ·
      refine ⟨94166009401331023813729271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62777339600887349209152847 94166009401331023813729271)
      ·
        refine ⟨141249014101996535720593907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94166009401331023813729271 141249014101996535720593907)
        ·
          refine ⟨211873521152994803580890861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141249014101996535720593907 211873521152994803580890861)
          ·
            refine ⟨79452570432373051342834073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 211873521152994803580890861 79452570432373051342834073)
            ·
              refine ⟨59589427824279788507125555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79452570432373051342834073 59589427824279788507125555)
              ·
                refine ⟨89384141736419682760688333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59589427824279788507125555 89384141736419682760688333)
                ·
                  refine ⟨33519053151157381035258125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 89384141736419682760688333 33519053151157381035258125)
                  ·
                    refine ⟨12569644931684017888221797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33519053151157381035258125 12569644931684017888221797)
                    ·
                      refine ⟨2356808424690753354041587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12569644931684017888221797 2356808424690753354041587)
                      ·
                        rfl

theorem cell23_4589868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 4].length) (baseStart_4589868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4589868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4589868 prefixEnd_4589868 := by exact prefixLift 4589868
  have htrace : WordTrace (prefixWord ++ tailWord_4589868) baseStart_4589868 baseEnd_4589868 := by
    simpa [prefixWord, tailWord_4589868, baseEnd_4589868] using wordTrace_append hprefix tailTrace_4589868
  have hstable : (prefixWord ++ tailWord_4589868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4589868).length < 2 ^ (prefixWord ++ tailWord_4589868).sum := by decide
  have hdescent : baseEnd_4589868 < baseStart_4589868 := by decide
  rcases family_descends (prefixWord ++ tailWord_4589868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4589925 : List Nat := [1, 3, 1, 3, 1, 3, 2, 3, 6]
def baseStart_4589925 : Nat := 118140960795 + 4589925 * 2 ^ 59
def prefixEnd_4589925 : Nat := 4983230072969 + 3 ^ 40 * 4589925 * 2
def baseEnd_4589925 : Nat := 261870854787562181225425

theorem tailTrace_4589925 : CollatzResearch.WordTrace tailWord_4589925 prefixEnd_4589925 261870854787562181225425 := by
  unfold tailWord_4589925
  simp only [CollatzResearch.WordTrace]
  refine ⟨167408317896493096625899229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111605545264328731083932819 167408317896493096625899229)
  ·
    refine ⟨62778119211184911234712211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167408317896493096625899229 62778119211184911234712211)
    ·
      refine ⟨94167178816777366852068317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62778119211184911234712211 94167178816777366852068317)
      ·
        refine ⟨35312692056291512569525619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94167178816777366852068317 35312692056291512569525619)
        ·
          refine ⟨52969038084437268854288429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35312692056291512569525619 52969038084437268854288429)
          ·
            refine ⟨19863389281663975820358161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52969038084437268854288429 19863389281663975820358161)
            ·
              refine ⟨14897541961247981865268621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19863389281663975820358161 14897541961247981865268621)
              ·
                refine ⟨5586578235467993199475733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14897541961247981865268621 5586578235467993199475733)
                ·
                  refine ⟨261870854787562181225425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5586578235467993199475733 261870854787562181225425)
                  ·
                    rfl

theorem cell23_4589925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 3, 6].length) (baseStart_4589925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4589925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4589925 prefixEnd_4589925 := by exact prefixLift 4589925
  have htrace : WordTrace (prefixWord ++ tailWord_4589925) baseStart_4589925 baseEnd_4589925 := by
    simpa [prefixWord, tailWord_4589925, baseEnd_4589925] using wordTrace_append hprefix tailTrace_4589925
  have hstable : (prefixWord ++ tailWord_4589925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4589925).length < 2 ^ (prefixWord ++ tailWord_4589925).sum := by decide
  have hdescent : baseEnd_4589925 < baseStart_4589925 := by decide
  rcases family_descends (prefixWord ++ tailWord_4589925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4589975 : List Nat := [1, 1, 3, 3, 1, 1, 2, 1, 5, 1, 4]
def baseStart_4589975 : Nat := 118140960795 + 4589975 * 2 ^ 59
def prefixEnd_4589975 : Nat := 4983230072969 + 3 ^ 40 * 4589975 * 2
def baseEnd_4589975 : Nat := 2356863367120784435403595

theorem tailTrace_4589975 : CollatzResearch.WordTrace tailWord_4589975 prefixEnd_4589975 2356863367120784435403595 := by
  unfold tailWord_4589975
  simp only [CollatzResearch.WordTrace]
  refine ⟨167410141546311955165219379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111606761030874636776812919 167410141546311955165219379)
  ·
    refine ⟨251115212319467932747829069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167410141546311955165219379 251115212319467932747829069)
    ·
      refine ⟨94168204619800474780435901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 251115212319467932747829069 94168204619800474780435901)
      ·
        refine ⟨35313076732425178042663463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94168204619800474780435901 35313076732425178042663463)
        ·
          refine ⟨52969615098637767063995195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35313076732425178042663463 52969615098637767063995195)
          ·
            refine ⟨79454422647956650595992793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52969615098637767063995195 79454422647956650595992793)
            ·
              refine ⟨59590816985967487946994595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79454422647956650595992793 59590816985967487946994595)
              ·
                refine ⟨89386225478951231920491893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59590816985967487946994595 89386225478951231920491893)
                ·
                  refine ⟨8379958638651677992546115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 89386225478951231920491893 8379958638651677992546115)
                  ·
                    refine ⟨12569937957977516988819173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8379958638651677992546115 12569937957977516988819173)
                    ·
                      refine ⟨2356863367120784435403595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12569937957977516988819173 2356863367120784435403595)
                      ·
                        rfl

theorem cell23_4589975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_4589975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4589975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4589975 prefixEnd_4589975 := by exact prefixLift 4589975
  have htrace : WordTrace (prefixWord ++ tailWord_4589975) baseStart_4589975 baseEnd_4589975 := by
    simpa [prefixWord, tailWord_4589975, baseEnd_4589975] using wordTrace_append hprefix tailTrace_4589975
  have hstable : (prefixWord ++ tailWord_4589975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4589975).length < 2 ^ (prefixWord ++ tailWord_4589975).sum := by decide
  have hdescent : baseEnd_4589975 < baseStart_4589975 := by decide
  rcases family_descends (prefixWord ++ tailWord_4589975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4590012 : List Nat := [2, 2, 2, 4, 1, 1, 1, 3, 1, 1, 5]
def baseStart_4590012 : Nat := 118140960795 + 4590012 * 2 ^ 59
def prefixEnd_4590012 : Nat := 4983230072969 + 3 ^ 40 * 4590012 * 2
def baseEnd_4590012 : Nat := 2356882365905000790640925

theorem tailTrace_4590012 : CollatzResearch.WordTrace tailWord_4590012 prefixEnd_4590012 2356882365905000790640925 := by
  unfold tailWord_4590012
  simp only [CollatzResearch.WordTrace]
  refine ⟨83705745523588955242158145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111607660698118606989544193 83705745523588955242158145)
  ·
    refine ⟨62779309142691716431618609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83705745523588955242158145 62779309142691716431618609)
    ·
      refine ⟨47084481857018787323713957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62779309142691716431618609 47084481857018787323713957)
      ·
        refine ⟨8828340348191022623196367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47084481857018787323713957 8828340348191022623196367)
        ·
          refine ⟨13242510522286533934794551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8828340348191022623196367 13242510522286533934794551)
          ·
            refine ⟨19863765783429800902191827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13242510522286533934794551 19863765783429800902191827)
            ·
              refine ⟨29795648675144701353287741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19863765783429800902191827 29795648675144701353287741)
              ·
                refine ⟨11173368253179263007482903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29795648675144701353287741 11173368253179263007482903)
                ·
                  refine ⟨16760052379768894511224355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11173368253179263007482903 16760052379768894511224355)
                  ·
                    refine ⟨25140078569653341766836533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16760052379768894511224355 25140078569653341766836533)
                    ·
                      refine ⟨2356882365905000790640925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25140078569653341766836533 2356882365905000790640925)
                      ·
                        rfl

theorem cell23_4590012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_4590012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4590012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4590012 prefixEnd_4590012 := by exact prefixLift 4590012
  have htrace : WordTrace (prefixWord ++ tailWord_4590012) baseStart_4590012 baseEnd_4590012 := by
    simpa [prefixWord, tailWord_4590012, baseEnd_4590012] using wordTrace_append hprefix tailTrace_4590012
  have hstable : (prefixWord ++ tailWord_4590012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4590012).length < 2 ^ (prefixWord ++ tailWord_4590012).sum := by decide
  have hdescent : baseEnd_4590012 < baseStart_4590012 := by decide
  rcases family_descends (prefixWord ++ tailWord_4590012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4590020 : List Nat := [2, 3, 3, 2, 2, 1, 3, 2, 1, 1, 3]
def baseStart_4590020 : Nat := 118140960795 + 4590020 * 2 ^ 59
def prefixEnd_4590020 : Nat := 4983230072969 + 3 ^ 40 * 4590020 * 2
def baseEnd_4590020 : Nat := 2356886473750236759340889

theorem tailTrace_4590020 : CollatzResearch.WordTrace tailWord_4590020 prefixEnd_4590020 2356886473750236759340889 := by
  unfold tailWord_4590020
  simp only [CollatzResearch.WordTrace]
  refine ⟨83705891415574463925303757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111607855220765951900405009 83705891415574463925303757)
  ·
    refine ⟨31389709280840423971988909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83705891415574463925303757 31389709280840423971988909)
    ·
      refine ⟨11771140980315158989495841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31389709280840423971988909 11771140980315158989495841)
      ·
        refine ⟨8828355735236369242121881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11771140980315158989495841 8828355735236369242121881)
        ·
          refine ⟨6621266801427276931591411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8828355735236369242121881 6621266801427276931591411)
          ·
            refine ⟨9931900202140915397387117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6621266801427276931591411 9931900202140915397387117)
            ·
              refine ⟨3724462575802843274020169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9931900202140915397387117 3724462575802843274020169)
              ·
                refine ⟨2793346931852132455515127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3724462575802843274020169 2793346931852132455515127)
                ·
                  refine ⟨4190020397778198683272691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2793346931852132455515127 4190020397778198683272691)
                  ·
                    refine ⟨6285030596667298024909037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4190020397778198683272691 6285030596667298024909037)
                    ·
                      refine ⟨2356886473750236759340889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6285030596667298024909037 2356886473750236759340889)
                      ·
                        rfl

theorem cell23_4590020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_4590020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4590020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4590020 prefixEnd_4590020 := by exact prefixLift 4590020
  have htrace : WordTrace (prefixWord ++ tailWord_4590020) baseStart_4590020 baseEnd_4590020 := by
    simpa [prefixWord, tailWord_4590020, baseEnd_4590020] using wordTrace_append hprefix tailTrace_4590020
  have hstable : (prefixWord ++ tailWord_4590020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4590020).length < 2 ^ (prefixWord ++ tailWord_4590020).sum := by decide
  have hdescent : baseEnd_4590020 < baseStart_4590020 := by decide
  rcases family_descends (prefixWord ++ tailWord_4590020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4590036 : List Nat := [2, 4, 1, 2, 2, 1, 4, 1, 2, 4]
def baseStart_4590036 : Nat := 118140960795 + 4590036 * 2 ^ 59
def prefixEnd_4590036 : Nat := 4983230072969 + 3 ^ 40 * 4590036 * 2
def baseEnd_4590036 : Nat := 785631563146902898913605

theorem tailTrace_4590036 : CollatzResearch.WordTrace tailWord_4590036 prefixEnd_4590036 785631563146902898913605 := by
  unfold tailWord_4590036
  simp only [CollatzResearch.WordTrace]
  refine ⟨83706183199545481291594981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111608244266060641722126641 83706183199545481291594981)
  ·
    refine ⟨15694909349914777742174059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83706183199545481291594981 15694909349914777742174059)
    ·
      refine ⟨23542364024872166613261089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15694909349914777742174059 23542364024872166613261089)
      ·
        refine ⟨17656773018654124959945817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23542364024872166613261089 17656773018654124959945817)
        ·
          refine ⟨13242579763990593719959363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17656773018654124959945817 13242579763990593719959363)
          ·
            refine ⟨19863869645985890579939045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13242579763990593719959363 19863869645985890579939045)
            ·
              refine ⟨3724475558622354483738571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19863869645985890579939045 3724475558622354483738571)
              ·
                refine ⟨5586713337933531725607857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3724475558622354483738571 5586713337933531725607857)
                ·
                  refine ⟨4190035003450148794205893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5586713337933531725607857 4190035003450148794205893)
                  ·
                    refine ⟨785631563146902898913605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4190035003450148794205893 785631563146902898913605)
                    ·
                      rfl

theorem cell23_4590036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 4, 1, 2, 4].length) (baseStart_4590036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4590036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4590036 prefixEnd_4590036 := by exact prefixLift 4590036
  have htrace : WordTrace (prefixWord ++ tailWord_4590036) baseStart_4590036 baseEnd_4590036 := by
    simpa [prefixWord, tailWord_4590036, baseEnd_4590036] using wordTrace_append hprefix tailTrace_4590036
  have hstable : (prefixWord ++ tailWord_4590036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4590036).length < 2 ^ (prefixWord ++ tailWord_4590036).sum := by decide
  have hdescent : baseEnd_4590036 < baseStart_4590036 := by decide
  rcases family_descends (prefixWord ++ tailWord_4590036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4590042 : List Nat := [3, 1, 1, 2, 3, 1, 2, 3, 1, 3, 3]
def baseStart_4590042 : Nat := 118140960795 + 4590042 * 2 ^ 59
def prefixEnd_4590042 : Nat := 4983230072969 + 3 ^ 40 * 4590042 * 2
def baseEnd_4590042 : Nat := 2356897770324635673265787

theorem tailTrace_4590042 : CollatzResearch.WordTrace tailWord_4590042 prefixEnd_4590042 2356897770324635673265787 := by
  unfold tailWord_4590042
  simp only [CollatzResearch.WordTrace]
  refine ⟨41853146309267306401977095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111608390158046150405272253 41853146309267306401977095)
  ·
    refine ⟨62779719463900959602965643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41853146309267306401977095 62779719463900959602965643)
    ·
      refine ⟨94169579195851439404448465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62779719463900959602965643 94169579195851439404448465)
      ·
        refine ⟨70627184396888579553336349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94169579195851439404448465 70627184396888579553336349)
        ·
          refine ⟨26485194148833217332501131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70627184396888579553336349 26485194148833217332501131)
          ·
            refine ⟨39727791223249825998751697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26485194148833217332501131 39727791223249825998751697)
            ·
              refine ⟨29795843417437369499063773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39727791223249825998751697 29795843417437369499063773)
              ·
                refine ⟨11173441281539013562148915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29795843417437369499063773 11173441281539013562148915)
                ·
                  refine ⟨16760161922308520343223373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11173441281539013562148915 16760161922308520343223373)
                  ·
                    refine ⟨6285060720865695128708765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16760161922308520343223373 6285060720865695128708765)
                    ·
                      refine ⟨2356897770324635673265787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6285060720865695128708765 2356897770324635673265787)
                      ·
                        rfl

theorem cell23_4590042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 3, 1, 3, 3].length) (baseStart_4590042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4590042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4590042 prefixEnd_4590042 := by exact prefixLift 4590042
  have htrace : WordTrace (prefixWord ++ tailWord_4590042) baseStart_4590042 baseEnd_4590042 := by
    simpa [prefixWord, tailWord_4590042, baseEnd_4590042] using wordTrace_append hprefix tailTrace_4590042
  have hstable : (prefixWord ++ tailWord_4590042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4590042).length < 2 ^ (prefixWord ++ tailWord_4590042).sum := by decide
  have hdescent : baseEnd_4590042 < baseStart_4590042 := by decide
  rcases family_descends (prefixWord ++ tailWord_4590042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4590085 : List Nat := [1, 3, 1, 1, 2, 2, 2, 2, 1, 3, 5]
def baseStart_4590085 : Nat := 118140960795 + 4590085 * 2 ^ 59
def prefixEnd_4590085 : Nat := 4983230072969 + 3 ^ 40 * 4590085 * 2
def baseEnd_4590085 : Nat := 2356919849992779005028089

theorem tailTrace_4590085 : CollatzResearch.WordTrace tailWord_4590085 prefixEnd_4590085 2356919849992779005028089 := by
  unfold tailWord_4590085
  simp only [CollatzResearch.WordTrace]
  refine ⟨167414153575913443951723709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111609435717275629301149139 167414153575913443951723709)
  ·
    refine ⟨62780307590967541481896391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167414153575913443951723709 62780307590967541481896391)
    ·
      refine ⟨94170461386451312222844587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62780307590967541481896391 94170461386451312222844587)
      ·
        refine ⟨141255692079676968334266881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94170461386451312222844587 141255692079676968334266881)
        ·
          refine ⟨105941769059757726250700161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141255692079676968334266881 105941769059757726250700161)
          ·
            refine ⟨79456326794818294688025121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105941769059757726250700161 79456326794818294688025121)
            ·
              refine ⟨59592245096113721016018841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79456326794818294688025121 59592245096113721016018841)
              ·
                refine ⟨44694183822085290762014131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59592245096113721016018841 44694183822085290762014131)
                ·
                  refine ⟨67041275733127936143021197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44694183822085290762014131 67041275733127936143021197)
                  ·
                    refine ⟨25140478399922976053632949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 67041275733127936143021197 25140478399922976053632949)
                    ·
                      refine ⟨2356919849992779005028089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25140478399922976053632949 2356919849992779005028089)
                      ·
                        rfl

theorem cell23_4590085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 3, 5].length) (baseStart_4590085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4590085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4590085 prefixEnd_4590085 := by exact prefixLift 4590085
  have htrace : WordTrace (prefixWord ++ tailWord_4590085) baseStart_4590085 baseEnd_4590085 := by
    simpa [prefixWord, tailWord_4590085, baseEnd_4590085] using wordTrace_append hprefix tailTrace_4590085
  have hstable : (prefixWord ++ tailWord_4590085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4590085).length < 2 ^ (prefixWord ++ tailWord_4590085).sum := by decide
  have hdescent : baseEnd_4590085 < baseStart_4590085 := by decide
  rcases family_descends (prefixWord ++ tailWord_4590085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4590092 : List Nat := [2, 2, 1, 2, 4, 2, 1, 1, 2, 6]
def baseStart_4590092 : Nat := 118140960795 + 4590092 * 2 ^ 59
def prefixEnd_4590092 : Nat := 4983230072969 + 3 ^ 40 * 4590092 * 2
def baseEnd_4590092 : Nat := 785641148119120159213519

theorem tailTrace_4590092 : CollatzResearch.WordTrace tailWord_4590092 prefixEnd_4590092 785641148119120159213519 := by
  unfold tailWord_4590092
  simp only [CollatzResearch.WordTrace]
  refine ⟨83707204443444042073614265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111609605924592056098152353 83707204443444042073614265)
  ·
    refine ⟨62780403332583031555210699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83707204443444042073614265 62780403332583031555210699)
    ·
      refine ⟨94170604998874547332816049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62780403332583031555210699 94170604998874547332816049)
      ·
        refine ⟨70627953749155910499612037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94170604998874547332816049 70627953749155910499612037)
        ·
          refine ⟨13242741327966733218677257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70627953749155910499612037 13242741327966733218677257)
          ·
            refine ⟨9932055995975049914007943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13242741327966733218677257 9932055995975049914007943)
            ·
              refine ⟨14898083993962574871011915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9932055995975049914007943 14898083993962574871011915)
              ·
                refine ⟨22347125990943862306517873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14898083993962574871011915 22347125990943862306517873)
                ·
                  refine ⟨16760344493207896729888405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22347125990943862306517873 16760344493207896729888405)
                  ·
                    refine ⟨785641148119120159213519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16760344493207896729888405 785641148119120159213519)
                    ·
                      rfl

theorem cell23_4590092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 2, 6].length) (baseStart_4590092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4590092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4590092 prefixEnd_4590092 := by exact prefixLift 4590092
  have htrace : WordTrace (prefixWord ++ tailWord_4590092) baseStart_4590092 baseEnd_4590092 := by
    simpa [prefixWord, tailWord_4590092, baseEnd_4590092] using wordTrace_append hprefix tailTrace_4590092
  have hstable : (prefixWord ++ tailWord_4590092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4590092).length < 2 ^ (prefixWord ++ tailWord_4590092).sum := by decide
  have hdescent : baseEnd_4590092 < baseStart_4590092 := by decide
  rcases family_descends (prefixWord ++ tailWord_4590092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4590093 : List Nat := [1, 7, 1, 1, 1, 2, 2, 1, 1, 3, 3]
def baseStart_4590093 : Nat := 118140960795 + 4590093 * 2 ^ 59
def prefixEnd_4590093 : Nat := 4983230072969 + 3 ^ 40 * 4590093 * 2
def baseEnd_4590093 : Nat := 2356923957838014973728053

theorem tailTrace_4590093 : CollatzResearch.WordTrace tailWord_4590093 prefixEnd_4590093 2356923957838014973728053 := by
  unfold tailWord_4590093
  simp only [CollatzResearch.WordTrace]
  refine ⟨167414445359884461318014933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111609630239922974212009955 167414445359884461318014933)
  ·
    refine ⟨3923776063122292062140975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 167414445359884461318014933 3923776063122292062140975)
    ·
      refine ⟨5885664094683438093211463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3923776063122292062140975 5885664094683438093211463)
      ·
        refine ⟨8828496142025157139817195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5885664094683438093211463 8828496142025157139817195)
        ·
          refine ⟨13242744213037735709725793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8828496142025157139817195 13242744213037735709725793)
          ·
            refine ⟨9932058159778301782294345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13242744213037735709725793 9932058159778301782294345)
            ·
              refine ⟨7449043619833726336720759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9932058159778301782294345 7449043619833726336720759)
              ·
                refine ⟨11173565429750589505081139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7449043619833726336720759 11173565429750589505081139)
                ·
                  refine ⟨16760348144625884257621709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11173565429750589505081139 16760348144625884257621709)
                  ·
                    refine ⟨6285130554234706596608141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16760348144625884257621709 6285130554234706596608141)
                    ·
                      refine ⟨2356923957838014973728053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6285130554234706596608141 2356923957838014973728053)
                      ·
                        rfl

theorem cell23_4590093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_4590093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4590093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4590093 prefixEnd_4590093 := by exact prefixLift 4590093
  have htrace : WordTrace (prefixWord ++ tailWord_4590093) baseStart_4590093 baseEnd_4590093 := by
    simpa [prefixWord, tailWord_4590093, baseEnd_4590093] using wordTrace_append hprefix tailTrace_4590093
  have hstable : (prefixWord ++ tailWord_4590093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4590093).length < 2 ^ (prefixWord ++ tailWord_4590093).sum := by decide
  have hdescent : baseEnd_4590093 < baseStart_4590093 := by decide
  rcases family_descends (prefixWord ++ tailWord_4590093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4590095 : List Nat := [1, 1, 2, 1, 1, 1, 2, 5, 1, 4, 4]
def baseStart_4590095 : Nat := 118140960795 + 4590095 * 2 ^ 59
def prefixEnd_4590095 : Nat := 4983230072969 + 3 ^ 40 * 4590095 * 2
def baseEnd_4590095 : Nat := 2356924984799323965903043

theorem tailTrace_4590095 : CollatzResearch.WordTrace tailWord_4590095 prefixEnd_4590095 2356924984799323965903043 := by
  unfold tailWord_4590095
  simp only [CollatzResearch.WordTrace]
  refine ⟨167414518305877215659587739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111609678870584810439725159 167414518305877215659587739)
  ·
    refine ⟨251121777458815823489381609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167414518305877215659587739 251121777458815823489381609)
    ·
      refine ⟨188341333094111867617036207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 251121777458815823489381609 188341333094111867617036207)
      ·
        refine ⟨282511999641167801425554311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188341333094111867617036207 282511999641167801425554311)
        ·
          refine ⟨423767999461751702138331467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 282511999641167801425554311 423767999461751702138331467)
          ·
            refine ⟨635651999192627553207497201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 423767999461751702138331467 635651999192627553207497201)
            ·
              refine ⟨476738999394470664905622901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 635651999192627553207497201 476738999394470664905622901)
              ·
                refine ⟨44694281193231624834902147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 476738999394470664905622901 44694281193231624834902147)
                ·
                  refine ⟨67041421789847437252353221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44694281193231624834902147 67041421789847437252353221)
                  ·
                    refine ⟨12570266585596394484816229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 67041421789847437252353221 12570266585596394484816229)
                    ·
                      refine ⟨2356924984799323965903043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12570266585596394484816229 2356924984799323965903043)
                      ·
                        rfl

theorem cell23_4590095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 4, 4].length) (baseStart_4590095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4590095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4590095 prefixEnd_4590095 := by exact prefixLift 4590095
  have htrace : WordTrace (prefixWord ++ tailWord_4590095) baseStart_4590095 baseEnd_4590095 := by
    simpa [prefixWord, tailWord_4590095, baseEnd_4590095] using wordTrace_append hprefix tailTrace_4590095
  have hstable : (prefixWord ++ tailWord_4590095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4590095).length < 2 ^ (prefixWord ++ tailWord_4590095).sum := by decide
  have hdescent : baseEnd_4590095 < baseStart_4590095 := by decide
  rcases family_descends (prefixWord ++ tailWord_4590095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4590099 : List Nat := [1, 1, 1, 2, 1, 5, 4, 1, 1, 4, 2]
def baseStart_4590099 : Nat := 118140960795 + 4590099 * 2 ^ 59
def prefixEnd_4590099 : Nat := 4983230072969 + 3 ^ 40 * 4590099 * 2
def baseEnd_4590099 : Nat := 2356927038721941950253025

theorem tailTrace_4590099 : CollatzResearch.WordTrace tailWord_4590099 prefixEnd_4590099 2356927038721941950253025 := by
  unfold tailWord_4590099
  simp only [CollatzResearch.WordTrace]
  refine ⟨167414664197862724342733351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111609776131908482895155567 167414664197862724342733351)
  ·
    refine ⟨251121996296794086514100027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167414664197862724342733351 251121996296794086514100027)
    ·
      refine ⟨376682994445191129771150041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251121996296794086514100027 376682994445191129771150041)
      ·
        refine ⟨282512245833893347328362531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 376682994445191129771150041 282512245833893347328362531)
        ·
          refine ⟨423768368750840020992543797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 282512245833893347328362531 423768368750840020992543797)
          ·
            refine ⟨39728284570391251968050981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 423768368750840020992543797 39728284570391251968050981)
            ·
              refine ⟨7449053356948359744009559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39728284570391251968050981 7449053356948359744009559)
              ·
                refine ⟨11173580035422539616014339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7449053356948359744009559 11173580035422539616014339)
                ·
                  refine ⟨16760370053133809424021509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11173580035422539616014339 16760370053133809424021509)
                  ·
                    refine ⟨3142569384962589267004033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16760370053133809424021509 3142569384962589267004033)
                    ·
                      refine ⟨2356927038721941950253025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3142569384962589267004033 2356927038721941950253025)
                      ·
                        rfl

theorem cell23_4590099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 1, 1, 4, 2].length) (baseStart_4590099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4590099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4590099 prefixEnd_4590099 := by exact prefixLift 4590099
  have htrace : WordTrace (prefixWord ++ tailWord_4590099) baseStart_4590099 baseEnd_4590099 := by
    simpa [prefixWord, tailWord_4590099, baseEnd_4590099] using wordTrace_append hprefix tailTrace_4590099
  have hstable : (prefixWord ++ tailWord_4590099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4590099).length < 2 ^ (prefixWord ++ tailWord_4590099).sum := by decide
  have hdescent : baseEnd_4590099 < baseStart_4590099 := by decide
  rcases family_descends (prefixWord ++ tailWord_4590099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4590105 : List Nat := [1, 2, 1, 2, 1, 1, 2, 6, 7]
def baseStart_4590105 : Nat := 118140960795 + 4590105 * 2 ^ 59
def prefixEnd_4590105 : Nat := 4983230072969 + 3 ^ 40 * 4590105 * 2
def baseEnd_4590105 : Nat := 261881124400652102975333

theorem tailTrace_4590105 : CollatzResearch.WordTrace tailWord_4590105 prefixEnd_4590105 261881124400652102975333 := by
  unfold tailWord_4590105
  simp only [CollatzResearch.WordTrace]
  refine ⟨167414883035840987367451769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111609922023893991578301179 167414883035840987367451769)
  ·
    refine ⟨125561162276880740525588827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167414883035840987367451769 125561162276880740525588827)
    ·
      refine ⟨188341743415321110788383241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125561162276880740525588827 188341743415321110788383241)
      ·
        refine ⟨141256307561490833091287431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188341743415321110788383241 141256307561490833091287431)
        ·
          refine ⟨211884461342236249636931147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141256307561490833091287431 211884461342236249636931147)
          ·
            refine ⟨317826692013354374455396721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 211884461342236249636931147 317826692013354374455396721)
            ·
              refine ⟨238370019010015780841547541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 317826692013354374455396721 238370019010015780841547541)
              ·
                refine ⟨11173594641094489726947541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 238370019010015780841547541 11173594641094489726947541)
                ·
                  refine ⟨261881124400652102975333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11173594641094489726947541 261881124400652102975333)
                  ·
                    rfl

theorem cell23_4590105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 6, 7].length) (baseStart_4590105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4590105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4590105 prefixEnd_4590105 := by exact prefixLift 4590105
  have htrace : WordTrace (prefixWord ++ tailWord_4590105) baseStart_4590105 baseEnd_4590105 := by
    simpa [prefixWord, tailWord_4590105, baseEnd_4590105] using wordTrace_append hprefix tailTrace_4590105
  have hstable : (prefixWord ++ tailWord_4590105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4590105).length < 2 ^ (prefixWord ++ tailWord_4590105).sum := by decide
  have hdescent : baseEnd_4590105 < baseStart_4590105 := by decide
  rcases family_descends (prefixWord ++ tailWord_4590105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4590120 : List Nat := [2, 1, 5, 2, 1, 3, 2, 1, 1, 3, 2]
def baseStart_4590120 : Nat := 118140960795 + 4590120 * 2 ^ 59
def prefixEnd_4590120 : Nat := 4983230072969 + 3 ^ 40 * 4590120 * 2
def baseEnd_4590120 : Nat := 2356937821815686368090429

theorem tailTrace_4590120 : CollatzResearch.WordTrace tailWord_4590120 prefixEnd_4590120 2356937821815686368090429 := by
  unfold tailWord_4590120
  simp only [CollatzResearch.WordTrace]
  refine ⟨83707715065393322464623907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111610286753857763286165209 83707715065393322464623907)
  ·
    refine ⟨125561572598089983696935861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83707715065393322464623907 125561572598089983696935861)
    ·
      refine ⟨11771397431070935971587737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 125561572598089983696935861 11771397431070935971587737)
      ·
        refine ⟨8828548073303201978690803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11771397431070935971587737 8828548073303201978690803)
        ·
          refine ⟨13242822109954802968036205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8828548073303201978690803 13242822109954802968036205)
          ·
            refine ⟨4966058291233051113013577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13242822109954802968036205 4966058291233051113013577)
            ·
              refine ⟨3724543718424788334760183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4966058291233051113013577 3724543718424788334760183)
              ·
                refine ⟨5586815577637182502140275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3724543718424788334760183 5586815577637182502140275)
                ·
                  refine ⟨8380223366455773753210413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5586815577637182502140275 8380223366455773753210413)
                  ·
                    refine ⟨3142583762420915157453905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8380223366455773753210413 3142583762420915157453905)
                    ·
                      refine ⟨2356937821815686368090429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3142583762420915157453905 2356937821815686368090429)
                      ·
                        rfl

theorem cell23_4590120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_4590120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4590120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4590120 prefixEnd_4590120 := by exact prefixLift 4590120
  have htrace : WordTrace (prefixWord ++ tailWord_4590120) baseStart_4590120 baseEnd_4590120 := by
    simpa [prefixWord, tailWord_4590120, baseEnd_4590120] using wordTrace_append hprefix tailTrace_4590120
  have hstable : (prefixWord ++ tailWord_4590120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4590120).length < 2 ^ (prefixWord ++ tailWord_4590120).sum := by decide
  have hdescent : baseEnd_4590120 < baseStart_4590120 := by decide
  rcases family_descends (prefixWord ++ tailWord_4590120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4590150 : List Nat := [6, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2]
def baseStart_4590150 : Nat := 118140960795 + 4590150 * 2 ^ 59
def prefixEnd_4590150 : Nat := 4983230072969 + 3 ^ 40 * 4590150 * 2
def baseEnd_4590150 : Nat := 2356953226235321250715291

theorem tailTrace_4590150 : CollatzResearch.WordTrace tailWord_4590150 prefixEnd_4590150 2356953226235321250715291 := by
  unfold tailWord_4590150
  simp only [CollatzResearch.WordTrace]
  refine ⟨5231766385021186251651247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 111611016213785306701893269 5231766385021186251651247)
  ·
    refine ⟨7847649577531779377476871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5231766385021186251651247 7847649577531779377476871)
    ·
      refine ⟨11771474366297669066215307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7847649577531779377476871 11771474366297669066215307)
      ·
        refine ⟨17657211549446503599322961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11771474366297669066215307 17657211549446503599322961)
        ·
          refine ⟨13242908662084877699492221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17657211549446503599322961 13242908662084877699492221)
          ·
            refine ⟨4966090748281829137309583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13242908662084877699492221 4966090748281829137309583)
            ·
              refine ⟨7449136122422743705964375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4966090748281829137309583 7449136122422743705964375)
              ·
                refine ⟨11173704183634115558946563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7449136122422743705964375 11173704183634115558946563)
                ·
                  refine ⟨16760556275451173338419845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11173704183634115558946563 16760556275451173338419845)
                  ·
                    refine ⟨3142604301647095000953721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16760556275451173338419845 3142604301647095000953721)
                    ·
                      refine ⟨2356953226235321250715291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3142604301647095000953721 2356953226235321250715291)
                      ·
                        rfl

theorem cell23_4590150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2].length) (baseStart_4590150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4590150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4590150 prefixEnd_4590150 := by exact prefixLift 4590150
  have htrace : WordTrace (prefixWord ++ tailWord_4590150) baseStart_4590150 baseEnd_4590150 := by
    simpa [prefixWord, tailWord_4590150, baseEnd_4590150] using wordTrace_append hprefix tailTrace_4590150
  have hstable : (prefixWord ++ tailWord_4590150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4590150).length < 2 ^ (prefixWord ++ tailWord_4590150).sum := by decide
  have hdescent : baseEnd_4590150 < baseStart_4590150 := by decide
  rcases family_descends (prefixWord ++ tailWord_4590150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4590189 : List Nat := [1, 5, 1, 1, 3, 1, 1, 1, 4, 1, 4]
def baseStart_4590189 : Nat := 118140960795 + 4590189 * 2 ^ 59
def prefixEnd_4590189 : Nat := 4983230072969 + 3 ^ 40 * 4590189 * 2
def baseEnd_4590189 : Nat := 2356973251980846598127611

theorem tailTrace_4590189 : CollatzResearch.WordTrace tailWord_4590189 prefixEnd_4590189 2356973251980846598127611 := by
  unfold tailWord_4590189
  simp only [CollatzResearch.WordTrace]
  refine ⟨167417946767536669713509621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111611964511691113142339747 167417946767536669713509621)
  ·
    refine ⟨15695432509456562785641527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 167417946767536669713509621 15695432509456562785641527)
    ·
      refine ⟨23543148764184844178462291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15695432509456562785641527 23543148764184844178462291)
      ·
        refine ⟨35314723146277266267693437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23543148764184844178462291 35314723146277266267693437)
        ·
          refine ⟨13243021179853974850385039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35314723146277266267693437 13243021179853974850385039)
          ·
            refine ⟨19864531769780962275577559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13243021179853974850385039 19864531769780962275577559)
            ·
              refine ⟨29796797654671443413366339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19864531769780962275577559 29796797654671443413366339)
              ·
                refine ⟨44695196482007165120049509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29796797654671443413366339 44695196482007165120049509)
                ·
                  refine ⟨8380349340376343460009283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44695196482007165120049509 8380349340376343460009283)
                  ·
                    refine ⟨12570524010564515190013925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8380349340376343460009283 12570524010564515190013925)
                    ·
                      refine ⟨2356973251980846598127611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12570524010564515190013925 2356973251980846598127611)
                      ·
                        rfl

theorem cell23_4590189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_4590189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4590189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4590189 prefixEnd_4590189 := by exact prefixLift 4590189
  have htrace : WordTrace (prefixWord ++ tailWord_4590189) baseStart_4590189 baseEnd_4590189 := by
    simpa [prefixWord, tailWord_4590189, baseEnd_4590189] using wordTrace_append hprefix tailTrace_4590189
  have hstable : (prefixWord ++ tailWord_4590189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4590189).length < 2 ^ (prefixWord ++ tailWord_4590189).sum := by decide
  have hdescent : baseEnd_4590189 < baseStart_4590189 := by decide
  rcases family_descends (prefixWord ++ tailWord_4590189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4590199 : List Nat := [1, 1, 3, 1, 1, 3, 5, 1, 3, 4]
def baseStart_4590199 : Nat := 118140960795 + 4590199 * 2 ^ 59
def prefixEnd_4590199 : Nat := 4983230072969 + 3 ^ 40 * 4590199 * 2
def baseEnd_4590199 : Nat := 785659462262463853000855

theorem tailTrace_4590199 : CollatzResearch.WordTrace tailWord_4590199 prefixEnd_4590199 785659462262463853000855 := by
  unfold tailWord_4590199
  simp only [CollatzResearch.WordTrace]
  refine ⟨167418311497500441421373651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111612207665000294280915767 167418311497500441421373651)
  ·
    refine ⟨251127467246250662132060477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167418311497500441421373651 251127467246250662132060477)
    ·
      refine ⟨94172800217343998299522679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 251127467246250662132060477 94172800217343998299522679)
      ·
        refine ⟨141259200326015997449284019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94172800217343998299522679 141259200326015997449284019)
        ·
          refine ⟨211888800489023996173926029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141259200326015997449284019 211888800489023996173926029)
          ·
            refine ⟨79458300183383998565222261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 211888800489023996173926029 79458300183383998565222261)
            ·
              refine ⟨7449215642192249865489587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 79458300183383998565222261 7449215642192249865489587)
              ·
                refine ⟨11173823463288374798234381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7449215642192249865489587 11173823463288374798234381)
                ·
                  refine ⟨4190183798733140549337893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11173823463288374798234381 4190183798733140549337893)
                  ·
                    refine ⟨785659462262463853000855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4190183798733140549337893 785659462262463853000855)
                    ·
                      rfl

theorem cell23_4590199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 1, 3, 4].length) (baseStart_4590199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4590199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4590199 prefixEnd_4590199 := by exact prefixLift 4590199
  have htrace : WordTrace (prefixWord ++ tailWord_4590199) baseStart_4590199 baseEnd_4590199 := by
    simpa [prefixWord, tailWord_4590199, baseEnd_4590199] using wordTrace_append hprefix tailTrace_4590199
  have hstable : (prefixWord ++ tailWord_4590199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4590199).length < 2 ^ (prefixWord ++ tailWord_4590199).sum := by decide
  have hdescent : baseEnd_4590199 < baseStart_4590199 := by decide
  rcases family_descends (prefixWord ++ tailWord_4590199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4590209 : List Nat := [1, 2, 4, 2, 1, 1, 1, 2, 4, 2, 3]
def baseStart_4590209 : Nat := 118140960795 + 4590209 * 2 ^ 59
def prefixEnd_4590209 : Nat := 4983230072969 + 3 ^ 40 * 4590209 * 2
def baseEnd_4590209 : Nat := 2356983521593936519877519

theorem tailTrace_4590209 : CollatzResearch.WordTrace tailWord_4590209 prefixEnd_4590209 2356983521593936519877519 := by
  unfold tailWord_4590209
  simp only [CollatzResearch.WordTrace]
  refine ⟨167418676227464213129237681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111612450818309475419491787 167418676227464213129237681)
  ·
    refine ⟨125564007170598159846928261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167418676227464213129237681 125564007170598159846928261)
    ·
      refine ⟨23543251344487154971299049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 125564007170598159846928261 23543251344487154971299049)
      ·
        refine ⟨17657438508365366228474287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23543251344487154971299049 17657438508365366228474287)
        ·
          refine ⟨26486157762548049342711431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17657438508365366228474287 26486157762548049342711431)
          ·
            refine ⟨39729236643822074014067147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26486157762548049342711431 39729236643822074014067147)
            ·
              refine ⟨59593854965733111021100721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39729236643822074014067147 59593854965733111021100721)
              ·
                refine ⟨44695391224299833265825541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59593854965733111021100721 44695391224299833265825541)
                ·
                  refine ⟨8380385854556218737342289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44695391224299833265825541 8380385854556218737342289)
                  ·
                    refine ⟨6285289390917164053006717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8380385854556218737342289 6285289390917164053006717)
                    ·
                      refine ⟨2356983521593936519877519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6285289390917164053006717 2356983521593936519877519)
                      ·
                        rfl

theorem cell23_4590209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_4590209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4590209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4590209 prefixEnd_4590209 := by exact prefixLift 4590209
  have htrace : WordTrace (prefixWord ++ tailWord_4590209) baseStart_4590209 baseEnd_4590209 := by
    simpa [prefixWord, tailWord_4590209, baseEnd_4590209] using wordTrace_append hprefix tailTrace_4590209
  have hstable : (prefixWord ++ tailWord_4590209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4590209).length < 2 ^ (prefixWord ++ tailWord_4590209).sum := by decide
  have hdescent : baseEnd_4590209 < baseStart_4590209 := by decide
  rcases family_descends (prefixWord ++ tailWord_4590209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4590226 : List Nat := [3, 2, 3, 1, 2, 1, 1, 3, 2, 2, 3]
def baseStart_4590226 : Nat := 118140960795 + 4590226 * 2 ^ 59
def prefixEnd_4590226 : Nat := 4983230072969 + 3 ^ 40 * 4590226 * 2
def baseEnd_4590226 : Nat := 2356992250765062953364941

theorem tailTrace_4590226 : CollatzResearch.WordTrace tailWord_4590226 prefixEnd_4590226 2356992250765062953364941 := by
  unfold tailWord_4590226
  simp only [CollatzResearch.WordTrace]
  refine ⟨41854824067100656258151633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111612864178935083355071021 41854824067100656258151633)
  ·
    refine ⟨31391118050325492193613725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41854824067100656258151633 31391118050325492193613725)
    ·
      refine ⟨11771669268872059572605147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31391118050325492193613725 11771669268872059572605147)
      ·
        refine ⟨17657503903308089358907721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11771669268872059572605147 17657503903308089358907721)
        ·
          refine ⟨13243127927481067019180791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17657503903308089358907721 13243127927481067019180791)
          ·
            refine ⟨19864691891221600528771187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13243127927481067019180791 19864691891221600528771187)
            ·
              refine ⟨29797037836832400793156781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19864691891221600528771187 29797037836832400793156781)
              ·
                refine ⟨11173889188812150297433793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29797037836832400793156781 11173889188812150297433793)
                ·
                  refine ⟨8380416891609112723075345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11173889188812150297433793 8380416891609112723075345)
                  ·
                    refine ⟨6285312668706834542306509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8380416891609112723075345 6285312668706834542306509)
                    ·
                      refine ⟨2356992250765062953364941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6285312668706834542306509 2356992250765062953364941)
                      ·
                        rfl

theorem cell23_4590226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_4590226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4590226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4590226 prefixEnd_4590226 := by exact prefixLift 4590226
  have htrace : WordTrace (prefixWord ++ tailWord_4590226) baseStart_4590226 baseEnd_4590226 := by
    simpa [prefixWord, tailWord_4590226, baseEnd_4590226] using wordTrace_append hprefix tailTrace_4590226
  have hstable : (prefixWord ++ tailWord_4590226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4590226).length < 2 ^ (prefixWord ++ tailWord_4590226).sum := by decide
  have hdescent : baseEnd_4590226 < baseStart_4590226 := by decide
  rcases family_descends (prefixWord ++ tailWord_4590226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4590279 : List Nat := [1, 1, 4, 1, 1, 1, 2, 1, 1, 8, 2]
def baseStart_4590279 : Nat := 118140960795 + 4590279 * 2 ^ 59
def prefixEnd_4590279 : Nat := 4983230072969 + 3 ^ 40 * 4590279 * 2
def baseEnd_4590279 : Nat := 2357019465239751246002197

theorem tailTrace_4590279 : CollatzResearch.WordTrace tailWord_4590279 prefixEnd_4590279 2357019465239751246002197 := by
  unfold tailWord_4590279
  simp only [CollatzResearch.WordTrace]
  refine ⟨167421229337210615084285891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111614152891473743389523927 167421229337210615084285891)
  ·
    refine ⟨251131844005815922626428837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167421229337210615084285891 251131844005815922626428837)
    ·
      refine ⟨47087220751090485492455407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 251131844005815922626428837 47087220751090485492455407)
      ·
        refine ⟨70630831126635728238683111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47087220751090485492455407 70630831126635728238683111)
        ·
          refine ⟨105946246689953592358024667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70630831126635728238683111 105946246689953592358024667)
          ·
            refine ⟨158919370034930388537037001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105946246689953592358024667 158919370034930388537037001)
            ·
              refine ⟨119189527526197791402777751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 158919370034930388537037001 119189527526197791402777751)
              ·
                refine ⟨178784291289296687104166627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119189527526197791402777751 178784291289296687104166627)
                ·
                  refine ⟨268176436933945030656249941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 178784291289296687104166627 268176436933945030656249941)
                  ·
                    refine ⟨3142692620319668328002929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 268176436933945030656249941 3142692620319668328002929)
                    ·
                      refine ⟨2357019465239751246002197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3142692620319668328002929 2357019465239751246002197)
                      ·
                        rfl

theorem cell23_4590279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 8, 2].length) (baseStart_4590279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4590279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4590279 prefixEnd_4590279 := by exact prefixLift 4590279
  have htrace : WordTrace (prefixWord ++ tailWord_4590279) baseStart_4590279 baseEnd_4590279 := by
    simpa [prefixWord, tailWord_4590279, baseEnd_4590279] using wordTrace_append hprefix tailTrace_4590279
  have hstable : (prefixWord ++ tailWord_4590279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4590279).length < 2 ^ (prefixWord ++ tailWord_4590279).sum := by decide
  have hdescent : baseEnd_4590279 < baseStart_4590279 := by decide
  rcases family_descends (prefixWord ++ tailWord_4590279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4590289 : List Nat := [1, 2, 2, 1, 2, 3, 2, 2, 4, 4]
def baseStart_4590289 : Nat := 118140960795 + 4590289 * 2 ^ 59
def prefixEnd_4590289 : Nat := 4983230072969 + 3 ^ 40 * 4590289 * 2
def baseEnd_4590289 : Nat := 785674866682098735625717

theorem tailTrace_4590289 : CollatzResearch.WordTrace tailWord_4590289 prefixEnd_4590289 785674866682098735625717 := by
  unfold tailWord_4590289
  simp only [CollatzResearch.WordTrace]
  refine ⟨167421594067174386792149921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111614396044782924528099947 167421594067174386792149921)
  ·
    refine ⟨125566195550380790094112441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167421594067174386792149921 125566195550380790094112441)
    ·
      refine ⟨94174646662785592570584331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125566195550380790094112441 94174646662785592570584331)
      ·
        refine ⟨141261969994178388855876497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94174646662785592570584331 141261969994178388855876497)
        ·
          refine ⟨105946477495633791641907373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141261969994178388855876497 105946477495633791641907373)
          ·
            refine ⟨39729929060862671865715265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105946477495633791641907373 39729929060862671865715265)
            ·
              refine ⟨29797446795647003899286449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39729929060862671865715265 29797446795647003899286449)
              ·
                refine ⟨22348085096735252924464837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29797446795647003899286449 22348085096735252924464837)
                ·
                  refine ⟨4190265955637859923337157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22348085096735252924464837 4190265955637859923337157)
                  ·
                    refine ⟨785674866682098735625717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4190265955637859923337157 785674866682098735625717)
                    ·
                      rfl

theorem cell23_4590289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 4, 4].length) (baseStart_4590289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4590289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4590289 prefixEnd_4590289 := by exact prefixLift 4590289
  have htrace : WordTrace (prefixWord ++ tailWord_4590289) baseStart_4590289 baseEnd_4590289 := by
    simpa [prefixWord, tailWord_4590289, baseEnd_4590289] using wordTrace_append hprefix tailTrace_4590289
  have hstable : (prefixWord ++ tailWord_4590289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4590289).length < 2 ^ (prefixWord ++ tailWord_4590289).sum := by decide
  have hdescent : baseEnd_4590289 < baseStart_4590289 := by decide
  rcases family_descends (prefixWord ++ tailWord_4590289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4590293 : List Nat := [1, 3, 2, 5, 1, 1, 1, 3, 1, 5]
def baseStart_4590293 : Nat := 118140960795 + 4590293 * 2 ^ 59
def prefixEnd_4590293 : Nat := 4983230072969 + 3 ^ 40 * 4590293 * 2
def baseEnd_4590293 : Nat := 785675551322971397075711

theorem tailTrace_4590293 : CollatzResearch.WordTrace tailWord_4590293 prefixEnd_4590293 785675551322971397075711 := by
  unfold tailWord_4590293
  simp only [CollatzResearch.WordTrace]
  refine ⟨167421739959159895475295533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111614493306106596983530355 167421739959159895475295533)
  ·
    refine ⟨62783152484684960803235825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167421739959159895475295533 62783152484684960803235825)
    ·
      refine ⟨47087364363513720602426869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62783152484684960803235825 47087364363513720602426869)
      ·
        refine ⟨4414440409079411306477519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47087364363513720602426869 4414440409079411306477519)
        ·
          refine ⟨6621660613619116959716279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4414440409079411306477519 6621660613619116959716279)
          ·
            refine ⟨9932490920428675439574419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6621660613619116959716279 9932490920428675439574419)
            ·
              refine ⟨14898736380643013159361629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9932490920428675439574419 14898736380643013159361629)
              ·
                refine ⟨5587026142741129934760611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14898736380643013159361629 5587026142741129934760611)
                ·
                  refine ⟨8380539214111694902140917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5587026142741129934760611 8380539214111694902140917)
                  ·
                    refine ⟨785675551322971397075711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8380539214111694902140917 785675551322971397075711)
                    ·
                      rfl

theorem cell23_4590293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 3, 1, 5].length) (baseStart_4590293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4590293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4590293 prefixEnd_4590293 := by exact prefixLift 4590293
  have htrace : WordTrace (prefixWord ++ tailWord_4590293) baseStart_4590293 baseEnd_4590293 := by
    simpa [prefixWord, tailWord_4590293, baseEnd_4590293] using wordTrace_append hprefix tailTrace_4590293
  have hstable : (prefixWord ++ tailWord_4590293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4590293).length < 2 ^ (prefixWord ++ tailWord_4590293).sum := by decide
  have hdescent : baseEnd_4590293 < baseStart_4590293 := by decide
  rcases family_descends (prefixWord ++ tailWord_4590293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4590296 : List Nat := [2, 1, 2, 2, 3, 3, 1, 3, 1, 1, 4]
def baseStart_4590296 : Nat := 118140960795 + 4590296 * 2 ^ 59
def prefixEnd_4590296 : Nat := 4983230072969 + 3 ^ 40 * 4590296 * 2
def baseEnd_4590296 : Nat := 2357028194410877679489619

theorem tailTrace_4590296 : CollatzResearch.WordTrace tailWord_4590296 prefixEnd_4590296 2357028194410877679489619 := by
  unfold tailWord_4590296
  simp only [CollatzResearch.WordTrace]
  refine ⟨83710924689074513493827371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111614566252099351325103161 83710924689074513493827371)
  ·
    refine ⟨125566387033611770240741057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83710924689074513493827371 125566387033611770240741057)
    ·
      refine ⟨94174790275208827680555793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125566387033611770240741057 94174790275208827680555793)
      ·
        refine ⟨70631092706406620760416845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94174790275208827680555793 70631092706406620760416845)
        ·
          refine ⟨26486659764902482785156317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70631092706406620760416845 26486659764902482785156317)
          ·
            refine ⟨9932497411838431044433619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26486659764902482785156317 9932497411838431044433619)
            ·
              refine ⟨14898746117757646566650429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9932497411838431044433619 14898746117757646566650429)
              ·
                refine ⟨5587029794159117462493911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14898746117757646566650429 5587029794159117462493911)
                ·
                  refine ⟨8380544691238676193740867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5587029794159117462493911 8380544691238676193740867)
                  ·
                    refine ⟨12570817036858014290611301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8380544691238676193740867 12570817036858014290611301)
                    ·
                      refine ⟨2357028194410877679489619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12570817036858014290611301 2357028194410877679489619)
                      ·
                        rfl

theorem cell23_4590296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 3, 1, 1, 4].length) (baseStart_4590296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4590296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4590296 prefixEnd_4590296 := by exact prefixLift 4590296
  have htrace : WordTrace (prefixWord ++ tailWord_4590296) baseStart_4590296 baseEnd_4590296 := by
    simpa [prefixWord, tailWord_4590296, baseEnd_4590296] using wordTrace_append hprefix tailTrace_4590296
  have hstable : (prefixWord ++ tailWord_4590296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4590296).length < 2 ^ (prefixWord ++ tailWord_4590296).sum := by decide
  have hdescent : baseEnd_4590296 < baseStart_4590296 := by decide
  rcases family_descends (prefixWord ++ tailWord_4590296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4590346 : List Nat := [3, 1, 2, 2, 1, 2, 1, 1, 6, 1, 3]
def baseStart_4590346 : Nat := 118140960795 + 4590346 * 2 ^ 59
def prefixEnd_4590346 : Nat := 4983230072969 + 3 ^ 40 * 4590346 * 2
def baseEnd_4590346 : Nat := 2357053868443602483864389

theorem tailTrace_4590346 : CollatzResearch.WordTrace tailWord_4590346 prefixEnd_4590346 2357053868443602483864389 := by
  unfold tailWord_4590346
  simp only [CollatzResearch.WordTrace]
  refine ⟨41855918256991971381743723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111615782018645257017983261 41855918256991971381743723)
  ·
    refine ⟨62783877385487957072615585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41855918256991971381743723 62783877385487957072615585)
    ·
      refine ⟨47087908039115967804461689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62783877385487957072615585 47087908039115967804461689)
      ·
        refine ⟨35315931029336975853346267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47087908039115967804461689 35315931029336975853346267)
        ·
          refine ⟨52973896544005463780019401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35315931029336975853346267 52973896544005463780019401)
          ·
            refine ⟨39730422408004097835014551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52973896544005463780019401 39730422408004097835014551)
            ·
              refine ⟨59595633612006146752521827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39730422408004097835014551 59595633612006146752521827)
              ·
                refine ⟨89393450418009220128782741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59595633612006146752521827 89393450418009220128782741)
                ·
                  refine ⟨4190317988344182193536691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 89393450418009220128782741 4190317988344182193536691)
                  ·
                    refine ⟨6285476982516273290305037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4190317988344182193536691 6285476982516273290305037)
                    ·
                      refine ⟨2357053868443602483864389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6285476982516273290305037 2357053868443602483864389)
                      ·
                        rfl

theorem cell23_4590346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 6, 1, 3].length) (baseStart_4590346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4590346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4590346 prefixEnd_4590346 := by exact prefixLift 4590346
  have htrace : WordTrace (prefixWord ++ tailWord_4590346) baseStart_4590346 baseEnd_4590346 := by
    simpa [prefixWord, tailWord_4590346, baseEnd_4590346] using wordTrace_append hprefix tailTrace_4590346
  have hstable : (prefixWord ++ tailWord_4590346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4590346).length < 2 ^ (prefixWord ++ tailWord_4590346).sum := by decide
  have hdescent : baseEnd_4590346 < baseStart_4590346 := by decide
  rcases family_descends (prefixWord ++ tailWord_4590346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4590369 : List Nat := [1, 2, 3, 2, 1, 2, 2, 1, 2, 3, 4]
def baseStart_4590369 : Nat := 118140960795 + 4590369 * 2 ^ 59
def prefixEnd_4590369 : Nat := 4983230072969 + 3 ^ 40 * 4590369 * 2
def baseEnd_4590369 : Nat := 2357065678498655893876783

theorem tailTrace_4590369 : CollatzResearch.WordTrace tailWord_4590369 prefixEnd_4590369 2357065678498655893876783 := by
  unfold tailWord_4590369
  simp only [CollatzResearch.WordTrace]
  refine ⟨167424511906884560455062161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111616341271256373636708107 167424511906884560455062161)
  ·
    refine ⟨125568383930163420341296621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167424511906884560455062161 125568383930163420341296621)
    ·
      refine ⟨47088143973811282627986233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125568383930163420341296621 47088143973811282627986233)
      ·
        refine ⟨35316107980358461970989675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47088143973811282627986233 35316107980358461970989675)
        ·
          refine ⟨52974161970537692956484513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35316107980358461970989675 52974161970537692956484513)
          ·
            refine ⟨39730621477903269717363385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52974161970537692956484513 39730621477903269717363385)
            ·
              refine ⟨29797966108427452288022539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39730621477903269717363385 29797966108427452288022539)
              ·
                refine ⟨44696949162641178432033809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29797966108427452288022539 44696949162641178432033809)
                ·
                  refine ⟨33522711871980883824025357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44696949162641178432033809 33522711871980883824025357)
                  ·
                    refine ⟨12571016951992831434009509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33522711871980883824025357 12571016951992831434009509)
                    ·
                      refine ⟨2357065678498655893876783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12571016951992831434009509 2357065678498655893876783)
                      ·
                        rfl

theorem cell23_4590369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_4590369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4590369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4590369 prefixEnd_4590369 := by exact prefixLift 4590369
  have htrace : WordTrace (prefixWord ++ tailWord_4590369) baseStart_4590369 baseEnd_4590369 := by
    simpa [prefixWord, tailWord_4590369, baseEnd_4590369] using wordTrace_append hprefix tailTrace_4590369
  have hstable : (prefixWord ++ tailWord_4590369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4590369).length < 2 ^ (prefixWord ++ tailWord_4590369).sum := by decide
  have hdescent : baseEnd_4590369 < baseStart_4590369 := by decide
  rcases family_descends (prefixWord ++ tailWord_4590369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4590419 : List Nat := [1, 1, 1, 2, 1, 1, 3, 2, 3, 5, 3]
def baseStart_4590419 : Nat := 118140960795 + 4590419 * 2 ^ 59
def prefixEnd_4590419 : Nat := 4983230072969 + 3 ^ 40 * 4590419 * 2
def baseEnd_4590419 : Nat := 2357091352531380698251553

theorem tailTrace_4590419 : CollatzResearch.WordTrace tailWord_4590419 prefixEnd_4590419 2357091352531380698251553 := by
  unfold tailWord_4590419
  simp only [CollatzResearch.WordTrace]
  refine ⟨167426335556703418994382311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111617557037802279329588207 167426335556703418994382311)
  ·
    refine ⟨251139503335055128491573467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167426335556703418994382311 251139503335055128491573467)
    ·
      refine ⟨376709255002582692737360201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251139503335055128491573467 376709255002582692737360201)
      ·
        refine ⟨282531941251937019553020151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 376709255002582692737360201 282531941251937019553020151)
        ·
          refine ⟨423797911877905529329530227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 282531941251937019553020151 423797911877905529329530227)
          ·
            refine ⟨635696867816858293994295341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 423797911877905529329530227 635696867816858293994295341)
            ·
              refine ⟨238386325431321860247860753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 635696867816858293994295341 238386325431321860247860753)
              ·
                refine ⟨178789744073491395185895565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 238386325431321860247860753 178789744073491395185895565)
                ·
                  refine ⟨67046154027559273194710837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 178789744073491395185895565 67046154027559273194710837)
                  ·
                    refine ⟨6285576940083681862004141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 67046154027559273194710837 6285576940083681862004141)
                    ·
                      refine ⟨2357091352531380698251553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6285576940083681862004141 2357091352531380698251553)
                      ·
                        rfl

theorem cell23_4590419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 5, 3].length) (baseStart_4590419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4590419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4590419 prefixEnd_4590419 := by exact prefixLift 4590419
  have htrace : WordTrace (prefixWord ++ tailWord_4590419) baseStart_4590419 baseEnd_4590419 := by
    simpa [prefixWord, tailWord_4590419, baseEnd_4590419] using wordTrace_append hprefix tailTrace_4590419
  have hstable : (prefixWord ++ tailWord_4590419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4590419).length < 2 ^ (prefixWord ++ tailWord_4590419).sum := by decide
  have hdescent : baseEnd_4590419 < baseStart_4590419 := by decide
  rcases family_descends (prefixWord ++ tailWord_4590419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4590436 : List Nat := [2, 3, 1, 1, 4, 1, 1, 1, 1, 5, 3]
def baseStart_4590436 : Nat := 118140960795 + 4590436 * 2 ^ 59
def prefixEnd_4590436 : Nat := 4983230072969 + 3 ^ 40 * 4590436 * 2
def baseEnd_4590436 : Nat := 2357100081702507131738975

theorem tailTrace_4590436 : CollatzResearch.WordTrace tailWord_4590436 prefixEnd_4590436 2357100081702507131738975 := by
  unfold tailWord_4590436
  simp only [CollatzResearch.WordTrace]
  refine ⟨83713477798820915448875581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111617970398427887265167441 83713477798820915448875581)
  ·
    refine ⟨31392554174557843293328343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83713477798820915448875581 31392554174557843293328343)
    ·
      refine ⟨47088831261836764939992515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31392554174557843293328343 47088831261836764939992515)
      ·
        refine ⟨70633246892755147409988773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47088831261836764939992515 70633246892755147409988773)
        ·
          refine ⟨13243733792391590139372895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70633246892755147409988773 13243733792391590139372895)
          ·
            refine ⟨19865600688587385209059343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13243733792391590139372895 19865600688587385209059343)
            ·
              refine ⟨29798401032881077813589015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19865600688587385209059343 29798401032881077813589015)
              ·
                refine ⟨44697601549321616720383523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29798401032881077813589015 44697601549321616720383523)
                ·
                  refine ⟨67046402323982425080575285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44697601549321616720383523 67046402323982425080575285)
                  ·
                    refine ⟨6285600217873352351303933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 67046402323982425080575285 6285600217873352351303933)
                    ·
                      refine ⟨2357100081702507131738975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6285600217873352351303933 2357100081702507131738975)
                      ·
                        rfl

theorem cell23_4590436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 1, 5, 3].length) (baseStart_4590436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4590436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4590436 prefixEnd_4590436 := by exact prefixLift 4590436
  have htrace : WordTrace (prefixWord ++ tailWord_4590436) baseStart_4590436 baseEnd_4590436 := by
    simpa [prefixWord, tailWord_4590436, baseEnd_4590436] using wordTrace_append hprefix tailTrace_4590436
  have hstable : (prefixWord ++ tailWord_4590436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4590436).length < 2 ^ (prefixWord ++ tailWord_4590436).sum := by decide
  have hdescent : baseEnd_4590436 < baseStart_4590436 := by decide
  rcases family_descends (prefixWord ++ tailWord_4590436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4590476 : List Nat := [2, 2, 1, 2, 1, 2, 2, 4, 2, 1, 4]
def baseStart_4590476 : Nat := 118140960795 + 4590476 * 2 ^ 59
def prefixEnd_4590476 : Nat := 4983230072969 + 3 ^ 40 * 4590476 * 2
def baseEnd_4590476 : Nat := 2357120620928686975238791

theorem tailTrace_4590476 : CollatzResearch.WordTrace tailWord_4590476 prefixEnd_4590476 2357120620928686975238791 := by
  unfold tailWord_4590476
  simp only [CollatzResearch.WordTrace]
  refine ⟨83714207258748458864603641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111618943011664611819471521 83714207258748458864603641)
  ·
    refine ⟨62785655444061344148452731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83714207258748458864603641 62785655444061344148452731)
    ·
      refine ⟨94178483166092016222679097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62785655444061344148452731 94178483166092016222679097)
      ·
        refine ⟨70633862374569012167009323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94178483166092016222679097 70633862374569012167009323)
        ·
          refine ⟨105950793561853518250513985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70633862374569012167009323 105950793561853518250513985)
          ·
            refine ⟨79463095171390138687885489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105950793561853518250513985 79463095171390138687885489)
            ·
              refine ⟨59597321378542604015914117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79463095171390138687885489 59597321378542604015914117)
              ·
                refine ⟨11174497758476738252983897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59597321378542604015914117 11174497758476738252983897)
                ·
                  refine ⟨8380873318857553689737923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11174497758476738252983897 8380873318857553689737923)
                  ·
                    refine ⟨12571309978286330534606885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8380873318857553689737923 12571309978286330534606885)
                    ·
                      refine ⟨2357120620928686975238791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12571309978286330534606885 2357120620928686975238791)
                      ·
                        rfl

theorem cell23_4590476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 4, 2, 1, 4].length) (baseStart_4590476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4590476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4590476 prefixEnd_4590476 := by exact prefixLift 4590476
  have htrace : WordTrace (prefixWord ++ tailWord_4590476) baseStart_4590476 baseEnd_4590476 := by
    simpa [prefixWord, tailWord_4590476, baseEnd_4590476] using wordTrace_append hprefix tailTrace_4590476
  have hstable : (prefixWord ++ tailWord_4590476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4590476).length < 2 ^ (prefixWord ++ tailWord_4590476).sum := by decide
  have hdescent : baseEnd_4590476 < baseStart_4590476 := by decide
  rcases family_descends (prefixWord ++ tailWord_4590476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4590489 : List Nat := [1, 2, 1, 2, 1, 3, 1, 1, 4, 1, 6]
def baseStart_4590489 : Nat := 118140960795 + 4590489 * 2 ^ 59
def prefixEnd_4590489 : Nat := 4983230072969 + 3 ^ 40 * 4590489 * 2
def baseEnd_4590489 : Nat := 2357127296177195424376231

theorem tailTrace_4590489 : CollatzResearch.WordTrace tailWord_4590489 prefixEnd_4590489 2357127296177195424376231 := by
  unfold tailWord_4590489
  simp only [CollatzResearch.WordTrace]
  refine ⟨167428888666449820949430521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111619259110966547299620347 167428888666449820949430521)
  ·
    refine ⟨125571666499837365712072891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167428888666449820949430521 125571666499837365712072891)
    ·
      refine ⟨188357499749756048568109337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125571666499837365712072891 188357499749756048568109337)
      ·
        refine ⟨141268124812317036426082003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188357499749756048568109337 141268124812317036426082003)
        ·
          refine ⟨211902187218475554639123005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141268124812317036426082003 211902187218475554639123005)
          ·
            refine ⟨79463320206928332989671127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 211902187218475554639123005 79463320206928332989671127)
            ·
              refine ⟨119194980310392499484506691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79463320206928332989671127 119194980310392499484506691)
              ·
                refine ⟨178792470465588749226760037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119194980310392499484506691 178792470465588749226760037)
                ·
                  refine ⟨33523588212297890480017507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 178792470465588749226760037 33523588212297890480017507)
                  ·
                    refine ⟨50285382318446835720026261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33523588212297890480017507 50285382318446835720026261)
                    ·
                      refine ⟨2357127296177195424376231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50285382318446835720026261 2357127296177195424376231)
                      ·
                        rfl

theorem cell23_4590489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 1, 6].length) (baseStart_4590489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4590489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4590489 prefixEnd_4590489 := by exact prefixLift 4590489
  have htrace : WordTrace (prefixWord ++ tailWord_4590489) baseStart_4590489 baseEnd_4590489 := by
    simpa [prefixWord, tailWord_4590489, baseEnd_4590489] using wordTrace_append hprefix tailTrace_4590489
  have hstable : (prefixWord ++ tailWord_4590489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4590489).length < 2 ^ (prefixWord ++ tailWord_4590489).sum := by decide
  have hdescent : baseEnd_4590489 < baseStart_4590489 := by decide
  rcases family_descends (prefixWord ++ tailWord_4590489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4590493 : List Nat := [1, 4, 2, 1, 2, 1, 1, 3, 2, 4, 2]
def baseStart_4590493 : Nat := 118140960795 + 4590493 * 2 ^ 59
def prefixEnd_4590493 : Nat := 4983230072969 + 3 ^ 40 * 4590493 * 2
def baseEnd_4590493 : Nat := 2357129350099813408726213

theorem tailTrace_4590493 : CollatzResearch.WordTrace tailWord_4590493 prefixEnd_4590493 2357129350099813408726213 := by
  unfold tailWord_4590493
  simp only [CollatzResearch.WordTrace]
  refine ⟨167429034558435329632576133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111619356372290219755050755 167429034558435329632576133)
  ·
    refine ⟨31392943979706624306108025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 167429034558435329632576133 31392943979706624306108025)
    ·
      refine ⟨23544707984779968229581019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31392943979706624306108025 23544707984779968229581019)
      ·
        refine ⟨35317061977169952344371529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23544707984779968229581019 35317061977169952344371529)
        ·
          refine ⟨26487796482877464258278647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35317061977169952344371529 26487796482877464258278647)
          ·
            refine ⟨39731694724316196387417971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26487796482877464258278647 39731694724316196387417971)
            ·
              refine ⟨59597542086474294581126957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39731694724316196387417971 59597542086474294581126957)
              ·
                refine ⟨22349078282427860467922609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59597542086474294581126957 22349078282427860467922609)
                ·
                  refine ⟨16761808711820895350941957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22349078282427860467922609 16761808711820895350941957)
                  ·
                    refine ⟨3142839133466417878301617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16761808711820895350941957 3142839133466417878301617)
                    ·
                      refine ⟨2357129350099813408726213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3142839133466417878301617 2357129350099813408726213)
                      ·
                        rfl

theorem cell23_4590493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 2, 4, 2].length) (baseStart_4590493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4590493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4590493 prefixEnd_4590493 := by exact prefixLift 4590493
  have htrace : WordTrace (prefixWord ++ tailWord_4590493) baseStart_4590493 baseEnd_4590493 := by
    simpa [prefixWord, tailWord_4590493, baseEnd_4590493] using wordTrace_append hprefix tailTrace_4590493
  have hstable : (prefixWord ++ tailWord_4590493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4590493).length < 2 ^ (prefixWord ++ tailWord_4590493).sum := by decide
  have hdescent : baseEnd_4590493 < baseStart_4590493 := by decide
  rcases family_descends (prefixWord ++ tailWord_4590493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4590496 : List Nat := [2, 1, 1, 4, 1, 1, 3, 2, 1, 4, 3]
def baseStart_4590496 : Nat := 118140960795 + 4590496 * 2 ^ 59
def prefixEnd_4590496 : Nat := 4983230072969 + 3 ^ 40 * 4590496 * 2
def baseEnd_4590496 : Nat := 2357130890541776896988699

theorem tailTrace_4590496 : CollatzResearch.WordTrace tailWord_4590496 prefixEnd_4590496 2357130890541776896988699 := by
  unfold tailWord_4590496
  simp only [CollatzResearch.WordTrace]
  refine ⟨83714571988712230572467671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111619429318282974096623561 83714571988712230572467671)
  ·
    refine ⟨125571857983068345858701507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83714571988712230572467671 125571857983068345858701507)
    ·
      refine ⟨188357786974602518788052261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125571857983068345858701507 188357786974602518788052261)
      ·
        refine ⟨35317085057737972272759799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 188357786974602518788052261 35317085057737972272759799)
        ·
          refine ⟨52975627586606958409139699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35317085057737972272759799 52975627586606958409139699)
          ·
            refine ⟨79463441379910437613709549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52975627586606958409139699 79463441379910437613709549)
            ·
              refine ⟨29798790517466414105141081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79463441379910437613709549 29798790517466414105141081)
              ·
                refine ⟨22349092888099810578855811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29798790517466414105141081 22349092888099810578855811)
                ·
                  refine ⟨33523639332149715868283717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22349092888099810578855811 33523639332149715868283717)
                  ·
                    refine ⟨6285682374778071725303197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33523639332149715868283717 6285682374778071725303197)
                    ·
                      refine ⟨2357130890541776896988699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6285682374778071725303197 2357130890541776896988699)
                      ·
                        rfl

theorem cell23_4590496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 1, 4, 3].length) (baseStart_4590496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4590496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4590496 prefixEnd_4590496 := by exact prefixLift 4590496
  have htrace : WordTrace (prefixWord ++ tailWord_4590496) baseStart_4590496 baseEnd_4590496 := by
    simpa [prefixWord, tailWord_4590496, baseEnd_4590496] using wordTrace_append hprefix tailTrace_4590496
  have hstable : (prefixWord ++ tailWord_4590496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4590496).length < 2 ^ (prefixWord ++ tailWord_4590496).sum := by decide
  have hdescent : baseEnd_4590496 < baseStart_4590496 := by decide
  rcases family_descends (prefixWord ++ tailWord_4590496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4590520 : List Nat := [2, 1, 2, 1, 2, 4, 3, 3, 1, 4]
def baseStart_4590520 : Nat := 118140960795 + 4590520 * 2 ^ 59
def prefixEnd_4590520 : Nat := 4983230072969 + 3 ^ 40 * 4590520 * 2
def baseEnd_4590520 : Nat := 785714404692494934362863

theorem tailTrace_4590520 : CollatzResearch.WordTrace tailWord_4590520 prefixEnd_4590520 785714404692494934362863 := by
  unfold tailWord_4590520
  simp only [CollatzResearch.WordTrace]
  refine ⟨83715009664668756621904507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111620012886225008829206009 83715009664668756621904507)
  ·
    refine ⟨125572514497003134932856761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83715009664668756621904507 125572514497003134932856761)
    ·
      refine ⟨94179385872752351199642571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125572514497003134932856761 94179385872752351199642571)
      ·
        refine ⟨141269078809128526799463857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94179385872752351199642571 141269078809128526799463857)
        ·
          refine ⟨105951809106846395099597893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141269078809128526799463857 105951809106846395099597893)
          ·
            refine ⟨19865964207533699081174605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 105951809106846395099597893 19865964207533699081174605)
            ·
              refine ⟨7449736577825137155440477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19865964207533699081174605 7449736577825137155440477)
              ·
                refine ⟨2793651216684426433290179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7449736577825137155440477 2793651216684426433290179)
                ·
                  refine ⟨4190476825026639649935269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2793651216684426433290179 4190476825026639649935269)
                  ·
                    refine ⟨785714404692494934362863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4190476825026639649935269 785714404692494934362863)
                    ·
                      rfl

theorem cell23_4590520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 3, 1, 4].length) (baseStart_4590520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4590520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4590520 prefixEnd_4590520 := by exact prefixLift 4590520
  have htrace : WordTrace (prefixWord ++ tailWord_4590520) baseStart_4590520 baseEnd_4590520 := by
    simpa [prefixWord, tailWord_4590520, baseEnd_4590520] using wordTrace_append hprefix tailTrace_4590520
  have hstable : (prefixWord ++ tailWord_4590520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4590520).length < 2 ^ (prefixWord ++ tailWord_4590520).sum := by decide
  have hdescent : baseEnd_4590520 < baseStart_4590520 := by decide
  rcases family_descends (prefixWord ++ tailWord_4590520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4590534 : List Nat := [6, 1, 3, 1, 1, 1, 1, 1, 1, 2, 5]
def baseStart_4590534 : Nat := 118140960795 + 4590534 * 2 ^ 59
def prefixEnd_4590534 : Nat := 4983230072969 + 3 ^ 40 * 4590534 * 2
def baseEnd_4590534 : Nat := 2357150402806647748313525

theorem tailTrace_4590534 : CollatzResearch.WordTrace tailWord_4590534 prefixEnd_4590534 2357150402806647748313525 := by
  unfold tailWord_4590534
  simp only [CollatzResearch.WordTrace]
  refine ⟨5232204060977712301088083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 111620353300857862423212437 5232204060977712301088083)
  ·
    refine ⟨7848306091466568451632125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5232204060977712301088083 7848306091466568451632125)
    ·
      refine ⟨2943114784299963169362047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7848306091466568451632125 2943114784299963169362047)
      ·
        refine ⟨4414672176449944754043071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2943114784299963169362047 4414672176449944754043071)
        ·
          refine ⟨6622008264674917131064607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4414672176449944754043071 6622008264674917131064607)
          ·
            refine ⟨9933012397012375696596911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6622008264674917131064607 9933012397012375696596911)
            ·
              refine ⟨14899518595518563544895367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9933012397012375696596911 14899518595518563544895367)
              ·
                refine ⟨22349277893277845317343051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14899518595518563544895367 22349277893277845317343051)
                ·
                  refine ⟨33523916839916767976014577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22349277893277845317343051 33523916839916767976014577)
                  ·
                    refine ⟨25142937629937575982010933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33523916839916767976014577 25142937629937575982010933)
                    ·
                      refine ⟨2357150402806647748313525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25142937629937575982010933 2357150402806647748313525)
                      ·
                        rfl

theorem cell23_4590534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_4590534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4590534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4590534 prefixEnd_4590534 := by exact prefixLift 4590534
  have htrace : WordTrace (prefixWord ++ tailWord_4590534) baseStart_4590534 baseEnd_4590534 := by
    simpa [prefixWord, tailWord_4590534, baseEnd_4590534] using wordTrace_append hprefix tailTrace_4590534
  have hstable : (prefixWord ++ tailWord_4590534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4590534).length < 2 ^ (prefixWord ++ tailWord_4590534).sum := by decide
  have hdescent : baseEnd_4590534 < baseStart_4590534 := by decide
  rcases family_descends (prefixWord ++ tailWord_4590534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4590550 : List Nat := [5, 2, 1, 1, 2, 2, 1, 3, 6]
def baseStart_4590550 : Nat := 118140960795 + 4590550 * 2 ^ 59
def prefixEnd_4590550 : Nat := 4983230072969 + 3 ^ 40 * 4590550 * 2
def baseEnd_4590550 : Nat := 261906513166346631745939

theorem tailTrace_4590550 : CollatzResearch.WordTrace tailWord_4590550 prefixEnd_4590550 261906513166346631745939 := by
  unfold tailWord_4590550
  simp only [CollatzResearch.WordTrace]
  refine ⟨10464444594951801772962569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 111620742346152552244934069 10464444594951801772962569)
  ·
    refine ⟨7848333446213851329721927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10464444594951801772962569 7848333446213851329721927)
    ·
      refine ⟨11772500169320776994582891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7848333446213851329721927 11772500169320776994582891)
      ·
        refine ⟨17658750253981165491874337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11772500169320776994582891 17658750253981165491874337)
        ·
          refine ⟨13244062690485874118905753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17658750253981165491874337 13244062690485874118905753)
          ·
            refine ⟨9933047017864405589179315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13244062690485874118905753 9933047017864405589179315)
            ·
              refine ⟨14899570526796608383768973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9933047017864405589179315 14899570526796608383768973)
              ·
                refine ⟨5587338947548728143913365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14899570526796608383768973 5587338947548728143913365)
                ·
                  refine ⟨261906513166346631745939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5587338947548728143913365 261906513166346631745939)
                  ·
                    rfl

theorem cell23_4590550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_4590550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4590550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4590550 prefixEnd_4590550 := by exact prefixLift 4590550
  have htrace : WordTrace (prefixWord ++ tailWord_4590550) baseStart_4590550 baseEnd_4590550 := by
    simpa [prefixWord, tailWord_4590550, baseEnd_4590550] using wordTrace_append hprefix tailTrace_4590550
  have hstable : (prefixWord ++ tailWord_4590550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4590550).length < 2 ^ (prefixWord ++ tailWord_4590550).sum := by decide
  have hdescent : baseEnd_4590550 < baseStart_4590550 := by decide
  rcases family_descends (prefixWord ++ tailWord_4590550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4590570 : List Nat := [3, 1, 3, 1, 2, 2, 1, 3, 2, 3, 2]
def baseStart_4590570 : Nat := 118140960795 + 4590570 * 2 ^ 59
def prefixEnd_4590570 : Nat := 4983230072969 + 3 ^ 40 * 4590570 * 2
def baseEnd_4590570 : Nat := 2357168888110209607463359

theorem tailTrace_4590570 : CollatzResearch.WordTrace tailWord_4590570 prefixEnd_4590570 2357168888110209607463359 := by
  unfold tailWord_4590570
  simp only [CollatzResearch.WordTrace]
  refine ⟨41857960744789092945782291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111621228652770914522086109 41857960744789092945782291)
  ·
    refine ⟨62786941117183639418673437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41857960744789092945782291 62786941117183639418673437)
    ·
      refine ⟨23545102918943864782002539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62786941117183639418673437 23545102918943864782002539)
      ·
        refine ⟨35317654378415797173003809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23545102918943864782002539 35317654378415797173003809)
        ·
          refine ⟨26488240783811847879752857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35317654378415797173003809 26488240783811847879752857)
          ·
            refine ⟨19866180587858885909814643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26488240783811847879752857 19866180587858885909814643)
            ·
              refine ⟨29799270881788328864721965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19866180587858885909814643 29799270881788328864721965)
              ·
                refine ⟨11174726580670623324270737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29799270881788328864721965 11174726580670623324270737)
                ·
                  refine ⟨8381044935502967493203053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11174726580670623324270737 8381044935502967493203053)
                  ·
                    refine ⟨3142891850813612809951145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8381044935502967493203053 3142891850813612809951145)
                    ·
                      refine ⟨2357168888110209607463359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3142891850813612809951145 2357168888110209607463359)
                      ·
                        rfl

theorem cell23_4590570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 3, 2, 3, 2].length) (baseStart_4590570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4590570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4590570 prefixEnd_4590570 := by exact prefixLift 4590570
  have htrace : WordTrace (prefixWord ++ tailWord_4590570) baseStart_4590570 baseEnd_4590570 := by
    simpa [prefixWord, tailWord_4590570, baseEnd_4590570] using wordTrace_append hprefix tailTrace_4590570
  have hstable : (prefixWord ++ tailWord_4590570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4590570).length < 2 ^ (prefixWord ++ tailWord_4590570).sum := by decide
  have hdescent : baseEnd_4590570 < baseStart_4590570 := by decide
  rcases family_descends (prefixWord ++ tailWord_4590570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4590603 : List Nat := [1, 1, 1, 1, 6, 2, 1, 2, 3, 2, 3]
def baseStart_4590603 : Nat := 118140960795 + 4590603 * 2 ^ 59
def prefixEnd_4590603 : Nat := 4983230072969 + 3 ^ 40 * 4590603 * 2
def baseEnd_4590603 : Nat := 2357185832971807978350707

theorem tailTrace_4590603 : CollatzResearch.WordTrace tailWord_4590603 prefixEnd_4590603 2357185832971807978350707 := by
  unfold tailWord_4590603
  simp only [CollatzResearch.WordTrace]
  refine ⟨167433046588036818419080463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111622031058691212279386975 167433046588036818419080463)
  ·
    refine ⟨251149569882055227628620695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167433046588036818419080463 251149569882055227628620695)
    ·
      refine ⟨376724354823082841442931043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251149569882055227628620695 376724354823082841442931043)
      ·
        refine ⟨565086532234624262164396565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 376724354823082841442931043 565086532234624262164396565)
        ·
          refine ⟨26488431198498012288956089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 565086532234624262164396565 26488431198498012288956089)
          ·
            refine ⟨19866323398873509216717067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26488431198498012288956089 19866323398873509216717067)
            ·
              refine ⟨29799485098310263825075601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19866323398873509216717067 29799485098310263825075601)
              ·
                refine ⟨22349613823732697868806701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29799485098310263825075601 22349613823732697868806701)
                ·
                  refine ⟨8381105183899761700802513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22349613823732697868806701 8381105183899761700802513)
                  ·
                    refine ⟨6285828887924821275601885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8381105183899761700802513 6285828887924821275601885)
                    ·
                      refine ⟨2357185832971807978350707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6285828887924821275601885 2357185832971807978350707)
                      ·
                        rfl

theorem cell23_4590603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 3, 2, 3].length) (baseStart_4590603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4590603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4590603 prefixEnd_4590603 := by exact prefixLift 4590603
  have htrace : WordTrace (prefixWord ++ tailWord_4590603) baseStart_4590603 baseEnd_4590603 := by
    simpa [prefixWord, tailWord_4590603, baseEnd_4590603] using wordTrace_append hprefix tailTrace_4590603
  have hstable : (prefixWord ++ tailWord_4590603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4590603).length < 2 ^ (prefixWord ++ tailWord_4590603).sum := by decide
  have hdescent : baseEnd_4590603 < baseStart_4590603 := by decide
  rcases family_descends (prefixWord ++ tailWord_4590603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4590613 : List Nat := [1, 3, 2, 1, 4, 1, 1, 3, 1, 2, 4]
def baseStart_4590613 : Nat := 118140960795 + 4590613 * 2 ^ 59
def prefixEnd_4590613 : Nat := 4983230072969 + 3 ^ 40 * 4590613 * 2
def baseEnd_4590613 : Nat := 2357190967778352939225661

theorem tailTrace_4590613 : CollatzResearch.WordTrace tailWord_4590613 prefixEnd_4590613 2357190967778352939225661 := by
  unfold tailWord_4590613
  simp only [CollatzResearch.WordTrace]
  refine ⟨167433411318000590126944493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111622274212000393417962995 167433411318000590126944493)
  ·
    refine ⟨62787529244250221297604185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167433411318000590126944493 62787529244250221297604185)
    ·
      refine ⟨47090646933187665973203139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62787529244250221297604185 47090646933187665973203139)
      ·
        refine ⟨70635970399781498959804709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47090646933187665973203139 70635970399781498959804709)
        ·
          refine ⟨13244244449959031054963383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70635970399781498959804709 13244244449959031054963383)
          ·
            refine ⟨19866366674938546582445075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13244244449959031054963383 19866366674938546582445075)
            ·
              refine ⟨29799550012407819873667613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19866366674938546582445075 29799550012407819873667613)
              ·
                refine ⟨11174831254652932452625355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29799550012407819873667613 11174831254652932452625355)
                ·
                  refine ⟨16762246881979398678938033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11174831254652932452625355 16762246881979398678938033)
                  ·
                    refine ⟨12571685161484549009203525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16762246881979398678938033 12571685161484549009203525)
                    ·
                      refine ⟨2357190967778352939225661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12571685161484549009203525 2357190967778352939225661)
                      ·
                        rfl

theorem cell23_4590613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 3, 1, 2, 4].length) (baseStart_4590613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4590613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4590613 prefixEnd_4590613 := by exact prefixLift 4590613
  have htrace : WordTrace (prefixWord ++ tailWord_4590613) baseStart_4590613 baseEnd_4590613 := by
    simpa [prefixWord, tailWord_4590613, baseEnd_4590613] using wordTrace_append hprefix tailTrace_4590613
  have hstable : (prefixWord ++ tailWord_4590613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4590613).length < 2 ^ (prefixWord ++ tailWord_4590613).sum := by decide
  have hdescent : baseEnd_4590613 < baseStart_4590613 := by decide
  rcases family_descends (prefixWord ++ tailWord_4590613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4590623 : List Nat := [1, 1, 2, 4, 1, 4, 3, 7]
def baseStart_4590623 : Nat := 118140960795 + 4590623 * 2 ^ 59
def prefixEnd_4590623 : Nat := 4983230072969 + 3 ^ 40 * 4590623 * 2
def baseEnd_4590623 : Nat := 87303559354996218522245

theorem tailTrace_4590623 : CollatzResearch.WordTrace tailWord_4590623 prefixEnd_4590623 87303559354996218522245 := by
  unfold tailWord_4590623
  simp only [CollatzResearch.WordTrace]
  refine ⟨167433776047964361834808523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111622517365309574556539015 167433776047964361834808523)
  ·
    refine ⟨251150664071946542752212785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167433776047964361834808523 251150664071946542752212785)
    ·
      refine ⟨188362998053959907064159589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 251150664071946542752212785 188362998053959907064159589)
      ·
        refine ⟨35318062135117482574529923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 188362998053959907064159589 35318062135117482574529923)
        ·
          refine ⟨52977093202676223861794885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35318062135117482574529923 52977093202676223861794885)
          ·
            refine ⟨9933204975501791974086541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52977093202676223861794885 9933204975501791974086541)
            ·
              refine ⟨3724951865813171990282453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9933204975501791974086541 3724951865813171990282453)
              ·
                refine ⟨87303559354996218522245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3724951865813171990282453 87303559354996218522245)
                ·
                  rfl

theorem cell23_4590623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 3, 7].length) (baseStart_4590623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4590623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4590623 prefixEnd_4590623 := by exact prefixLift 4590623
  have htrace : WordTrace (prefixWord ++ tailWord_4590623) baseStart_4590623 baseEnd_4590623 := by
    simpa [prefixWord, tailWord_4590623, baseEnd_4590623] using wordTrace_append hprefix tailTrace_4590623
  have hstable : (prefixWord ++ tailWord_4590623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4590623).length < 2 ^ (prefixWord ++ tailWord_4590623).sum := by decide
  have hdescent : baseEnd_4590623 < baseStart_4590623 := by decide
  rcases family_descends (prefixWord ++ tailWord_4590623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4590634 : List Nat := [3, 1, 4, 1, 3, 2, 2, 1, 1, 1, 4]
def baseStart_4590634 : Nat := 118140960795 + 4590634 * 2 ^ 59
def prefixEnd_4590634 : Nat := 4983230072969 + 3 ^ 40 * 4590634 * 2
def baseEnd_4590634 : Nat := 2357201750872097357063065

theorem tailTrace_4590634 : CollatzResearch.WordTrace tailWord_4590634 prefixEnd_4590634 2357201750872097357063065 := by
  unfold tailWord_4590634
  simp only [CollatzResearch.WordTrace]
  refine ⟨41858544312731127678364739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111622784833949673808972637 41858544312731127678364739)
  ·
    refine ⟨62787816469096691517547109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41858544312731127678364739 62787816469096691517547109)
    ·
      refine ⟨11772715587955629659540083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62787816469096691517547109 11772715587955629659540083)
      ·
        refine ⟨17659073381933444489310125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11772715587955629659540083 17659073381933444489310125)
        ·
          refine ⟨6622152518225041683491297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17659073381933444489310125 6622152518225041683491297)
          ·
            refine ⟨4966614388668781262618473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6622152518225041683491297 4966614388668781262618473)
            ·
              refine ⟨3724960791501585946963855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4966614388668781262618473 3724960791501585946963855)
              ·
                refine ⟨5587441187252378920445783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3724960791501585946963855 5587441187252378920445783)
                ·
                  refine ⟨8381161780878568380668675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5587441187252378920445783 8381161780878568380668675)
                  ·
                    refine ⟨12571742671317852571003013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8381161780878568380668675 12571742671317852571003013)
                    ·
                      refine ⟨2357201750872097357063065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12571742671317852571003013 2357201750872097357063065)
                      ·
                        rfl

theorem cell23_4590634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 2, 1, 1, 1, 4].length) (baseStart_4590634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4590634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4590634 prefixEnd_4590634 := by exact prefixLift 4590634
  have htrace : WordTrace (prefixWord ++ tailWord_4590634) baseStart_4590634 baseEnd_4590634 := by
    simpa [prefixWord, tailWord_4590634, baseEnd_4590634] using wordTrace_append hprefix tailTrace_4590634
  have hstable : (prefixWord ++ tailWord_4590634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4590634).length < 2 ^ (prefixWord ++ tailWord_4590634).sum := by decide
  have hdescent : baseEnd_4590634 < baseStart_4590634 := by decide
  rcases family_descends (prefixWord ++ tailWord_4590634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4590644 : List Nat := [2, 5, 1, 2, 1, 3, 1, 2, 2, 4]
def baseStart_4590644 : Nat := 118140960795 + 4590644 * 2 ^ 59
def prefixEnd_4590644 : Nat := 4983230072969 + 3 ^ 40 * 4590644 * 2
def baseEnd_4590644 : Nat := 785735628559547439312673

theorem tailTrace_4590644 : CollatzResearch.WordTrace tailWord_4590644 prefixEnd_4590644 785735628559547439312673 := by
  unfold tailWord_4590644
  simp only [CollatzResearch.WordTrace]
  refine ⟨83717270990444141210661493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111623027987258854947548657 83717270990444141210661493)
  ·
    refine ⟨7848494155354138238499515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 83717270990444141210661493 7848494155354138238499515)
    ·
      refine ⟨11772741233031207357749273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7848494155354138238499515 11772741233031207357749273)
      ·
        refine ⟨8829555924773405518311955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11772741233031207357749273 8829555924773405518311955)
        ·
          refine ⟨13244333887160108277467933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8829555924773405518311955 13244333887160108277467933)
          ·
            refine ⟨4966625207685040604050475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13244333887160108277467933 4966625207685040604050475)
            ·
              refine ⟨7449937811527560906075713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4966625207685040604050475 7449937811527560906075713)
              ·
                refine ⟨5587453358645670679556785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7449937811527560906075713 5587453358645670679556785)
                ·
                  refine ⟨4190590018984253009667589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5587453358645670679556785 4190590018984253009667589)
                  ·
                    refine ⟨785735628559547439312673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4190590018984253009667589 785735628559547439312673)
                    ·
                      rfl

theorem cell23_4590644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_4590644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4590644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4590644 prefixEnd_4590644 := by exact prefixLift 4590644
  have htrace : WordTrace (prefixWord ++ tailWord_4590644) baseStart_4590644 baseEnd_4590644 := by
    simpa [prefixWord, tailWord_4590644, baseEnd_4590644] using wordTrace_append hprefix tailTrace_4590644
  have hstable : (prefixWord ++ tailWord_4590644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4590644).length < 2 ^ (prefixWord ++ tailWord_4590644).sum := by decide
  have hdescent : baseEnd_4590644 < baseStart_4590644 := by decide
  rcases family_descends (prefixWord ++ tailWord_4590644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4590677 : List Nat := [1, 3, 2, 2, 1, 2, 4, 2, 1, 3, 2]
def baseStart_4590677 : Nat := 118140960795 + 4590677 * 2 ^ 59
def prefixEnd_4590677 : Nat := 4983230072969 + 3 ^ 40 * 4590677 * 2
def baseEnd_4590677 : Nat := 2357223830540240688825367

theorem tailTrace_4590677 : CollatzResearch.WordTrace tailWord_4590677 prefixEnd_4590677 2357223830540240688825367 := by
  unfold tailWord_4590677
  simp only [CollatzResearch.WordTrace]
  refine ⟨167435745589768729057274285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111623830393179152704849523 167435745589768729057274285)
  ·
    refine ⟨62788404596163273396477857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167435745589768729057274285 62788404596163273396477857)
    ·
      refine ⟨47091303447122455047358393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62788404596163273396477857 47091303447122455047358393)
      ·
        refine ⟨35318477585341841285518795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47091303447122455047358393 35318477585341841285518795)
        ·
          refine ⟨52977716378012761928278193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35318477585341841285518795 52977716378012761928278193)
          ·
            refine ⟨39733287283509571446208645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52977716378012761928278193 39733287283509571446208645)
            ·
              refine ⟨7449991365658044646164121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39733287283509571446208645 7449991365658044646164121)
              ·
                refine ⟨5587493524243533484623091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7449991365658044646164121 5587493524243533484623091)
                ·
                  refine ⟨8381240286365300226934637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5587493524243533484623091 8381240286365300226934637)
                  ·
                    refine ⟨3142965107386987585100489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8381240286365300226934637 3142965107386987585100489)
                    ·
                      refine ⟨2357223830540240688825367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3142965107386987585100489 2357223830540240688825367)
                      ·
                        rfl

theorem cell23_4590677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 2, 1, 3, 2].length) (baseStart_4590677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4590677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4590677 prefixEnd_4590677 := by exact prefixLift 4590677
  have htrace : WordTrace (prefixWord ++ tailWord_4590677) baseStart_4590677 baseEnd_4590677 := by
    simpa [prefixWord, tailWord_4590677, baseEnd_4590677] using wordTrace_append hprefix tailTrace_4590677
  have hstable : (prefixWord ++ tailWord_4590677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4590677).length < 2 ^ (prefixWord ++ tailWord_4590677).sum := by decide
  have hdescent : baseEnd_4590677 < baseStart_4590677 := by decide
  rcases family_descends (prefixWord ++ tailWord_4590677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4590685 : List Nat := [1, 4, 4, 1, 3, 1, 1, 3, 1, 2, 2]
def baseStart_4590685 : Nat := 118140960795 + 4590685 * 2 ^ 59
def prefixEnd_4590685 : Nat := 4983230072969 + 3 ^ 40 * 4590685 * 2
def baseEnd_4590685 : Nat := 2357227938385476657525331

theorem tailTrace_4590685 : CollatzResearch.WordTrace tailWord_4590685 prefixEnd_4590685 2357227938385476657525331 := by
  unfold tailWord_4590685
  simp only [CollatzResearch.WordTrace]
  refine ⟨167436037373739746423565509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111624024915826497615710339 167436037373739746423565509)
  ·
    refine ⟨31394257007576202454418533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 167436037373739746423565509 31394257007576202454418533)
    ·
      refine ⟨5886423188920537960203475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31394257007576202454418533 5886423188920537960203475)
      ·
        refine ⟨8829634783380806940305213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5886423188920537960203475 8829634783380806940305213)
        ·
          refine ⟨3311113043767802602614455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8829634783380806940305213 3311113043767802602614455)
          ·
            refine ⟨4966669565651703903921683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3311113043767802602614455 4966669565651703903921683)
            ·
              refine ⟨7450004348477555855882525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4966669565651703903921683 7450004348477555855882525)
              ·
                refine ⟨2793751630679083445955947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7450004348477555855882525 2793751630679083445955947)
                ·
                  refine ⟨4190627446018625168933921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2793751630679083445955947 4190627446018625168933921)
                  ·
                    refine ⟨3142970584513968876700441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4190627446018625168933921 3142970584513968876700441)
                    ·
                      refine ⟨2357227938385476657525331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3142970584513968876700441 2357227938385476657525331)
                      ·
                        rfl

theorem cell23_4590685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_4590685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4590685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4590685 prefixEnd_4590685 := by exact prefixLift 4590685
  have htrace : WordTrace (prefixWord ++ tailWord_4590685) baseStart_4590685 baseEnd_4590685 := by
    simpa [prefixWord, tailWord_4590685, baseEnd_4590685] using wordTrace_append hprefix tailTrace_4590685
  have hstable : (prefixWord ++ tailWord_4590685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4590685).length < 2 ^ (prefixWord ++ tailWord_4590685).sum := by decide
  have hdescent : baseEnd_4590685 < baseStart_4590685 := by decide
  rcases family_descends (prefixWord ++ tailWord_4590685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4590693 : List Nat := [1, 3, 1, 3, 2, 1, 3, 1, 2, 1, 5]
def baseStart_4590693 : Nat := 118140960795 + 4590693 * 2 ^ 59
def prefixEnd_4590693 : Nat := 4983230072969 + 3 ^ 40 * 4590693 * 2
def baseEnd_4590693 : Nat := 2357232046230712626225293

theorem tailTrace_4590693 : CollatzResearch.WordTrace tailWord_4590693 prefixEnd_4590693 2357232046230712626225293 := by
  unfold tailWord_4590693
  simp only [CollatzResearch.WordTrace]
  refine ⟨167436329157710763789856733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111624219438473842526571155 167436329157710763789856733)
  ·
    refine ⟨62788623434141536421196275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167436329157710763789856733 62788623434141536421196275)
    ·
      refine ⟨94182935151212304631794413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62788623434141536421196275 94182935151212304631794413)
      ·
        refine ⟨35318600681704614236922905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94182935151212304631794413 35318600681704614236922905)
        ·
          refine ⟨26488950511278460677692179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35318600681704614236922905 26488950511278460677692179)
          ·
            refine ⟨39733425766917691016538269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26488950511278460677692179 39733425766917691016538269)
            ·
              refine ⟨14900034662594134131201851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39733425766917691016538269 14900034662594134131201851)
              ·
                refine ⟨22350051993891201196802777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14900034662594134131201851 22350051993891201196802777)
                ·
                  refine ⟨16762538995418400897602083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22350051993891201196802777 16762538995418400897602083)
                  ·
                    refine ⟨25143808493127601346403125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16762538995418400897602083 25143808493127601346403125)
                    ·
                      refine ⟨2357232046230712626225293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25143808493127601346403125 2357232046230712626225293)
                      ·
                        rfl

theorem cell23_4590693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_4590693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4590693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4590693 prefixEnd_4590693 := by exact prefixLift 4590693
  have htrace : WordTrace (prefixWord ++ tailWord_4590693) baseStart_4590693 baseEnd_4590693 := by
    simpa [prefixWord, tailWord_4590693, baseEnd_4590693] using wordTrace_append hprefix tailTrace_4590693
  have hstable : (prefixWord ++ tailWord_4590693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4590693).length < 2 ^ (prefixWord ++ tailWord_4590693).sum := by decide
  have hdescent : baseEnd_4590693 < baseStart_4590693 := by decide
  rcases family_descends (prefixWord ++ tailWord_4590693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4590710 : List Nat := [5, 1, 1, 2, 1, 1, 2, 1, 2, 4, 3]
def baseStart_4590710 : Nat := 118140960795 + 4590710 * 2 ^ 59
def prefixEnd_4590710 : Nat := 4983230072969 + 3 ^ 40 * 4590710 * 2
def baseEnd_4590710 : Nat := 2357240775401839059712715

theorem tailTrace_4590710 : CollatzResearch.WordTrace tailWord_4590710 prefixEnd_4590710 2357240775401839059712715 := by
  unfold tailWord_4590710
  simp only [CollatzResearch.WordTrace]
  refine ⟨10464809324915573480826599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 111624632799099450462150389 10464809324915573480826599)
  ·
    refine ⟨15697213987373360221239899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10464809324915573480826599 15697213987373360221239899)
    ·
      refine ⟨23545820981060040331859849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15697213987373360221239899 23545820981060040331859849)
      ·
        refine ⟨17659365735795030248894887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23545820981060040331859849 17659365735795030248894887)
        ·
          refine ⟨26489048603692545373342331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17659365735795030248894887 26489048603692545373342331)
          ·
            refine ⟨39733572905538818060013497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26489048603692545373342331 39733572905538818060013497)
            ·
              refine ⟨29800179679154113545010123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39733572905538818060013497 29800179679154113545010123)
              ·
                refine ⟨44700269518731170317515185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29800179679154113545010123 44700269518731170317515185)
                ·
                  refine ⟨33525202139048377738136389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44700269518731170317515185 33525202139048377738136389)
                  ·
                    refine ⟨6285975401071570825900573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33525202139048377738136389 6285975401071570825900573)
                    ·
                      refine ⟨2357240775401839059712715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6285975401071570825900573 2357240775401839059712715)
                      ·
                        rfl

theorem cell23_4590710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_4590710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4590710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4590710 prefixEnd_4590710 := by exact prefixLift 4590710
  have htrace : WordTrace (prefixWord ++ tailWord_4590710) baseStart_4590710 baseEnd_4590710 := by
    simpa [prefixWord, tailWord_4590710, baseEnd_4590710] using wordTrace_append hprefix tailTrace_4590710
  have hstable : (prefixWord ++ tailWord_4590710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4590710).length < 2 ^ (prefixWord ++ tailWord_4590710).sum := by decide
  have hdescent : baseEnd_4590710 < baseStart_4590710 := by decide
  rcases family_descends (prefixWord ++ tailWord_4590710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4590718 : List Nat := [4, 2, 4, 1, 1, 1, 1, 3, 2, 1, 3]
def baseStart_4590718 : Nat := 118140960795 + 4590718 * 2 ^ 59
def prefixEnd_4590718 : Nat := 4983230072969 + 3 ^ 40 * 4590718 * 2
def baseEnd_4590718 : Nat := 2357244883247075028412679

theorem tailTrace_4590718 : CollatzResearch.WordTrace tailWord_4590718 prefixEnd_4590718 2357244883247075028412679 := by
  unfold tailWord_4590718
  simp only [CollatzResearch.WordTrace]
  refine ⟨20929655122827524132439601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111624827321746795373011205 20929655122827524132439601)
  ·
    refine ⟨15697241342120643099329701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20929655122827524132439601 15697241342120643099329701)
    ·
      refine ⟨2943232751647620581124319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15697241342120643099329701 2943232751647620581124319)
      ·
        refine ⟨4414849127471430871686479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2943232751647620581124319 4414849127471430871686479)
        ·
          refine ⟨6622273691207146307529719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4414849127471430871686479 6622273691207146307529719)
          ·
            refine ⟨9933410536810719461294579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6622273691207146307529719 9933410536810719461294579)
            ·
              refine ⟨14900115805216079191941869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9933410536810719461294579 14900115805216079191941869)
              ·
                refine ⟨5587543426956029696978201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14900115805216079191941869 5587543426956029696978201)
                ·
                  refine ⟨4190657570217022272733651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5587543426956029696978201 4190657570217022272733651)
                  ·
                    refine ⟨6285986355325533409100477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4190657570217022272733651 6285986355325533409100477)
                    ·
                      refine ⟨2357244883247075028412679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6285986355325533409100477 2357244883247075028412679)
                      ·
                        rfl

theorem cell23_4590718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_4590718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4590718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4590718 prefixEnd_4590718 := by exact prefixLift 4590718
  have htrace : WordTrace (prefixWord ++ tailWord_4590718) baseStart_4590718 baseEnd_4590718 := by
    simpa [prefixWord, tailWord_4590718, baseEnd_4590718] using wordTrace_append hprefix tailTrace_4590718
  have hstable : (prefixWord ++ tailWord_4590718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4590718).length < 2 ^ (prefixWord ++ tailWord_4590718).sum := by decide
  have hdescent : baseEnd_4590718 < baseStart_4590718 := by decide
  rcases family_descends (prefixWord ++ tailWord_4590718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4590723 : List Nat := [1, 1, 1, 3, 3, 2, 2, 1, 1, 5, 3]
def baseStart_4590723 : Nat := 118140960795 + 4590723 * 2 ^ 59
def prefixEnd_4590723 : Nat := 4983230072969 + 3 ^ 40 * 4590723 * 2
def baseEnd_4590723 : Nat := 2357247450650347508850155

theorem tailTrace_4590723 : CollatzResearch.WordTrace tailWord_4590723 prefixEnd_4590723 2357247450650347508850155 := by
  unfold tailWord_4590723
  simp only [CollatzResearch.WordTrace]
  refine ⟨167437423347602078913448823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111624948898401385942299215 167437423347602078913448823)
  ·
    refine ⟨251156135021403118370173235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167437423347602078913448823 251156135021403118370173235)
    ·
      refine ⟨376734202532104677555259853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251156135021403118370173235 376734202532104677555259853)
      ·
        refine ⟨141275325949539254083222445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 376734202532104677555259853 141275325949539254083222445)
        ·
          refine ⟨52978247231077220281208417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 141275325949539254083222445 52978247231077220281208417)
          ·
            refine ⟨39733685423307915210906313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52978247231077220281208417 39733685423307915210906313)
            ·
              refine ⟨29800264067480936408179735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39733685423307915210906313 29800264067480936408179735)
              ·
                refine ⟨44700396101221404612269603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29800264067480936408179735 44700396101221404612269603)
                ·
                  refine ⟨67050594151832106918404405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44700396101221404612269603 67050594151832106918404405)
                  ·
                    refine ⟨6285993201734260023600413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 67050594151832106918404405 6285993201734260023600413)
                    ·
                      refine ⟨2357247450650347508850155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6285993201734260023600413 2357247450650347508850155)
                      ·
                        rfl

theorem cell23_4590723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 5, 3].length) (baseStart_4590723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4590723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4590723 prefixEnd_4590723 := by exact prefixLift 4590723
  have htrace : WordTrace (prefixWord ++ tailWord_4590723) baseStart_4590723 baseEnd_4590723 := by
    simpa [prefixWord, tailWord_4590723, baseEnd_4590723] using wordTrace_append hprefix tailTrace_4590723
  have hstable : (prefixWord ++ tailWord_4590723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4590723).length < 2 ^ (prefixWord ++ tailWord_4590723).sum := by decide
  have hdescent : baseEnd_4590723 < baseStart_4590723 := by decide
  rcases family_descends (prefixWord ++ tailWord_4590723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4590724 : List Nat := [2, 3, 2, 1, 2, 3, 1, 3, 2, 2, 2]
def baseStart_4590724 : Nat := 118140960795 + 4590724 * 2 ^ 59
def prefixEnd_4590724 : Nat := 4983230072969 + 3 ^ 40 * 4590724 * 2
def baseEnd_4590724 : Nat := 2357247964131002004937651

theorem tailTrace_4590724 : CollatzResearch.WordTrace tailWord_4590724 prefixEnd_4590724 2357247964131002004937651 := by
  unfold tailWord_4590724
  simp only [CollatzResearch.WordTrace]
  refine ⟨83718729910299228042117613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111624973213732304056156817 83718729910299228042117613)
  ·
    refine ⟨31394523716362210515794105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83718729910299228042117613 31394523716362210515794105)
    ·
      refine ⟨23545892787271657886845579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31394523716362210515794105 23545892787271657886845579)
      ·
        refine ⟨35318839180907486830268369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23545892787271657886845579 35318839180907486830268369)
        ·
          refine ⟨26489129385680615122701277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35318839180907486830268369 26489129385680615122701277)
          ·
            refine ⟨9933423519630230671012979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26489129385680615122701277 9933423519630230671012979)
            ·
              refine ⟨14900135279445346006519469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9933423519630230671012979 14900135279445346006519469)
              ·
                refine ⟨5587550729792004752444801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14900135279445346006519469 5587550729792004752444801)
                ·
                  refine ⟨4190663047344003564333601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5587550729792004752444801 4190663047344003564333601)
                  ·
                    refine ⟨3142997285508002673250201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4190663047344003564333601 3142997285508002673250201)
                    ·
                      refine ⟨2357247964131002004937651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3142997285508002673250201 2357247964131002004937651)
                      ·
                        rfl

theorem cell23_4590724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 3, 2, 2, 2].length) (baseStart_4590724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4590724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4590724 prefixEnd_4590724 := by exact prefixLift 4590724
  have htrace : WordTrace (prefixWord ++ tailWord_4590724) baseStart_4590724 baseEnd_4590724 := by
    simpa [prefixWord, tailWord_4590724, baseEnd_4590724] using wordTrace_append hprefix tailTrace_4590724
  have hstable : (prefixWord ++ tailWord_4590724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4590724).length < 2 ^ (prefixWord ++ tailWord_4590724).sum := by decide
  have hdescent : baseEnd_4590724 < baseStart_4590724 := by decide
  rcases family_descends (prefixWord ++ tailWord_4590724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4590753 : List Nat := [1, 2, 3, 3, 1, 1, 1, 1, 3, 2, 5]
def baseStart_4590753 : Nat := 118140960795 + 4590753 * 2 ^ 59
def prefixEnd_4590753 : Nat := 4983230072969 + 3 ^ 40 * 4590753 * 2
def baseEnd_4590753 : Nat := 2357262855069982391475017

theorem tailTrace_4590753 : CollatzResearch.WordTrace tailWord_4590753 prefixEnd_4590753 2357262855069982391475017 := by
  unfold tailWord_4590753
  simp only [CollatzResearch.WordTrace]
  refine ⟨167438517537493394037040913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111625678358328929358027275 167438517537493394037040913)
  ·
    refine ⟨125578888153120045527780685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167438517537493394037040913 125578888153120045527780685)
    ·
      refine ⟨47092083057420017072917757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125578888153120045527780685 47092083057420017072917757)
      ·
        refine ⟨17659531146532506402344159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47092083057420017072917757 17659531146532506402344159)
        ·
          refine ⟨26489296719798759603516239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17659531146532506402344159 26489296719798759603516239)
          ·
            refine ⟨39733945079698139405274359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26489296719798759603516239 39733945079698139405274359)
            ·
              refine ⟨59600917619547209107911539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39733945079698139405274359 59600917619547209107911539)
              ·
                refine ⟨89401376429320813661867309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59600917619547209107911539 89401376429320813661867309)
                ·
                  refine ⟨33525516160995305123200241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 89401376429320813661867309 33525516160995305123200241)
                  ·
                    refine ⟨25144137120746478842400181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33525516160995305123200241 25144137120746478842400181)
                    ·
                      refine ⟨2357262855069982391475017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25144137120746478842400181 2357262855069982391475017)
                      ·
                        rfl

theorem cell23_4590753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_4590753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4590753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4590753 prefixEnd_4590753 := by exact prefixLift 4590753
  have htrace : WordTrace (prefixWord ++ tailWord_4590753) baseStart_4590753 baseEnd_4590753 := by
    simpa [prefixWord, tailWord_4590753, baseEnd_4590753] using wordTrace_append hprefix tailTrace_4590753
  have hstable : (prefixWord ++ tailWord_4590753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4590753).length < 2 ^ (prefixWord ++ tailWord_4590753).sum := by decide
  have hdescent : baseEnd_4590753 < baseStart_4590753 := by decide
  rcases family_descends (prefixWord ++ tailWord_4590753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4590807 : List Nat := [1, 1, 3, 2, 1, 2, 3, 5, 1, 4]
def baseStart_4590807 : Nat := 118140960795 + 4590807 * 2 ^ 59
def prefixEnd_4590807 : Nat := 4983230072969 + 3 ^ 40 * 4590807 * 2
def baseEnd_4590807 : Nat := 785763527675108393399923

theorem tailTrace_4590807 : CollatzResearch.WordTrace tailWord_4590807 prefixEnd_4590807 785763527675108393399923 := by
  unfold tailWord_4590807
  simp only [CollatzResearch.WordTrace]
  refine ⟨167440487079297761259506675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111626991386198507506337783 167440487079297761259506675)
  ·
    refine ⟨251160730618946641889260013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167440487079297761259506675 251160730618946641889260013)
    ·
      refine ⟨94185273982104990708472505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 251160730618946641889260013 94185273982104990708472505)
      ·
        refine ⟨70638955486578743031354379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94185273982104990708472505 70638955486578743031354379)
        ·
          refine ⟨105958433229868114547031569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70638955486578743031354379 105958433229868114547031569)
          ·
            refine ⟨79468824922401085910273677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105958433229868114547031569 79468824922401085910273677)
            ·
              refine ⟨29800809345900407216352629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79468824922401085910273677 29800809345900407216352629)
              ·
                refine ⟨2793825876178163176533059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29800809345900407216352629 2793825876178163176533059)
                ·
                  refine ⟨4190738814267244764799589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2793825876178163176533059 4190738814267244764799589)
                  ·
                    refine ⟨785763527675108393399923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4190738814267244764799589 785763527675108393399923)
                    ·
                      rfl

theorem cell23_4590807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 5, 1, 4].length) (baseStart_4590807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4590807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4590807 prefixEnd_4590807 := by exact prefixLift 4590807
  have htrace : WordTrace (prefixWord ++ tailWord_4590807) baseStart_4590807 baseEnd_4590807 := by
    simpa [prefixWord, tailWord_4590807, baseEnd_4590807] using wordTrace_append hprefix tailTrace_4590807
  have hstable : (prefixWord ++ tailWord_4590807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4590807).length < 2 ^ (prefixWord ++ tailWord_4590807).sum := by decide
  have hdescent : baseEnd_4590807 < baseStart_4590807 := by decide
  rcases family_descends (prefixWord ++ tailWord_4590807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4590820 : List Nat := [2, 3, 1, 1, 1, 2, 5, 2, 6]
def baseStart_4590820 : Nat := 118140960795 + 4590820 * 2 ^ 59
def prefixEnd_4590820 : Nat := 4983230072969 + 3 ^ 40 * 4590820 * 2
def baseEnd_4590820 : Nat := 261921917585981514370801

theorem tailTrace_4590820 : CollatzResearch.WordTrace tailWord_4590820 prefixEnd_4590820 261921917585981514370801 := by
  unfold tailWord_4590820
  simp only [CollatzResearch.WordTrace]
  refine ⟨83720480614125332239864957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111627307485500442986486609 83720480614125332239864957)
  ·
    refine ⟨31395180230296999589949359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83720480614125332239864957 31395180230296999589949359)
    ·
      refine ⟨47092770345445499384924039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31395180230296999589949359 47092770345445499384924039)
      ·
        refine ⟨70639155518168249077386059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47092770345445499384924039 70639155518168249077386059)
        ·
          refine ⟨105958733277252373616079089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70639155518168249077386059 105958733277252373616079089)
          ·
            refine ⟨79469049957939280212059317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105958733277252373616079089 79469049957939280212059317)
            ·
              refine ⟨7450223433556807519880561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 79469049957939280212059317 7450223433556807519880561)
              ·
                refine ⟨5587667575167605639910421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7450223433556807519880561 5587667575167605639910421)
                ·
                  refine ⟨261921917585981514370801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5587667575167605639910421 261921917585981514370801)
                  ·
                    rfl

theorem cell23_4590820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 2, 6].length) (baseStart_4590820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4590820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4590820 prefixEnd_4590820 := by exact prefixLift 4590820
  have htrace : WordTrace (prefixWord ++ tailWord_4590820) baseStart_4590820 baseEnd_4590820 := by
    simpa [prefixWord, tailWord_4590820, baseEnd_4590820] using wordTrace_append hprefix tailTrace_4590820
  have hstable : (prefixWord ++ tailWord_4590820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4590820).length < 2 ^ (prefixWord ++ tailWord_4590820).sum := by decide
  have hdescent : baseEnd_4590820 < baseStart_4590820 := by decide
  rcases family_descends (prefixWord ++ tailWord_4590820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4590847 : List Nat := [1, 1, 2, 2, 1, 5, 2, 2, 3, 1, 3]
def baseStart_4590847 : Nat := 118140960795 + 4590847 * 2 ^ 59
def prefixEnd_4590847 : Nat := 4983230072969 + 3 ^ 40 * 4590847 * 2
def baseEnd_4590847 : Nat := 2357311122251505023699585

theorem tailTrace_4590847 : CollatzResearch.WordTrace tailWord_4590847 prefixEnd_4590847 2357311122251505023699585 := by
  unfold tailWord_4590847
  simp only [CollatzResearch.WordTrace]
  refine ⟨167441945999152848090962795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111627963999435232060641863 167441945999152848090962795)
  ·
    refine ⟨251162918998729272136444193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167441945999152848090962795 251162918998729272136444193)
    ·
      refine ⟨188372189249046954102333145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 251162918998729272136444193 188372189249046954102333145)
      ·
        refine ⟨141279141936785215576749859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188372189249046954102333145 141279141936785215576749859)
        ·
          refine ⟨211918712905177823365124789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141279141936785215576749859 211918712905177823365124789)
          ·
            refine ⟨19867379334860420940480449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 211918712905177823365124789 19867379334860420940480449)
            ·
              refine ⟨14900534501145315705360337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19867379334860420940480449 14900534501145315705360337)
              ·
                refine ⟨11175400875858986779020253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14900534501145315705360337 11175400875858986779020253)
                ·
                  refine ⟨4190775328447120042132595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11175400875858986779020253 4190775328447120042132595)
                  ·
                    refine ⟨6286162992670680063198893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4190775328447120042132595 6286162992670680063198893)
                    ·
                      refine ⟨2357311122251505023699585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6286162992670680063198893 2357311122251505023699585)
                      ·
                        rfl

theorem cell23_4590847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 2, 3, 1, 3].length) (baseStart_4590847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4590847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4590847 prefixEnd_4590847 := by exact prefixLift 4590847
  have htrace : WordTrace (prefixWord ++ tailWord_4590847) baseStart_4590847 baseEnd_4590847 := by
    simpa [prefixWord, tailWord_4590847, baseEnd_4590847] using wordTrace_append hprefix tailTrace_4590847
  have hstable : (prefixWord ++ tailWord_4590847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4590847).length < 2 ^ (prefixWord ++ tailWord_4590847).sum := by decide
  have hdescent : baseEnd_4590847 < baseStart_4590847 := by decide
  rcases family_descends (prefixWord ++ tailWord_4590847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4590857 : List Nat := [1, 2, 1, 1, 3, 3, 2, 3, 2, 3, 2]
def baseStart_4590857 : Nat := 118140960795 + 4590857 * 2 ^ 59
def prefixEnd_4590857 : Nat := 4983230072969 + 3 ^ 40 * 4590857 * 2
def baseEnd_4590857 : Nat := 2357316257058049984574539

theorem tailTrace_4590857 : CollatzResearch.WordTrace tailWord_4590857 prefixEnd_4590857 2357316257058049984574539 := by
  unfold tailWord_4590857
  simp only [CollatzResearch.WordTrace]
  refine ⟨167442310729116619798826825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111628207152744413199217883 167442310729116619798826825)
  ·
    refine ⟨125581733046837464849120119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167442310729116619798826825 125581733046837464849120119)
    ·
      refine ⟨188372599570256197273680179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125581733046837464849120119 188372599570256197273680179)
      ·
        refine ⟨282558899355384295910520269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188372599570256197273680179 282558899355384295910520269)
        ·
          refine ⟨105959587258269110966445101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 282558899355384295910520269 105959587258269110966445101)
          ·
            refine ⟨39734845221850916612416913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105959587258269110966445101 39734845221850916612416913)
            ·
              refine ⟨29801133916388187459312685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39734845221850916612416913 29801133916388187459312685)
              ·
                refine ⟨11175425218645570297242257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29801133916388187459312685 11175425218645570297242257)
                ·
                  refine ⟨8381568913984177722931693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11175425218645570297242257 8381568913984177722931693)
                  ·
                    refine ⟨3143088342744066646099385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8381568913984177722931693 3143088342744066646099385)
                    ·
                      refine ⟨2357316257058049984574539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3143088342744066646099385 2357316257058049984574539)
                      ·
                        rfl

theorem cell23_4590857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 3, 2, 3, 2].length) (baseStart_4590857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4590857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4590857 prefixEnd_4590857 := by exact prefixLift 4590857
  have htrace : WordTrace (prefixWord ++ tailWord_4590857) baseStart_4590857 baseEnd_4590857 := by
    simpa [prefixWord, tailWord_4590857, baseEnd_4590857] using wordTrace_append hprefix tailTrace_4590857
  have hstable : (prefixWord ++ tailWord_4590857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4590857).length < 2 ^ (prefixWord ++ tailWord_4590857).sum := by decide
  have hdescent : baseEnd_4590857 < baseStart_4590857 := by decide
  rcases family_descends (prefixWord ++ tailWord_4590857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4590874 : List Nat := [3, 1, 1, 3, 3, 2, 1, 2, 2, 3, 2]
def baseStart_4590874 : Nat := 118140960795 + 4590874 * 2 ^ 59
def prefixEnd_4590874 : Nat := 4983230072969 + 3 ^ 40 * 4590874 * 2
def baseEnd_4590874 : Nat := 2357324986229176418061961

theorem tailTrace_4590874 : CollatzResearch.WordTrace tailWord_4590874 prefixEnd_4590874 2357324986229176418061961 := by
  unfold tailWord_4590874
  simp only [CollatzResearch.WordTrace]
  refine ⟨41860732692513757925548919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111628620513370021134797117 41860732692513757925548919)
  ·
    refine ⟨62791099038770636888323379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41860732692513757925548919 62791099038770636888323379)
    ·
      refine ⟨94186648558155955332485069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62791099038770636888323379 94186648558155955332485069)
      ·
        refine ⟨35319993209308483249681901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94186648558155955332485069 35319993209308483249681901)
        ·
          refine ⟨13244997453490681218630713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35319993209308483249681901 13244997453490681218630713)
          ·
            refine ⟨9933748090118010913973035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13244997453490681218630713 9933748090118010913973035)
            ·
              refine ⟨14900622135177016370959553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9933748090118010913973035 14900622135177016370959553)
              ·
                refine ⟨11175466601382762278219665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14900622135177016370959553 11175466601382762278219665)
                ·
                  refine ⟨8381599951037071708664749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11175466601382762278219665 8381599951037071708664749)
                  ·
                    refine ⟨3143099981638901890749281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8381599951037071708664749 3143099981638901890749281)
                    ·
                      refine ⟨2357324986229176418061961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3143099981638901890749281 2357324986229176418061961)
                      ·
                        rfl

theorem cell23_4590874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 2, 2, 3, 2].length) (baseStart_4590874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4590874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4590874 prefixEnd_4590874 := by exact prefixLift 4590874
  have htrace : WordTrace (prefixWord ++ tailWord_4590874) baseStart_4590874 baseEnd_4590874 := by
    simpa [prefixWord, tailWord_4590874, baseEnd_4590874] using wordTrace_append hprefix tailTrace_4590874
  have hstable : (prefixWord ++ tailWord_4590874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4590874).length < 2 ^ (prefixWord ++ tailWord_4590874).sum := by decide
  have hdescent : baseEnd_4590874 < baseStart_4590874 := by decide
  rcases family_descends (prefixWord ++ tailWord_4590874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4590910 : List Nat := [4, 2, 1, 2, 1, 1, 1, 11]
def baseStart_4590910 : Nat := 118140960795 + 4590910 * 2 ^ 59
def prefixEnd_4590910 : Nat := 4983230072969 + 3 ^ 40 * 4590910 * 2
def baseEnd_4590910 : Nat := 87309017464175491748585

theorem tailTrace_4590910 : CollatzResearch.WordTrace tailWord_4590910 prefixEnd_4590910 87309017464175491748585 := by
  unfold tailWord_4590910
  simp only [CollatzResearch.WordTrace]
  refine ⟨20930530474740576231313273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111629495865283073233670789 20930530474740576231313273)
  ·
    refine ⟨15697897856055432173484955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20930530474740576231313273 15697897856055432173484955)
    ·
      refine ⟨23546846784083148260227433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15697897856055432173484955 23546846784083148260227433)
      ·
        refine ⟨17660135088062361195170575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23546846784083148260227433 17660135088062361195170575)
        ·
          refine ⟨26490202632093541792755863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17660135088062361195170575 26490202632093541792755863)
          ·
            refine ⟨39735303948140312689133795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26490202632093541792755863 39735303948140312689133795)
            ·
              refine ⟨59602955922210469033700693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39735303948140312689133795 59602955922210469033700693)
              ·
                refine ⟨87309017464175491748585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 59602955922210469033700693 87309017464175491748585)
                ·
                  rfl

theorem cell23_4590910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 11].length) (baseStart_4590910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4590910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4590910 prefixEnd_4590910 := by exact prefixLift 4590910
  have htrace : WordTrace (prefixWord ++ tailWord_4590910) baseStart_4590910 baseEnd_4590910 := by
    simpa [prefixWord, tailWord_4590910, baseEnd_4590910] using wordTrace_append hprefix tailTrace_4590910
  have hstable : (prefixWord ++ tailWord_4590910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4590910).length < 2 ^ (prefixWord ++ tailWord_4590910).sum := by decide
  have hdescent : baseEnd_4590910 < baseStart_4590910 := by decide
  rcases family_descends (prefixWord ++ tailWord_4590910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4590937 : List Nat := [1, 2, 1, 2, 2, 2, 2, 3, 4, 1, 3]
def baseStart_4590937 : Nat := 118140960795 + 4590937 * 2 ^ 59
def prefixEnd_4590937 : Nat := 4983230072969 + 3 ^ 40 * 4590937 * 2
def baseEnd_4590937 : Nat := 2357357335510409671574171

theorem tailTrace_4590937 : CollatzResearch.WordTrace tailWord_4590937 prefixEnd_4590937 2357357335510409671574171 := by
  unfold tailWord_4590937
  simp only [CollatzResearch.WordTrace]
  refine ⟨167445228568826793461739065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111630152379217862307826043 167445228568826793461739065)
  ·
    refine ⟨125583921426620095096304299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167445228568826793461739065 125583921426620095096304299)
    ·
      refine ⟨188375882139930142644456449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125583921426620095096304299 188375882139930142644456449)
      ·
        refine ⟨141281911604947606983342337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188375882139930142644456449 141281911604947606983342337)
        ·
          refine ⟨105961433703710705237506753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141281911604947606983342337 105961433703710705237506753)
          ·
            refine ⟨79471075277783028928130065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105961433703710705237506753 79471075277783028928130065)
            ·
              refine ⟨59603306458337271696097549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79471075277783028928130065 59603306458337271696097549)
              ·
                refine ⟨22351239921876476886036581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59603306458337271696097549 22351239921876476886036581)
                ·
                  refine ⟨4190857485351839416131859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22351239921876476886036581 4190857485351839416131859)
                  ·
                    refine ⟨6286286228027759124197789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4190857485351839416131859 6286286228027759124197789)
                    ·
                      refine ⟨2357357335510409671574171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6286286228027759124197789 2357357335510409671574171)
                      ·
                        rfl

theorem cell23_4590937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 4, 1, 3].length) (baseStart_4590937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4590937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4590937 prefixEnd_4590937 := by exact prefixLift 4590937
  have htrace : WordTrace (prefixWord ++ tailWord_4590937) baseStart_4590937 baseEnd_4590937 := by
    simpa [prefixWord, tailWord_4590937, baseEnd_4590937] using wordTrace_append hprefix tailTrace_4590937
  have hstable : (prefixWord ++ tailWord_4590937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4590937).length < 2 ^ (prefixWord ++ tailWord_4590937).sum := by decide
  have hdescent : baseEnd_4590937 < baseStart_4590937 := by decide
  rcases family_descends (prefixWord ++ tailWord_4590937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4590938 : List Nat := [3, 1, 1, 2, 1, 2, 6, 2, 1, 2, 2]
def baseStart_4590938 : Nat := 118140960795 + 4590938 * 2 ^ 59
def prefixEnd_4590938 : Nat := 4983230072969 + 3 ^ 40 * 4590938 * 2
def baseEnd_4590938 : Nat := 2357357848991064167661667

theorem tailTrace_4590938 : CollatzResearch.WordTrace tailWord_4590938 prefixEnd_4590938 2357357848991064167661667 := by
  unfold tailWord_4590938
  simp only [CollatzResearch.WordTrace]
  refine ⟨41861316260455792658131367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111630176694548780421683645 41861316260455792658131367)
  ·
    refine ⟨62791974390683688987197051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41861316260455792658131367 62791974390683688987197051)
    ·
      refine ⟨94187961586025533480795577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62791974390683688987197051 94187961586025533480795577)
      ·
        refine ⟨70640971189519150110596683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94187961586025533480795577 70640971189519150110596683)
        ·
          refine ⟨105961456784278725165895025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70640971189519150110596683 105961456784278725165895025)
          ·
            refine ⟨79471092588209043874421269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105961456784278725165895025 79471092588209043874421269)
            ·
              refine ⟨3725207465072298931613497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 79471092588209043874421269 3725207465072298931613497)
              ·
                refine ⟨2793905598804224198710123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3725207465072298931613497 2793905598804224198710123)
                ·
                  refine ⟨4190858398206336298065185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2793905598804224198710123 4190858398206336298065185)
                  ·
                    refine ⟨3143143798654752223548889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4190858398206336298065185 3143143798654752223548889)
                    ·
                      refine ⟨2357357848991064167661667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3143143798654752223548889 2357357848991064167661667)
                      ·
                        rfl

theorem cell23_4590938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 6, 2, 1, 2, 2].length) (baseStart_4590938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4590938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4590938 prefixEnd_4590938 := by exact prefixLift 4590938
  have htrace : WordTrace (prefixWord ++ tailWord_4590938) baseStart_4590938 baseEnd_4590938 := by
    simpa [prefixWord, tailWord_4590938, baseEnd_4590938] using wordTrace_append hprefix tailTrace_4590938
  have hstable : (prefixWord ++ tailWord_4590938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4590938).length < 2 ^ (prefixWord ++ tailWord_4590938).sum := by decide
  have hdescent : baseEnd_4590938 < baseStart_4590938 := by decide
  rcases family_descends (prefixWord ++ tailWord_4590938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4590960 : List Nat := [2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 4]
def baseStart_4590960 : Nat := 118140960795 + 4590960 * 2 ^ 59
def prefixEnd_4590960 : Nat := 4983230072969 + 3 ^ 40 * 4590960 * 2
def baseEnd_4590960 : Nat := 2357369145565463081586565

theorem tailTrace_4590960 : CollatzResearch.WordTrace tailWord_4590960 prefixEnd_4590960 2357369145565463081586565 := by
  unfold tailWord_4590960
  simp only [CollatzResearch.WordTrace]
  refine ⟨83723033723871734194913167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111630711631828978926550889 83723033723871734194913167)
  ·
    refine ⟨125584550585807601292369751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83723033723871734194913167 125584550585807601292369751)
    ·
      refine ⟨188376825878711401938554627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125584550585807601292369751 188376825878711401938554627)
      ·
        refine ⟨282565238818067102907831941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188376825878711401938554627 282565238818067102907831941)
        ·
          refine ⟨52980982278387581795218489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 282565238818067102907831941 52980982278387581795218489)
          ·
            refine ⟨39735736708790686346413867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52980982278387581795218489 39735736708790686346413867)
            ·
              refine ⟨59603605063186029519620801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39735736708790686346413867 59603605063186029519620801)
              ·
                refine ⟨44702703797389522139715601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59603605063186029519620801 44702703797389522139715601)
                ·
                  refine ⟨33527027848042141604786701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44702703797389522139715601 33527027848042141604786701)
                  ·
                    refine ⟨12572635443015803101795013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33527027848042141604786701 12572635443015803101795013)
                    ·
                      refine ⟨2357369145565463081586565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12572635443015803101795013 2357369145565463081586565)
                      ·
                        rfl

theorem cell23_4590960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 4].length) (baseStart_4590960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4590960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4590960 prefixEnd_4590960 := by exact prefixLift 4590960
  have htrace : WordTrace (prefixWord ++ tailWord_4590960) baseStart_4590960 baseEnd_4590960 := by
    simpa [prefixWord, tailWord_4590960, baseEnd_4590960] using wordTrace_append hprefix tailTrace_4590960
  have hstable : (prefixWord ++ tailWord_4590960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4590960).length < 2 ^ (prefixWord ++ tailWord_4590960).sum := by decide
  have hdescent : baseEnd_4590960 < baseStart_4590960 := by decide
  rcases family_descends (prefixWord ++ tailWord_4590960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4590981 : List Nat := [1, 3, 1, 1, 3, 1, 6, 1, 1, 3, 2]
def baseStart_4590981 : Nat := 118140960795 + 4590981 * 2 ^ 59
def prefixEnd_4590981 : Nat := 4983230072969 + 3 ^ 40 * 4590981 * 2
def baseEnd_4590981 : Nat := 2357379928659207499423969

theorem tailTrace_4590981 : CollatzResearch.WordTrace tailWord_4590981 prefixEnd_4590981 2357379928659207499423969 := by
  unfold tailWord_4590981
  simp only [CollatzResearch.WordTrace]
  refine ⟨167446833380667388976340797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111631222253778259317560531 167446833380667388976340797)
  ·
    refine ⟨62792562517750270866127799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167446833380667388976340797 62792562517750270866127799)
    ·
      refine ⟨94188843776625406299191699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62792562517750270866127799 94188843776625406299191699)
      ·
        refine ⟨141283265664938109448787549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94188843776625406299191699 141283265664938109448787549)
        ·
          refine ⟨52981224624351791043295331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 141283265664938109448787549 52981224624351791043295331)
          ·
            refine ⟨79471836936527686564942997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52981224624351791043295331 79471836936527686564942997)
            ·
              refine ⟨3725242356399735307731703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 79471836936527686564942997 3725242356399735307731703)
              ·
                refine ⟨5587863534599602961597555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3725242356399735307731703 5587863534599602961597555)
                ·
                  refine ⟨8381795301899404442396333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5587863534599602961597555 8381795301899404442396333)
                  ·
                    refine ⟨3143173238212276665898625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8381795301899404442396333 3143173238212276665898625)
                    ·
                      refine ⟨2357379928659207499423969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3143173238212276665898625 2357379928659207499423969)
                      ·
                        rfl

theorem cell23_4590981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 6, 1, 1, 3, 2].length) (baseStart_4590981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4590981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4590981 prefixEnd_4590981 := by exact prefixLift 4590981
  have htrace : WordTrace (prefixWord ++ tailWord_4590981) baseStart_4590981 baseEnd_4590981 := by
    simpa [prefixWord, tailWord_4590981, baseEnd_4590981] using wordTrace_append hprefix tailTrace_4590981
  have hstable : (prefixWord ++ tailWord_4590981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4590981).length < 2 ^ (prefixWord ++ tailWord_4590981).sum := by decide
  have hdescent : baseEnd_4590981 < baseStart_4590981 := by decide
  rcases family_descends (prefixWord ++ tailWord_4590981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4591007 : List Nat := [1, 1, 2, 5, 1, 2, 2, 1, 2, 2, 4]
def baseStart_4591007 : Nat := 118140960795 + 4591007 * 2 ^ 59
def prefixEnd_4591007 : Nat := 4983230072969 + 3 ^ 40 * 4591007 * 2
def baseEnd_4591007 : Nat := 2357393279156224397698849

theorem tailTrace_4591007 : CollatzResearch.WordTrace tailWord_4591007 prefixEnd_4591007 2357393279156224397698849 := by
  unfold tailWord_4591007
  simp only [CollatzResearch.WordTrace]
  refine ⟨167447781678573195416787275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111631854452382130277858183 167447781678573195416787275)
  ·
    refine ⟨251171672517859793125180913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167447781678573195416787275 251171672517859793125180913)
    ·
      refine ⟨188378754388394844843885685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 251171672517859793125180913 188378754388394844843885685)
      ·
        refine ⟨17660508223912016704114283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 188378754388394844843885685 17660508223912016704114283)
        ·
          refine ⟨26490762335868025056171425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17660508223912016704114283 26490762335868025056171425)
          ·
            refine ⟨19868071751901018792128569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26490762335868025056171425 19868071751901018792128569)
            ·
              refine ⟨14901053813925764094096427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19868071751901018792128569 14901053813925764094096427)
              ·
                refine ⟨22351580720888646141144641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14901053813925764094096427 22351580720888646141144641)
                ·
                  refine ⟨16763685540666484605858481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22351580720888646141144641 16763685540666484605858481)
                  ·
                    refine ⟨12572764155499863454393861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16763685540666484605858481 12572764155499863454393861)
                    ·
                      refine ⟨2357393279156224397698849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12572764155499863454393861 2357393279156224397698849)
                      ·
                        rfl

theorem cell23_4591007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_4591007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4591007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4591007 prefixEnd_4591007 := by exact prefixLift 4591007
  have htrace : WordTrace (prefixWord ++ tailWord_4591007) baseStart_4591007 baseEnd_4591007 := by
    simpa [prefixWord, tailWord_4591007, baseEnd_4591007] using wordTrace_append hprefix tailTrace_4591007
  have hstable : (prefixWord ++ tailWord_4591007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4591007).length < 2 ^ (prefixWord ++ tailWord_4591007).sum := by decide
  have hdescent : baseEnd_4591007 < baseStart_4591007 := by decide
  rcases family_descends (prefixWord ++ tailWord_4591007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4591047 : List Nat := [1, 1, 4, 1, 1, 3, 3, 2, 2, 5]
def baseStart_4591047 : Nat := 118140960795 + 4591047 * 2 ^ 59
def prefixEnd_4591047 : Nat := 4983230072969 + 3 ^ 40 * 4591047 * 2
def baseEnd_4591047 : Nat := 785804606127468080399555

theorem tailTrace_4591047 : CollatzResearch.WordTrace tailWord_4591047 prefixEnd_4591047 785804606127468080399555 := by
  unfold tailWord_4591047
  simp only [CollatzResearch.WordTrace]
  refine ⟨167449240598428282248243395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111632827065618854832162263 167449240598428282248243395)
  ·
    refine ⟨251173860897642423372365093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167449240598428282248243395 251173860897642423372365093)
    ·
      refine ⟨47095098918307954382318455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 251173860897642423372365093 47095098918307954382318455)
      ·
        refine ⟨70642648377461931573477683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47095098918307954382318455 70642648377461931573477683)
        ·
          refine ⟨105963972566192897360216525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70642648377461931573477683 105963972566192897360216525)
          ·
            refine ⟨39736489712322336510081197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105963972566192897360216525 39736489712322336510081197)
            ·
              refine ⟨14901183642120876191280449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39736489712322336510081197 14901183642120876191280449)
              ·
                refine ⟨11175887731590657143460337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14901183642120876191280449 11175887731590657143460337)
                ·
                  refine ⟨8381915798692992857595253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11175887731590657143460337 8381915798692992857595253)
                  ·
                    refine ⟨785804606127468080399555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8381915798692992857595253 785804606127468080399555)
                    ·
                      rfl

theorem cell23_4591047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 2, 2, 5].length) (baseStart_4591047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4591047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4591047 prefixEnd_4591047 := by exact prefixLift 4591047
  have htrace : WordTrace (prefixWord ++ tailWord_4591047) baseStart_4591047 baseEnd_4591047 := by
    simpa [prefixWord, tailWord_4591047, baseEnd_4591047] using wordTrace_append hprefix tailTrace_4591047
  have hstable : (prefixWord ++ tailWord_4591047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4591047).length < 2 ^ (prefixWord ++ tailWord_4591047).sum := by decide
  have hdescent : baseEnd_4591047 < baseStart_4591047 := by decide
  rcases family_descends (prefixWord ++ tailWord_4591047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4591062 : List Nat := [5, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2]
def baseStart_4591062 : Nat := 118140960795 + 4591062 * 2 ^ 59
def prefixEnd_4591062 : Nat := 4983230072969 + 3 ^ 40 * 4591062 * 2
def baseEnd_4591062 : Nat := 2357421520592221682511097

theorem tailTrace_4591062 : CollatzResearch.WordTrace tailWord_4591062 prefixEnd_4591062 2357421520592221682511097 := by
  unfold tailWord_4591062
  simp only [CollatzResearch.WordTrace]
  refine ⟨10465611730835871238127465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 111633191795582626540026293 10465611730835871238127465)
  ·
    refine ⟨7849208798126903428595599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10465611730835871238127465 7849208798126903428595599)
    ·
      refine ⟨11773813197190355142893399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7849208798126903428595599 11773813197190355142893399)
      ·
        refine ⟨17660719795785532714340099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11773813197190355142893399 17660719795785532714340099)
        ·
          refine ⟨26491079693678299071510149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17660719795785532714340099 26491079693678299071510149)
          ·
            refine ⟨4967077442564681075908153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26491079693678299071510149 4967077442564681075908153)
            ·
              refine ⟨3725308081923510806931115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4967077442564681075908153 3725308081923510806931115)
              ·
                refine ⟨5587962122885266210396673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3725308081923510806931115 5587962122885266210396673)
                ·
                  refine ⟨4190971592163949657797505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5587962122885266210396673 4190971592163949657797505)
                  ·
                    refine ⟨3143228694122962243348129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4190971592163949657797505 3143228694122962243348129)
                    ·
                      refine ⟨2357421520592221682511097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3143228694122962243348129 2357421520592221682511097)
                      ·
                        rfl

theorem cell23_4591062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2].length) (baseStart_4591062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4591062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4591062 prefixEnd_4591062 := by exact prefixLift 4591062
  have htrace : WordTrace (prefixWord ++ tailWord_4591062) baseStart_4591062 baseEnd_4591062 := by
    simpa [prefixWord, tailWord_4591062, baseEnd_4591062] using wordTrace_append hprefix tailTrace_4591062
  have hstable : (prefixWord ++ tailWord_4591062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4591062).length < 2 ^ (prefixWord ++ tailWord_4591062).sum := by decide
  have hdescent : baseEnd_4591062 < baseStart_4591062 := by decide
  rcases family_descends (prefixWord ++ tailWord_4591062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4591087 : List Nat := [1, 1, 2, 1, 4, 1, 2, 3, 1, 4, 3]
def baseStart_4591087 : Nat := 118140960795 + 4591087 * 2 ^ 59
def prefixEnd_4591087 : Nat := 4983230072969 + 3 ^ 40 * 4591087 * 2
def baseEnd_4591087 : Nat := 2357434357608584084698481

theorem tailTrace_4591087 : CollatzResearch.WordTrace tailWord_4591087 prefixEnd_4591087 2357434357608584084698481 := by
  unfold tailWord_4591087
  simp only [CollatzResearch.WordTrace]
  refine ⟨167450699518283369079699515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111633799678855579386466343 167450699518283369079699515)
  ·
    refine ⟨251176049277425053619549273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167450699518283369079699515 251176049277425053619549273)
    ·
      refine ⟨188382036958068790214661955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 251176049277425053619549273 188382036958068790214661955)
      ·
        refine ⟨282573055437103185321992933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188382036958068790214661955 282573055437103185321992933)
        ·
          refine ⟨52982447894456847247873675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 282573055437103185321992933 52982447894456847247873675)
          ·
            refine ⟨79473671841685270871810513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52982447894456847247873675 79473671841685270871810513)
            ·
              refine ⟨59605253881263953153857885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79473671841685270871810513 59605253881263953153857885)
              ·
                refine ⟨22351970205473982432696707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59605253881263953153857885 22351970205473982432696707)
                ·
                  refine ⟨33527955308210973649045061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22351970205473982432696707 33527955308210973649045061)
                  ·
                    refine ⟨6286491620289557559195949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33527955308210973649045061 6286491620289557559195949)
                    ·
                      refine ⟨2357434357608584084698481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6286491620289557559195949 2357434357608584084698481)
                      ·
                        rfl

theorem cell23_4591087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 4, 3].length) (baseStart_4591087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4591087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4591087 prefixEnd_4591087 := by exact prefixLift 4591087
  have htrace : WordTrace (prefixWord ++ tailWord_4591087) baseStart_4591087 baseEnd_4591087 := by
    simpa [prefixWord, tailWord_4591087, baseEnd_4591087] using wordTrace_append hprefix tailTrace_4591087
  have hstable : (prefixWord ++ tailWord_4591087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4591087).length < 2 ^ (prefixWord ++ tailWord_4591087).sum := by decide
  have hdescent : baseEnd_4591087 < baseStart_4591087 := by decide
  rcases family_descends (prefixWord ++ tailWord_4591087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4591102 : List Nat := [4, 2, 2, 3, 2, 1, 2, 2, 5]
def baseStart_4591102 : Nat := 118140960795 + 4591102 * 2 ^ 59
def prefixEnd_4591102 : Nat := 4983230072969 + 3 ^ 40 * 4591102 * 2
def baseEnd_4591102 : Nat := 261938006646489058445657

theorem tailTrace_4591102 : CollatzResearch.WordTrace tailWord_4591102 prefixEnd_4591102 261938006646489058445657 := by
  unfold tailWord_4591102
  simp only [CollatzResearch.WordTrace]
  refine ⟨20931405826653628330186945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111634164408819351094330373 20931405826653628330186945)
  ·
    refine ⟨15698554369990221247640209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20931405826653628330186945 15698554369990221247640209)
    ·
      refine ⟨11773915777492665935730157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15698554369990221247640209 11773915777492665935730157)
      ·
        refine ⟨4415218416559749725898809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11773915777492665935730157 4415218416559749725898809)
        ·
          refine ⟨3311413812419812294424107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4415218416559749725898809 3311413812419812294424107)
          ·
            refine ⟨4967120718629718441636161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3311413812419812294424107 4967120718629718441636161)
            ·
              refine ⟨3725340538972288831227121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4967120718629718441636161 3725340538972288831227121)
              ·
                refine ⟨2794005404229216623420341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3725340538972288831227121 2794005404229216623420341)
                ·
                  refine ⟨261938006646489058445657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2794005404229216623420341 261938006646489058445657)
                  ·
                    rfl

theorem cell23_4591102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 2, 2, 5].length) (baseStart_4591102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4591102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4591102 prefixEnd_4591102 := by exact prefixLift 4591102
  have htrace : WordTrace (prefixWord ++ tailWord_4591102) baseStart_4591102 baseEnd_4591102 := by
    simpa [prefixWord, tailWord_4591102, baseEnd_4591102] using wordTrace_append hprefix tailTrace_4591102
  have hstable : (prefixWord ++ tailWord_4591102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4591102).length < 2 ^ (prefixWord ++ tailWord_4591102).sum := by decide
  have hdescent : baseEnd_4591102 < baseStart_4591102 := by decide
  rcases family_descends (prefixWord ++ tailWord_4591102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4591158 : List Nat := [5, 1, 2, 1, 3, 2, 1, 2, 6]
def baseStart_4591158 : Nat := 118140960795 + 4591158 * 2 ^ 59
def prefixEnd_4591158 : Nat := 4983230072969 + 3 ^ 40 * 4591158 * 2
def baseEnd_4591158 : Nat := 261941201637228145212295

theorem tailTrace_4591158 : CollatzResearch.WordTrace tailWord_4591158 prefixEnd_4591158 261941201637228145212295 := by
  unfold tailWord_4591158
  simp only [CollatzResearch.WordTrace]
  refine ⟨10465830568814134262845883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 111635526067350765470356085 10465830568814134262845883)
  ·
    refine ⟨15698745853221201394268825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10465830568814134262845883 15698745853221201394268825)
    ·
      refine ⟨11774059389915901045701619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15698745853221201394268825 11774059389915901045701619)
      ·
        refine ⟨17661089084873851568552429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11774059389915901045701619 17661089084873851568552429)
        ·
          refine ⟨6622908406827694338207161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17661089084873851568552429 6622908406827694338207161)
          ·
            refine ⟨4967181305120770753655371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6622908406827694338207161 4967181305120770753655371)
            ·
              refine ⟨7450771957681156130483057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4967181305120770753655371 7450771957681156130483057)
              ·
                refine ⟨5588078968260867097862293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7450771957681156130483057 5588078968260867097862293)
                ·
                  refine ⟨261941201637228145212295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5588078968260867097862293 261941201637228145212295)
                  ·
                    rfl

theorem cell23_4591158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 2, 6].length) (baseStart_4591158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4591158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4591158 prefixEnd_4591158 := by exact prefixLift 4591158
  have htrace : WordTrace (prefixWord ++ tailWord_4591158) baseStart_4591158 baseEnd_4591158 := by
    simpa [prefixWord, tailWord_4591158, baseEnd_4591158] using wordTrace_append hprefix tailTrace_4591158
  have hstable : (prefixWord ++ tailWord_4591158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4591158).length < 2 ^ (prefixWord ++ tailWord_4591158).sum := by decide
  have hdescent : baseEnd_4591158 < baseStart_4591158 := by decide
  rcases family_descends (prefixWord ++ tailWord_4591158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4591187 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 7, 2, 4]
def baseStart_4591187 : Nat := 118140960795 + 4591187 * 2 ^ 59
def prefixEnd_4591187 : Nat := 4983230072969 + 3 ^ 40 * 4591187 * 2
def baseEnd_4591187 : Nat := 2357485705674033693448021

theorem tailTrace_4591187 : CollatzResearch.WordTrace tailWord_4591187 prefixEnd_4591187 2357485705674033693448021 := by
  unfold tailWord_4591187
  simp only [CollatzResearch.WordTrace]
  refine ⟨167454346817921086158339815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111636231211947390772226543 167454346817921086158339815)
  ·
    refine ⟨251181520226881629237509723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167454346817921086158339815 251181520226881629237509723)
    ·
      refine ⟨376772280340322443856264585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251181520226881629237509723 376772280340322443856264585)
      ·
        refine ⟨282579210255241832892198439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 376772280340322443856264585 282579210255241832892198439)
        ·
          refine ⟨423868815382862749338297659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 282579210255241832892198439 423868815382862749338297659)
          ·
            refine ⟨635803223074294124007446489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 423868815382862749338297659 635803223074294124007446489)
            ·
              refine ⟨476852417305720593005584867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 635803223074294124007446489 476852417305720593005584867)
              ·
                refine ⟨715278625958580889508377301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 476852417305720593005584867 715278625958580889508377301)
                ·
                  refine ⟨16764342795904239597852593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 715278625958580889508377301 16764342795904239597852593)
                  ·
                    refine ⟨12573257096928179698389445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16764342795904239597852593 12573257096928179698389445)
                    ·
                      refine ⟨2357485705674033693448021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12573257096928179698389445 2357485705674033693448021)
                      ·
                        rfl

theorem cell23_4591187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 7, 2, 4].length) (baseStart_4591187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4591187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4591187 prefixEnd_4591187 := by exact prefixLift 4591187
  have htrace : WordTrace (prefixWord ++ tailWord_4591187) baseStart_4591187 baseEnd_4591187 := by
    simpa [prefixWord, tailWord_4591187, baseEnd_4591187] using wordTrace_append hprefix tailTrace_4591187
  have hstable : (prefixWord ++ tailWord_4591187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4591187).length < 2 ^ (prefixWord ++ tailWord_4591187).sum := by decide
  have hdescent : baseEnd_4591187 < baseStart_4591187 := by decide
  rcases family_descends (prefixWord ++ tailWord_4591187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4591191 : List Nat := [1, 1, 3, 2, 2, 4, 2, 2, 1, 1, 4]
def baseStart_4591191 : Nat := 118140960795 + 4591191 * 2 ^ 59
def prefixEnd_4591191 : Nat := 4983230072969 + 3 ^ 40 * 4591191 * 2
def baseEnd_4591191 : Nat := 2357487759596651677798003

theorem tailTrace_4591191 : CollatzResearch.WordTrace tailWord_4591191 prefixEnd_4591191 2357487759596651677798003 := by
  unfold tailWord_4591191
  simp only [CollatzResearch.WordTrace]
  refine ⟨167454492709906594841485427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111636328473271063227656951 167454492709906594841485427)
  ·
    refine ⟨251181739064859892262228141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167454492709906594841485427 251181739064859892262228141)
    ·
      refine ⟨94193152149322459598335553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 251181739064859892262228141 94193152149322459598335553)
      ·
        refine ⟨70644864111991844698751665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94193152149322459598335553 70644864111991844698751665)
        ·
          refine ⟨52983648083993883524063749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70644864111991844698751665 52983648083993883524063749)
          ·
            refine ⟨9934434015748853160761953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52983648083993883524063749 9934434015748853160761953)
            ·
              refine ⟨7450825511811639870571465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9934434015748853160761953 7450825511811639870571465)
              ·
                refine ⟨5588119133858729902928599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7450825511811639870571465 5588119133858729902928599)
                ·
                  refine ⟨8382178700788094854392899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5588119133858729902928599 8382178700788094854392899)
                  ·
                    refine ⟨12573268051182142281589349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8382178700788094854392899 12573268051182142281589349)
                    ·
                      refine ⟨2357487759596651677798003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12573268051182142281589349 2357487759596651677798003)
                      ·
                        rfl

theorem cell23_4591191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 2, 1, 1, 4].length) (baseStart_4591191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4591191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4591191 prefixEnd_4591191 := by exact prefixLift 4591191
  have htrace : WordTrace (prefixWord ++ tailWord_4591191) baseStart_4591191 baseEnd_4591191 := by
    simpa [prefixWord, tailWord_4591191, baseEnd_4591191] using wordTrace_append hprefix tailTrace_4591191
  have hstable : (prefixWord ++ tailWord_4591191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4591191).length < 2 ^ (prefixWord ++ tailWord_4591191).sum := by decide
  have hdescent : baseEnd_4591191 < baseStart_4591191 := by decide
  rcases family_descends (prefixWord ++ tailWord_4591191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4591194 : List Nat := [3, 1, 1, 2, 1, 1, 1, 5, 3, 2, 3]
def baseStart_4591194 : Nat := 118140960795 + 4591194 * 2 ^ 59
def prefixEnd_4591194 : Nat := 4983230072969 + 3 ^ 40 * 4591194 * 2
def baseEnd_4591194 : Nat := 2357489300038615166060489

theorem tailTrace_4591194 : CollatzResearch.WordTrace tailWord_4591194 prefixEnd_4591194 2357489300038615166060489 := by
  unfold tailWord_4591194
  simp only [CollatzResearch.WordTrace]
  refine ⟨41863650532223931588461159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111636401419263817569229757 41863650532223931588461159)
  ·
    refine ⟨62795475798335897382691739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41863650532223931588461159 62795475798335897382691739)
    ·
      refine ⟨94193213697503846074037609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62795475798335897382691739 94193213697503846074037609)
      ·
        refine ⟨70644910273127884555528207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94193213697503846074037609 70644910273127884555528207)
        ·
          refine ⟨105967365409691826833292311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70644910273127884555528207 105967365409691826833292311)
          ·
            refine ⟨158951048114537740249938467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105967365409691826833292311 158951048114537740249938467)
            ·
              refine ⟨238426572171806610374907701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 158951048114537740249938467 238426572171806610374907701)
              ·
                refine ⟨22352491141106869722647597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 238426572171806610374907701 22352491141106869722647597)
                ·
                  refine ⟨8382184177915076145992849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22352491141106869722647597 8382184177915076145992849)
                  ·
                    refine ⟨6286638133436307109494637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8382184177915076145992849 6286638133436307109494637)
                    ·
                      refine ⟨2357489300038615166060489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6286638133436307109494637 2357489300038615166060489)
                      ·
                        rfl

theorem cell23_4591194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 3, 2, 3].length) (baseStart_4591194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4591194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4591194 prefixEnd_4591194 := by exact prefixLift 4591194
  have htrace : WordTrace (prefixWord ++ tailWord_4591194) baseStart_4591194 baseEnd_4591194 := by
    simpa [prefixWord, tailWord_4591194, baseEnd_4591194] using wordTrace_append hprefix tailTrace_4591194
  have hstable : (prefixWord ++ tailWord_4591194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4591194).length < 2 ^ (prefixWord ++ tailWord_4591194).sum := by decide
  have hdescent : baseEnd_4591194 < baseStart_4591194 := by decide
  rcases family_descends (prefixWord ++ tailWord_4591194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4591227 : List Nat := [1, 1, 1, 1, 1, 4, 4, 1, 2, 7]
def baseStart_4591227 : Nat := 118140960795 + 4591227 * 2 ^ 59
def prefixEnd_4591227 : Nat := 4983230072969 + 3 ^ 40 * 4591227 * 2
def baseEnd_4591227 : Nat := 785835414966737845649279

theorem tailTrace_4591227 : CollatzResearch.WordTrace tailWord_4591227 prefixEnd_4591227 785835414966737845649279 := by
  unfold tailWord_4591227
  simp only [CollatzResearch.WordTrace]
  refine ⟨167455805737776172989795935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111637203825184115326530623 167455805737776172989795935)
  ·
    refine ⟨251183708606664259484693903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167455805737776172989795935 251183708606664259484693903)
    ·
      refine ⟨376775562909996389227040855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251183708606664259484693903 376775562909996389227040855)
      ·
        refine ⟨565163344364994583840561283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 376775562909996389227040855 565163344364994583840561283)
        ·
          refine ⟨847745016547491875760841925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 565163344364994583840561283 847745016547491875760841925)
          ·
            refine ⟨158952190602654726705157861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 847745016547491875760841925 158952190602654726705157861)
            ·
              refine ⟨29803535737997761257217099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 158952190602654726705157861 29803535737997761257217099)
              ·
                refine ⟨44705303606996641885825649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29803535737997761257217099 44705303606996641885825649)
                ·
                  refine ⟨33528977705247481414369237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44705303606996641885825649 33528977705247481414369237)
                  ·
                    refine ⟨785835414966737845649279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33528977705247481414369237 785835414966737845649279)
                    ·
                      rfl

theorem cell23_4591227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 7].length) (baseStart_4591227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4591227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4591227 prefixEnd_4591227 := by exact prefixLift 4591227
  have htrace : WordTrace (prefixWord ++ tailWord_4591227) baseStart_4591227 baseEnd_4591227 := by
    simpa [prefixWord, tailWord_4591227, baseEnd_4591227] using wordTrace_append hprefix tailTrace_4591227
  have hstable : (prefixWord ++ tailWord_4591227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4591227).length < 2 ^ (prefixWord ++ tailWord_4591227).sum := by decide
  have hdescent : baseEnd_4591227 < baseStart_4591227 := by decide
  rcases family_descends (prefixWord ++ tailWord_4591227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4591257 : List Nat := [1, 2, 1, 2, 1, 2, 2, 1, 3, 8]
def baseStart_4591257 : Nat := 118140960795 + 4591257 * 2 ^ 59
def prefixEnd_4591257 : Nat := 4983230072969 + 3 ^ 40 * 4591257 * 2
def baseEnd_4591257 : Nat := 785840549773282806524233

theorem tailTrace_4591257 : CollatzResearch.WordTrace tailWord_4591257 prefixEnd_4591257 785840549773282806524233 := by
  unfold tailWord_4591257
  simp only [CollatzResearch.WordTrace]
  refine ⟨167456899927667488113388025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111637933285111658742258683 167456899927667488113388025)
  ·
    refine ⟨125592674945750616085041019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167456899927667488113388025 125592674945750616085041019)
    ·
      refine ⟨188389012418625924127561529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125592674945750616085041019 188389012418625924127561529)
      ·
        refine ⟨141291759313969443095671147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188389012418625924127561529 141291759313969443095671147)
        ·
          refine ⟨211937638970954164643506721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141291759313969443095671147 211937638970954164643506721)
          ·
            refine ⟨158953229228215623482630041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 211937638970954164643506721 158953229228215623482630041)
            ·
              refine ⟨119214921921161717611972531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 158953229228215623482630041 119214921921161717611972531)
              ·
                refine ⟨178822382881742576417958797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119214921921161717611972531 178822382881742576417958797)
                ·
                  refine ⟨67058393580653466156734549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 178822382881742576417958797 67058393580653466156734549)
                  ·
                    refine ⟨785840549773282806524233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 67058393580653466156734549 785840549773282806524233)
                    ·
                      rfl

theorem cell23_4591257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 8].length) (baseStart_4591257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4591257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4591257 prefixEnd_4591257 := by exact prefixLift 4591257
  have htrace : WordTrace (prefixWord ++ tailWord_4591257) baseStart_4591257 baseEnd_4591257 := by
    simpa [prefixWord, tailWord_4591257, baseEnd_4591257] using wordTrace_append hprefix tailTrace_4591257
  have hstable : (prefixWord ++ tailWord_4591257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4591257).length < 2 ^ (prefixWord ++ tailWord_4591257).sum := by decide
  have hdescent : baseEnd_4591257 < baseStart_4591257 := by decide
  rcases family_descends (prefixWord ++ tailWord_4591257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4591302 : List Nat := [6, 1, 2, 1, 1, 1, 2, 1, 3, 3, 2]
def baseStart_4591302 : Nat := 118140960795 + 4591302 * 2 ^ 59
def prefixEnd_4591302 : Nat := 4983230072969 + 3 ^ 40 * 4591302 * 2
def baseEnd_4591302 : Nat := 2357544755949300743509993

theorem tailTrace_4591302 : CollatzResearch.WordTrace tailWord_4591302 prefixEnd_4591302 2357544755949300743509993 := by
  unfold tailWord_4591302
  simp only [CollatzResearch.WordTrace]
  refine ⟨5233079412890764399961755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 111639027475002973865850773 5233079412890764399961755)
  ·
    refine ⟨7849619119336146599942633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5233079412890764399961755 7849619119336146599942633)
    ·
      refine ⟨5887214339502109949956975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7849619119336146599942633 5887214339502109949956975)
      ·
        refine ⟨8830821509253164924935463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5887214339502109949956975 8830821509253164924935463)
        ·
          refine ⟨13246232263879747387403195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8830821509253164924935463 13246232263879747387403195)
          ·
            refine ⟨19869348395819621081104793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13246232263879747387403195 19869348395819621081104793)
            ·
              refine ⟨14902011296864715810828595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19869348395819621081104793 14902011296864715810828595)
              ·
                refine ⟨22353016945297073716242893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14902011296864715810828595 22353016945297073716242893)
                ·
                  refine ⟨8382381354486402643591085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22353016945297073716242893 8382381354486402643591085)
                  ·
                    refine ⟨3143393007932400991346657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8382381354486402643591085 3143393007932400991346657)
                    ·
                      refine ⟨2357544755949300743509993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3143393007932400991346657 2357544755949300743509993)
                      ·
                        rfl

theorem cell23_4591302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_4591302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4591302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4591302 prefixEnd_4591302 := by exact prefixLift 4591302
  have htrace : WordTrace (prefixWord ++ tailWord_4591302) baseStart_4591302 baseEnd_4591302 := by
    simpa [prefixWord, tailWord_4591302, baseEnd_4591302] using wordTrace_append hprefix tailTrace_4591302
  have hstable : (prefixWord ++ tailWord_4591302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4591302).length < 2 ^ (prefixWord ++ tailWord_4591302).sum := by decide
  have hdescent : baseEnd_4591302 < baseStart_4591302 := by decide
  rcases family_descends (prefixWord ++ tailWord_4591302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4591304 : List Nat := [2, 1, 3, 1, 2, 2, 3, 2, 7]
def baseStart_4591304 : Nat := 118140960795 + 4591304 * 2 ^ 59
def prefixEnd_4591304 : Nat := 4983230072969 + 3 ^ 40 * 4591304 * 2
def baseEnd_4591304 : Nat := 261949531434512192853887

theorem tailTrace_4591304 : CollatzResearch.WordTrace tailWord_4591304 prefixEnd_4591304 261949531434512192853887 := by
  unfold tailWord_4591304
  simp only [CollatzResearch.WordTrace]
  refine ⟨83729307079248607570174483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111639076105664810093565977 83729307079248607570174483)
  ·
    refine ⟨125593960618872911355261725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83729307079248607570174483 125593960618872911355261725)
    ·
      refine ⟨47097735232077341758223147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125593960618872911355261725 47097735232077341758223147)
      ·
        refine ⟨70646602848116012637334721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47097735232077341758223147 70646602848116012637334721)
        ·
          refine ⟨52984952136087009478001041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70646602848116012637334721 52984952136087009478001041)
          ·
            refine ⟨39738714102065257108500781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52984952136087009478001041 39738714102065257108500781)
            ·
              refine ⟨14902017788274471415687793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39738714102065257108500781 14902017788274471415687793)
              ·
                refine ⟨11176513341205853561765845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14902017788274471415687793 11176513341205853561765845)
                ·
                  refine ⟨261949531434512192853887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11176513341205853561765845 261949531434512192853887)
                  ·
                    rfl

theorem cell23_4591304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 2, 7].length) (baseStart_4591304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4591304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4591304 prefixEnd_4591304 := by exact prefixLift 4591304
  have htrace : WordTrace (prefixWord ++ tailWord_4591304) baseStart_4591304 baseEnd_4591304 := by
    simpa [prefixWord, tailWord_4591304, baseEnd_4591304] using wordTrace_append hprefix tailTrace_4591304
  have hstable : (prefixWord ++ tailWord_4591304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4591304).length < 2 ^ (prefixWord ++ tailWord_4591304).sum := by decide
  have hdescent : baseEnd_4591304 < baseStart_4591304 := by decide
  rcases family_descends (prefixWord ++ tailWord_4591304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4591321 : List Nat := [1, 2, 1, 2, 3, 3, 1, 5, 5]
def baseStart_4591321 : Nat := 118140960795 + 4591321 * 2 ^ 59
def prefixEnd_4591321 : Nat := 4983230072969 + 3 ^ 40 * 4591321 * 2
def baseEnd_4591321 : Nat := 261950501342415129908045

theorem tailTrace_4591321 : CollatzResearch.WordTrace tailWord_4591321 prefixEnd_4591321 261950501342415129908045 := by
  unfold tailWord_4591321
  simp only [CollatzResearch.WordTrace]
  refine ⟨167459234199435627043717817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111639489466290418029145211 167459234199435627043717817)
  ·
    refine ⟨125594425649576720282788363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167459234199435627043717817 125594425649576720282788363)
    ·
      refine ⟨188391638474365080424182545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125594425649576720282788363 188391638474365080424182545)
      ·
        refine ⟨141293728855773810318136909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188391638474365080424182545 141293728855773810318136909)
        ·
          refine ⟨52985148320915178869301341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 141293728855773810318136909 52985148320915178869301341)
          ·
            refine ⟨19869430620343192075988003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52985148320915178869301341 19869430620343192075988003)
            ·
              refine ⟨29804145930514788113982005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19869430620343192075988003 29804145930514788113982005)
              ·
                refine ⟨2794138680985761385685813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29804145930514788113982005 2794138680985761385685813)
                ·
                  refine ⟨261950501342415129908045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2794138680985761385685813 261950501342415129908045)
                  ·
                    rfl

theorem cell23_4591321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 5, 5].length) (baseStart_4591321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4591321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4591321 prefixEnd_4591321 := by exact prefixLift 4591321
  have htrace : WordTrace (prefixWord ++ tailWord_4591321) baseStart_4591321 baseEnd_4591321 := by
    simpa [prefixWord, tailWord_4591321, baseEnd_4591321] using wordTrace_append hprefix tailTrace_4591321
  have hstable : (prefixWord ++ tailWord_4591321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4591321).length < 2 ^ (prefixWord ++ tailWord_4591321).sum := by decide
  have hdescent : baseEnd_4591321 < baseStart_4591321 := by decide
  rcases family_descends (prefixWord ++ tailWord_4591321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4591371 : List Nat := [1, 1, 1, 1, 5, 1, 2, 2, 1, 6, 2]
def baseStart_4591371 : Nat := 118140960795 + 4591371 * 2 ^ 59
def prefixEnd_4591371 : Nat := 4983230072969 + 3 ^ 40 * 4591371 * 2
def baseEnd_4591371 : Nat := 2357580186114460973547175

theorem tailTrace_4591371 : CollatzResearch.WordTrace tailWord_4591371 prefixEnd_4591371 2357580186114460973547175 := by
  unfold tailWord_4591371
  simp only [CollatzResearch.WordTrace]
  refine ⟨167461057849254485583037967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111640705232836323722025311 167461057849254485583037967)
  ·
    refine ⟨251191586773881728374556951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167461057849254485583037967 251191586773881728374556951)
    ·
      refine ⟨376787380160822592561835427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251191586773881728374556951 376787380160822592561835427)
      ·
        refine ⟨565181070241233888842753141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 376787380160822592561835427 565181070241233888842753141)
        ·
          refine ⟨52985725335115677079008107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 565181070241233888842753141 52985725335115677079008107)
          ·
            refine ⟨79478588002673515618512161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52985725335115677079008107 79478588002673515618512161)
            ·
              refine ⟨59608941002005136713884121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79478588002673515618512161 59608941002005136713884121)
              ·
                refine ⟨44706705751503852535413091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59608941002005136713884121 44706705751503852535413091)
                ·
                  refine ⟨67060058627255778803119637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44706705751503852535413091 67060058627255778803119637)
                  ·
                    refine ⟨3143440248152614631396233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 67060058627255778803119637 3143440248152614631396233)
                    ·
                      refine ⟨2357580186114460973547175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3143440248152614631396233 2357580186114460973547175)
                      ·
                        rfl

theorem cell23_4591371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 6, 2].length) (baseStart_4591371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4591371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4591371 prefixEnd_4591371 := by exact prefixLift 4591371
  have htrace : WordTrace (prefixWord ++ tailWord_4591371) baseStart_4591371 baseEnd_4591371 := by
    simpa [prefixWord, tailWord_4591371, baseEnd_4591371] using wordTrace_append hprefix tailTrace_4591371
  have hstable : (prefixWord ++ tailWord_4591371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4591371).length < 2 ^ (prefixWord ++ tailWord_4591371).sum := by decide
  have hdescent : baseEnd_4591371 < baseStart_4591371 := by decide
  rcases family_descends (prefixWord ++ tailWord_4591371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4591384 : List Nat := [2, 1, 2, 3, 1, 1, 2, 1, 1, 3, 6]
def baseStart_4591384 : Nat := 118140960795 + 4591384 * 2 ^ 59
def prefixEnd_4591384 : Nat := 4983230072969 + 3 ^ 40 * 4591384 * 2
def baseEnd_4591384 : Nat := 2357586861362969422684615

theorem tailTrace_4591384 : CollatzResearch.WordTrace tailWord_4591384 prefixEnd_4591384 2357586861362969422684615 := by
  unfold tailWord_4591384
  simp only [CollatzResearch.WordTrace]
  refine ⟨83730765999103694401630603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111641021332138259202174137 83730765999103694401630603)
  ·
    refine ⟨125596148998655541602445905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83730765999103694401630603 125596148998655541602445905)
    ·
      refine ⟨94197111748991656201834429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125596148998655541602445905 94197111748991656201834429)
      ·
        refine ⟨35323916905871871075687911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94197111748991656201834429 35323916905871871075687911)
        ·
          refine ⟨52985875358807806613531867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35323916905871871075687911 52985875358807806613531867)
          ·
            refine ⟨79478813038211709920297801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52985875358807806613531867 79478813038211709920297801)
            ·
              refine ⟨59609109778658782440223351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79478813038211709920297801 59609109778658782440223351)
              ·
                refine ⟨89413664667988173660335027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59609109778658782440223351 89413664667988173660335027)
                ·
                  refine ⟨134120497001982260490502541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89413664667988173660335027 134120497001982260490502541)
                  ·
                    refine ⟨50295186375743347683938453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 134120497001982260490502541 50295186375743347683938453)
                    ·
                      refine ⟨2357586861362969422684615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50295186375743347683938453 2357586861362969422684615)
                      ·
                        rfl

theorem cell23_4591384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_4591384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4591384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4591384 prefixEnd_4591384 := by exact prefixLift 4591384
  have htrace : WordTrace (prefixWord ++ tailWord_4591384) baseStart_4591384 baseEnd_4591384 := by
    simpa [prefixWord, tailWord_4591384, baseEnd_4591384] using wordTrace_append hprefix tailTrace_4591384
  have hstable : (prefixWord ++ tailWord_4591384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4591384).length < 2 ^ (prefixWord ++ tailWord_4591384).sum := by decide
  have hdescent : baseEnd_4591384 < baseStart_4591384 := by decide
  rcases family_descends (prefixWord ++ tailWord_4591384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4591458 : List Nat := [3, 3, 2, 1, 2, 1, 1, 2, 3, 5]
def baseStart_4591458 : Nat := 118140960795 + 4591458 * 2 ^ 59
def prefixEnd_4591458 : Nat := 4983230072969 + 3 ^ 40 * 4591458 * 2
def baseEnd_4591458 : Nat := 785874952977134044386425

theorem tailTrace_4591458 : CollatzResearch.WordTrace tailWord_4591458 prefixEnd_4591458 785874952977134044386425 := by
  unfold tailWord_4591458
  simp only [CollatzResearch.WordTrace]
  refine ⟨41866057749984824860363757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111642820666626199627636685 41866057749984824860363757)
  ·
    refine ⟨15699771656244309322636409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41866057749984824860363757 15699771656244309322636409)
    ·
      refine ⟨11774828742183231991977307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15699771656244309322636409 11774828742183231991977307)
      ·
        refine ⟨17662243113274847987965961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11774828742183231991977307 17662243113274847987965961)
        ·
          refine ⟨13246682334956135990974471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17662243113274847987965961 13246682334956135990974471)
          ·
            refine ⟨19870023502434203986461707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13246682334956135990974471 19870023502434203986461707)
            ·
              refine ⟨29805035253651305979692561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19870023502434203986461707 29805035253651305979692561)
              ·
                refine ⟨22353776440238479484769421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29805035253651305979692561 22353776440238479484769421)
                ·
                  refine ⟨8382666165089429806788533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22353776440238479484769421 8382666165089429806788533)
                  ·
                    refine ⟨785874952977134044386425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8382666165089429806788533 785874952977134044386425)
                    ·
                      rfl

theorem cell23_4591458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_4591458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4591458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4591458 prefixEnd_4591458 := by exact prefixLift 4591458
  have htrace : WordTrace (prefixWord ++ tailWord_4591458) baseStart_4591458 baseEnd_4591458 := by
    simpa [prefixWord, tailWord_4591458, baseEnd_4591458] using wordTrace_append hprefix tailTrace_4591458
  have hstable : (prefixWord ++ tailWord_4591458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4591458).length < 2 ^ (prefixWord ++ tailWord_4591458).sum := by decide
  have hdescent : baseEnd_4591458 < baseStart_4591458 := by decide
  rcases family_descends (prefixWord ++ tailWord_4591458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4591471 : List Nat := [1, 1, 2, 1, 3, 1, 1, 1, 8, 4]
def baseStart_4591471 : Nat := 118140960795 + 4591471 * 2 ^ 59
def prefixEnd_4591471 : Nat := 4983230072969 + 3 ^ 40 * 4591471 * 2
def baseEnd_4591471 : Nat := 785877178059970194098905

theorem tailTrace_4591471 : CollatzResearch.WordTrace tailWord_4591471 prefixEnd_4591471 785877178059970194098905 := by
  unfold tailWord_4591471
  simp only [CollatzResearch.WordTrace]
  refine ⟨167464705148892202661678267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111643136765928135107785511 167464705148892202661678267)
  ·
    refine ⟨251197057723338303992517401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167464705148892202661678267 251197057723338303992517401)
    ·
      refine ⟨188397793292503727994388051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 251197057723338303992517401 188397793292503727994388051)
      ·
        refine ⟨282596689938755591991582077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188397793292503727994388051 282596689938755591991582077)
        ·
          refine ⟨105973758727033346996843279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 282596689938755591991582077 105973758727033346996843279)
          ·
            refine ⟨158960638090550020495264919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105973758727033346996843279 158960638090550020495264919)
            ·
              refine ⟨238440957135825030742897379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 158960638090550020495264919 238440957135825030742897379)
              ·
                refine ⟨357661435703737546114346069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 238440957135825030742897379 357661435703737546114346069)
                ·
                  refine ⟨4191344949653174368527493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 357661435703737546114346069 4191344949653174368527493)
                  ·
                    refine ⟨785877178059970194098905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4191344949653174368527493 785877178059970194098905)
                    ·
                      rfl

theorem cell23_4591471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 8, 4].length) (baseStart_4591471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4591471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4591471 prefixEnd_4591471 := by exact prefixLift 4591471
  have htrace : WordTrace (prefixWord ++ tailWord_4591471) baseStart_4591471 baseEnd_4591471 := by
    simpa [prefixWord, tailWord_4591471, baseEnd_4591471] using wordTrace_append hprefix tailTrace_4591471
  have hstable : (prefixWord ++ tailWord_4591471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4591471).length < 2 ^ (prefixWord ++ tailWord_4591471).sum := by decide
  have hdescent : baseEnd_4591471 < baseStart_4591471 := by decide
  rcases family_descends (prefixWord ++ tailWord_4591471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4591495 : List Nat := [1, 1, 4, 2, 4, 1, 1, 3, 1, 1, 4]
def baseStart_4591495 : Nat := 118140960795 + 4591495 * 2 ^ 59
def prefixEnd_4591495 : Nat := 4983230072969 + 3 ^ 40 * 4591495 * 2
def baseEnd_4591495 : Nat := 2357643857715618488396605

theorem tailTrace_4591495 : CollatzResearch.WordTrace tailWord_4591495 prefixEnd_4591495 2357643857715618488396605 := by
  unfold tailWord_4591495
  simp only [CollatzResearch.WordTrace]
  refine ⟨167465580500805254760551939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111643720333870169840367959 167465580500805254760551939)
  ·
    refine ⟨251198370751207882140827909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167465580500805254760551939 251198370751207882140827909)
    ·
      refine ⟨47099694515851477901405233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 251198370751207882140827909 47099694515851477901405233)
      ·
        refine ⟨35324770886888608426053925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47099694515851477901405233 35324770886888608426053925)
        ·
          refine ⟨6623394541291614079885111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35324770886888608426053925 6623394541291614079885111)
          ·
            refine ⟨9935091811937421119827667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6623394541291614079885111 9935091811937421119827667)
            ·
              refine ⟨14902637717906131679741501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9935091811937421119827667 14902637717906131679741501)
              ·
                refine ⟨5588489144214799379903063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14902637717906131679741501 5588489144214799379903063)
                ·
                  refine ⟨8382733716322199069854595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5588489144214799379903063 8382733716322199069854595)
                  ·
                    refine ⟨12574100574483298604781893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8382733716322199069854595 12574100574483298604781893)
                    ·
                      refine ⟨2357643857715618488396605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12574100574483298604781893 2357643857715618488396605)
                      ·
                        rfl

theorem cell23_4591495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 3, 1, 1, 4].length) (baseStart_4591495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4591495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4591495 prefixEnd_4591495 := by exact prefixLift 4591495
  have htrace : WordTrace (prefixWord ++ tailWord_4591495) baseStart_4591495 baseEnd_4591495 := by
    simpa [prefixWord, tailWord_4591495, baseEnd_4591495] using wordTrace_append hprefix tailTrace_4591495
  have hstable : (prefixWord ++ tailWord_4591495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4591495).length < 2 ^ (prefixWord ++ tailWord_4591495).sum := by decide
  have hdescent : baseEnd_4591495 < baseStart_4591495 := by decide
  rcases family_descends (prefixWord ++ tailWord_4591495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4591522 : List Nat := [3, 3, 1, 2, 4, 1, 1, 1, 1, 6]
def baseStart_4591522 : Nat := 118140960795 + 4591522 * 2 ^ 59
def prefixEnd_4591522 : Nat := 4983230072969 + 3 ^ 40 * 4591522 * 2
def baseEnd_4591522 : Nat := 785885907231096627586327

theorem tailTrace_4591522 : CollatzResearch.WordTrace tailWord_4591522 prefixEnd_4591522 785885907231096627586327 := by
  unfold tailWord_4591522
  simp only [CollatzResearch.WordTrace]
  refine ⟨41866641317926859592946205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111644376847804958914523213 41866641317926859592946205)
  ·
    refine ⟨15699990494222572347354827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41866641317926859592946205 15699990494222572347354827)
    ·
      refine ⟨23549985741333858521032241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15699990494222572347354827 23549985741333858521032241)
      ·
        refine ⟨17662489306000393890774181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23549985741333858521032241 17662489306000393890774181)
        ·
          refine ⟨3311716744875073854520159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17662489306000393890774181 3311716744875073854520159)
          ·
            refine ⟨4967575117312610781780239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3311716744875073854520159 4967575117312610781780239)
            ·
              refine ⟨7451362675968916172670359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4967575117312610781780239 7451362675968916172670359)
              ·
                refine ⟨11177044013953374259005539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7451362675968916172670359 11177044013953374259005539)
                ·
                  refine ⟨16765566020930061388508309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11177044013953374259005539 16765566020930061388508309)
                  ·
                    refine ⟨785885907231096627586327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16765566020930061388508309 785885907231096627586327)
                    ·
                      rfl

theorem cell23_4591522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 1, 1, 6].length) (baseStart_4591522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4591522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4591522 prefixEnd_4591522 := by exact prefixLift 4591522
  have htrace : WordTrace (prefixWord ++ tailWord_4591522) baseStart_4591522 baseEnd_4591522 := by
    simpa [prefixWord, tailWord_4591522, baseEnd_4591522] using wordTrace_append hprefix tailTrace_4591522
  have hstable : (prefixWord ++ tailWord_4591522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4591522).length < 2 ^ (prefixWord ++ tailWord_4591522).sum := by decide
  have hdescent : baseEnd_4591522 < baseStart_4591522 := by decide
  rcases family_descends (prefixWord ++ tailWord_4591522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4591538 : List Nat := [3, 2, 1, 1, 1, 1, 1, 2, 2, 7, 2]
def baseStart_4591538 : Nat := 118140960795 + 4591538 * 2 ^ 59
def prefixEnd_4591538 : Nat := 4983230072969 + 3 ^ 40 * 4591538 * 2
def baseEnd_4591538 : Nat := 2357665937383761820158907

theorem tailTrace_4591538 : CollatzResearch.WordTrace tailWord_4591538 prefixEnd_4591538 2357665937383761820158907 := by
  unfold tailWord_4591538
  simp only [CollatzResearch.WordTrace]
  refine ⟨41866787209912368276091817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111644765893099648736244845 41866787209912368276091817)
  ·
    refine ⟨31400090407434276207068863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41866787209912368276091817 31400090407434276207068863)
    ·
      refine ⟨47100135611151414310603295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31400090407434276207068863 47100135611151414310603295)
      ·
        refine ⟨70650203416727121465904943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47100135611151414310603295 70650203416727121465904943)
        ·
          refine ⟨105975305125090682198857415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70650203416727121465904943 105975305125090682198857415)
          ·
            refine ⟨158962957687636023298286123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105975305125090682198857415 158962957687636023298286123)
            ·
              refine ⟨238444436531454034947429185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 158962957687636023298286123 238444436531454034947429185)
              ·
                refine ⟨178833327398590526210571889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 238444436531454034947429185 178833327398590526210571889)
                ·
                  refine ⟨134124995548942894657928917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 178833327398590526210571889 134124995548942894657928917)
                  ·
                    refine ⟨3143554583178349093545209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 134124995548942894657928917 3143554583178349093545209)
                    ·
                      refine ⟨2357665937383761820158907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3143554583178349093545209 2357665937383761820158907)
                      ·
                        rfl

theorem cell23_4591538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 2, 7, 2].length) (baseStart_4591538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4591538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4591538 prefixEnd_4591538 := by exact prefixLift 4591538
  have htrace : WordTrace (prefixWord ++ tailWord_4591538) baseStart_4591538 baseEnd_4591538 := by
    simpa [prefixWord, tailWord_4591538, baseEnd_4591538] using wordTrace_append hprefix tailTrace_4591538
  have hstable : (prefixWord ++ tailWord_4591538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4591538).length < 2 ^ (prefixWord ++ tailWord_4591538).sum := by decide
  have hdescent : baseEnd_4591538 < baseStart_4591538 := by decide
  rcases family_descends (prefixWord ++ tailWord_4591538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4591606 : List Nat := [5, 1, 1, 1, 4, 1, 3, 1, 1, 3, 2]
def baseStart_4591606 : Nat := 118140960795 + 4591606 * 2 ^ 59
def prefixEnd_4591606 : Nat := 4983230072969 + 3 ^ 40 * 4591606 * 2
def baseEnd_4591606 : Nat := 2357700854068267554108595

theorem tailTrace_4591606 : CollatzResearch.WordTrace tailWord_4591606 prefixEnd_4591606 2357700854068267554108595 := by
  unfold tailWord_4591606
  simp only [CollatzResearch.WordTrace]
  refine ⟨10466851812712695044865167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 111646419335602080478561781 10466851812712695044865167)
  ·
    refine ⟨15700277719069042567297751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10466851812712695044865167 15700277719069042567297751)
    ·
      refine ⟨23550416578603563850946627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15700277719069042567297751 23550416578603563850946627)
      ·
        refine ⟨35325624867905345776419941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23550416578603563850946627 35325624867905345776419941)
        ·
          refine ⟨6623554662732252333078739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35325624867905345776419941 6623554662732252333078739)
          ·
            refine ⟨9935331994098378499618109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6623554662732252333078739 9935331994098378499618109)
            ·
              refine ⟨3725749497786891937356791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9935331994098378499618109 3725749497786891937356791)
              ·
                refine ⟨5588624246680337906035187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3725749497786891937356791 5588624246680337906035187)
                ·
                  refine ⟨8382936370020506859052781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5588624246680337906035187 8382936370020506859052781)
                  ·
                    refine ⟨3143601138757690072144793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8382936370020506859052781 3143601138757690072144793)
                    ·
                      refine ⟨2357700854068267554108595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3143601138757690072144793 2357700854068267554108595)
                      ·
                        rfl

theorem cell23_4591606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 3, 1, 1, 3, 2].length) (baseStart_4591606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4591606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4591606 prefixEnd_4591606 := by exact prefixLift 4591606
  have htrace : WordTrace (prefixWord ++ tailWord_4591606) baseStart_4591606 baseEnd_4591606 := by
    simpa [prefixWord, tailWord_4591606, baseEnd_4591606] using wordTrace_append hprefix tailTrace_4591606
  have hstable : (prefixWord ++ tailWord_4591606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4591606).length < 2 ^ (prefixWord ++ tailWord_4591606).sum := by decide
  have hdescent : baseEnd_4591606 < baseStart_4591606 := by decide
  rcases family_descends (prefixWord ++ tailWord_4591606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4591629 : List Nat := [1, 7, 1, 2, 1, 1, 1, 1, 2, 6]
def baseStart_4591629 : Nat := 118140960795 + 4591629 * 2 ^ 59
def prefixEnd_4591629 : Nat := 4983230072969 + 3 ^ 40 * 4591629 * 2
def baseEnd_4591629 : Nat := 785904221374440321373663

theorem tailTrace_4591629 : CollatzResearch.WordTrace tailWord_4591629 prefixEnd_4591629 785904221374440321373663 := by
  unfold tailWord_4591629
  simp only [CollatzResearch.WordTrace]
  refine ⟨167470467882319795645929941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111646978588213197097286627 167470467882319795645929941)
  ·
    refine ⟨3925089090991870210451483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 167470467882319795645929941 3925089090991870210451483)
    ·
      refine ⟨5887633636487805315677225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3925089090991870210451483 5887633636487805315677225)
      ·
        refine ⟨4415725227365853986757919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5887633636487805315677225 4415725227365853986757919)
        ·
          refine ⟨6623587841048780980136879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4415725227365853986757919 6623587841048780980136879)
          ·
            refine ⟨9935381761573171470205319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6623587841048780980136879 9935381761573171470205319)
            ·
              refine ⟨14903072642359757205307979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9935381761573171470205319 14903072642359757205307979)
              ·
                refine ⟨22354608963539635807961969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14903072642359757205307979 22354608963539635807961969)
                ·
                  refine ⟨16765956722654726855971477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22354608963539635807961969 16765956722654726855971477)
                  ·
                    refine ⟨785904221374440321373663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16765956722654726855971477 785904221374440321373663)
                    ·
                      rfl

theorem cell23_4591629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_4591629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4591629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4591629 prefixEnd_4591629 := by exact prefixLift 4591629
  have htrace : WordTrace (prefixWord ++ tailWord_4591629) baseStart_4591629 baseEnd_4591629 := by
    simpa [prefixWord, tailWord_4591629, baseEnd_4591629] using wordTrace_append hprefix tailTrace_4591629
  have hstable : (prefixWord ++ tailWord_4591629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4591629).length < 2 ^ (prefixWord ++ tailWord_4591629).sum := by decide
  have hdescent : baseEnd_4591629 < baseStart_4591629 := by decide
  rcases family_descends (prefixWord ++ tailWord_4591629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4591636 : List Nat := [2, 4, 3, 2, 1, 1, 2, 1, 1, 4, 2]
def baseStart_4591636 : Nat := 118140960795 + 4591636 * 2 ^ 59
def prefixEnd_4591636 : Nat := 4983230072969 + 3 ^ 40 * 4591636 * 2
def baseEnd_4591636 : Nat := 2357716258487902436733457

theorem tailTrace_4591636 : CollatzResearch.WordTrace tailWord_4591636 prefixEnd_4591636 2357716258487902436733457 := by
  unfold tailWord_4591636
  simp only [CollatzResearch.WordTrace]
  refine ⟨83735361596647217920717381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111647148795529623894289841 83735361596647217920717381)
  ·
    refine ⟨15700380299371353360134509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83735361596647217920717381 15700380299371353360134509)
    ·
      refine ⟨5887642612264257510050441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15700380299371353360134509 5887642612264257510050441)
      ·
        refine ⟨4415731959198193132537831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5887642612264257510050441 4415731959198193132537831)
        ·
          refine ⟨6623597938797289698806747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4415731959198193132537831 6623597938797289698806747)
          ·
            refine ⟨9935396908195934548210121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6623597938797289698806747 9935396908195934548210121)
            ·
              refine ⟨7451547681146950911157591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9935396908195934548210121 7451547681146950911157591)
              ·
                refine ⟨11177321521720426366736387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7451547681146950911157591 11177321521720426366736387)
                ·
                  refine ⟨16765982282580639550104581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11177321521720426366736387 16765982282580639550104581)
                  ·
                    refine ⟨3143621677983869915644609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16765982282580639550104581 3143621677983869915644609)
                    ·
                      refine ⟨2357716258487902436733457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3143621677983869915644609 2357716258487902436733457)
                      ·
                        rfl

theorem cell23_4591636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_4591636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4591636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4591636 prefixEnd_4591636 := by exact prefixLift 4591636
  have htrace : WordTrace (prefixWord ++ tailWord_4591636) baseStart_4591636 baseEnd_4591636 := by
    simpa [prefixWord, tailWord_4591636, baseEnd_4591636] using wordTrace_append hprefix tailTrace_4591636
  have hstable : (prefixWord ++ tailWord_4591636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4591636).length < 2 ^ (prefixWord ++ tailWord_4591636).sum := by decide
  have hdescent : baseEnd_4591636 < baseStart_4591636 := by decide
  rcases family_descends (prefixWord ++ tailWord_4591636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4591765 : List Nat := [1, 3, 2, 1, 1, 1, 5, 1, 3, 1, 4]
def baseStart_4591765 : Nat := 118140960795 + 4591765 * 2 ^ 59
def prefixEnd_4591765 : Nat := 4983230072969 + 3 ^ 40 * 4591765 * 2
def baseEnd_4591765 : Nat := 2357782497492332432020363

theorem tailTrace_4591765 : CollatzResearch.WordTrace tailWord_4591765 prefixEnd_4591765 2357782497492332432020363 := by
  unfold tailWord_4591765
  simp only [CollatzResearch.WordTrace]
  refine ⟨167475428209827090872880749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111650285473218060581920499 167475428209827090872880749)
  ·
    refine ⟨62803285578685159077330281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167475428209827090872880749 62803285578685159077330281)
    ·
      refine ⟨47102464184013869307997711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62803285578685159077330281 47102464184013869307997711)
      ·
        refine ⟨70653696276020803961996567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47102464184013869307997711 70653696276020803961996567)
        ·
          refine ⟨105980544414031205942994851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70653696276020803961996567 105980544414031205942994851)
          ·
            refine ⟨158970816621046808914492277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105980544414031205942994851 158970816621046808914492277)
            ·
              refine ⟨14903514058223138335733651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 158970816621046808914492277 14903514058223138335733651)
              ·
                refine ⟨22355271087334707503600477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14903514058223138335733651 22355271087334707503600477)
                ·
                  refine ⟨8383226657750515313850179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22355271087334707503600477 8383226657750515313850179)
                  ·
                    refine ⟨12574839986625772970775269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8383226657750515313850179 12574839986625772970775269)
                    ·
                      refine ⟨2357782497492332432020363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12574839986625772970775269 2357782497492332432020363)
                      ·
                        rfl

theorem cell23_4591765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 3, 1, 4].length) (baseStart_4591765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4591765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4591765 prefixEnd_4591765 := by exact prefixLift 4591765
  have htrace : WordTrace (prefixWord ++ tailWord_4591765) baseStart_4591765 baseEnd_4591765 := by
    simpa [prefixWord, tailWord_4591765, baseEnd_4591765] using wordTrace_append hprefix tailTrace_4591765
  have hstable : (prefixWord ++ tailWord_4591765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4591765).length < 2 ^ (prefixWord ++ tailWord_4591765).sum := by decide
  have hdescent : baseEnd_4591765 < baseStart_4591765 := by decide
  rcases family_descends (prefixWord ++ tailWord_4591765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4591775 : List Nat := [1, 1, 2, 6, 1, 1, 1, 1, 3, 6]
def baseStart_4591775 : Nat := 118140960795 + 4591775 * 2 ^ 59
def prefixEnd_4591775 : Nat := 4983230072969 + 3 ^ 40 * 4591775 * 2
def baseEnd_4591775 : Nat := 785929210766292464298439

theorem tailTrace_4591775 : CollatzResearch.WordTrace tailWord_4591775 prefixEnd_4591775 785929210766292464298439 := by
  unfold tailWord_4591775
  simp only [CollatzResearch.WordTrace]
  refine ⟨167475792939790862580744779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111650528626527241720496519 167475792939790862580744779)
  ·
    refine ⟨251213689409686293871117169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167475792939790862580744779 251213689409686293871117169)
    ·
      refine ⟨188410267057264720403337877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 251213689409686293871117169 188410267057264720403337877)
      ·
        refine ⟨8831731268309283768906463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 188410267057264720403337877 8831731268309283768906463)
        ·
          refine ⟨13247596902463925653359695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8831731268309283768906463 13247596902463925653359695)
          ·
            refine ⟨19871395353695888480039543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13247596902463925653359695 19871395353695888480039543)
            ·
              refine ⟨29807093030543832720059315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19871395353695888480039543 29807093030543832720059315)
              ·
                refine ⟨44710639545815749080088973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29807093030543832720059315 44710639545815749080088973)
                ·
                  refine ⟨16766489829680905905033365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44710639545815749080088973 16766489829680905905033365)
                  ·
                    refine ⟨785929210766292464298439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16766489829680905905033365 785929210766292464298439)
                    ·
                      rfl

theorem cell23_4591775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 3, 6].length) (baseStart_4591775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4591775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4591775 prefixEnd_4591775 := by exact prefixLift 4591775
  have htrace : WordTrace (prefixWord ++ tailWord_4591775) baseStart_4591775 baseEnd_4591775 := by
    simpa [prefixWord, tailWord_4591775, baseEnd_4591775] using wordTrace_append hprefix tailTrace_4591775
  have hstable : (prefixWord ++ tailWord_4591775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4591775).length < 2 ^ (prefixWord ++ tailWord_4591775).sum := by decide
  have hdescent : baseEnd_4591775 < baseStart_4591775 := by decide
  rcases family_descends (prefixWord ++ tailWord_4591775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4591809 : List Nat := [1, 2, 6, 1, 2, 1, 2, 1, 1, 6]
def baseStart_4591809 : Nat := 118140960795 + 4591809 * 2 ^ 59
def prefixEnd_4591809 : Nat := 4983230072969 + 3 ^ 40 * 4591809 * 2
def baseEnd_4591809 : Nat := 785935030213710086623387

theorem tailTrace_4591809 : CollatzResearch.WordTrace tailWord_4591809 prefixEnd_4591809 785935030213710086623387 := by
  unfold tailWord_4591809
  simp only [CollatzResearch.WordTrace]
  refine ⟨167477033021667686387482481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111651355347778457591654987 167477033021667686387482481)
  ·
    refine ⟨125607774766250764790611861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167477033021667686387482481 125607774766250764790611861)
    ·
      refine ⟨5887864442168004599559931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 125607774766250764790611861 5887864442168004599559931)
      ·
        refine ⟨8831796663252006899339897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5887864442168004599559931 8831796663252006899339897)
        ·
          refine ⟨6623847497439005174504923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8831796663252006899339897 6623847497439005174504923)
          ·
            refine ⟨9935771246158507761757385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6623847497439005174504923 9935771246158507761757385)
            ·
              refine ⟨7451828434618880821318039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9935771246158507761757385 7451828434618880821318039)
              ·
                refine ⟨11177742651928321231977059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7451828434618880821318039 11177742651928321231977059)
                ·
                  refine ⟨16766613977892481847965589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11177742651928321231977059 16766613977892481847965589)
                  ·
                    refine ⟨785935030213710086623387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16766613977892481847965589 785935030213710086623387)
                    ·
                      rfl

theorem cell23_4591809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_4591809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4591809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4591809 prefixEnd_4591809 := by exact prefixLift 4591809
  have htrace : WordTrace (prefixWord ++ tailWord_4591809) baseStart_4591809 baseEnd_4591809 := by
    simpa [prefixWord, tailWord_4591809, baseEnd_4591809] using wordTrace_append hprefix tailTrace_4591809
  have hstable : (prefixWord ++ tailWord_4591809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4591809).length < 2 ^ (prefixWord ++ tailWord_4591809).sum := by decide
  have hdescent : baseEnd_4591809 < baseStart_4591809 := by decide
  rcases family_descends (prefixWord ++ tailWord_4591809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4591812 : List Nat := [2, 3, 3, 1, 2, 1, 1, 3, 1, 2, 4]
def baseStart_4591812 : Nat := 118140960795 + 4591812 * 2 ^ 59
def prefixEnd_4591812 : Nat := 4983230072969 + 3 ^ 40 * 4591812 * 2
def baseEnd_4591812 : Nat := 2357806631083093748132647

theorem tailTrace_4591812 : CollatzResearch.WordTrace tailWord_4591812 prefixEnd_4591812 2357806631083093748132647 := by
  unfold tailWord_4591812
  simp only [CollatzResearch.WordTrace]
  refine ⟨83738571220328408949920845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111651428293771211933227793 83738571220328408949920845)
  ·
    refine ⟨31401964207623153356220317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83738571220328408949920845 31401964207623153356220317)
    ·
      refine ⟨11775736577858682508582619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31401964207623153356220317 11775736577858682508582619)
      ·
        refine ⟨17663604866788023762873929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11775736577858682508582619 17663604866788023762873929)
        ·
          refine ⟨13247703650091017822155447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17663604866788023762873929 13247703650091017822155447)
          ·
            refine ⟨19871555475136526733233171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13247703650091017822155447 19871555475136526733233171)
            ·
              refine ⟨29807333212704790099849757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19871555475136526733233171 29807333212704790099849757)
              ·
                refine ⟨11177749954764296287443659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29807333212704790099849757 11177749954764296287443659)
                ·
                  refine ⟨16766624932146444431165489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11177749954764296287443659 16766624932146444431165489)
                  ·
                    refine ⟨12574968699109833323374117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16766624932146444431165489 12574968699109833323374117)
                    ·
                      refine ⟨2357806631083093748132647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12574968699109833323374117 2357806631083093748132647)
                      ·
                        rfl

theorem cell23_4591812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_4591812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4591812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4591812 prefixEnd_4591812 := by exact prefixLift 4591812
  have htrace : WordTrace (prefixWord ++ tailWord_4591812) baseStart_4591812 baseEnd_4591812 := by
    simpa [prefixWord, tailWord_4591812, baseEnd_4591812] using wordTrace_append hprefix tailTrace_4591812
  have hstable : (prefixWord ++ tailWord_4591812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4591812).length < 2 ^ (prefixWord ++ tailWord_4591812).sum := by decide
  have hdescent : baseEnd_4591812 < baseStart_4591812 := by decide
  rcases family_descends (prefixWord ++ tailWord_4591812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4591822 : List Nat := [4, 1, 1, 1, 4, 2, 3, 7]
def baseStart_4591822 : Nat := 118140960795 + 4591822 * 2 ^ 59
def prefixEnd_4591822 : Nat := 4983230072969 + 3 ^ 40 * 4591822 * 2
def baseEnd_4591822 : Nat := 87326361699616248481763

theorem tailTrace_4591822 : CollatzResearch.WordTrace tailWord_4591822 prefixEnd_4591822 87326361699616248481763 := by
  unfold tailWord_4591822
  simp only [CollatzResearch.WordTrace]
  refine ⟨20934688396327573700963215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111651671447080393071803813 20934688396327573700963215)
  ·
    refine ⟨31402032594491360551444823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20934688396327573700963215 31402032594491360551444823)
    ·
      refine ⟨47103048891737040827167235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31402032594491360551444823 47103048891737040827167235)
      ·
        refine ⟨70654573337605561240750853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47103048891737040827167235 70654573337605561240750853)
        ·
          refine ⟨13247732500801042732640785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70654573337605561240750853 13247732500801042732640785)
          ·
            refine ⟨9935799375600782049480589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13247732500801042732640785 9935799375600782049480589)
            ·
              refine ⟨3725924765850293268555221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9935799375600782049480589 3725924765850293268555221)
              ·
                refine ⟨87326361699616248481763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3725924765850293268555221 87326361699616248481763)
                ·
                  rfl

theorem cell23_4591822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 3, 7].length) (baseStart_4591822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4591822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4591822 prefixEnd_4591822 := by exact prefixLift 4591822
  have htrace : WordTrace (prefixWord ++ tailWord_4591822) baseStart_4591822 baseEnd_4591822 := by
    simpa [prefixWord, tailWord_4591822, baseEnd_4591822] using wordTrace_append hprefix tailTrace_4591822
  have hstable : (prefixWord ++ tailWord_4591822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4591822).length < 2 ^ (prefixWord ++ tailWord_4591822).sum := by decide
  have hdescent : baseEnd_4591822 < baseStart_4591822 := by decide
  rcases family_descends (prefixWord ++ tailWord_4591822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4591832 : List Nat := [2, 1, 2, 2, 4, 1, 2, 2, 1, 3, 3]
def baseStart_4591832 : Nat := 118140960795 + 4591832 * 2 ^ 59
def prefixEnd_4591832 : Nat := 4983230072969 + 3 ^ 40 * 4591832 * 2
def baseEnd_4591832 : Nat := 2357816900696183669882555

theorem tailTrace_4591832 : CollatzResearch.WordTrace tailWord_4591832 prefixEnd_4591832 2357816900696183669882555 := by
  unfold tailWord_4591832
  simp only [CollatzResearch.WordTrace]
  refine ⟨83738935950292180657784875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111651914600389574210379833 83738935950292180657784875)
  ·
    refine ⟨125608403925438270986677313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83738935950292180657784875 125608403925438270986677313)
    ·
      refine ⟨94206302944078703240007985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125608403925438270986677313 94206302944078703240007985)
      ·
        refine ⟨70654727208059027430005989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94206302944078703240007985 70654727208059027430005989)
        ·
          refine ⟨13247761351511067643126123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70654727208059027430005989 13247761351511067643126123)
          ·
            refine ⟨19871642027266601464689185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13247761351511067643126123 19871642027266601464689185)
            ·
              refine ⟨14903731520449951098516889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19871642027266601464689185 14903731520449951098516889)
              ·
                refine ⟨11177798640337463323887667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14903731520449951098516889 11177798640337463323887667)
                ·
                  refine ⟨16766697960506194985831501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11177798640337463323887667 16766697960506194985831501)
                  ·
                    refine ⟨6287511735189823119686813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16766697960506194985831501 6287511735189823119686813)
                    ·
                      refine ⟨2357816900696183669882555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6287511735189823119686813 2357816900696183669882555)
                      ·
                        rfl

theorem cell23_4591832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 2, 1, 3, 3].length) (baseStart_4591832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4591832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4591832 prefixEnd_4591832 := by exact prefixLift 4591832
  have htrace : WordTrace (prefixWord ++ tailWord_4591832) baseStart_4591832 baseEnd_4591832 := by
    simpa [prefixWord, tailWord_4591832, baseEnd_4591832] using wordTrace_append hprefix tailTrace_4591832
  have hstable : (prefixWord ++ tailWord_4591832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4591832).length < 2 ^ (prefixWord ++ tailWord_4591832).sum := by decide
  have hdescent : baseEnd_4591832 < baseStart_4591832 := by decide
  rcases family_descends (prefixWord ++ tailWord_4591832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4591843 : List Nat := [1, 1, 1, 8, 2, 1, 1, 2, 2, 4]
def baseStart_4591843 : Nat := 118140960795 + 4591843 * 2 ^ 59
def prefixEnd_4591843 : Nat := 4983230072969 + 3 ^ 40 * 4591843 * 2
def baseEnd_4591843 : Nat := 785940849661127708948335

theorem tailTrace_4591843 : CollatzResearch.WordTrace tailWord_4591843 prefixEnd_4591843 785940849661127708948335 := by
  unfold tailWord_4591843
  simp only [CollatzResearch.WordTrace]
  refine ⟨167478273103544510194220183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111652182069029673462813455 167478273103544510194220183)
  ·
    refine ⟨251217409655316765291330275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167478273103544510194220183 251217409655316765291330275)
    ·
      refine ⟨376826114482975147936995413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251217409655316765291330275 376826114482975147936995413)
      ·
        refine ⟨4415931029097365014886665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 376826114482975147936995413 4415931029097365014886665)
        ·
          refine ⟨3311948271823023761164999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4415931029097365014886665 3311948271823023761164999)
          ·
            refine ⟨4967922407734535641747499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3311948271823023761164999 4967922407734535641747499)
            ·
              refine ⟨7451883611601803462621249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4967922407734535641747499 7451883611601803462621249)
              ·
                refine ⟨5588912708701352596965937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7451883611601803462621249 5588912708701352596965937)
                ·
                  refine ⟨4191684531526014447724453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5588912708701352596965937 4191684531526014447724453)
                  ·
                    refine ⟨785940849661127708948335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4191684531526014447724453 785940849661127708948335)
                    ·
                      rfl

theorem cell23_4591843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 2, 2, 4].length) (baseStart_4591843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4591843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4591843 prefixEnd_4591843 := by exact prefixLift 4591843
  have htrace : WordTrace (prefixWord ++ tailWord_4591843) baseStart_4591843 baseEnd_4591843 := by
    simpa [prefixWord, tailWord_4591843, baseEnd_4591843] using wordTrace_append hprefix tailTrace_4591843
  have hstable : (prefixWord ++ tailWord_4591843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4591843).length < 2 ^ (prefixWord ++ tailWord_4591843).sum := by decide
  have hdescent : baseEnd_4591843 < baseStart_4591843 := by decide
  rcases family_descends (prefixWord ++ tailWord_4591843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4591866 : List Nat := [3, 1, 1, 1, 1, 6, 3, 1, 2, 1, 3]
def baseStart_4591866 : Nat := 118140960795 + 4591866 * 2 ^ 59
def prefixEnd_4591866 : Nat := 4983230072969 + 3 ^ 40 * 4591866 * 2
def baseEnd_4591866 : Nat := 2357834359038436536857399

theorem tailTrace_4591866 : CollatzResearch.WordTrace tailWord_4591866 prefixEnd_4591866 2357834359038436536857399 := by
  unfold tailWord_4591866
  simp only [CollatzResearch.WordTrace]
  refine ⟨41869777995615296280576863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111652741321640790081538301 41869777995615296280576863)
  ·
    refine ⟨62804666993422944420865295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41869777995615296280576863 62804666993422944420865295)
    ·
      refine ⟨94207000490134416631297943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62804666993422944420865295 94207000490134416631297943)
      ·
        refine ⟨141310500735201624946946915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94207000490134416631297943 141310500735201624946946915)
        ·
          refine ⟨211965751102802437420420373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141310500735201624946946915 211965751102802437420420373)
          ·
            refine ⟨9935894582943864254082205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 211965751102802437420420373 9935894582943864254082205)
            ·
              refine ⟨3725960468603949095280827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9935894582943864254082205 3725960468603949095280827)
              ·
                refine ⟨5588940702905923642921241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3725960468603949095280827 5588940702905923642921241)
                ·
                  refine ⟨4191705527179442732190931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5588940702905923642921241 4191705527179442732190931)
                  ·
                    refine ⟨6287558290769164098286397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4191705527179442732190931 6287558290769164098286397)
                    ·
                      refine ⟨2357834359038436536857399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6287558290769164098286397 2357834359038436536857399)
                      ·
                        rfl

theorem cell23_4591866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 3, 1, 2, 1, 3].length) (baseStart_4591866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4591866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4591866 prefixEnd_4591866 := by exact prefixLift 4591866
  have htrace : WordTrace (prefixWord ++ tailWord_4591866) baseStart_4591866 baseEnd_4591866 := by
    simpa [prefixWord, tailWord_4591866, baseEnd_4591866] using wordTrace_append hprefix tailTrace_4591866
  have hstable : (prefixWord ++ tailWord_4591866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4591866).length < 2 ^ (prefixWord ++ tailWord_4591866).sum := by decide
  have hdescent : baseEnd_4591866 < baseStart_4591866 := by decide
  rcases family_descends (prefixWord ++ tailWord_4591866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4591875 : List Nat := [1, 1, 1, 3, 2, 3, 2, 2, 2, 1, 5]
def baseStart_4591875 : Nat := 118140960795 + 4591875 * 2 ^ 59
def prefixEnd_4591875 : Nat := 4983230072969 + 3 ^ 40 * 4591875 * 2
def baseEnd_4591875 : Nat := 2357838980364327001644857

theorem tailTrace_4591875 : CollatzResearch.WordTrace tailWord_4591875 prefixEnd_4591875 2357838980364327001644857 := by
  unfold tailWord_4591875
  simp only [CollatzResearch.WordTrace]
  refine ⟨167479440239428579659385079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111652960159619053106256719 167479440239428579659385079)
  ·
    refine ⟨251219160359142869489077619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167479440239428579659385079 251219160359142869489077619)
    ·
      refine ⟨376828740538714304233616429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251219160359142869489077619 376828740538714304233616429)
      ·
        refine ⟨141310777702017864087606161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 376828740538714304233616429 141310777702017864087606161)
        ·
          refine ⟨105983083276513398065704621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141310777702017864087606161 105983083276513398065704621)
          ·
            refine ⟨39743656228692524274639233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105983083276513398065704621 39743656228692524274639233)
            ·
              refine ⟨29807742171519393205979425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39743656228692524274639233 29807742171519393205979425)
              ·
                refine ⟨22355806628639544904484569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29807742171519393205979425 22355806628639544904484569)
                ·
                  refine ⟨16766854971479658678363427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22355806628639544904484569 16766854971479658678363427)
                  ·
                    refine ⟨25150282457219488017545141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16766854971479658678363427 25150282457219488017545141)
                    ·
                      refine ⟨2357838980364327001644857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25150282457219488017545141 2357838980364327001644857)
                      ·
                        rfl

theorem cell23_4591875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 2, 1, 5].length) (baseStart_4591875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4591875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4591875 prefixEnd_4591875 := by exact prefixLift 4591875
  have htrace : WordTrace (prefixWord ++ tailWord_4591875) baseStart_4591875 baseEnd_4591875 := by
    simpa [prefixWord, tailWord_4591875, baseEnd_4591875] using wordTrace_append hprefix tailTrace_4591875
  have hstable : (prefixWord ++ tailWord_4591875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4591875).length < 2 ^ (prefixWord ++ tailWord_4591875).sum := by decide
  have hdescent : baseEnd_4591875 < baseStart_4591875 := by decide
  rcases family_descends (prefixWord ++ tailWord_4591875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4591889 : List Nat := [1, 2, 2, 1, 1, 5, 1, 2, 4, 2, 2]
def baseStart_4591889 : Nat := 118140960795 + 4591889 * 2 ^ 59
def prefixEnd_4591889 : Nat := 4983230072969 + 3 ^ 40 * 4591889 * 2
def baseEnd_4591889 : Nat := 2357846169093489946869793

theorem tailTrace_4591889 : CollatzResearch.WordTrace tailWord_4591889 prefixEnd_4591889 2357846169093489946869793 := by
  unfold tailWord_4591889
  simp only [CollatzResearch.WordTrace]
  refine ⟨167479950861377860050394721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111653300574251906700263147 167479950861377860050394721)
  ·
    refine ⟨125609963146033395037796041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167479950861377860050394721 125609963146033395037796041)
    ·
      refine ⟨94207472359525046278347031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125609963146033395037796041 94207472359525046278347031)
      ·
        refine ⟨141311208539287569417520547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94207472359525046278347031 141311208539287569417520547)
        ·
          refine ⟨211966812808931354126280821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141311208539287569417520547 211966812808931354126280821)
          ·
            refine ⟨19871888700837314449338827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 211966812808931354126280821 19871888700837314449338827)
            ·
              refine ⟨29807833051255971674008241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19871888700837314449338827 29807833051255971674008241)
              ·
                refine ⟨22355874788441978755506181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29807833051255971674008241 22355874788441978755506181)
                ·
                  refine ⟨4191726522832871016657409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22355874788441978755506181 4191726522832871016657409)
                  ·
                    refine ⟨3143794892124653262493057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4191726522832871016657409 3143794892124653262493057)
                    ·
                      refine ⟨2357846169093489946869793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3143794892124653262493057 2357846169093489946869793)
                      ·
                        rfl

theorem cell23_4591889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 4, 2, 2].length) (baseStart_4591889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4591889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4591889 prefixEnd_4591889 := by exact prefixLift 4591889
  have htrace : WordTrace (prefixWord ++ tailWord_4591889) baseStart_4591889 baseEnd_4591889 := by
    simpa [prefixWord, tailWord_4591889, baseEnd_4591889] using wordTrace_append hprefix tailTrace_4591889
  have hstable : (prefixWord ++ tailWord_4591889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4591889).length < 2 ^ (prefixWord ++ tailWord_4591889).sum := by decide
  have hdescent : baseEnd_4591889 < baseStart_4591889 := by decide
  rcases family_descends (prefixWord ++ tailWord_4591889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4591906 : List Nat := [3, 3, 1, 1, 3, 1, 2, 1, 4, 2, 2]
def baseStart_4591906 : Nat := 118140960795 + 4591906 * 2 ^ 59
def prefixEnd_4591906 : Nat := 4983230072969 + 3 ^ 40 * 4591906 * 2
def baseEnd_4591906 : Nat := 2357854898264616380357215

theorem tailTrace_4591906 : CollatzResearch.WordTrace tailWord_4591906 prefixEnd_4591906 2357854898264616380357215 := by
  unfold tailWord_4591906
  simp only [CollatzResearch.WordTrace]
  refine ⟨41870142725579067988440893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111653713934877514635842381 41870142725579067988440893)
  ·
    refine ⟨15701303522092150495665335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41870142725579067988440893 15701303522092150495665335)
    ·
      refine ⟨23551955283138225743498003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15701303522092150495665335 23551955283138225743498003)
      ·
        refine ⟨35327932924707338615247005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23551955283138225743498003 35327932924707338615247005)
        ·
          refine ⟨13247974846765251980717627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35327932924707338615247005 13247974846765251980717627)
          ·
            refine ⟨19871962270147877971076441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13247974846765251980717627 19871962270147877971076441)
            ·
              refine ⟨14903971702610908478307331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19871962270147877971076441 14903971702610908478307331)
              ·
                refine ⟨22355957553916362717460997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14903971702610908478307331 22355957553916362717460997)
                ·
                  refine ⟨4191742041359318009523937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22355957553916362717460997 4191742041359318009523937)
                  ·
                    refine ⟨3143806531019488507142953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4191742041359318009523937 3143806531019488507142953)
                    ·
                      refine ⟨2357854898264616380357215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3143806531019488507142953 2357854898264616380357215)
                      ·
                        rfl

theorem cell23_4591906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 4, 2, 2].length) (baseStart_4591906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4591906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4591906 prefixEnd_4591906 := by exact prefixLift 4591906
  have htrace : WordTrace (prefixWord ++ tailWord_4591906) baseStart_4591906 baseEnd_4591906 := by
    simpa [prefixWord, tailWord_4591906, baseEnd_4591906] using wordTrace_append hprefix tailTrace_4591906
  have hstable : (prefixWord ++ tailWord_4591906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4591906).length < 2 ^ (prefixWord ++ tailWord_4591906).sum := by decide
  have hdescent : baseEnd_4591906 < baseStart_4591906 := by decide
  rcases family_descends (prefixWord ++ tailWord_4591906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4591917 : List Nat := [1, 5, 3, 1, 3, 1, 2, 1, 2, 1, 3]
def baseStart_4591917 : Nat := 118140960795 + 4591917 * 2 ^ 59
def prefixEnd_4591917 : Nat := 4983230072969 + 3 ^ 40 * 4591917 * 2
def baseEnd_4591917 : Nat := 2357860546551815837319665

theorem tailTrace_4591917 : CollatzResearch.WordTrace tailWord_4591917 prefixEnd_4591917 2357860546551815837319665 := by
  unfold tailWord_4591917
  simp only [CollatzResearch.WordTrace]
  refine ⟨167480972105276420832414005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111653981403517613888276003 167480972105276420832414005)
  ·
    refine ⟨15701341134869664453038813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 167480972105276420832414005 15701341134869664453038813)
    ·
      refine ⟨5888002925576124169889555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15701341134869664453038813 5888002925576124169889555)
      ·
        refine ⟨8832004388364186254834333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5888002925576124169889555 8832004388364186254834333)
        ·
          refine ⟨3312001645636569845562875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8832004388364186254834333 3312001645636569845562875)
          ·
            refine ⟨4968002468454854768344313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3312001645636569845562875 4968002468454854768344313)
            ·
              refine ⟨3726001851341141076258235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4968002468454854768344313 3726001851341141076258235)
              ·
                refine ⟨5589002777011711614387353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3726001851341141076258235 5589002777011711614387353)
                ·
                  refine ⟨4191752082758783710790515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5589002777011711614387353 4191752082758783710790515)
                  ·
                    refine ⟨6287628124138175566185773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4191752082758783710790515 6287628124138175566185773)
                    ·
                      refine ⟨2357860546551815837319665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6287628124138175566185773 2357860546551815837319665)
                      ·
                        rfl

theorem cell23_4591917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_4591917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4591917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4591917 prefixEnd_4591917 := by exact prefixLift 4591917
  have htrace : WordTrace (prefixWord ++ tailWord_4591917) baseStart_4591917 baseEnd_4591917 := by
    simpa [prefixWord, tailWord_4591917, baseEnd_4591917] using wordTrace_append hprefix tailTrace_4591917
  have hstable : (prefixWord ++ tailWord_4591917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4591917).length < 2 ^ (prefixWord ++ tailWord_4591917).sum := by decide
  have hdescent : baseEnd_4591917 < baseStart_4591917 := by decide
  rcases family_descends (prefixWord ++ tailWord_4591917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4591935 : List Nat := [1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 7]
def baseStart_4591935 : Nat := 118140960795 + 4591935 * 2 ^ 59
def prefixEnd_4591935 : Nat := 4983230072969 + 3 ^ 40 * 4591935 * 2
def baseEnd_4591935 : Nat := 2357869789203596766894581

theorem tailTrace_4591935 : CollatzResearch.WordTrace tailWord_4591935 prefixEnd_4591935 2357869789203596766894581 := by
  unfold tailWord_4591935
  simp only [CollatzResearch.WordTrace]
  refine ⟨167481628619211209906569259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111654419079474139937712839 167481628619211209906569259)
  ·
    refine ⟨251222442928816814859853889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167481628619211209906569259 251222442928816814859853889)
    ·
      refine ⟨188416832196612611144890417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 251222442928816814859853889 188416832196612611144890417)
      ·
        refine ⟨141312624147459458358667813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188416832196612611144890417 141312624147459458358667813)
        ·
          refine ⟨26496117027648648442250215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 141312624147459458358667813 26496117027648648442250215)
          ·
            refine ⟨39744175541472972663375323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26496117027648648442250215 39744175541472972663375323)
            ·
              refine ⟨59616263312209458995062985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39744175541472972663375323 59616263312209458995062985)
              ·
                refine ⟨44712197484157094246297239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59616263312209458995062985 44712197484157094246297239)
                ·
                  refine ⟨67068296226235641369445859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44712197484157094246297239 67068296226235641369445859)
                  ·
                    refine ⟨100602444339353462054168789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 67068296226235641369445859 100602444339353462054168789)
                    ·
                      refine ⟨2357869789203596766894581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 100602444339353462054168789 2357869789203596766894581)
                      ·
                        rfl

theorem cell23_4591935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 7].length) (baseStart_4591935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4591935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4591935 prefixEnd_4591935 := by exact prefixLift 4591935
  have htrace : WordTrace (prefixWord ++ tailWord_4591935) baseStart_4591935 baseEnd_4591935 := by
    simpa [prefixWord, tailWord_4591935, baseEnd_4591935] using wordTrace_append hprefix tailTrace_4591935
  have hstable : (prefixWord ++ tailWord_4591935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4591935).length < 2 ^ (prefixWord ++ tailWord_4591935).sum := by decide
  have hdescent : baseEnd_4591935 < baseStart_4591935 := by decide
  rcases family_descends (prefixWord ++ tailWord_4591935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4591985 : List Nat := [1, 2, 2, 2, 1, 2, 1, 2, 10]
def baseStart_4591985 : Nat := 118140960795 + 4591985 * 2 ^ 59
def prefixEnd_4591985 : Nat := 4983230072969 + 3 ^ 40 * 4591985 * 2
def baseEnd_4591985 : Nat := 261988384804035730141039

theorem tailTrace_4591985 : CollatzResearch.WordTrace tailWord_4591985 prefixEnd_4591985 261988384804035730141039 := by
  unfold tailWord_4591985
  simp only [CollatzResearch.WordTrace]
  refine ⟨167483452269030068445889409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111655634846020045630592939 167483452269030068445889409)
  ·
    refine ⟨125612589201772551334417057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167483452269030068445889409 125612589201772551334417057)
    ·
      refine ⟨94209441901329413500812793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125612589201772551334417057 94209441901329413500812793)
      ·
        refine ⟨70657081425997060125609595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94209441901329413500812793 70657081425997060125609595)
        ·
          refine ⟨105985622138995590188414393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70657081425997060125609595 105985622138995590188414393)
          ·
            refine ⟨79489216604246692641310795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105985622138995590188414393 79489216604246692641310795)
            ·
              refine ⟨119233824906370038961966193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79489216604246692641310795 119233824906370038961966193)
              ·
                refine ⟨89425368679777529221474645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 119233824906370038961966193 89425368679777529221474645)
                ·
                  refine ⟨261988384804035730141039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 89425368679777529221474645 261988384804035730141039)
                  ·
                    rfl

theorem cell23_4591985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 10].length) (baseStart_4591985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4591985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4591985 prefixEnd_4591985 := by exact prefixLift 4591985
  have htrace : WordTrace (prefixWord ++ tailWord_4591985) baseStart_4591985 baseEnd_4591985 := by
    simpa [prefixWord, tailWord_4591985, baseEnd_4591985] using wordTrace_append hprefix tailTrace_4591985
  have hstable : (prefixWord ++ tailWord_4591985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4591985).length < 2 ^ (prefixWord ++ tailWord_4591985).sum := by decide
  have hdescent : baseEnd_4591985 < baseStart_4591985 := by decide
  rcases family_descends (prefixWord ++ tailWord_4591985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4591989 : List Nat := [1, 3, 4, 1, 2, 1, 1, 1, 5, 4]
def baseStart_4591989 : Nat := 118140960795 + 4591989 * 2 ^ 59
def prefixEnd_4591989 : Nat := 4983230072969 + 3 ^ 40 * 4591989 * 2
def baseEnd_4591989 : Nat := 785965839052979851873111

theorem tailTrace_4591989 : CollatzResearch.WordTrace tailWord_4591989 prefixEnd_4591989 785965839052979851873111 := by
  unfold tailWord_4591989
  simp only [CollatzResearch.WordTrace]
  refine ⟨167483598161015577129035021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111655732107343718086023347 167483598161015577129035021)
  ·
    refine ⟨62806349310380841423388133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167483598161015577129035021 62806349310380841423388133)
    ·
      refine ⟨11776190495696407766885275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62806349310380841423388133 11776190495696407766885275)
      ·
        refine ⟨17664285743544611650327913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11776190495696407766885275 17664285743544611650327913)
        ·
          refine ⟨13248214307658458737745935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17664285743544611650327913 13248214307658458737745935)
          ·
            refine ⟨19872321461487688106618903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13248214307658458737745935 19872321461487688106618903)
            ·
              refine ⟨29808482192231532159928355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19872321461487688106618903 29808482192231532159928355)
              ·
                refine ⟨44712723288347298239892533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29808482192231532159928355 44712723288347298239892533)
                ·
                  refine ⟨4191817808282559209989925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44712723288347298239892533 4191817808282559209989925)
                  ·
                    refine ⟨785965839052979851873111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4191817808282559209989925 785965839052979851873111)
                    ·
                      rfl

theorem cell23_4591989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_4591989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4591989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4591989 prefixEnd_4591989 := by exact prefixLift 4591989
  have htrace : WordTrace (prefixWord ++ tailWord_4591989) baseStart_4591989 baseEnd_4591989 := by
    simpa [prefixWord, tailWord_4591989, baseEnd_4591989] using wordTrace_append hprefix tailTrace_4591989
  have hstable : (prefixWord ++ tailWord_4591989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4591989).length < 2 ^ (prefixWord ++ tailWord_4591989).sum := by decide
  have hdescent : baseEnd_4591989 < baseStart_4591989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4591989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4592049 : List Nat := [1, 2, 2, 4, 1, 2, 1, 4, 1, 5]
def baseStart_4592049 : Nat := 118140960795 + 4592049 * 2 ^ 59
def prefixEnd_4592049 : Nat := 4983230072969 + 3 ^ 40 * 4592049 * 2
def baseEnd_4592049 : Nat := 785976108666069773623019

theorem tailTrace_4592049 : CollatzResearch.WordTrace tailWord_4592049 prefixEnd_4592049 785976108666069773623019 := by
  unfold tailWord_4592049
  simp only [CollatzResearch.WordTrace]
  refine ⟨167485786540798207376219201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111657191027198804917479467 167485786540798207376219201)
  ·
    refine ⟨125614339905598655532164401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167485786540798207376219201 125614339905598655532164401)
    ·
      refine ⟨94210754929198991649123301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125614339905598655532164401 94210754929198991649123301)
      ·
        refine ⟨17664516549224810934210619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94210754929198991649123301 17664516549224810934210619)
        ·
          refine ⟨26496774823837216401315929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17664516549224810934210619 26496774823837216401315929)
          ·
            refine ⟨19872581117877912300986947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26496774823837216401315929 19872581117877912300986947)
            ·
              refine ⟨29808871676816868451480421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19872581117877912300986947 29808871676816868451480421)
              ·
                refine ⟨5589163439403162834652579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29808871676816868451480421 5589163439403162834652579)
                ·
                  refine ⟨8383745159104744251978869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5589163439403162834652579 8383745159104744251978869)
                  ·
                    refine ⟨785976108666069773623019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8383745159104744251978869 785976108666069773623019)
                    ·
                      rfl

theorem cell23_4592049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 4, 1, 5].length) (baseStart_4592049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4592049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4592049 prefixEnd_4592049 := by exact prefixLift 4592049
  have htrace : WordTrace (prefixWord ++ tailWord_4592049) baseStart_4592049 baseEnd_4592049 := by
    simpa [prefixWord, tailWord_4592049, baseEnd_4592049] using wordTrace_append hprefix tailTrace_4592049
  have hstable : (prefixWord ++ tailWord_4592049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4592049).length < 2 ^ (prefixWord ++ tailWord_4592049).sum := by decide
  have hdescent : baseEnd_4592049 < baseStart_4592049 := by decide
  rcases family_descends (prefixWord ++ tailWord_4592049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4592079 : List Nat := [1, 1, 2, 1, 1, 4, 1, 6, 2, 4]
def baseStart_4592079 : Nat := 118140960795 + 4592079 * 2 ^ 59
def prefixEnd_4592079 : Nat := 4983230072969 + 3 ^ 40 * 4592079 * 2
def baseEnd_4592079 : Nat := 785981243472614734497973

theorem tailTrace_4592079 : CollatzResearch.WordTrace tailWord_4592079 prefixEnd_4592079 785981243472614734497973 := by
  unfold tailWord_4592079
  simp only [CollatzResearch.WordTrace]
  refine ⟨167486880730689522499811291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111657920487126348333207527 167486880730689522499811291)
  ·
    refine ⟨251230321096034283749716937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167486880730689522499811291 251230321096034283749716937)
    ·
      refine ⟨188422740822025712812287703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 251230321096034283749716937 188422740822025712812287703)
      ·
        refine ⟨282634111233038569218431555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188422740822025712812287703 282634111233038569218431555)
        ·
          refine ⟨423951166849557853827647333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 282634111233038569218431555 423951166849557853827647333)
          ·
            refine ⟨79490843784292097592683875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 423951166849557853827647333 79490843784292097592683875)
            ·
              refine ⟨119236265676438146389025813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79490843784292097592683875 119236265676438146389025813)
              ·
                refine ⟨5589199953583038111985585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 119236265676438146389025813 5589199953583038111985585)
                ·
                  refine ⟨4191899965187278583989189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5589199953583038111985585 4191899965187278583989189)
                  ·
                    refine ⟨785981243472614734497973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4191899965187278583989189 785981243472614734497973)
                    ·
                      rfl

theorem cell23_4592079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 6, 2, 4].length) (baseStart_4592079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4592079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4592079 prefixEnd_4592079 := by exact prefixLift 4592079
  have htrace : WordTrace (prefixWord ++ tailWord_4592079) baseStart_4592079 baseEnd_4592079 := by
    simpa [prefixWord, tailWord_4592079, baseEnd_4592079] using wordTrace_append hprefix tailTrace_4592079
  have hstable : (prefixWord ++ tailWord_4592079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4592079).length < 2 ^ (prefixWord ++ tailWord_4592079).sum := by decide
  have hdescent : baseEnd_4592079 < baseStart_4592079 := by decide
  rcases family_descends (prefixWord ++ tailWord_4592079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4592086 : List Nat := [5, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4]
def baseStart_4592086 : Nat := 118140960795 + 4592086 * 2 ^ 59
def prefixEnd_4592086 : Nat := 4983230072969 + 3 ^ 40 * 4592086 * 2
def baseEnd_4592086 : Nat := 2357947324782425676106387

theorem tailTrace_4592086 : CollatzResearch.WordTrace tailWord_4592086 prefixEnd_4592086 2357947324782425676106387 := by
  unfold tailWord_4592086
  simp only [CollatzResearch.WordTrace]
  refine ⟨10467946002604010168457257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 111658090694442775130210741 10467946002604010168457257)
  ·
    refine ⟨7850959501953007626342943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10467946002604010168457257 7850959501953007626342943)
    ·
      refine ⟨11776439252929511439514415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7850959501953007626342943 11776439252929511439514415)
      ·
        refine ⟨17664658879394267159271623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11776439252929511439514415 17664658879394267159271623)
        ·
          refine ⟨26496988319091400738907435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17664658879394267159271623 26496988319091400738907435)
          ·
            refine ⟨39745482478637101108361153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26496988319091400738907435 39745482478637101108361153)
            ·
              refine ⟨29809111858977825831270865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39745482478637101108361153 29809111858977825831270865)
              ·
                refine ⟨22356833894233369373453149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29809111858977825831270865 22356833894233369373453149)
                ·
                  refine ⟨8383812710337513515044931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22356833894233369373453149 8383812710337513515044931)
                  ·
                    refine ⟨12575719065506270272567397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8383812710337513515044931 12575719065506270272567397)
                    ·
                      refine ⟨2357947324782425676106387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12575719065506270272567397 2357947324782425676106387)
                      ·
                        rfl

theorem cell23_4592086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_4592086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4592086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4592086 prefixEnd_4592086 := by exact prefixLift 4592086
  have htrace : WordTrace (prefixWord ++ tailWord_4592086) baseStart_4592086 baseEnd_4592086 := by
    simpa [prefixWord, tailWord_4592086, baseEnd_4592086] using wordTrace_append hprefix tailTrace_4592086
  have hstable : (prefixWord ++ tailWord_4592086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4592086).length < 2 ^ (prefixWord ++ tailWord_4592086).sum := by decide
  have hdescent : baseEnd_4592086 < baseStart_4592086 := by decide
  rcases family_descends (prefixWord ++ tailWord_4592086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4592089 : List Nat := [1, 2, 1, 2, 4, 1, 2, 2, 3, 2, 3]
def baseStart_4592089 : Nat := 118140960795 + 4592089 * 2 ^ 59
def prefixEnd_4592089 : Nat := 4983230072969 + 3 ^ 40 * 4592089 * 2
def baseEnd_4592089 : Nat := 2357948865224389164368873

theorem tailTrace_4592089 : CollatzResearch.WordTrace tailWord_4592089 prefixEnd_4592089 2357948865224389164368873 := by
  unfold tailWord_4592089
  simp only [CollatzResearch.WordTrace]
  refine ⟨167487245460653294207675321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111658163640435529471783547 167487245460653294207675321)
  ·
    refine ⟨125615434095489970655756491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167487245460653294207675321 125615434095489970655756491)
    ·
      refine ⟨188423151143234955983634737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125615434095489970655756491 188423151143234955983634737)
      ·
        refine ⟨141317363357426216987726053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188423151143234955983634737 141317363357426216987726053)
        ·
          refine ⟨26497005629517415685198635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 141317363357426216987726053 26497005629517415685198635)
          ·
            refine ⟨39745508444276123527797953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26497005629517415685198635 39745508444276123527797953)
            ·
              refine ⟨29809131333207092645848465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39745508444276123527797953 29809131333207092645848465)
              ·
                refine ⟨22356848499905319484386349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29809131333207092645848465 22356848499905319484386349)
                ·
                  refine ⟨8383818187464494806644881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22356848499905319484386349 8383818187464494806644881)
                  ·
                    refine ⟨6287863640598371104983661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8383818187464494806644881 6287863640598371104983661)
                    ·
                      refine ⟨2357948865224389164368873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6287863640598371104983661 2357948865224389164368873)
                      ·
                        rfl

theorem cell23_4592089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 3, 2, 3].length) (baseStart_4592089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4592089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4592089 prefixEnd_4592089 := by exact prefixLift 4592089
  have htrace : WordTrace (prefixWord ++ tailWord_4592089) baseStart_4592089 baseEnd_4592089 := by
    simpa [prefixWord, tailWord_4592089, baseEnd_4592089] using wordTrace_append hprefix tailTrace_4592089
  have hstable : (prefixWord ++ tailWord_4592089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4592089).length < 2 ^ (prefixWord ++ tailWord_4592089).sum := by decide
  have hdescent : baseEnd_4592089 < baseStart_4592089 := by decide
  rcases family_descends (prefixWord ++ tailWord_4592089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4592106 : List Nat := [3, 1, 3, 1, 3, 2, 1, 1, 3, 2, 3]
def baseStart_4592106 : Nat := 118140960795 + 4592106 * 2 ^ 59
def prefixEnd_4592106 : Nat := 4983230072969 + 3 ^ 40 * 4592106 * 2
def baseEnd_4592106 : Nat := 2357957594395515597856295

theorem tailTrace_4592106 : CollatzResearch.WordTrace tailWord_4592106 prefixEnd_4592106 2357957594395515597856295 := by
  unfold tailWord_4592106
  simp only [CollatzResearch.WordTrace]
  refine ⟨41871966375397926527761043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111658577001061137407362781 41871966375397926527761043)
  ·
    refine ⟨62807949563096889791641565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41871966375397926527761043 62807949563096889791641565)
    ·
      refine ⟨23552981086161333671865587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62807949563096889791641565 23552981086161333671865587)
      ·
        refine ⟨35329471629242000507798381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23552981086161333671865587 35329471629242000507798381)
        ·
          refine ⟨13248551860965750190424393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35329471629242000507798381 13248551860965750190424393)
          ·
            refine ⟨9936413895724312642818295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13248551860965750190424393 9936413895724312642818295)
            ·
              refine ⟨14904620843586468964227443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9936413895724312642818295 14904620843586468964227443)
              ·
                refine ⟨22356931265379703446341165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14904620843586468964227443 22356931265379703446341165)
                ·
                  refine ⟨8383849224517388792377937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22356931265379703446341165 8383849224517388792377937)
                  ·
                    refine ⟨6287886918388041594283453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8383849224517388792377937 6287886918388041594283453)
                    ·
                      refine ⟨2357957594395515597856295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6287886918388041594283453 2357957594395515597856295)
                      ·
                        rfl

theorem cell23_4592106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 3, 2, 3].length) (baseStart_4592106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4592106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4592106 prefixEnd_4592106 := by exact prefixLift 4592106
  have htrace : WordTrace (prefixWord ++ tailWord_4592106) baseStart_4592106 baseEnd_4592106 := by
    simpa [prefixWord, tailWord_4592106, baseEnd_4592106] using wordTrace_append hprefix tailTrace_4592106
  have hstable : (prefixWord ++ tailWord_4592106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4592106).length < 2 ^ (prefixWord ++ tailWord_4592106).sum := by decide
  have hdescent : baseEnd_4592106 < baseStart_4592106 := by decide
  rcases family_descends (prefixWord ++ tailWord_4592106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4592109 : List Nat := [1, 5, 1, 3, 1, 1, 2, 9]
def baseStart_4592109 : Nat := 118140960795 + 4592109 * 2 ^ 59
def prefixEnd_4592109 : Nat := 4983230072969 + 3 ^ 40 * 4592109 * 2
def baseEnd_4592109 : Nat := 87331819808795521708103

theorem tailTrace_4592109 : CollatzResearch.WordTrace tailWord_4592109 prefixEnd_4592109 87331819808795521708103 := by
  unfold tailWord_4592109
  simp only [CollatzResearch.WordTrace]
  refine ⟨167487974920580837623403381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111658649947053891748935587 167487974920580837623403381)
  ·
    refine ⟨15701997648804453527194067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 167487974920580837623403381 15701997648804453527194067)
    ·
      refine ⟨23552996473206680290791101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15701997648804453527194067 23552996473206680290791101)
      ·
        refine ⟨8832373677452505109046663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23552996473206680290791101 8832373677452505109046663)
        ·
          refine ⟨13248560516178757663569995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8832373677452505109046663 13248560516178757663569995)
          ·
            refine ⟨19872840774268136495354993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13248560516178757663569995 19872840774268136495354993)
            ·
              refine ⟨14904630580701102371516245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19872840774268136495354993 14904630580701102371516245)
              ·
                refine ⟨87331819808795521708103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14904630580701102371516245 87331819808795521708103)
                ·
                  rfl

theorem cell23_4592109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 9].length) (baseStart_4592109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4592109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4592109 prefixEnd_4592109 := by exact prefixLift 4592109
  have htrace : WordTrace (prefixWord ++ tailWord_4592109) baseStart_4592109 baseEnd_4592109 := by
    simpa [prefixWord, tailWord_4592109, baseEnd_4592109] using wordTrace_append hprefix tailTrace_4592109
  have hstable : (prefixWord ++ tailWord_4592109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4592109).length < 2 ^ (prefixWord ++ tailWord_4592109).sum := by decide
  have hdescent : baseEnd_4592109 < baseStart_4592109 := by decide
  rcases family_descends (prefixWord ++ tailWord_4592109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4592130 : List Nat := [3, 4, 1, 2, 2, 1, 2, 2, 2, 4]
def baseStart_4592130 : Nat := 118140960795 + 4592130 * 2 ^ 59
def prefixEnd_4592130 : Nat := 4983230072969 + 3 ^ 40 * 4592130 * 2
def baseEnd_4592130 : Nat := 785989972643741167985395

theorem tailTrace_4592130 : CollatzResearch.WordTrace tailWord_4592130 prefixEnd_4592130 785989972643741167985395 := by
  unfold tailWord_4592130
  simp only [CollatzResearch.WordTrace]
  refine ⟨41872185213376189552479461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111659160569003172139945229 41872185213376189552479461)
  ·
    refine ⟨7851034727508035541089899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41872185213376189552479461 7851034727508035541089899)
    ·
      refine ⟨11776552091262053311634849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7851034727508035541089899 11776552091262053311634849)
      ·
        refine ⟨8832414068446539983726137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11776552091262053311634849 8832414068446539983726137)
        ·
          refine ⟨6624310551334904987794603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8832414068446539983726137 6624310551334904987794603)
          ·
            refine ⟨9936465827002357481691905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6624310551334904987794603 9936465827002357481691905)
            ·
              refine ⟨7452349370251768111268929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9936465827002357481691905 7452349370251768111268929)
              ·
                refine ⟨5589262027688826083451697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7452349370251768111268929 5589262027688826083451697)
                ·
                  refine ⟨4191946520766619562588773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5589262027688826083451697 4191946520766619562588773)
                  ·
                    refine ⟨785989972643741167985395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4191946520766619562588773 785989972643741167985395)
                    ·
                      rfl

theorem cell23_4592130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_4592130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4592130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4592130 prefixEnd_4592130 := by exact prefixLift 4592130
  have htrace : WordTrace (prefixWord ++ tailWord_4592130) baseStart_4592130 baseEnd_4592130 := by
    simpa [prefixWord, tailWord_4592130, baseEnd_4592130] using wordTrace_append hprefix tailTrace_4592130
  have hstable : (prefixWord ++ tailWord_4592130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4592130).length < 2 ^ (prefixWord ++ tailWord_4592130).sum := by decide
  have hdescent : baseEnd_4592130 < baseStart_4592130 := by decide
  rcases family_descends (prefixWord ++ tailWord_4592130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4592176 : List Nat := [2, 1, 1, 1, 2, 3, 4, 2, 1, 4, 2]
def baseStart_4592176 : Nat := 118140960795 + 4592176 * 2 ^ 59
def prefixEnd_4592176 : Nat := 4983230072969 + 3 ^ 40 * 4592176 * 2
def baseEnd_4592176 : Nat := 2357993538041330323980973

theorem tailTrace_4592176 : CollatzResearch.WordTrace tailWord_4592176 prefixEnd_4592176 2357993538041330323980973 := by
  unfold tailWord_4592176
  simp only [CollatzResearch.WordTrace]
  refine ⟨83745209305669054033046191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111660279074225405377394921 83745209305669054033046191)
  ·
    refine ⟨125617813958503581049569287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83745209305669054033046191 125617813958503581049569287)
    ·
      refine ⟨188426720937755371574353931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125617813958503581049569287 188426720937755371574353931)
      ·
        refine ⟨282640081406633057361530897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188426720937755371574353931 282640081406633057361530897)
        ·
          refine ⟨211980061054974793021148173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 282640081406633057361530897 211980061054974793021148173)
          ·
            refine ⟨79492522895615547382930565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 211980061054974793021148173 79492522895615547382930565)
            ·
              refine ⟨14904848042927915134299481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79492522895615547382930565 14904848042927915134299481)
              ·
                refine ⟨11178636032195936350724611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14904848042927915134299481 11178636032195936350724611)
                ·
                  refine ⟨16767954048293904526086917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11178636032195936350724611 16767954048293904526086917)
                  ·
                    refine ⟨3143991384055107098641297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16767954048293904526086917 3143991384055107098641297)
                    ·
                      refine ⟨2357993538041330323980973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3143991384055107098641297 2357993538041330323980973)
                      ·
                        rfl

theorem cell23_4592176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 2, 1, 4, 2].length) (baseStart_4592176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4592176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4592176 prefixEnd_4592176 := by exact prefixLift 4592176
  have htrace : WordTrace (prefixWord ++ tailWord_4592176) baseStart_4592176 baseEnd_4592176 := by
    simpa [prefixWord, tailWord_4592176, baseEnd_4592176] using wordTrace_append hprefix tailTrace_4592176
  have hstable : (prefixWord ++ tailWord_4592176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4592176).length < 2 ^ (prefixWord ++ tailWord_4592176).sum := by decide
  have hdescent : baseEnd_4592176 < baseStart_4592176 := by decide
  rcases family_descends (prefixWord ++ tailWord_4592176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4592199 : List Nat := [1, 1, 4, 1, 4, 1, 1, 3, 7]
def baseStart_4592199 : Nat := 118140960795 + 4592199 * 2 ^ 59
def prefixEnd_4592199 : Nat := 4983230072969 + 3 ^ 40 * 4592199 * 2
def baseEnd_4592199 : Nat := 262000594232931525999263

theorem tailTrace_4592199 : CollatzResearch.WordTrace tailWord_4592199 prefixEnd_4592199 262000594232931525999263 := by
  unfold tailWord_4592199
  simp only [CollatzResearch.WordTrace]
  refine ⟨167491257490254782994179651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111660838326836521996119767 167491257490254782994179651)
  ·
    refine ⟨251236886235382174491269477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167491257490254782994179651 251236886235382174491269477)
    ·
      refine ⟨47106916169134157717113027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 251236886235382174491269477 47106916169134157717113027)
      ·
        refine ⟨70660374253701236575669541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47106916169134157717113027 70660374253701236575669541)
        ·
          refine ⟨13248820172568981857938039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70660374253701236575669541 13248820172568981857938039)
          ·
            refine ⟨19873230258853472786907059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13248820172568981857938039 19873230258853472786907059)
            ·
              refine ⟨29809845388280209180360589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19873230258853472786907059 29809845388280209180360589)
              ·
                refine ⟨11178692020605078442635221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29809845388280209180360589 11178692020605078442635221)
                ·
                  refine ⟨262000594232931525999263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11178692020605078442635221 262000594232931525999263)
                  ·
                    rfl

theorem cell23_4592199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 3, 7].length) (baseStart_4592199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4592199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4592199 prefixEnd_4592199 := by exact prefixLift 4592199
  have htrace : WordTrace (prefixWord ++ tailWord_4592199) baseStart_4592199 baseEnd_4592199 := by
    simpa [prefixWord, tailWord_4592199, baseEnd_4592199] using wordTrace_append hprefix tailTrace_4592199
  have hstable : (prefixWord ++ tailWord_4592199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4592199).length < 2 ^ (prefixWord ++ tailWord_4592199).sum := by decide
  have hdescent : baseEnd_4592199 < baseStart_4592199 := by decide
  rcases family_descends (prefixWord ++ tailWord_4592199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4592293 : List Nat := [1, 3, 1, 2, 1, 2, 1, 7, 1, 4]
def baseStart_4592293 : Nat := 118140960795 + 4592293 * 2 ^ 59
def prefixEnd_4592293 : Nat := 4983230072969 + 3 ^ 40 * 4592293 * 2
def baseEnd_4592293 : Nat := 786017871759302122072645

theorem tailTrace_4592293 : CollatzResearch.WordTrace tailWord_4592293 prefixEnd_4592293 786017871759302122072645 := by
  unfold tailWord_4592293
  simp only [CollatzResearch.WordTrace]
  refine ⟨167494685951914237048101533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111663123967942824698734355 167494685951914237048101533)
  ·
    refine ⟨62810507231967838893038075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167494685951914237048101533 62810507231967838893038075)
    ·
      refine ⟨94215760847951758339557113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62810507231967838893038075 94215760847951758339557113)
      ·
        refine ⟨70661820635963818754667835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94215760847951758339557113 70661820635963818754667835)
        ·
          refine ⟨105992730953945728132001753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70661820635963818754667835 105992730953945728132001753)
          ·
            refine ⟨79494548215459296099001315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105992730953945728132001753 79494548215459296099001315)
            ·
              refine ⟨119241822323188944148501973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79494548215459296099001315 119241822323188944148501973)
              ·
                refine ⟨2794730210699740878480515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 119241822323188944148501973 2794730210699740878480515)
                ·
                  refine ⟨4192095316049611317720773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2794730210699740878480515 4192095316049611317720773)
                  ·
                    refine ⟨786017871759302122072645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4192095316049611317720773 786017871759302122072645)
                    ·
                      rfl

theorem cell23_4592293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 7, 1, 4].length) (baseStart_4592293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4592293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4592293 prefixEnd_4592293 := by exact prefixLift 4592293
  have htrace : WordTrace (prefixWord ++ tailWord_4592293) baseStart_4592293 baseEnd_4592293 := by
    simpa [prefixWord, tailWord_4592293, baseEnd_4592293] using wordTrace_append hprefix tailTrace_4592293
  have hstable : (prefixWord ++ tailWord_4592293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4592293).length < 2 ^ (prefixWord ++ tailWord_4592293).sum := by decide
  have hdescent : baseEnd_4592293 < baseStart_4592293 := by decide
  rcases family_descends (prefixWord ++ tailWord_4592293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4592343 : List Nat := [1, 1, 3, 2, 1, 5, 1, 1, 1, 5, 2]
def baseStart_4592343 : Nat := 118140960795 + 4592343 * 2 ^ 59
def prefixEnd_4592343 : Nat := 4983230072969 + 3 ^ 40 * 4592343 * 2
def baseEnd_4592343 : Nat := 2358079289310631170592705

theorem tailTrace_4592343 : CollatzResearch.WordTrace tailWord_4592343 prefixEnd_4592343 2358079289310631170592705 := by
  unfold tailWord_4592343
  simp only [CollatzResearch.WordTrace]
  refine ⟨167496509601733095587421683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111664339734488730391614455 167496509601733095587421683)
  ·
    refine ⟨251244764402599643381132525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167496509601733095587421683 251244764402599643381132525)
    ·
      refine ⟨94216786650974866267924697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 251244764402599643381132525 94216786650974866267924697)
      ·
        refine ⟨70662589988231149700943523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94216786650974866267924697 70662589988231149700943523)
        ·
          refine ⟨105993884982346724551415285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70662589988231149700943523 105993884982346724551415285)
          ·
            refine ⟨9936926717095005426695183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 105993884982346724551415285 9936926717095005426695183)
            ·
              refine ⟨14905390075642508140042775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9936926717095005426695183 14905390075642508140042775)
              ·
                refine ⟨22358085113463762210064163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14905390075642508140042775 22358085113463762210064163)
                ·
                  refine ⟨33537127670195643315096245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22358085113463762210064163 33537127670195643315096245)
                  ·
                    refine ⟨3144105719080841560790273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33537127670195643315096245 3144105719080841560790273)
                    ·
                      refine ⟨2358079289310631170592705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3144105719080841560790273 2358079289310631170592705)
                      ·
                        rfl

theorem cell23_4592343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 5, 2].length) (baseStart_4592343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4592343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4592343 prefixEnd_4592343 := by exact prefixLift 4592343
  have htrace : WordTrace (prefixWord ++ tailWord_4592343) baseStart_4592343 baseEnd_4592343 := by
    simpa [prefixWord, tailWord_4592343, baseEnd_4592343] using wordTrace_append hprefix tailTrace_4592343
  have hstable : (prefixWord ++ tailWord_4592343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4592343).length < 2 ^ (prefixWord ++ tailWord_4592343).sum := by decide
  have hdescent : baseEnd_4592343 < baseStart_4592343 := by decide
  rcases family_descends (prefixWord ++ tailWord_4592343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4592353 : List Nat := [1, 2, 3, 1, 4, 2, 1, 3, 1, 5]
def baseStart_4592353 : Nat := 118140960795 + 4592353 * 2 ^ 59
def prefixEnd_4592353 : Nat := 4983230072969 + 3 ^ 40 * 4592353 * 2
def baseEnd_4592353 : Nat := 786028141372392043822553

theorem tailTrace_4592353 : CollatzResearch.WordTrace tailWord_4592353 prefixEnd_4592353 786028141372392043822553 := by
  unfold tailWord_4592353
  simp only [CollatzResearch.WordTrace]
  refine ⟨167496874331696867295285713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111664582887797911530190475 167496874331696867295285713)
  ·
    refine ⟨125622655748772650471464285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167496874331696867295285713 125622655748772650471464285)
    ·
      refine ⟨47108495905789743926799107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125622655748772650471464285 47108495905789743926799107)
      ·
        refine ⟨70662743858684615890198661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47108495905789743926799107 70662743858684615890198661)
        ·
          refine ⟨13249264473503365479412249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70662743858684615890198661 13249264473503365479412249)
          ·
            refine ⟨9936948355127524109559187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13249264473503365479412249 9936948355127524109559187)
            ·
              refine ⟨14905422532691286164338781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9936948355127524109559187 14905422532691286164338781)
              ·
                refine ⟨5589533449759232311627043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14905422532691286164338781 5589533449759232311627043)
                ·
                  refine ⟨8384300174638848467440565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5589533449759232311627043 8384300174638848467440565)
                  ·
                    refine ⟨786028141372392043822553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8384300174638848467440565 786028141372392043822553)
                    ·
                      rfl

theorem cell23_4592353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 3, 1, 5].length) (baseStart_4592353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4592353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4592353 prefixEnd_4592353 := by exact prefixLift 4592353
  have htrace : WordTrace (prefixWord ++ tailWord_4592353) baseStart_4592353 baseEnd_4592353 := by
    simpa [prefixWord, tailWord_4592353, baseEnd_4592353] using wordTrace_append hprefix tailTrace_4592353
  have hstable : (prefixWord ++ tailWord_4592353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4592353).length < 2 ^ (prefixWord ++ tailWord_4592353).sum := by decide
  have hdescent : baseEnd_4592353 < baseStart_4592353 := by decide
  rcases family_descends (prefixWord ++ tailWord_4592353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4592376 : List Nat := [2, 1, 2, 1, 1, 2, 5, 2, 1, 1, 5]
def baseStart_4592376 : Nat := 118140960795 + 4592376 * 2 ^ 59
def prefixEnd_4592376 : Nat := 4983230072969 + 3 ^ 40 * 4592376 * 2
def baseEnd_4592376 : Nat := 2358096234172229541480053

theorem tailTrace_4592376 : CollatzResearch.WordTrace tailWord_4592376 prefixEnd_4592376 2358096234172229541480053 := by
  unfold tailWord_4592376
  simp only [CollatzResearch.WordTrace]
  refine ⟨83748856605306771111686491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111665142140409028148915321 83748856605306771111686491)
  ·
    refine ⟨125623284907960156667529737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83748856605306771111686491 125623284907960156667529737)
    ·
      refine ⟨94217463680970117500647303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125623284907960156667529737 94217463680970117500647303)
      ·
        refine ⟨141326195521455176250970955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94217463680970117500647303 141326195521455176250970955)
        ·
          refine ⟨211989293282182764376456433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141326195521455176250970955 211989293282182764376456433)
          ·
            refine ⟨158991969961637073282342325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 211989293282182764376456433 158991969961637073282342325)
            ·
              refine ⟨14905497183903475620219593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 158991969961637073282342325 14905497183903475620219593)
              ·
                refine ⟨11179122887927606715164695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14905497183903475620219593 11179122887927606715164695)
                ·
                  refine ⟨16768684331891410072747043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11179122887927606715164695 16768684331891410072747043)
                  ·
                    refine ⟨25153026497837115109120565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16768684331891410072747043 25153026497837115109120565)
                    ·
                      refine ⟨2358096234172229541480053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25153026497837115109120565 2358096234172229541480053)
                      ·
                        rfl

theorem cell23_4592376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 2, 1, 1, 5].length) (baseStart_4592376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4592376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4592376 prefixEnd_4592376 := by exact prefixLift 4592376
  have htrace : WordTrace (prefixWord ++ tailWord_4592376) baseStart_4592376 baseEnd_4592376 := by
    simpa [prefixWord, tailWord_4592376, baseEnd_4592376] using wordTrace_append hprefix tailTrace_4592376
  have hstable : (prefixWord ++ tailWord_4592376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4592376).length < 2 ^ (prefixWord ++ tailWord_4592376).sum := by decide
  have hdescent : baseEnd_4592376 < baseStart_4592376 := by decide
  rcases family_descends (prefixWord ++ tailWord_4592376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4592393 : List Nat := [1, 2, 1, 1, 3, 2, 3, 4, 1, 2, 3]
def baseStart_4592393 : Nat := 118140960795 + 4592393 * 2 ^ 59
def prefixEnd_4592393 : Nat := 4983230072969 + 3 ^ 40 * 4592393 * 2
def baseEnd_4592393 : Nat := 2358104963343355974967475

theorem tailTrace_4592393 : CollatzResearch.WordTrace tailWord_4592393 prefixEnd_4592393 2358104963343355974967475 := by
  unfold tailWord_4592393
  simp only [CollatzResearch.WordTrace]
  refine ⟨167498333251551954126741833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111665555501034636084494555 167498333251551954126741833)
  ·
    refine ⟨125623749938663965595056375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167498333251551954126741833 125623749938663965595056375)
    ·
      refine ⟨188435624907995948392584563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125623749938663965595056375 188435624907995948392584563)
      ·
        refine ⟨282653437361993922588876845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188435624907995948392584563 282653437361993922588876845)
        ·
          refine ⟨105995039010747720970828817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 282653437361993922588876845 105995039010747720970828817)
          ·
            refine ⟨79496279258060790728121613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105995039010747720970828817 79496279258060790728121613)
            ·
              refine ⟨29811104721772796523045605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79496279258060790728121613 29811104721772796523045605)
              ·
                refine ⟨5589582135332399348071051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29811104721772796523045605 5589582135332399348071051)
                ·
                  refine ⟨8384373202998599022106577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5589582135332399348071051 8384373202998599022106577)
                  ·
                    refine ⟨6288279902248949266579933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8384373202998599022106577 6288279902248949266579933)
                    ·
                      refine ⟨2358104963343355974967475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6288279902248949266579933 2358104963343355974967475)
                      ·
                        rfl

theorem cell23_4592393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 4, 1, 2, 3].length) (baseStart_4592393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4592393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4592393 prefixEnd_4592393 := by exact prefixLift 4592393
  have htrace : WordTrace (prefixWord ++ tailWord_4592393) baseStart_4592393 baseEnd_4592393 := by
    simpa [prefixWord, tailWord_4592393, baseEnd_4592393] using wordTrace_append hprefix tailTrace_4592393
  have hstable : (prefixWord ++ tailWord_4592393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4592393).length < 2 ^ (prefixWord ++ tailWord_4592393).sum := by decide
  have hdescent : baseEnd_4592393 < baseStart_4592393 := by decide
  rcases family_descends (prefixWord ++ tailWord_4592393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4592440 : List Nat := [2, 1, 2, 1, 3, 2, 3, 3, 2, 1, 3]
def baseStart_4592440 : Nat := 118140960795 + 4592440 * 2 ^ 59
def prefixEnd_4592440 : Nat := 4983230072969 + 3 ^ 40 * 4592440 * 2
def baseEnd_4592440 : Nat := 2358129096934117291079759

theorem tailTrace_4592440 : CollatzResearch.WordTrace tailWord_4592440 prefixEnd_4592440 2358129096934117291079759 := by
  unfold tailWord_4592440
  simp only [CollatzResearch.WordTrace]
  refine ⟨83750023741190840576851387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111666698321587787435801849 83750023741190840576851387)
  ·
    refine ⟨125625035611786260865277081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83750023741190840576851387 125625035611786260865277081)
    ·
      refine ⟨94218776708839695648957811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125625035611786260865277081 94218776708839695648957811)
      ·
        refine ⟨141328165063259543473436717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94218776708839695648957811 141328165063259543473436717)
        ·
          refine ⟨52998061898722328802538769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 141328165063259543473436717 52998061898722328802538769)
          ·
            refine ⟨39748546424041746601904077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52998061898722328802538769 39748546424041746601904077)
            ·
              refine ⟨14905704909015654975714029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39748546424041746601904077 14905704909015654975714029)
              ·
                refine ⟨5589639340880870615892761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14905704909015654975714029 5589639340880870615892761)
                ·
                  refine ⟨4192229505660652961919571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5589639340880870615892761 4192229505660652961919571)
                  ·
                    refine ⟨6288344258490979442879357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4192229505660652961919571 6288344258490979442879357)
                    ·
                      refine ⟨2358129096934117291079759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6288344258490979442879357 2358129096934117291079759)
                      ·
                        rfl

theorem cell23_4592440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 3, 2, 1, 3].length) (baseStart_4592440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4592440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4592440 prefixEnd_4592440 := by exact prefixLift 4592440
  have htrace : WordTrace (prefixWord ++ tailWord_4592440) baseStart_4592440 baseEnd_4592440 := by
    simpa [prefixWord, tailWord_4592440, baseEnd_4592440] using wordTrace_append hprefix tailTrace_4592440
  have hstable : (prefixWord ++ tailWord_4592440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4592440).length < 2 ^ (prefixWord ++ tailWord_4592440).sum := by decide
  have hdescent : baseEnd_4592440 < baseStart_4592440 := by decide
  rcases family_descends (prefixWord ++ tailWord_4592440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4592483 : List Nat := [1, 1, 1, 5, 3, 1, 1, 1, 2, 4, 3]
def baseStart_4592483 : Nat := 118140960795 + 4592483 * 2 ^ 59
def prefixEnd_4592483 : Nat := 4983230072969 + 3 ^ 40 * 4592483 * 2
def baseEnd_4592483 : Nat := 2358151176602260622842061

theorem tailTrace_4592483 : CollatzResearch.WordTrace tailWord_4592483 prefixEnd_4592483 2358151176602260622842061 := by
  unfold tailWord_4592483
  simp only [CollatzResearch.WordTrace]
  refine ⟨167501615821225899497518103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111667743880817266331678735 167501615821225899497518103)
  ·
    refine ⟨251252423731838849246277155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167501615821225899497518103 251252423731838849246277155)
    ·
      refine ⟨376878635597758273869415733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251252423731838849246277155 376878635597758273869415733)
      ·
        refine ⟨35332372087289838175257725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 376878635597758273869415733 35332372087289838175257725)
        ·
          refine ⟨13249639532733689315721647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35332372087289838175257725 13249639532733689315721647)
          ·
            refine ⟨19874459299100533973582471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13249639532733689315721647 19874459299100533973582471)
            ·
              refine ⟨29811688948650800960373707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19874459299100533973582471 29811688948650800960373707)
              ·
                refine ⟨44717533422976201440560561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29811688948650800960373707 44717533422976201440560561)
                ·
                  refine ⟨33538150067232151080420421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44717533422976201440560561 33538150067232151080420421)
                  ·
                    refine ⟨6288403137606028327578829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33538150067232151080420421 6288403137606028327578829)
                    ·
                      refine ⟨2358151176602260622842061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6288403137606028327578829 2358151176602260622842061)
                      ·
                        rfl

theorem cell23_4592483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 4, 3].length) (baseStart_4592483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4592483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4592483 prefixEnd_4592483 := by exact prefixLift 4592483
  have htrace : WordTrace (prefixWord ++ tailWord_4592483) baseStart_4592483 baseEnd_4592483 := by
    simpa [prefixWord, tailWord_4592483, baseEnd_4592483] using wordTrace_append hprefix tailTrace_4592483
  have hstable : (prefixWord ++ tailWord_4592483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4592483).length < 2 ^ (prefixWord ++ tailWord_4592483).sum := by decide
  have hdescent : baseEnd_4592483 < baseStart_4592483 := by decide
  rcases family_descends (prefixWord ++ tailWord_4592483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4592497 : List Nat := [1, 2, 2, 2, 1, 4, 2, 3, 2, 2, 2]
def baseStart_4592497 : Nat := 118140960795 + 4592497 * 2 ^ 59
def prefixEnd_4592497 : Nat := 4983230072969 + 3 ^ 40 * 4592497 * 2
def baseEnd_4592497 : Nat := 2358158365331423568066997

theorem tailTrace_4592497 : CollatzResearch.WordTrace tailWord_4592497 prefixEnd_4592497 2358158365331423568066997 := by
  unfold tailWord_4592497
  simp only [CollatzResearch.WordTrace]
  refine ⟨167502126443175179888527745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111668084295450119925685163 167502126443175179888527745)
  ·
    refine ⟨125626594832381384916395809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167502126443175179888527745 125626594832381384916395809)
    ·
      refine ⟨94219946124286038687296857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125626594832381384916395809 94219946124286038687296857)
      ·
        refine ⟨70664959593214529015472643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94219946124286038687296857 70664959593214529015472643)
        ·
          refine ⟨105997439389821793523208965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70664959593214529015472643 105997439389821793523208965)
          ·
            refine ⟨19874519885591586285601681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 105997439389821793523208965 19874519885591586285601681)
            ·
              refine ⟨14905889914193689714201261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19874519885591586285601681 14905889914193689714201261)
              ·
                refine ⟨5589708717822633642825473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14905889914193689714201261 5589708717822633642825473)
                ·
                  refine ⟨4192281538366975232119105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5589708717822633642825473 4192281538366975232119105)
                  ·
                    refine ⟨3144211153775231424089329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4192281538366975232119105 3144211153775231424089329)
                    ·
                      refine ⟨2358158365331423568066997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3144211153775231424089329 2358158365331423568066997)
                      ·
                        rfl

theorem cell23_4592497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 3, 2, 2, 2].length) (baseStart_4592497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4592497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4592497 prefixEnd_4592497 := by exact prefixLift 4592497
  have htrace : WordTrace (prefixWord ++ tailWord_4592497) baseStart_4592497 baseEnd_4592497 := by
    simpa [prefixWord, tailWord_4592497, baseEnd_4592497] using wordTrace_append hprefix tailTrace_4592497
  have hstable : (prefixWord ++ tailWord_4592497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4592497).length < 2 ^ (prefixWord ++ tailWord_4592497).sum := by decide
  have hdescent : baseEnd_4592497 < baseStart_4592497 := by decide
  rcases family_descends (prefixWord ++ tailWord_4592497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4592520 : List Nat := [2, 1, 3, 3, 2, 1, 1, 5, 5]
def baseStart_4592520 : Nat := 118140960795 + 4592520 * 2 ^ 59
def prefixEnd_4592520 : Nat := 4983230072969 + 3 ^ 40 * 4592520 * 2
def baseEnd_4592520 : Nat := 262018908376275219786599

theorem tailTrace_4592520 : CollatzResearch.WordTrace tailWord_4592520 prefixEnd_4592520 262018908376275219786599 := by
  unfold tailWord_4592520
  simp only [CollatzResearch.WordTrace]
  refine ⟨83751482661045927408307507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111668643548061236544410009 83751482661045927408307507)
  ·
    refine ⟨125627223991568891112461261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83751482661045927408307507 125627223991568891112461261)
    ·
      refine ⟨47110208996838334167172973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125627223991568891112461261 47110208996838334167172973)
      ·
        refine ⟨17666328373814375312689865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47110208996838334167172973 17666328373814375312689865)
        ·
          refine ⟨13249746280360781484517399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17666328373814375312689865 13249746280360781484517399)
          ·
            refine ⟨19874619420541172226776099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13249746280360781484517399 19874619420541172226776099)
            ·
              refine ⟨29811929130811758340164149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19874619420541172226776099 29811929130811758340164149)
              ·
                refine ⟨2794868356013602344390389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29811929130811758340164149 2794868356013602344390389)
                ·
                  refine ⟨262018908376275219786599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2794868356013602344390389 262018908376275219786599)
                  ·
                    rfl

theorem cell23_4592520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 5, 5].length) (baseStart_4592520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4592520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4592520 prefixEnd_4592520 := by exact prefixLift 4592520
  have htrace : WordTrace (prefixWord ++ tailWord_4592520) baseStart_4592520 baseEnd_4592520 := by
    simpa [prefixWord, tailWord_4592520, baseEnd_4592520] using wordTrace_append hprefix tailTrace_4592520
  have hstable : (prefixWord ++ tailWord_4592520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4592520).length < 2 ^ (prefixWord ++ tailWord_4592520).sum := by decide
  have hdescent : baseEnd_4592520 < baseStart_4592520 := by decide
  rcases family_descends (prefixWord ++ tailWord_4592520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4592563 : List Nat := [1, 1, 1, 2, 3, 1, 2, 3, 5, 4]
def baseStart_4592563 : Nat := 118140960795 + 4592563 * 2 ^ 59
def prefixEnd_4592563 : Nat := 4983230072969 + 3 ^ 40 * 4592563 * 2
def baseEnd_4592563 : Nat := 786064085018206769947231

theorem tailTrace_4592563 : CollatzResearch.WordTrace tailWord_4592563 prefixEnd_4592563 786064085018206769947231 := by
  unfold tailWord_4592563
  simp only [CollatzResearch.WordTrace]
  refine ⟨167504533660936073160430343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111669689107290715440286895 167504533660936073160430343)
  ·
    refine ⟨251256800491404109740645515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167504533660936073160430343 251256800491404109740645515)
    ·
      refine ⟨376885200737106164610968273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251256800491404109740645515 376885200737106164610968273)
      ·
        refine ⟨282663900552829623458226205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 376885200737106164610968273 282663900552829623458226205)
        ·
          refine ⟨105998962707311108796834827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 282663900552829623458226205 105998962707311108796834827)
          ·
            refine ⟨158998444060966663195252241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105998962707311108796834827 158998444060966663195252241)
            ·
              refine ⟨119248833045724997396439181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 158998444060966663195252241 119248833045724997396439181)
              ·
                refine ⟨44718312392146874023664693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 119248833045724997396439181 44718312392146874023664693)
                ·
                  refine ⟨4192341786763769439718565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44718312392146874023664693 4192341786763769439718565)
                  ·
                    refine ⟨786064085018206769947231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4192341786763769439718565 786064085018206769947231)
                    ·
                      rfl

theorem cell23_4592563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 5, 4].length) (baseStart_4592563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4592563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4592563 prefixEnd_4592563 := by exact prefixLift 4592563
  have htrace : WordTrace (prefixWord ++ tailWord_4592563) baseStart_4592563 baseEnd_4592563 := by
    simpa [prefixWord, tailWord_4592563, baseEnd_4592563] using wordTrace_append hprefix tailTrace_4592563
  have hstable : (prefixWord ++ tailWord_4592563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4592563).length < 2 ^ (prefixWord ++ tailWord_4592563).sum := by decide
  have hdescent : baseEnd_4592563 < baseStart_4592563 := by decide
  rcases family_descends (prefixWord ++ tailWord_4592563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4592590 : List Nat := [4, 1, 1, 1, 2, 3, 1, 1, 4, 2, 3]
def baseStart_4592590 : Nat := 118140960795 + 4592590 * 2 ^ 59
def prefixEnd_4592590 : Nat := 4983230072969 + 3 ^ 40 * 4592590 * 2
def baseEnd_4592590 : Nat := 2358206119032291704204069

theorem tailTrace_4592590 : CollatzResearch.WordTrace tailWord_4592590 prefixEnd_4592590 2358206119032291704204069 := by
  unfold tailWord_4592590
  simp only [CollatzResearch.WordTrace]
  refine ⟨20938189803979782096457903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111670345621225504514442149 20938189803979782096457903)
  ·
    refine ⟨31407284705969673144686855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20938189803979782096457903 31407284705969673144686855)
    ·
      refine ⟨47110927058954509717030283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31407284705969673144686855 47110927058954509717030283)
      ·
        refine ⟨70666390588431764575545425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47110927058954509717030283 70666390588431764575545425)
        ·
          refine ⟨52999792941323823431659069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70666390588431764575545425 52999792941323823431659069)
          ·
            refine ⟨19874922352996433786872151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52999792941323823431659069 19874922352996433786872151)
            ·
              refine ⟨29812383529494650680308227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19874922352996433786872151 29812383529494650680308227)
              ·
                refine ⟨44718575294241976020462341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29812383529494650680308227 44718575294241976020462341)
                ·
                  refine ⟨8384732867670370503836689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44718575294241976020462341 8384732867670370503836689)
                  ·
                    refine ⟨6288549650752777877877517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8384732867670370503836689 6288549650752777877877517)
                    ·
                      refine ⟨2358206119032291704204069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6288549650752777877877517 2358206119032291704204069)
                      ·
                        rfl

theorem cell23_4592590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 4, 2, 3].length) (baseStart_4592590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4592590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4592590 prefixEnd_4592590 := by exact prefixLift 4592590
  have htrace : WordTrace (prefixWord ++ tailWord_4592590) baseStart_4592590 baseEnd_4592590 := by
    simpa [prefixWord, tailWord_4592590, baseEnd_4592590] using wordTrace_append hprefix tailTrace_4592590
  have hstable : (prefixWord ++ tailWord_4592590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4592590).length < 2 ^ (prefixWord ++ tailWord_4592590).sum := by decide
  have hdescent : baseEnd_4592590 < baseStart_4592590 := by decide
  rcases family_descends (prefixWord ++ tailWord_4592590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4592593 : List Nat := [1, 2, 2, 1, 2, 1, 4, 4, 6]
def baseStart_4592593 : Nat := 118140960795 + 4592593 * 2 ^ 59
def prefixEnd_4592593 : Nat := 4983230072969 + 3 ^ 40 * 4592593 * 2
def baseEnd_4592593 : Nat := 262023073274917243607395

theorem tailTrace_4592593 : CollatzResearch.WordTrace tailWord_4592593 prefixEnd_4592593 262023073274917243607395 := by
  unfold tailWord_4592593
  simp only [CollatzResearch.WordTrace]
  refine ⟨167505627850827388284022433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111670418567218258856014955 167505627850827388284022433)
  ·
    refine ⟨125629220888120541213016825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167505627850827388284022433 125629220888120541213016825)
    ·
      refine ⟨94221915666090405909762619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125629220888120541213016825 94221915666090405909762619)
      ·
        refine ⟨141332873499135608864643929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94221915666090405909762619 141332873499135608864643929)
        ·
          refine ⟨105999655124351706648482947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141332873499135608864643929 105999655124351706648482947)
          ·
            refine ⟨158999482686527559972724421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105999655124351706648482947 158999482686527559972724421)
            ·
              refine ⟨29812403003723917494885829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 158999482686527559972724421 29812403003723917494885829)
              ·
                refine ⟨5589825563198234530291093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29812403003723917494885829 5589825563198234530291093)
                ·
                  refine ⟨262023073274917243607395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5589825563198234530291093 262023073274917243607395)
                  ·
                    rfl

theorem cell23_4592593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 4, 6].length) (baseStart_4592593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4592593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4592593 prefixEnd_4592593 := by exact prefixLift 4592593
  have htrace : WordTrace (prefixWord ++ tailWord_4592593) baseStart_4592593 baseEnd_4592593 := by
    simpa [prefixWord, tailWord_4592593, baseEnd_4592593] using wordTrace_append hprefix tailTrace_4592593
  have hstable : (prefixWord ++ tailWord_4592593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4592593).length < 2 ^ (prefixWord ++ tailWord_4592593).sum := by decide
  have hdescent : baseEnd_4592593 < baseStart_4592593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4592593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4592647 : List Nat := [1, 1, 4, 3, 1, 1, 1, 4, 2, 3, 2]
def baseStart_4592647 : Nat := 118140960795 + 4592647 * 2 ^ 59
def prefixEnd_4592647 : Nat := 4983230072969 + 3 ^ 40 * 4592647 * 2
def baseEnd_4592647 : Nat := 2358235387429597981191307

theorem tailTrace_4592647 : CollatzResearch.WordTrace tailWord_4592647 prefixEnd_4592647 2358235387429597981191307 := by
  unfold tailWord_4592647
  simp only [CollatzResearch.WordTrace]
  refine ⟨167507597392631755506488195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111671731595087837004325463 167507597392631755506488195)
  ·
    refine ⟨251261396088947633259732293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167507597392631755506488195 251261396088947633259732293)
    ·
      refine ⟨47111511766677681236199805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 251261396088947633259732293 47111511766677681236199805)
      ·
        refine ⟨17666816912504130463574927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47111511766677681236199805 17666816912504130463574927)
        ·
          refine ⟨26500225368756195695362391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17666816912504130463574927 26500225368756195695362391)
          ·
            refine ⟨39750338053134293543043587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26500225368756195695362391 39750338053134293543043587)
            ·
              refine ⟨59625507079701440314565381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39750338053134293543043587 59625507079701440314565381)
              ·
                refine ⟨11179782577444020058981009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59625507079701440314565381 11179782577444020058981009)
                ·
                  refine ⟨8384836933083015044235757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11179782577444020058981009 8384836933083015044235757)
                  ·
                    refine ⟨3144313849906130641588409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8384836933083015044235757 3144313849906130641588409)
                    ·
                      refine ⟨2358235387429597981191307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3144313849906130641588409 2358235387429597981191307)
                      ·
                        rfl

theorem cell23_4592647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 4, 2, 3, 2].length) (baseStart_4592647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4592647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4592647 prefixEnd_4592647 := by exact prefixLift 4592647
  have htrace : WordTrace (prefixWord ++ tailWord_4592647) baseStart_4592647 baseEnd_4592647 := by
    simpa [prefixWord, tailWord_4592647, baseEnd_4592647] using wordTrace_append hprefix tailTrace_4592647
  have hstable : (prefixWord ++ tailWord_4592647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4592647).length < 2 ^ (prefixWord ++ tailWord_4592647).sum := by decide
  have hdescent : baseEnd_4592647 < baseStart_4592647 := by decide
  rcases family_descends (prefixWord ++ tailWord_4592647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4592690 : List Nat := [3, 2, 1, 1, 2, 2, 1, 4, 1, 2, 4]
def baseStart_4592690 : Nat := 118140960795 + 4592690 * 2 ^ 59
def prefixEnd_4592690 : Nat := 4983230072969 + 3 ^ 40 * 4592690 * 2
def baseEnd_4592690 : Nat := 2358257467097741312953609

theorem tailTrace_4592690 : CollatzResearch.WordTrace tailWord_4592690 prefixEnd_4592690 2358257467097741312953609 := by
  unfold tailWord_4592690
  simp only [CollatzResearch.WordTrace]
  refine ⟨41877291432868993462575881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111672777154317315900202349 41877291432868993462575881)
  ·
    refine ⟨31407968574651745096931911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41877291432868993462575881 31407968574651745096931911)
    ·
      refine ⟨47111952861977617645397867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31407968574651745096931911 47111952861977617645397867)
      ·
        refine ⟨70667929292966426468096801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47111952861977617645397867 70667929292966426468096801)
        ·
          refine ⟨53000946969724819851072601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70667929292966426468096801 53000946969724819851072601)
          ·
            refine ⟨39750710227293614888304451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53000946969724819851072601 39750710227293614888304451)
            ·
              refine ⟨59626065340940422332456677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39750710227293614888304451 59626065340940422332456677)
              ·
                refine ⟨11179887251426329187335627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59626065340940422332456677 11179887251426329187335627)
                ·
                  refine ⟨16769830877139493781003441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11179887251426329187335627 16769830877139493781003441)
                  ·
                    refine ⟨12577373157854620335752581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16769830877139493781003441 12577373157854620335752581)
                    ·
                      refine ⟨2358257467097741312953609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12577373157854620335752581 2358257467097741312953609)
                      ·
                        rfl

theorem cell23_4592690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 4, 1, 2, 4].length) (baseStart_4592690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4592690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4592690 prefixEnd_4592690 := by exact prefixLift 4592690
  have htrace : WordTrace (prefixWord ++ tailWord_4592690) baseStart_4592690 baseEnd_4592690 := by
    simpa [prefixWord, tailWord_4592690, baseEnd_4592690] using wordTrace_append hprefix tailTrace_4592690
  have hstable : (prefixWord ++ tailWord_4592690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4592690).length < 2 ^ (prefixWord ++ tailWord_4592690).sum := by decide
  have hdescent : baseEnd_4592690 < baseStart_4592690 := by decide
  rcases family_descends (prefixWord ++ tailWord_4592690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4592694 : List Nat := [5, 1, 2, 1, 1, 3, 1, 3, 1, 1, 4]
def baseStart_4592694 : Nat := 118140960795 + 4592694 * 2 ^ 59
def prefixEnd_4592694 : Nat := 4983230072969 + 3 ^ 40 * 4592694 * 2
def baseEnd_4592694 : Nat := 2358259521020359297303591

theorem tailTrace_4592694 : CollatzResearch.WordTrace tailWord_4592694 prefixEnd_4592694 2358259521020359297303591 := by
  unfold tailWord_4592694
  simp only [CollatzResearch.WordTrace]
  refine ⟨10469331976466342658340571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 111672874415640988355632757 10469331976466342658340571)
  ·
    refine ⟨15703997964699513987510857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10469331976466342658340571 15703997964699513987510857)
    ·
      refine ⟨11777998473524635490633143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15703997964699513987510857 11777998473524635490633143)
      ·
        refine ⟨17666997710286953235949715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11777998473524635490633143 17666997710286953235949715)
        ·
          refine ⟨26500496565430429853924573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17666997710286953235949715 26500496565430429853924573)
          ·
            refine ⟨9937686212036411195221715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26500496565430429853924573 9937686212036411195221715)
            ·
              refine ⟨14906529318054616792832573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9937686212036411195221715 14906529318054616792832573)
              ·
                refine ⟨5589948494270481297312215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14906529318054616792832573 5589948494270481297312215)
                ·
                  refine ⟨8384922741405721945968323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5589948494270481297312215 8384922741405721945968323)
                  ·
                    refine ⟨12577384112108582918952485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8384922741405721945968323 12577384112108582918952485)
                    ·
                      refine ⟨2358259521020359297303591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12577384112108582918952485 2358259521020359297303591)
                      ·
                        rfl

theorem cell23_4592694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_4592694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4592694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4592694 prefixEnd_4592694 := by exact prefixLift 4592694
  have htrace : WordTrace (prefixWord ++ tailWord_4592694) baseStart_4592694 baseEnd_4592694 := by
    simpa [prefixWord, tailWord_4592694, baseEnd_4592694] using wordTrace_append hprefix tailTrace_4592694
  have hstable : (prefixWord ++ tailWord_4592694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4592694).length < 2 ^ (prefixWord ++ tailWord_4592694).sum := by decide
  have hdescent : baseEnd_4592694 < baseStart_4592694 := by decide
  rcases family_descends (prefixWord ++ tailWord_4592694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4592703 : List Nat := [1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 6]
def baseStart_4592703 : Nat := 118140960795 + 4592703 * 2 ^ 59
def prefixEnd_4592703 : Nat := 4983230072969 + 3 ^ 40 * 4592703 * 2
def baseEnd_4592703 : Nat := 2358264142346249762091049

theorem tailTrace_4592703 : CollatzResearch.WordTrace tailWord_4592703 prefixEnd_4592703 2358264142346249762091049 := by
  unfold tailWord_4592703
  simp only [CollatzResearch.WordTrace]
  refine ⟨167509639880428877070526763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111673093253619251380351175 167509639880428877070526763)
  ·
    refine ⟨251264459820643315605790145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167509639880428877070526763 251264459820643315605790145)
    ·
      refine ⟨188448344865482486704342609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 251264459820643315605790145 188448344865482486704342609)
      ·
        refine ⟨141336258649111865028256957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188448344865482486704342609 141336258649111865028256957)
        ·
          refine ⟨53001096993416949385596359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 141336258649111865028256957 53001096993416949385596359)
          ·
            refine ⟨79501645490125424078394539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53001096993416949385596359 79501645490125424078394539)
            ·
              refine ⟨119252468235188136117591809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79501645490125424078394539 119252468235188136117591809)
              ·
                refine ⟨89439351176391102088193857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 119252468235188136117591809 89439351176391102088193857)
                ·
                  refine ⟨67079513382293326566145393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 89439351176391102088193857 67079513382293326566145393)
                  ·
                    refine ⟨50309635036719994924609045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 67079513382293326566145393 50309635036719994924609045)
                    ·
                      refine ⟨2358264142346249762091049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50309635036719994924609045 2358264142346249762091049)
                      ·
                        rfl

theorem cell23_4592703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 6].length) (baseStart_4592703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4592703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4592703 prefixEnd_4592703 := by exact prefixLift 4592703
  have htrace : WordTrace (prefixWord ++ tailWord_4592703) baseStart_4592703 baseEnd_4592703 := by
    simpa [prefixWord, tailWord_4592703, baseEnd_4592703] using wordTrace_append hprefix tailTrace_4592703
  have hstable : (prefixWord ++ tailWord_4592703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4592703).length < 2 ^ (prefixWord ++ tailWord_4592703).sum := by decide
  have hdescent : baseEnd_4592703 < baseStart_4592703 := by decide
  rcases family_descends (prefixWord ++ tailWord_4592703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4592711 : List Nat := [1, 1, 4, 1, 3, 2, 2, 4, 1, 2, 2]
def baseStart_4592711 : Nat := 118140960795 + 4592711 * 2 ^ 59
def prefixEnd_4592711 : Nat := 4983230072969 + 3 ^ 40 * 4592711 * 2
def baseEnd_4592711 : Nat := 2358268250191485730791013

theorem tailTrace_4592711 : CollatzResearch.WordTrace tailWord_4592711 prefixEnd_4592711 2358268250191485730791013 := by
  unfold tailWord_4592711
  simp only [CollatzResearch.WordTrace]
  refine ⟨167509931664399894436817987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111673287776266596291211991 167509931664399894436817987)
  ·
    refine ⟨251264897496599841655226981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167509931664399894436817987 251264897496599841655226981)
    ·
      refine ⟨47112168280612470310355059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 251264897496599841655226981 47112168280612470310355059)
      ·
        refine ⟨70668252420918705465532589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47112168280612470310355059 70668252420918705465532589)
        ·
          refine ⟨26500594657844514549574721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70668252420918705465532589 26500594657844514549574721)
          ·
            refine ⟨19875445993383385912181041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26500594657844514549574721 19875445993383385912181041)
            ·
              refine ⟨14906584495037539434135781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19875445993383385912181041 14906584495037539434135781)
              ·
                refine ⟨2794984592819538643900459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14906584495037539434135781 2794984592819538643900459)
                ·
                  refine ⟨4192476889229307965850689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2794984592819538643900459 4192476889229307965850689)
                  ·
                    refine ⟨3144357666921980974388017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4192476889229307965850689 3144357666921980974388017)
                    ·
                      refine ⟨2358268250191485730791013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3144357666921980974388017 2358268250191485730791013)
                      ·
                        rfl

theorem cell23_4592711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 4, 1, 2, 2].length) (baseStart_4592711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4592711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4592711 prefixEnd_4592711 := by exact prefixLift 4592711
  have htrace : WordTrace (prefixWord ++ tailWord_4592711) baseStart_4592711 baseEnd_4592711 := by
    simpa [prefixWord, tailWord_4592711, baseEnd_4592711] using wordTrace_append hprefix tailTrace_4592711
  have hstable : (prefixWord ++ tailWord_4592711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4592711).length < 2 ^ (prefixWord ++ tailWord_4592711).sum := by decide
  have hdescent : baseEnd_4592711 < baseStart_4592711 := by decide
  rcases family_descends (prefixWord ++ tailWord_4592711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4592713 : List Nat := [1, 2, 1, 1, 2, 2, 2, 3, 2, 7]
def baseStart_4592713 : Nat := 118140960795 + 4592713 * 2 ^ 59
def prefixEnd_4592713 : Nat := 4983230072969 + 3 ^ 40 * 4592713 * 2
def baseEnd_4592713 : Nat := 786089759050931574322001

theorem tailTrace_4592713 : CollatzResearch.WordTrace tailWord_4592713 prefixEnd_4592713 786089759050931574322001 := by
  unfold tailWord_4592713
  simp only [CollatzResearch.WordTrace]
  refine ⟨167510004610392648778390793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111673336406928432518927195 167510004610392648778390793)
  ·
    refine ⟨125632503457794486583793095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167510004610392648778390793 125632503457794486583793095)
    ·
      refine ⟨188448755186691729875689643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125632503457794486583793095 188448755186691729875689643)
      ·
        refine ⟨282673132780037594813534465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188448755186691729875689643 282673132780037594813534465)
        ·
          refine ⟨212004849585028196110150849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 282673132780037594813534465 212004849585028196110150849)
          ·
            refine ⟨159003637188771147082613137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 212004849585028196110150849 159003637188771147082613137)
            ·
              refine ⟨119252727891578360311959853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 159003637188771147082613137 119252727891578360311959853)
              ·
                refine ⟨44719772959341885116984945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 119252727891578360311959853 44719772959341885116984945)
                ·
                  refine ⟨33539829719506413837738709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44719772959341885116984945 33539829719506413837738709)
                  ·
                    refine ⟨786089759050931574322001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33539829719506413837738709 786089759050931574322001)
                    ·
                      rfl

theorem cell23_4592713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 7].length) (baseStart_4592713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4592713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4592713 prefixEnd_4592713 := by exact prefixLift 4592713
  have htrace : WordTrace (prefixWord ++ tailWord_4592713) baseStart_4592713 baseEnd_4592713 := by
    simpa [prefixWord, tailWord_4592713, baseEnd_4592713] using wordTrace_append hprefix tailTrace_4592713
  have hstable : (prefixWord ++ tailWord_4592713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4592713).length < 2 ^ (prefixWord ++ tailWord_4592713).sum := by decide
  have hdescent : baseEnd_4592713 < baseStart_4592713 := by decide
  rcases family_descends (prefixWord ++ tailWord_4592713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4592723 : List Nat := [1, 1, 1, 2, 1, 1, 2, 4, 1, 4, 5]
def baseStart_4592723 : Nat := 118140960795 + 4592723 * 2 ^ 59
def prefixEnd_4592723 : Nat := 4983230072969 + 3 ^ 40 * 4592723 * 2
def baseEnd_4592723 : Nat := 2358274411959339683840957

theorem tailTrace_4592723 : CollatzResearch.WordTrace tailWord_4592723 prefixEnd_4592723 2358274411959339683840957 := by
  unfold tailWord_4592723
  simp only [CollatzResearch.WordTrace]
  refine ⟨167510369340356420486254823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111673579560237613657503215 167510369340356420486254823)
  ·
    refine ⟨251265554010534630729382235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167510369340356420486254823 251265554010534630729382235)
    ·
      refine ⟨376898331015801946094073353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251265554010534630729382235 376898331015801946094073353)
      ·
        refine ⟨282673748261851459570555015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 376898331015801946094073353 282673748261851459570555015)
        ·
          refine ⟨424010622392777189355832523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 282673748261851459570555015 424010622392777189355832523)
          ·
            refine ⟨636015933589165784033748785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 424010622392777189355832523 636015933589165784033748785)
            ·
              refine ⟨477011950191874338025311589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 636015933589165784033748785 477011950191874338025311589)
              ·
                refine ⟨89439740660976438379745923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 477011950191874338025311589 89439740660976438379745923)
                ·
                  refine ⟨134159610991464657569618885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89439740660976438379745923 134159610991464657569618885)
                  ·
                    refine ⟨25154927060899623294303541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 134159610991464657569618885 25154927060899623294303541)
                    ·
                      refine ⟨2358274411959339683840957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25154927060899623294303541 2358274411959339683840957)
                      ·
                        rfl

theorem cell23_4592723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 4, 5].length) (baseStart_4592723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4592723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4592723 prefixEnd_4592723 := by exact prefixLift 4592723
  have htrace : WordTrace (prefixWord ++ tailWord_4592723) baseStart_4592723 baseEnd_4592723 := by
    simpa [prefixWord, tailWord_4592723, baseEnd_4592723] using wordTrace_append hprefix tailTrace_4592723
  have hstable : (prefixWord ++ tailWord_4592723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4592723).length < 2 ^ (prefixWord ++ tailWord_4592723).sum := by decide
  have hdescent : baseEnd_4592723 < baseStart_4592723 := by decide
  rcases family_descends (prefixWord ++ tailWord_4592723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4592734 : List Nat := [4, 4, 1, 1, 1, 2, 1, 9]
def baseStart_4592734 : Nat := 118140960795 + 4592734 * 2 ^ 59
def prefixEnd_4592734 : Nat := 4983230072969 + 3 ^ 40 * 4592734 * 2
def baseEnd_4592734 : Nat := 87343705935057005214941

theorem tailTrace_4592734 : CollatzResearch.WordTrace tailWord_4592734 prefixEnd_4592734 87343705935057005214941 := by
  unfold tailWord_4592734
  simp only [CollatzResearch.WordTrace]
  refine ⟨20938846317914571170613157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111673847028877712909936837 20938846317914571170613157)
  ·
    refine ⟨3926033684608982094489967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20938846317914571170613157 3926033684608982094489967)
    ·
      refine ⟨5889050526913473141734951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3926033684608982094489967 5889050526913473141734951)
      ·
        refine ⟨8833575790370209712602427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5889050526913473141734951 8833575790370209712602427)
        ·
          refine ⟨13250363685555314568903641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8833575790370209712602427 13250363685555314568903641)
          ·
            refine ⟨9937772764166485926677731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13250363685555314568903641 9937772764166485926677731)
            ·
              refine ⟨14906659146249728890016597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9937772764166485926677731 14906659146249728890016597)
              ·
                refine ⟨87343705935057005214941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14906659146249728890016597 87343705935057005214941)
                ·
                  rfl

theorem cell23_4592734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 9].length) (baseStart_4592734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4592734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4592734 prefixEnd_4592734 := by exact prefixLift 4592734
  have htrace : WordTrace (prefixWord ++ tailWord_4592734) baseStart_4592734 baseEnd_4592734 := by
    simpa [prefixWord, tailWord_4592734, baseEnd_4592734] using wordTrace_append hprefix tailTrace_4592734
  have hstable : (prefixWord ++ tailWord_4592734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4592734).length < 2 ^ (prefixWord ++ tailWord_4592734).sum := by decide
  have hdescent : baseEnd_4592734 < baseStart_4592734 := by decide
  rcases family_descends (prefixWord ++ tailWord_4592734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4592737 : List Nat := [1, 2, 3, 1, 1, 2, 2, 3, 3, 3, 2]
def baseStart_4592737 : Nat := 118140960795 + 4592737 * 2 ^ 59
def prefixEnd_4592737 : Nat := 4983230072969 + 3 ^ 40 * 4592737 * 2
def baseEnd_4592737 : Nat := 2358281600688502629065893

theorem tailTrace_4592737 : CollatzResearch.WordTrace tailWord_4592737 prefixEnd_4592737 2358281600688502629065893 := by
  unfold tailWord_4592737
  simp only [CollatzResearch.WordTrace]
  refine ⟨167510879962305700877264465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111673919974870467251509643 167510879962305700877264465)
  ·
    refine ⟨125633159971729275657948349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167510879962305700877264465 125633159971729275657948349)
    ·
      refine ⟨47112434989398478371730631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125633159971729275657948349 47112434989398478371730631)
      ·
        refine ⟨70668652484097717557595947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47112434989398478371730631 70668652484097717557595947)
        ·
          refine ⟨106002978726146576336393921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70668652484097717557595947 106002978726146576336393921)
          ·
            refine ⟨79502234044609932252295441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106002978726146576336393921 79502234044609932252295441)
            ·
              refine ⟨59626675533457449189221581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79502234044609932252295441 59626675533457449189221581)
              ·
                refine ⟨22360003325046543445958093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59626675533457449189221581 22360003325046543445958093)
                ·
                  refine ⟨8385001246892453792234285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22360003325046543445958093 8385001246892453792234285)
                  ·
                    refine ⟨3144375467584670172087857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8385001246892453792234285 3144375467584670172087857)
                    ·
                      refine ⟨2358281600688502629065893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3144375467584670172087857 2358281600688502629065893)
                      ·
                        rfl

theorem cell23_4592737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 3, 3, 2].length) (baseStart_4592737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4592737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4592737 prefixEnd_4592737 := by exact prefixLift 4592737
  have htrace : WordTrace (prefixWord ++ tailWord_4592737) baseStart_4592737 baseEnd_4592737 := by
    simpa [prefixWord, tailWord_4592737, baseEnd_4592737] using wordTrace_append hprefix tailTrace_4592737
  have hstable : (prefixWord ++ tailWord_4592737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4592737).length < 2 ^ (prefixWord ++ tailWord_4592737).sum := by decide
  have hdescent : baseEnd_4592737 < baseStart_4592737 := by decide
  rcases family_descends (prefixWord ++ tailWord_4592737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4592754 : List Nat := [3, 2, 1, 2, 2, 1, 1, 5, 1, 3, 2]
def baseStart_4592754 : Nat := 118140960795 + 4592754 * 2 ^ 59
def prefixEnd_4592754 : Nat := 4983230072969 + 3 ^ 40 * 4592754 * 2
def baseEnd_4592754 : Nat := 2358290329859629062553315

theorem tailTrace_4592754 : CollatzResearch.WordTrace tailWord_4592754 prefixEnd_4592754 2358290329859629062553315 := by
  unfold tailWord_4592754
  simp only [CollatzResearch.WordTrace]
  refine ⟨41877875000811028195158329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111674333335496075187088877 41877875000811028195158329)
  ·
    refine ⟨31408406250608271146368747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41877875000811028195158329 31408406250608271146368747)
    ·
      refine ⟨47112609375912406719553121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31408406250608271146368747 47112609375912406719553121)
      ·
        refine ⟨35334457031934305039664841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47112609375912406719553121 35334457031934305039664841)
        ·
          refine ⟨26500842773950728779748631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35334457031934305039664841 26500842773950728779748631)
          ·
            refine ⟨39751264160926093169622947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26500842773950728779748631 39751264160926093169622947)
            ·
              refine ⟨59626896241389139754434421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39751264160926093169622947 59626896241389139754434421)
              ·
                refine ⟨5590021522630231851978227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 59626896241389139754434421 5590021522630231851978227)
                ·
                  refine ⟨8385032283945347777967341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5590021522630231851978227 8385032283945347777967341)
                  ·
                    refine ⟨3144387106479505416737753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8385032283945347777967341 3144387106479505416737753)
                    ·
                      refine ⟨2358290329859629062553315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3144387106479505416737753 2358290329859629062553315)
                      ·
                        rfl

theorem cell23_4592754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 5, 1, 3, 2].length) (baseStart_4592754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4592754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4592754 prefixEnd_4592754 := by exact prefixLift 4592754
  have htrace : WordTrace (prefixWord ++ tailWord_4592754) baseStart_4592754 baseEnd_4592754 := by
    simpa [prefixWord, tailWord_4592754, baseEnd_4592754] using wordTrace_append hprefix tailTrace_4592754
  have hstable : (prefixWord ++ tailWord_4592754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4592754).length < 2 ^ (prefixWord ++ tailWord_4592754).sum := by decide
  have hdescent : baseEnd_4592754 < baseStart_4592754 := by decide
  rcases family_descends (prefixWord ++ tailWord_4592754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4592780 : List Nat := [2, 2, 1, 2, 1, 1, 1, 5, 2, 2, 4]
def baseStart_4592780 : Nat := 118140960795 + 4592780 * 2 ^ 59
def prefixEnd_4592780 : Nat := 4983230072969 + 3 ^ 40 * 4592780 * 2
def baseEnd_4592780 : Nat := 2358303680356645960828195

theorem tailTrace_4592780 : CollatzResearch.WordTrace tailWord_4592780 prefixEnd_4592780 2358303680356645960828195 := by
  unfold tailWord_4592780
  simp only [CollatzResearch.WordTrace]
  refine ⟨83756224150574959610539897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111674965534099946147386529 83756224150574959610539897)
  ·
    refine ⟨62817168112931219707904923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83756224150574959610539897 62817168112931219707904923)
    ·
      refine ⟨94225752169396829561857385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62817168112931219707904923 94225752169396829561857385)
      ·
        refine ⟨70669314127047622171393039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94225752169396829561857385 70669314127047622171393039)
        ·
          refine ⟨106003971190571433257089559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70669314127047622171393039 106003971190571433257089559)
          ·
            refine ⟨159005956785857149885634339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106003971190571433257089559 159005956785857149885634339)
            ·
              refine ⟨238508935178785724828451509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159005956785857149885634339 238508935178785724828451509)
              ·
                refine ⟨22360212673011161702667329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 238508935178785724828451509 22360212673011161702667329)
                ·
                  refine ⟨16770159504758371277000497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22360212673011161702667329 16770159504758371277000497)
                  ·
                    refine ⟨12577619628568778457750373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16770159504758371277000497 12577619628568778457750373)
                    ·
                      refine ⟨2358303680356645960828195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12577619628568778457750373 2358303680356645960828195)
                      ·
                        rfl

theorem cell23_4592780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 2, 2, 4].length) (baseStart_4592780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4592780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4592780 prefixEnd_4592780 := by exact prefixLift 4592780
  have htrace : WordTrace (prefixWord ++ tailWord_4592780) baseStart_4592780 baseEnd_4592780 := by
    simpa [prefixWord, tailWord_4592780, baseEnd_4592780] using wordTrace_append hprefix tailTrace_4592780
  have hstable : (prefixWord ++ tailWord_4592780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4592780).length < 2 ^ (prefixWord ++ tailWord_4592780).sum := by decide
  have hdescent : baseEnd_4592780 < baseStart_4592780 := by decide
  rcases family_descends (prefixWord ++ tailWord_4592780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4592857 : List Nat := [1, 2, 1, 2, 3, 1, 1, 1, 3, 6, 2]
def baseStart_4592857 : Nat := 118140960795 + 4592857 * 2 ^ 59
def prefixEnd_4592857 : Nat := 4983230072969 + 3 ^ 40 * 4592857 * 2
def baseEnd_4592857 : Nat := 2358343218367042159565341

theorem tailTrace_4592857 : CollatzResearch.WordTrace tailWord_4592857 prefixEnd_4592857 2358343218367042159565341 := by
  unfold tailWord_4592857
  simp only [CollatzResearch.WordTrace]
  refine ⟨167515256721870961371632825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111676837814580640914421883 167515256721870961371632825)
  ·
    refine ⟨125636442541403221028724619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167515256721870961371632825 125636442541403221028724619)
    ·
      refine ⟨188454663812104831543086929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125636442541403221028724619 188454663812104831543086929)
      ·
        refine ⟨141340997859078623657315197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188454663812104831543086929 141340997859078623657315197)
        ·
          refine ⟨53002874197154483871493199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 141340997859078623657315197 53002874197154483871493199)
          ·
            refine ⟨79504311295731725807239799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53002874197154483871493199 79504311295731725807239799)
            ·
              refine ⟨119256466943597588710859699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79504311295731725807239799 119256466943597588710859699)
              ·
                refine ⟨178884700415396383066289549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119256466943597588710859699 178884700415396383066289549)
                ·
                  refine ⟨67081762655773643649858581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 178884700415396383066289549 67081762655773643649858581)
                  ·
                    refine ⟨3144457624489389546087121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 67081762655773643649858581 3144457624489389546087121)
                    ·
                      refine ⟨2358343218367042159565341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3144457624489389546087121 2358343218367042159565341)
                      ·
                        rfl

theorem cell23_4592857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 6, 2].length) (baseStart_4592857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4592857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4592857 prefixEnd_4592857 := by exact prefixLift 4592857
  have htrace : WordTrace (prefixWord ++ tailWord_4592857) baseStart_4592857 baseEnd_4592857 := by
    simpa [prefixWord, tailWord_4592857, baseEnd_4592857] using wordTrace_append hprefix tailTrace_4592857
  have hstable : (prefixWord ++ tailWord_4592857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4592857).length < 2 ^ (prefixWord ++ tailWord_4592857).sum := by decide
  have hdescent : baseEnd_4592857 < baseStart_4592857 := by decide
  rcases family_descends (prefixWord ++ tailWord_4592857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4592874 : List Nat := [3, 1, 3, 1, 1, 3, 1, 2, 2, 4, 2]
def baseStart_4592874 : Nat := 118140960795 + 4592874 * 2 ^ 59
def prefixEnd_4592874 : Nat := 4983230072969 + 3 ^ 40 * 4592874 * 2
def baseEnd_4592874 : Nat := 2358351947538168593052763

theorem tailTrace_4592874 : CollatzResearch.WordTrace tailWord_4592874 prefixEnd_4592874 2358351947538168593052763 := by
  unfold tailWord_4592874
  simp only [CollatzResearch.WordTrace]
  refine ⟨41878969190702343318750419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111677251175206248850001117 41878969190702343318750419)
  ·
    refine ⟨62818453786053514978125629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41878969190702343318750419 62818453786053514978125629)
    ·
      refine ⟨23556920169770068116797111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62818453786053514978125629 23556920169770068116797111)
      ·
        refine ⟨35335380254655102175195667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23556920169770068116797111 35335380254655102175195667)
        ·
          refine ⟨53003070381982653262793501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35335380254655102175195667 53003070381982653262793501)
          ·
            refine ⟨19876151393243494973547563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53003070381982653262793501 19876151393243494973547563)
            ·
              refine ⟨29814227089865242460321345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19876151393243494973547563 29814227089865242460321345)
              ·
                refine ⟨22360670317398931845241009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29814227089865242460321345 22360670317398931845241009)
                ·
                  refine ⟨16770502738049198883930757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22360670317398931845241009 16770502738049198883930757)
                  ·
                    refine ⟨3144469263384224790737017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16770502738049198883930757 3144469263384224790737017)
                    ·
                      refine ⟨2358351947538168593052763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3144469263384224790737017 2358351947538168593052763)
                      ·
                        rfl

theorem cell23_4592874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 2, 4, 2].length) (baseStart_4592874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4592874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4592874 prefixEnd_4592874 := by exact prefixLift 4592874
  have htrace : WordTrace (prefixWord ++ tailWord_4592874) baseStart_4592874 baseEnd_4592874 := by
    simpa [prefixWord, tailWord_4592874, baseEnd_4592874] using wordTrace_append hprefix tailTrace_4592874
  have hstable : (prefixWord ++ tailWord_4592874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4592874).length < 2 ^ (prefixWord ++ tailWord_4592874).sum := by decide
  have hdescent : baseEnd_4592874 < baseStart_4592874 := by decide
  rcases family_descends (prefixWord ++ tailWord_4592874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4592894 : List Nat := [4, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3]
def baseStart_4592894 : Nat := 118140960795 + 4592894 * 2 ^ 59
def prefixEnd_4592894 : Nat := 4983230072969 + 3 ^ 40 * 4592894 * 2
def baseEnd_4592894 : Nat := 2358362217151258514802671

theorem tailTrace_4592894 : CollatzResearch.WordTrace tailWord_4592894 prefixEnd_4592894 2358362217151258514802671 := by
  unfold tailWord_4592894
  simp only [CollatzResearch.WordTrace]
  refine ⟨20939575777842114586341217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111677737481824611127153157 20939575777842114586341217)
  ·
    refine ⟨15704681833381585939755913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20939575777842114586341217 15704681833381585939755913)
    ·
      refine ⟨11778511375036189454816935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15704681833381585939755913 11778511375036189454816935)
      ·
        refine ⟨17667767062554284182225403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11778511375036189454816935 17667767062554284182225403)
        ·
          refine ⟨26501650593831426273338105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17667767062554284182225403 26501650593831426273338105)
          ·
            refine ⟨19876237945373569705003579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26501650593831426273338105 19876237945373569705003579)
            ·
              refine ⟨29814356918060354557505369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19876237945373569705003579 29814356918060354557505369)
              ·
                refine ⟨22360767688545265918129027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29814356918060354557505369 22360767688545265918129027)
                ·
                  refine ⟨33541151532817898877193541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22360767688545265918129027 33541151532817898877193541)
                  ·
                    refine ⟨6288965912403356039473789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33541151532817898877193541 6288965912403356039473789)
                    ·
                      refine ⟨2358362217151258514802671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6288965912403356039473789 2358362217151258514802671)
                      ·
                        rfl

theorem cell23_4592894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_4592894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4592894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4592894 prefixEnd_4592894 := by exact prefixLift 4592894
  have htrace : WordTrace (prefixWord ++ tailWord_4592894) baseStart_4592894 baseEnd_4592894 := by
    simpa [prefixWord, tailWord_4592894, baseEnd_4592894] using wordTrace_append hprefix tailTrace_4592894
  have hstable : (prefixWord ++ tailWord_4592894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4592894).length < 2 ^ (prefixWord ++ tailWord_4592894).sum := by decide
  have hdescent : baseEnd_4592894 < baseStart_4592894 := by decide
  rcases family_descends (prefixWord ++ tailWord_4592894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4592924 : List Nat := [2, 2, 3, 1, 1, 1, 2, 2, 5, 1, 3]
def baseStart_4592924 : Nat := 118140960795 + 4592924 * 2 ^ 59
def prefixEnd_4592924 : Nat := 4983230072969 + 3 ^ 40 * 4592924 * 2
def baseEnd_4592924 : Nat := 2358377621570893397427533

theorem tailTrace_4592924 : CollatzResearch.WordTrace tailWord_4592924 prefixEnd_4592924 2358377621570893397427533 := by
  unfold tailWord_4592924
  simp only [CollatzResearch.WordTrace]
  refine ⟨83758850206314115907160913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111678466941752154542881217 83758850206314115907160913)
  ·
    refine ⟨62819137654735586930370685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83758850206314115907160913 62819137654735586930370685)
    ·
      refine ⟨23557176620525845098889007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62819137654735586930370685 23557176620525845098889007)
      ·
        refine ⟨35335764930788767648333511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23557176620525845098889007 35335764930788767648333511)
        ·
          refine ⟨53003647396183151472500267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35335764930788767648333511 53003647396183151472500267)
          ·
            refine ⟨79505471094274727208750401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53003647396183151472500267 79505471094274727208750401)
            ·
              refine ⟨59629103320706045406562801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79505471094274727208750401 59629103320706045406562801)
              ·
                refine ⟨44721827490529534054922101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59629103320706045406562801 44721827490529534054922101)
                ·
                  refine ⟨4192671327237143817648947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44721827490529534054922101 4192671327237143817648947)
                  ·
                    refine ⟨6289006990855715726473421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4192671327237143817648947 6289006990855715726473421)
                    ·
                      refine ⟨2358377621570893397427533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6289006990855715726473421 2358377621570893397427533)
                      ·
                        rfl

theorem cell23_4592924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 5, 1, 3].length) (baseStart_4592924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4592924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4592924 prefixEnd_4592924 := by exact prefixLift 4592924
  have htrace : WordTrace (prefixWord ++ tailWord_4592924) baseStart_4592924 baseEnd_4592924 := by
    simpa [prefixWord, tailWord_4592924, baseEnd_4592924] using wordTrace_append hprefix tailTrace_4592924
  have hstable : (prefixWord ++ tailWord_4592924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4592924).length < 2 ^ (prefixWord ++ tailWord_4592924).sum := by decide
  have hdescent : baseEnd_4592924 < baseStart_4592924 := by decide
  rcases family_descends (prefixWord ++ tailWord_4592924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4592961 : List Nat := [1, 2, 5, 2, 1, 1, 3, 2, 1, 5]
def baseStart_4592961 : Nat := 118140960795 + 4592961 * 2 ^ 59
def prefixEnd_4592961 : Nat := 4983230072969 + 3 ^ 40 * 4592961 * 2
def baseEnd_4592961 : Nat := 786132206785036584221621

theorem tailTrace_4592961 : CollatzResearch.WordTrace tailWord_4592961 prefixEnd_4592961 786132206785036584221621 := by
  unfold tailWord_4592961
  simp only [CollatzResearch.WordTrace]
  refine ⟨167519049913494187133418737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111679366608996124755612491 167519049913494187133418737)
  ·
    refine ⟨125639287435120640350064053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167519049913494187133418737 125639287435120640350064053)
    ·
      refine ⟨11778683197042560032818505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 125639287435120640350064053 11778683197042560032818505)
      ·
        refine ⟨8834012397781920024613879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11778683197042560032818505 8834012397781920024613879)
        ·
          refine ⟨13251018596672880036920819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8834012397781920024613879 13251018596672880036920819)
          ·
            refine ⟨19876527895009320055381229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13251018596672880036920819 19876527895009320055381229)
            ·
              refine ⟨7453697960628495020767961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19876527895009320055381229 7453697960628495020767961)
              ·
                refine ⟨5590273470471371265575971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7453697960628495020767961 5590273470471371265575971)
                ·
                  refine ⟨8385410205707056898363957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5590273470471371265575971 8385410205707056898363957)
                  ·
                    refine ⟨786132206785036584221621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8385410205707056898363957 786132206785036584221621)
                    ·
                      rfl

theorem cell23_4592961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_4592961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4592961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4592961 prefixEnd_4592961 := by exact prefixLift 4592961
  have htrace : WordTrace (prefixWord ++ tailWord_4592961) baseStart_4592961 baseEnd_4592961 := by
    simpa [prefixWord, tailWord_4592961, baseEnd_4592961] using wordTrace_append hprefix tailTrace_4592961
  have hstable : (prefixWord ++ tailWord_4592961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4592961).length < 2 ^ (prefixWord ++ tailWord_4592961).sum := by decide
  have hdescent : baseEnd_4592961 < baseStart_4592961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4592961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4592994 : List Nat := [3, 3, 2, 1, 1, 1, 1, 2, 3, 2, 4]
def baseStart_4592994 : Nat := 118140960795 + 4592994 * 2 ^ 59
def prefixEnd_4592994 : Nat := 4983230072969 + 3 ^ 40 * 4592994 * 2
def baseEnd_4592994 : Nat := 2358413565216708123552211

theorem tailTrace_4592994 : CollatzResearch.WordTrace tailWord_4592994 prefixEnd_4592994 2358413565216708123552211 := by
  unfold tailWord_4592994
  simp only [CollatzResearch.WordTrace]
  refine ⟨41880063380593658442342509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111680169014916422512913357 41880063380593658442342509)
  ·
    refine ⟨15705023767722621915878441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41880063380593658442342509 15705023767722621915878441)
    ·
      refine ⟨11778767825791966436908831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15705023767722621915878441 11778767825791966436908831)
      ·
        refine ⟨17668151738687949655363247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11778767825791966436908831 17668151738687949655363247)
        ·
          refine ⟨26502227608031924483044871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17668151738687949655363247 26502227608031924483044871)
          ·
            refine ⟨39753341412047886724567307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26502227608031924483044871 39753341412047886724567307)
            ·
              refine ⟨59630012118071830086850961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39753341412047886724567307 59630012118071830086850961)
              ·
                refine ⟨44722509088553872565138221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59630012118071830086850961 44722509088553872565138221)
                ·
                  refine ⟨16770940908207702211926833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44722509088553872565138221 16770940908207702211926833)
                  ·
                    refine ⟨12578205681155776658945125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16770940908207702211926833 12578205681155776658945125)
                    ·
                      refine ⟨2358413565216708123552211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12578205681155776658945125 2358413565216708123552211)
                      ·
                        rfl

theorem cell23_4592994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_4592994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4592994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4592994 prefixEnd_4592994 := by exact prefixLift 4592994
  have htrace : WordTrace (prefixWord ++ tailWord_4592994) baseStart_4592994 baseEnd_4592994 := by
    simpa [prefixWord, tailWord_4592994, baseEnd_4592994] using wordTrace_append hprefix tailTrace_4592994
  have hstable : (prefixWord ++ tailWord_4592994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4592994).length < 2 ^ (prefixWord ++ tailWord_4592994).sum := by decide
  have hdescent : baseEnd_4592994 < baseStart_4592994 := by decide
  rcases family_descends (prefixWord ++ tailWord_4592994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4593004 : List Nat := [2, 2, 1, 1, 5, 3, 1, 8]
def baseStart_4593004 : Nat := 118140960795 + 4593004 * 2 ^ 59
def prefixEnd_4593004 : Nat := 4983230072969 + 3 ^ 40 * 4593004 * 2
def baseEnd_4593004 : Nat := 87348840741601966089895

theorem tailTrace_4593004 : CollatzResearch.WordTrace tailWord_4593004 prefixEnd_4593004 87348840741601966089895 := by
  unfold tailWord_4593004
  simp only [CollatzResearch.WordTrace]
  refine ⟨83760309126169202738617033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111680412168225603651489377 83760309126169202738617033)
  ·
    refine ⟨62820231844626902053962775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83760309126169202738617033 62820231844626902053962775)
    ·
      refine ⟨94230347766940353080944163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62820231844626902053962775 94230347766940353080944163)
      ·
        refine ⟨141345521650410529621416245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94230347766940353080944163 141345521650410529621416245)
        ·
          refine ⟨13251142654725987152007773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 141345521650410529621416245 13251142654725987152007773)
          ·
            refine ⟨4969178495522245182002915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13251142654725987152007773 4969178495522245182002915)
            ·
              refine ⟨7453767743283367773004373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4969178495522245182002915 7453767743283367773004373)
              ·
                refine ⟨87348840741601966089895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7453767743283367773004373 87348840741601966089895)
                ·
                  rfl

theorem cell23_4593004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 8].length) (baseStart_4593004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4593004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4593004 prefixEnd_4593004 := by exact prefixLift 4593004
  have htrace : WordTrace (prefixWord ++ tailWord_4593004) baseStart_4593004 baseEnd_4593004 := by
    simpa [prefixWord, tailWord_4593004, baseEnd_4593004] using wordTrace_append hprefix tailTrace_4593004
  have hstable : (prefixWord ++ tailWord_4593004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4593004).length < 2 ^ (prefixWord ++ tailWord_4593004).sum := by decide
  have hdescent : baseEnd_4593004 < baseStart_4593004 := by decide
  rcases family_descends (prefixWord ++ tailWord_4593004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4593041 : List Nat := [1, 2, 2, 1, 1, 1, 2, 7, 1, 3, 2]
def baseStart_4593041 : Nat := 118140960795 + 4593041 * 2 ^ 59
def prefixEnd_4593041 : Nat := 4983230072969 + 3 ^ 40 * 4593041 * 2
def baseEnd_4593041 : Nat := 2358437698807469439664495

theorem tailTrace_4593041 : CollatzResearch.WordTrace tailWord_4593041 prefixEnd_4593041 2358437698807469439664495 := by
  unfold tailWord_4593041
  simp only [CollatzResearch.WordTrace]
  refine ⟨167521967753204360796330977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111681311835469573864220651 167521967753204360796330977)
  ·
    refine ⟨125641475814903270597248233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167521967753204360796330977 125641475814903270597248233)
    ·
      refine ⟨94231106861177452947936175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125641475814903270597248233 94231106861177452947936175)
      ·
        refine ⟨141346660291766179421904263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94231106861177452947936175 141346660291766179421904263)
        ·
          refine ⟨212019990437649269132856395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141346660291766179421904263 212019990437649269132856395)
          ·
            refine ⟨318029985656473903699284593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212019990437649269132856395 318029985656473903699284593)
            ·
              refine ⟨238522489242355427774463445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 318029985656473903699284593 238522489242355427774463445)
              ·
                refine ⟨5590370841617705338463987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 238522489242355427774463445 5590370841617705338463987)
                ·
                  refine ⟨8385556262426558007695981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5590370841617705338463987 8385556262426558007695981)
                  ·
                    refine ⟨3144583598409959252885993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8385556262426558007695981 3144583598409959252885993)
                    ·
                      refine ⟨2358437698807469439664495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3144583598409959252885993 2358437698807469439664495)
                      ·
                        rfl

theorem cell23_4593041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 3, 2].length) (baseStart_4593041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4593041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4593041 prefixEnd_4593041 := by exact prefixLift 4593041
  have htrace : WordTrace (prefixWord ++ tailWord_4593041) baseStart_4593041 baseEnd_4593041 := by
    simpa [prefixWord, tailWord_4593041, baseEnd_4593041] using wordTrace_append hprefix tailTrace_4593041
  have hstable : (prefixWord ++ tailWord_4593041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4593041).length < 2 ^ (prefixWord ++ tailWord_4593041).sum := by decide
  have hdescent : baseEnd_4593041 < baseStart_4593041 := by decide
  rcases family_descends (prefixWord ++ tailWord_4593041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4593042 : List Nat := [3, 2, 3, 3, 2, 1, 1, 2, 2, 4]
def baseStart_4593042 : Nat := 118140960795 + 4593042 * 2 ^ 59
def prefixEnd_4593042 : Nat := 4983230072969 + 3 ^ 40 * 4593042 * 2
def baseEnd_4593042 : Nat := 786146070762707978583997

theorem tailTrace_4593042 : CollatzResearch.WordTrace tailWord_4593042 prefixEnd_4593042 786146070762707978583997 := by
  unfold tailWord_4593042
  simp only [CollatzResearch.WordTrace]
  refine ⟨41880501056550184491779345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111681336150800491978078253 41880501056550184491779345)
  ·
    refine ⟨31410375792412638368834509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41880501056550184491779345 31410375792412638368834509)
    ·
      refine ⟨11778890922154739388312941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31410375792412638368834509 11778890922154739388312941)
      ·
        refine ⟨4417084095808027270617353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11778890922154739388312941 4417084095808027270617353)
        ·
          refine ⟨3312813071856020452963015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4417084095808027270617353 3312813071856020452963015)
          ·
            refine ⟨4969219607784030679444523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3312813071856020452963015 4969219607784030679444523)
            ·
              refine ⟨7453829411676046019166785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4969219607784030679444523 7453829411676046019166785)
              ·
                refine ⟨5590372058757034514375089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7453829411676046019166785 5590372058757034514375089)
                ·
                  refine ⟨4192779044067775885781317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5590372058757034514375089 4192779044067775885781317)
                  ·
                    refine ⟨786146070762707978583997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4192779044067775885781317 786146070762707978583997)
                    ·
                      rfl

theorem cell23_4593042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_4593042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4593042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4593042 prefixEnd_4593042 := by exact prefixLift 4593042
  have htrace : WordTrace (prefixWord ++ tailWord_4593042) baseStart_4593042 baseEnd_4593042 := by
    simpa [prefixWord, tailWord_4593042, baseEnd_4593042] using wordTrace_append hprefix tailTrace_4593042
  have hstable : (prefixWord ++ tailWord_4593042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4593042).length < 2 ^ (prefixWord ++ tailWord_4593042).sum := by decide
  have hdescent : baseEnd_4593042 < baseStart_4593042 := by decide
  rcases family_descends (prefixWord ++ tailWord_4593042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4593048 : List Nat := [2, 1, 2, 5, 2, 1, 1, 1, 4, 1, 3]
def baseStart_4593048 : Nat := 118140960795 + 4593048 * 2 ^ 59
def prefixEnd_4593048 : Nat := 4983230072969 + 3 ^ 40 * 4593048 * 2
def baseEnd_4593048 : Nat := 2358441293172050912276963

theorem tailTrace_4593048 : CollatzResearch.WordTrace tailWord_4593048 prefixEnd_4593048 2358441293172050912276963 := by
  unfold tailWord_4593048
  simp only [CollatzResearch.WordTrace]
  refine ⟨83761111532089500495917899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111681482042786000661223865 83761111532089500495917899)
  ·
    refine ⟨125641667298134250743876849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83761111532089500495917899 125641667298134250743876849)
    ·
      refine ⟨94231250473600688057907637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125641667298134250743876849 94231250473600688057907637)
      ·
        refine ⟨8834179731900064505428841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 94231250473600688057907637 8834179731900064505428841)
        ·
          refine ⟨6625634798925048379071631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8834179731900064505428841 6625634798925048379071631)
          ·
            refine ⟨9938452198387572568607447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6625634798925048379071631 9938452198387572568607447)
            ·
              refine ⟨14907678297581358852911171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9938452198387572568607447 14907678297581358852911171)
              ·
                refine ⟨22361517446372038279366757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14907678297581358852911171 22361517446372038279366757)
                ·
                  refine ⟨4192784521194757177381267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22361517446372038279366757 4192784521194757177381267)
                  ·
                    refine ⟨6289176781792135766071901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4192784521194757177381267 6289176781792135766071901)
                    ·
                      refine ⟨2358441293172050912276963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6289176781792135766071901 2358441293172050912276963)
                      ·
                        rfl

theorem cell23_4593048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_4593048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4593048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4593048 prefixEnd_4593048 := by exact prefixLift 4593048
  have htrace : WordTrace (prefixWord ++ tailWord_4593048) baseStart_4593048 baseEnd_4593048 := by
    simpa [prefixWord, tailWord_4593048, baseEnd_4593048] using wordTrace_append hprefix tailTrace_4593048
  have hstable : (prefixWord ++ tailWord_4593048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4593048).length < 2 ^ (prefixWord ++ tailWord_4593048).sum := by decide
  have hdescent : baseEnd_4593048 < baseStart_4593048 := by decide
  rcases family_descends (prefixWord ++ tailWord_4593048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4593067 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 5, 4, 4]
def baseStart_4593067 : Nat := 118140960795 + 4593067 * 2 ^ 59
def prefixEnd_4593067 : Nat := 4983230072969 + 3 ^ 40 * 4593067 * 2
def baseEnd_4593067 : Nat := 2358451049304486337939375

theorem tailTrace_4593067 : CollatzResearch.WordTrace tailWord_4593067 prefixEnd_4593067 2358451049304486337939375 := by
  unfold tailWord_4593067
  simp only [CollatzResearch.WordTrace]
  refine ⟨167522916051110167236777455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111681944034073444824518303 167522916051110167236777455)
  ·
    refine ⟨251284374076665250855166183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167522916051110167236777455 251284374076665250855166183)
    ·
      refine ⟨376926561114997876282749275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251284374076665250855166183 376926561114997876282749275)
      ·
        refine ⟨565389841672496814424123913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 376926561114997876282749275 565389841672496814424123913)
        ·
          refine ⟨424042381254372610818092935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 565389841672496814424123913 424042381254372610818092935)
          ·
            refine ⟨636063571881558916227139403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 424042381254372610818092935 636063571881558916227139403)
            ·
              refine ⟨954095357822338374340709105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 636063571881558916227139403 954095357822338374340709105)
              ·
                refine ⟨715571518366753780755531829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 954095357822338374340709105 715571518366753780755531829)
                ·
                  refine ⟨67084829846883166945831109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 715571518366753780755531829 67084829846883166945831109)
                  ·
                    refine ⟨12578405596290593802343333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 67084829846883166945831109 12578405596290593802343333)
                    ·
                      refine ⟨2358451049304486337939375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12578405596290593802343333 2358451049304486337939375)
                      ·
                        rfl

theorem cell23_4593067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 4, 4].length) (baseStart_4593067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4593067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4593067 prefixEnd_4593067 := by exact prefixLift 4593067
  have htrace : WordTrace (prefixWord ++ tailWord_4593067) baseStart_4593067 baseEnd_4593067 := by
    simpa [prefixWord, tailWord_4593067, baseEnd_4593067] using wordTrace_append hprefix tailTrace_4593067
  have hstable : (prefixWord ++ tailWord_4593067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4593067).length < 2 ^ (prefixWord ++ tailWord_4593067).sum := by decide
  have hdescent : baseEnd_4593067 < baseStart_4593067 := by decide
  rcases family_descends (prefixWord ++ tailWord_4593067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4593134 : List Nat := [4, 1, 2, 1, 2, 1, 1, 2, 1, 1, 7]
def baseStart_4593134 : Nat := 118140960795 + 4593134 * 2 ^ 59
def prefixEnd_4593134 : Nat := 4983230072969 + 3 ^ 40 * 4593134 * 2
def baseEnd_4593134 : Nat := 2358485452508337575801567

theorem tailTrace_4593134 : CollatzResearch.WordTrace tailWord_4593134 prefixEnd_4593134 2358485452508337575801567 := by
  unfold tailWord_4593134
  simp only [CollatzResearch.WordTrace]
  refine ⟨20940669967733429709933307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111683573161244958452977637 20940669967733429709933307)
  ·
    refine ⟨31411004951600144564899961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20940669967733429709933307 31411004951600144564899961)
    ·
      refine ⟨23558253713700108423674971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31411004951600144564899961 23558253713700108423674971)
      ·
        refine ⟨35337380570550162635512457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23558253713700108423674971 35337380570550162635512457)
        ·
          refine ⟨26503035427912621976634343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35337380570550162635512457 26503035427912621976634343)
          ·
            refine ⟨39754553141868932964951515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26503035427912621976634343 39754553141868932964951515)
            ·
              refine ⟨59631829712803399447427273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39754553141868932964951515 59631829712803399447427273)
              ·
                refine ⟨44723872284602549585570455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59631829712803399447427273 44723872284602549585570455)
                ·
                  refine ⟨67085808426903824378355683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44723872284602549585570455 67085808426903824378355683)
                  ·
                    refine ⟨100628712640355736567533525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 67085808426903824378355683 100628712640355736567533525)
                    ·
                      refine ⟨2358485452508337575801567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 100628712640355736567533525 2358485452508337575801567)
                      ·
                        rfl

theorem cell23_4593134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_4593134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4593134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4593134 prefixEnd_4593134 := by exact prefixLift 4593134
  have htrace : WordTrace (prefixWord ++ tailWord_4593134) baseStart_4593134 baseEnd_4593134 := by
    simpa [prefixWord, tailWord_4593134, baseEnd_4593134] using wordTrace_append hprefix tailTrace_4593134
  have hstable : (prefixWord ++ tailWord_4593134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4593134).length < 2 ^ (prefixWord ++ tailWord_4593134).sum := by decide
  have hdescent : baseEnd_4593134 < baseStart_4593134 := by decide
  rcases family_descends (prefixWord ++ tailWord_4593134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4593161 : List Nat := [1, 2, 1, 1, 3, 1, 4, 2, 2, 4, 2]
def baseStart_4593161 : Nat := 118140960795 + 4593161 * 2 ^ 59
def prefixEnd_4593161 : Nat := 4983230072969 + 3 ^ 40 * 4593161 * 2
def baseEnd_4593161 : Nat := 2358499316486008970163943

theorem tailTrace_4593161 : CollatzResearch.WordTrace tailWord_4593161 prefixEnd_4593161 2358499316486008970163943 := by
  unfold tailWord_4593161
  simp only [CollatzResearch.WordTrace]
  refine ⟨167526344512769621290699337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111684229675179747527132891 167526344512769621290699337)
  ·
    refine ⟨125644758384577215968024503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167526344512769621290699337 125644758384577215968024503)
    ·
      refine ⟨188467137576865823952036755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125644758384577215968024503 188467137576865823952036755)
      ·
        refine ⟨282700706365298735928055133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188467137576865823952036755 282700706365298735928055133)
        ·
          refine ⟨106012764886987025973020675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 282700706365298735928055133 106012764886987025973020675)
          ·
            refine ⟨159019147330480538959531013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106012764886987025973020675 159019147330480538959531013)
            ·
              refine ⟨29816090124465101054912065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 159019147330480538959531013 29816090124465101054912065)
              ·
                refine ⟨22362067593348825791184049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29816090124465101054912065 22362067593348825791184049)
                ·
                  refine ⟨16771550695011619343388037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22362067593348825791184049 16771550695011619343388037)
                  ·
                    refine ⟨3144665755314678626885257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16771550695011619343388037 3144665755314678626885257)
                    ·
                      refine ⟨2358499316486008970163943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3144665755314678626885257 2358499316486008970163943)
                      ·
                        rfl

theorem cell23_4593161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 2, 4, 2].length) (baseStart_4593161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4593161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4593161 prefixEnd_4593161 := by exact prefixLift 4593161
  have htrace : WordTrace (prefixWord ++ tailWord_4593161) baseStart_4593161 baseEnd_4593161 := by
    simpa [prefixWord, tailWord_4593161, baseEnd_4593161] using wordTrace_append hprefix tailTrace_4593161
  have hstable : (prefixWord ++ tailWord_4593161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4593161).length < 2 ^ (prefixWord ++ tailWord_4593161).sum := by decide
  have hdescent : baseEnd_4593161 < baseStart_4593161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4593161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4593181 : List Nat := [1, 4, 2, 2, 1, 1, 2, 2, 1, 4, 3]
def baseStart_4593181 : Nat := 118140960795 + 4593181 * 2 ^ 59
def prefixEnd_4593181 : Nat := 4983230072969 + 3 ^ 40 * 4593181 * 2
def baseEnd_4593181 : Nat := 2358509586099098891913851

theorem tailTrace_4593181 : CollatzResearch.WordTrace tailWord_4593181 prefixEnd_4593181 2358509586099098891913851 := by
  unfold tailWord_4593181
  simp only [CollatzResearch.WordTrace]
  refine ⟨167527073972697164706427397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111684715981798109804284931 167527073972697164706427397)
  ·
    refine ⟨31411326369880718382455137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 167527073972697164706427397 31411326369880718382455137)
    ·
      refine ⟨23558494777410538786841353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31411326369880718382455137 23558494777410538786841353)
      ·
        refine ⟨17668871083057904090131015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23558494777410538786841353 17668871083057904090131015)
        ·
          refine ⟨26503306624586856135196523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17668871083057904090131015 26503306624586856135196523)
          ·
            refine ⟨39754959936880284202794785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26503306624586856135196523 39754959936880284202794785)
            ·
              refine ⟨29816219952660213152096089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39754959936880284202794785 29816219952660213152096089)
              ·
                refine ⟨22362164964495159864072067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29816219952660213152096089 22362164964495159864072067)
                ·
                  refine ⟨33543247446742739796108101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22362164964495159864072067 33543247446742739796108101)
                  ·
                    refine ⟨6289358896264263711770269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33543247446742739796108101 6289358896264263711770269)
                    ·
                      refine ⟨2358509586099098891913851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6289358896264263711770269 2358509586099098891913851)
                      ·
                        rfl

theorem cell23_4593181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_4593181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4593181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4593181 prefixEnd_4593181 := by exact prefixLift 4593181
  have htrace : WordTrace (prefixWord ++ tailWord_4593181) baseStart_4593181 baseEnd_4593181 := by
    simpa [prefixWord, tailWord_4593181, baseEnd_4593181] using wordTrace_append hprefix tailTrace_4593181
  have hstable : (prefixWord ++ tailWord_4593181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4593181).length < 2 ^ (prefixWord ++ tailWord_4593181).sum := by decide
  have hdescent : baseEnd_4593181 < baseStart_4593181 := by decide
  rcases family_descends (prefixWord ++ tailWord_4593181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4593198 : List Nat := [4, 1, 3, 1, 2, 2, 1, 1, 1, 4, 3]
def baseStart_4593198 : Nat := 118140960795 + 4593198 * 2 ^ 59
def prefixEnd_4593198 : Nat := 4983230072969 + 3 ^ 40 * 4593198 * 2
def baseEnd_4593198 : Nat := 2358518315270225325401273

theorem tailTrace_4593198 : CollatzResearch.WordTrace tailWord_4593198 prefixEnd_4593198 2358518315270225325401273 := by
  unfold tailWord_4593198
  simp only [CollatzResearch.WordTrace]
  refine ⟨20940961751704447076224531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111685129342423717739864165 20940961751704447076224531)
  ·
    refine ⟨31411442627556670614336797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20940961751704447076224531 31411442627556670614336797)
    ·
      refine ⟨11779290985333751480376299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31411442627556670614336797 11779290985333751480376299)
      ·
        refine ⟨17668936478000627220564449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11779290985333751480376299 17668936478000627220564449)
        ·
          refine ⟨13251702358500470415423337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17668936478000627220564449 13251702358500470415423337)
          ·
            refine ⟨9938776768875352811567503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13251702358500470415423337 9938776768875352811567503)
            ·
              refine ⟨14908165153313029217351255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9938776768875352811567503 14908165153313029217351255)
              ·
                refine ⟨22362247729969543826026883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14908165153313029217351255 22362247729969543826026883)
                ·
                  refine ⟨33543371594954315739040325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22362247729969543826026883 33543371594954315739040325)
                  ·
                    refine ⟨6289382174053934201070061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33543371594954315739040325 6289382174053934201070061)
                    ·
                      refine ⟨2358518315270225325401273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6289382174053934201070061 2358518315270225325401273)
                      ·
                        rfl

theorem cell23_4593198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_4593198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4593198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4593198 prefixEnd_4593198 := by exact prefixLift 4593198
  have htrace : WordTrace (prefixWord ++ tailWord_4593198) baseStart_4593198 baseEnd_4593198 := by
    simpa [prefixWord, tailWord_4593198, baseEnd_4593198] using wordTrace_append hprefix tailTrace_4593198
  have hstable : (prefixWord ++ tailWord_4593198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4593198).length < 2 ^ (prefixWord ++ tailWord_4593198).sum := by decide
  have hdescent : baseEnd_4593198 < baseStart_4593198 := by decide
  rcases family_descends (prefixWord ++ tailWord_4593198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4593205 : List Nat := [1, 3, 3, 1, 1, 4, 2, 3, 1, 4]
def baseStart_4593205 : Nat := 118140960795 + 4593205 * 2 ^ 59
def prefixEnd_4593205 : Nat := 4983230072969 + 3 ^ 40 * 4593205 * 2
def baseEnd_4593205 : Nat := 786173969878268932671247

theorem tailTrace_4593205 : CollatzResearch.WordTrace tailWord_4593205 prefixEnd_4593205 786173969878268932671247 := by
  unfold tailWord_4593205
  simp only [CollatzResearch.WordTrace]
  refine ⟨167527949324610216805301069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111685299549740144536867379 167527949324610216805301069)
  ·
    refine ⟨62822980996728831301987901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167527949324610216805301069 62822980996728831301987901)
    ·
      refine ⟨23558617873773311738245463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62822980996728831301987901 23558617873773311738245463)
      ·
        refine ⟨35337926810659967607368195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23558617873773311738245463 35337926810659967607368195)
        ·
          refine ⟨53006890215989951411052293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35337926810659967607368195 53006890215989951411052293)
          ·
            refine ⟨9938791915498115889572305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53006890215989951411052293 9938791915498115889572305)
            ·
              refine ⟨7454093936623586917179229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9938791915498115889572305 7454093936623586917179229)
              ·
                refine ⟨2795285226233845093942211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7454093936623586917179229 2795285226233845093942211)
                ·
                  refine ⟨4192927839350767640913317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2795285226233845093942211 4192927839350767640913317)
                  ·
                    refine ⟨786173969878268932671247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4192927839350767640913317 786173969878268932671247)
                    ·
                      rfl

theorem cell23_4593205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 3, 1, 4].length) (baseStart_4593205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4593205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4593205 prefixEnd_4593205 := by exact prefixLift 4593205
  have htrace : WordTrace (prefixWord ++ tailWord_4593205) baseStart_4593205 baseEnd_4593205 := by
    simpa [prefixWord, tailWord_4593205, baseEnd_4593205] using wordTrace_append hprefix tailTrace_4593205
  have hstable : (prefixWord ++ tailWord_4593205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4593205).length < 2 ^ (prefixWord ++ tailWord_4593205).sum := by decide
  have hdescent : baseEnd_4593205 < baseStart_4593205 := by decide
  rcases family_descends (prefixWord ++ tailWord_4593205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4593222 : List Nat := [6, 1, 1, 1, 3, 1, 2, 1, 3, 4]
def baseStart_4593222 : Nat := 118140960795 + 4593222 * 2 ^ 59
def prefixEnd_4593222 : Nat := 4983230072969 + 3 ^ 40 * 4593222 * 2
def baseEnd_4593222 : Nat := 786176879601977743833721

theorem tailTrace_4593222 : CollatzResearch.WordTrace tailWord_4593222 prefixEnd_4593222 786176879601977743833721 := by
  unfold tailWord_4593222
  simp only [CollatzResearch.WordTrace]
  refine ⟨5235267792673394647145935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 111685712910365752472446613 5235267792673394647145935)
  ·
    refine ⟨7852901689010091970718903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5235267792673394647145935 7852901689010091970718903)
    ·
      refine ⟨11779352533515137956078355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7852901689010091970718903 11779352533515137956078355)
      ·
        refine ⟨17669028800272706934117533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11779352533515137956078355 17669028800272706934117533)
        ·
          refine ⟨6625885800102265100294075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17669028800272706934117533 6625885800102265100294075)
          ·
            refine ⟨9938828700153397650441113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6625885800102265100294075 9938828700153397650441113)
            ·
              refine ⟨7454121525115048237830835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9938828700153397650441113 7454121525115048237830835)
              ·
                refine ⟨11181182287672572356746253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7454121525115048237830835 11181182287672572356746253)
                ·
                  refine ⟨4192943357877214633779845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11181182287672572356746253 4192943357877214633779845)
                  ·
                    refine ⟨786176879601977743833721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4192943357877214633779845 786176879601977743833721)
                    ·
                      rfl

theorem cell23_4593222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_4593222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4593222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4593222 prefixEnd_4593222 := by exact prefixLift 4593222
  have htrace : WordTrace (prefixWord ++ tailWord_4593222) baseStart_4593222 baseEnd_4593222 := by
    simpa [prefixWord, tailWord_4593222, baseEnd_4593222] using wordTrace_append hprefix tailTrace_4593222
  have hstable : (prefixWord ++ tailWord_4593222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4593222).length < 2 ^ (prefixWord ++ tailWord_4593222).sum := by decide
  have hdescent : baseEnd_4593222 < baseStart_4593222 := by decide
  rcases family_descends (prefixWord ++ tailWord_4593222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4593228 : List Nat := [2, 2, 1, 3, 1, 3, 1, 3, 3, 1, 3]
def baseStart_4593228 : Nat := 118140960795 + 4593228 * 2 ^ 59
def prefixEnd_4593228 : Nat := 4983230072969 + 3 ^ 40 * 4593228 * 2
def baseEnd_4593228 : Nat := 2358533719689860208026135

theorem tailTrace_4593228 : CollatzResearch.WordTrace tailWord_4593228 prefixEnd_4593228 2358533719689860208026135 := by
  unfold tailWord_4593228
  simp only [CollatzResearch.WordTrace]
  refine ⟨83764394101763445866694169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111685858802351261155592225 83764394101763445866694169)
  ·
    refine ⟨62823295576322584400020627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83764394101763445866694169 62823295576322584400020627)
    ·
      refine ⟨94234943364483876600030941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62823295576322584400020627 94234943364483876600030941)
      ·
        refine ⟨35338103761681453725011603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94234943364483876600030941 35338103761681453725011603)
        ·
          refine ⟨53007155642522180587517405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35338103761681453725011603 53007155642522180587517405)
          ·
            refine ⟨19877683365945817720319027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53007155642522180587517405 19877683365945817720319027)
            ·
              refine ⟨29816525048918726580478541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19877683365945817720319027 29816525048918726580478541)
              ·
                refine ⟨11181196893344522467679453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29816525048918726580478541 11181196893344522467679453)
                ·
                  refine ⟨4192948835004195925379795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11181196893344522467679453 4192948835004195925379795)
                  ·
                    refine ⟨6289423252506293888069693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4192948835004195925379795 6289423252506293888069693)
                    ·
                      refine ⟨2358533719689860208026135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6289423252506293888069693 2358533719689860208026135)
                      ·
                        rfl

theorem cell23_4593228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 3, 3, 1, 3].length) (baseStart_4593228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4593228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4593228 prefixEnd_4593228 := by exact prefixLift 4593228
  have htrace : WordTrace (prefixWord ++ tailWord_4593228) baseStart_4593228 baseEnd_4593228 := by
    simpa [prefixWord, tailWord_4593228, baseEnd_4593228] using wordTrace_append hprefix tailTrace_4593228
  have hstable : (prefixWord ++ tailWord_4593228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4593228).length < 2 ^ (prefixWord ++ tailWord_4593228).sum := by decide
  have hdescent : baseEnd_4593228 < baseStart_4593228 := by decide
  rcases family_descends (prefixWord ++ tailWord_4593228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4593271 : List Nat := [1, 1, 3, 1, 1, 3, 1, 2, 5, 2, 3]
def baseStart_4593271 : Nat := 118140960795 + 4593271 * 2 ^ 59
def prefixEnd_4593271 : Nat := 4983230072969 + 3 ^ 40 * 4593271 * 2
def baseEnd_4593271 : Nat := 2358555799358003539788437

theorem tailTrace_4593271 : CollatzResearch.WordTrace tailWord_4593271 prefixEnd_4593271 2358555799358003539788437 := by
  unfold tailWord_4593271
  simp only [CollatzResearch.WordTrace]
  refine ⟨167530356542371110077203667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111686904361580740051469111 167530356542371110077203667)
  ·
    refine ⟨251295534813556665115805501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167530356542371110077203667 251295534813556665115805501)
    ·
      refine ⟨94235825555083749418427063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 251295534813556665115805501 94235825555083749418427063)
      ·
        refine ⟨141353738332625624127640595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94235825555083749418427063 141353738332625624127640595)
        ·
          refine ⟨212030607498938436191460893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141353738332625624127640595 212030607498938436191460893)
          ·
            refine ⟨79511477812101913571797835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 212030607498938436191460893 79511477812101913571797835)
            ·
              refine ⟨119267216718152870357696753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79511477812101913571797835 119267216718152870357696753)
              ·
                refine ⟨89450412538614652768272565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 119267216718152870357696753 89450412538614652768272565)
                ·
                  refine ⟨8385976175495123697025553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 89450412538614652768272565 8385976175495123697025553)
                  ·
                    refine ⟨6289482131621342772769165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8385976175495123697025553 6289482131621342772769165)
                    ·
                      refine ⟨2358555799358003539788437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6289482131621342772769165 2358555799358003539788437)
                      ·
                        rfl

theorem cell23_4593271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 5, 2, 3].length) (baseStart_4593271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4593271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4593271 prefixEnd_4593271 := by exact prefixLift 4593271
  have htrace : WordTrace (prefixWord ++ tailWord_4593271) baseStart_4593271 baseEnd_4593271 := by
    simpa [prefixWord, tailWord_4593271, baseEnd_4593271] using wordTrace_append hprefix tailTrace_4593271
  have hstable : (prefixWord ++ tailWord_4593271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4593271).length < 2 ^ (prefixWord ++ tailWord_4593271).sum := by decide
  have hdescent : baseEnd_4593271 < baseStart_4593271 := by decide
  rcases family_descends (prefixWord ++ tailWord_4593271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4593281 : List Nat := [1, 2, 4, 2, 1, 2, 1, 2, 1, 1, 6]
def baseStart_4593281 : Nat := 118140960795 + 4593281 * 2 ^ 59
def prefixEnd_4593281 : Nat := 4983230072969 + 3 ^ 40 * 4593281 * 2
def baseEnd_4593281 : Nat := 2358560934164548500663391

theorem tailTrace_4593281 : CollatzResearch.WordTrace tailWord_4593281 prefixEnd_4593281 2358560934164548500663391 := by
  unfold tailWord_4593281
  simp only [CollatzResearch.WordTrace]
  refine ⟨167530721272334881785067697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111687147514889921190045131 167530721272334881785067697)
  ·
    refine ⟨125648040954251161338800773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167530721272334881785067697 125648040954251161338800773)
    ·
      refine ⟨23559007678922092751025145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 125648040954251161338800773 23559007678922092751025145)
      ·
        refine ⟨17669255759191569563268859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23559007678922092751025145 17669255759191569563268859)
        ·
          refine ⟨26503883638787354344903289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17669255759191569563268859 26503883638787354344903289)
          ·
            refine ⟨19877912729090515758677467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26503883638787354344903289 19877912729090515758677467)
            ·
              refine ⟨29816869093635773638016201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19877912729090515758677467 29816869093635773638016201)
              ·
                refine ⟨22362651820226830228512151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29816869093635773638016201 22362651820226830228512151)
                ·
                  refine ⟨33543977730340245342768227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22362651820226830228512151 33543977730340245342768227)
                  ·
                    refine ⟨50315966595510368014152341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33543977730340245342768227 50315966595510368014152341)
                    ·
                      refine ⟨2358560934164548500663391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50315966595510368014152341 2358560934164548500663391)
                      ·
                        rfl

theorem cell23_4593281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_4593281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4593281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4593281 prefixEnd_4593281 := by exact prefixLift 4593281
  have htrace : WordTrace (prefixWord ++ tailWord_4593281) baseStart_4593281 baseEnd_4593281 := by
    simpa [prefixWord, tailWord_4593281, baseEnd_4593281] using wordTrace_append hprefix tailTrace_4593281
  have hstable : (prefixWord ++ tailWord_4593281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4593281).length < 2 ^ (prefixWord ++ tailWord_4593281).sum := by decide
  have hdescent : baseEnd_4593281 < baseStart_4593281 := by decide
  rcases family_descends (prefixWord ++ tailWord_4593281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4593301 : List Nat := [1, 3, 2, 1, 1, 1, 1, 2, 5, 3, 3]
def baseStart_4593301 : Nat := 118140960795 + 4593301 * 2 ^ 59
def prefixEnd_4593301 : Nat := 4983230072969 + 3 ^ 40 * 4593301 * 2
def baseEnd_4593301 : Nat := 2358571203777638422413299

theorem tailTrace_4593301 : CollatzResearch.WordTrace tailWord_4593301 prefixEnd_4593301 2358571203777638422413299 := by
  unfold tailWord_4593301
  simp only [CollatzResearch.WordTrace]
  refine ⟨167531450732262425200795757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111687633821508283467197171 167531450732262425200795757)
  ·
    refine ⟨62824294024598409450298409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167531450732262425200795757 62824294024598409450298409)
    ·
      refine ⟨47118220518448807087723807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62824294024598409450298409 47118220518448807087723807)
      ·
        refine ⟨70677330777673210631585711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47118220518448807087723807 70677330777673210631585711)
        ·
          refine ⟨106015996166509815947378567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70677330777673210631585711 106015996166509815947378567)
          ·
            refine ⟨159023994249764723921067851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106015996166509815947378567 159023994249764723921067851)
            ·
              refine ⟨238535991374647085881601777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159023994249764723921067851 238535991374647085881601777)
              ·
                refine ⟨178901993530985314411201333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 238535991374647085881601777 178901993530985314411201333)
                ·
                  refine ⟨16772061893529873226050125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 178901993530985314411201333 16772061893529873226050125)
                  ·
                    refine ⟨6289523210073702459768797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16772061893529873226050125 6289523210073702459768797)
                    ·
                      refine ⟨2358571203777638422413299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6289523210073702459768797 2358571203777638422413299)
                      ·
                        rfl

theorem cell23_4593301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 5, 3, 3].length) (baseStart_4593301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4593301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4593301 prefixEnd_4593301 := by exact prefixLift 4593301
  have htrace : WordTrace (prefixWord ++ tailWord_4593301) baseStart_4593301 baseEnd_4593301 := by
    simpa [prefixWord, tailWord_4593301, baseEnd_4593301] using wordTrace_append hprefix tailTrace_4593301
  have hstable : (prefixWord ++ tailWord_4593301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4593301).length < 2 ^ (prefixWord ++ tailWord_4593301).sum := by decide
  have hdescent : baseEnd_4593301 < baseStart_4593301 := by decide
  rcases family_descends (prefixWord ++ tailWord_4593301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4593335 : List Nat := [1, 1, 3, 1, 5, 1, 1, 4, 2, 1, 3]
def baseStart_4593335 : Nat := 118140960795 + 4593335 * 2 ^ 59
def prefixEnd_4593335 : Nat := 4983230072969 + 3 ^ 40 * 4593335 * 2
def baseEnd_4593335 : Nat := 2358588662119891289388143

theorem tailTrace_4593335 : CollatzResearch.WordTrace tailWord_4593335 prefixEnd_4593335 2358588662119891289388143 := by
  unfold tailWord_4593335
  simp only [CollatzResearch.WordTrace]
  refine ⟨167532690814139249007533459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111688460542759499338355639 167532690814139249007533459)
  ·
    refine ⟨251299036221208873511300189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167532690814139249007533459 251299036221208873511300189)
    ·
      refine ⟨94237138582953327566737571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 251299036221208873511300189 94237138582953327566737571)
      ·
        refine ⟨141355707874429991350106357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94237138582953327566737571 141355707874429991350106357)
        ·
          refine ⟨13252097613227811689072471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 141355707874429991350106357 13252097613227811689072471)
          ·
            refine ⟨19878146419841717533608707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13252097613227811689072471 19878146419841717533608707)
            ·
              refine ⟨29817219629762576300413061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19878146419841717533608707 29817219629762576300413061)
              ·
                refine ⟨5590728680580483056327449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29817219629762576300413061 5590728680580483056327449)
                ·
                  refine ⟨4193046510435362292245587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5590728680580483056327449 4193046510435362292245587)
                  ·
                    refine ⟨6289569765653043438368381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4193046510435362292245587 6289569765653043438368381)
                    ·
                      refine ⟨2358588662119891289388143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6289569765653043438368381 2358588662119891289388143)
                      ·
                        rfl

theorem cell23_4593335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 4, 2, 1, 3].length) (baseStart_4593335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4593335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4593335 prefixEnd_4593335 := by exact prefixLift 4593335
  have htrace : WordTrace (prefixWord ++ tailWord_4593335) baseStart_4593335 baseEnd_4593335 := by
    simpa [prefixWord, tailWord_4593335, baseEnd_4593335] using wordTrace_append hprefix tailTrace_4593335
  have hstable : (prefixWord ++ tailWord_4593335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4593335).length < 2 ^ (prefixWord ++ tailWord_4593335).sum := by decide
  have hdescent : baseEnd_4593335 < baseStart_4593335 := by decide
  rcases family_descends (prefixWord ++ tailWord_4593335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4593341 : List Nat := [1, 4, 1, 2, 1, 2, 1, 1, 1, 5, 4]
def baseStart_4593341 : Nat := 118140960795 + 4593341 * 2 ^ 59
def prefixEnd_4593341 : Nat := 4983230072969 + 3 ^ 40 * 4593341 * 2
def baseEnd_4593341 : Nat := 2358591743003818265913115

theorem tailTrace_4593341 : CollatzResearch.WordTrace tailWord_4593341 prefixEnd_4593341 2358591743003818265913115 := by
  unfold tailWord_4593341
  simp only [CollatzResearch.WordTrace]
  refine ⟨167532909652117512032251877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111688606434745008021501251 167532909652117512032251877)
  ·
    refine ⟨31412420559772033506047227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 167532909652117512032251877 31412420559772033506047227)
    ·
      refine ⟨47118630839658050259070841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31412420559772033506047227 47118630839658050259070841)
      ·
        refine ⟨35338973129743537694303131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47118630839658050259070841 35338973129743537694303131)
        ·
          refine ⟨53008459694615306541454697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35338973129743537694303131 53008459694615306541454697)
          ·
            refine ⟨39756344770961479906091023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53008459694615306541454697 39756344770961479906091023)
            ·
              refine ⟨59634517156442219859136535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39756344770961479906091023 59634517156442219859136535)
              ·
                refine ⟨89451775734663329788704803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59634517156442219859136535 89451775734663329788704803)
                ·
                  refine ⟨134177663601994994683057205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89451775734663329788704803 134177663601994994683057205)
                  ·
                    refine ⟨12579155962687030751536613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 134177663601994994683057205 12579155962687030751536613)
                    ·
                      refine ⟨2358591743003818265913115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12579155962687030751536613 2358591743003818265913115)
                      ·
                        rfl

theorem cell23_4593341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_4593341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4593341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4593341 prefixEnd_4593341 := by exact prefixLift 4593341
  have htrace : WordTrace (prefixWord ++ tailWord_4593341) baseStart_4593341 baseEnd_4593341 := by
    simpa [prefixWord, tailWord_4593341, baseEnd_4593341] using wordTrace_append hprefix tailTrace_4593341
  have hstable : (prefixWord ++ tailWord_4593341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4593341).length < 2 ^ (prefixWord ++ tailWord_4593341).sum := by decide
  have hdescent : baseEnd_4593341 < baseStart_4593341 := by decide
  rcases family_descends (prefixWord ++ tailWord_4593341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4593351 : List Nat := [1, 1, 4, 1, 1, 1, 5, 1, 2, 6]
def baseStart_4593351 : Nat := 118140960795 + 4593351 * 2 ^ 59
def prefixEnd_4593351 : Nat := 4983230072969 + 3 ^ 40 * 4593351 * 2
def baseEnd_4593351 : Nat := 786198959270121075596023

theorem tailTrace_4593351 : CollatzResearch.WordTrace tailWord_4593351 prefixEnd_4593351 786198959270121075596023 := by
  unfold tailWord_4593351
  simp only [CollatzResearch.WordTrace]
  refine ⟨167533274382081283740115907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111688849588054189160077271 167533274382081283740115907)
  ·
    refine ⟨251299911573121925610173861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167533274382081283740115907 251299911573121925610173861)
    ·
      refine ⟨47118733419960361051907599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 251299911573121925610173861 47118733419960361051907599)
      ·
        refine ⟨70678100129940541577861399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47118733419960361051907599 70678100129940541577861399)
        ·
          refine ⟨106017150194910812366792099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70678100129940541577861399 106017150194910812366792099)
          ·
            refine ⟨159025725292366218550188149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106017150194910812366792099 159025725292366218550188149)
            ·
              refine ⟨14908661746159332989080139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 159025725292366218550188149 14908661746159332989080139)
              ·
                refine ⟨22362992619238999483620209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14908661746159332989080139 22362992619238999483620209)
                ·
                  refine ⟨16772244464429249612715157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22362992619238999483620209 16772244464429249612715157)
                  ·
                    refine ⟨786198959270121075596023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16772244464429249612715157 786198959270121075596023)
                    ·
                      rfl

theorem cell23_4593351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 2, 6].length) (baseStart_4593351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4593351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4593351 prefixEnd_4593351 := by exact prefixLift 4593351
  have htrace : WordTrace (prefixWord ++ tailWord_4593351) baseStart_4593351 baseEnd_4593351 := by
    simpa [prefixWord, tailWord_4593351, baseEnd_4593351] using wordTrace_append hprefix tailTrace_4593351
  have hstable : (prefixWord ++ tailWord_4593351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4593351).length < 2 ^ (prefixWord ++ tailWord_4593351).sum := by decide
  have hdescent : baseEnd_4593351 < baseStart_4593351 := by decide
  rcases family_descends (prefixWord ++ tailWord_4593351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4593375 : List Nat := [1, 1, 2, 3, 2, 2, 2, 2, 4, 2, 2]
def baseStart_4593375 : Nat := 118140960795 + 4593375 * 2 ^ 59
def prefixEnd_4593375 : Nat := 4983230072969 + 3 ^ 40 * 4593375 * 2
def baseEnd_4593375 : Nat := 2358609201346071132887959

theorem tailTrace_4593375 : CollatzResearch.WordTrace tailWord_4593375 prefixEnd_4593375 2358609201346071132887959 := by
  unfold tailWord_4593375
  simp only [CollatzResearch.WordTrace]
  refine ⟨167534149733994335838989579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111689433155996223892659719 167534149733994335838989579)
  ·
    refine ⟨251301224600991503758484369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167534149733994335838989579 251301224600991503758484369)
    ·
      refine ⟨188475918450743627818863277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 251301224600991503758484369 188475918450743627818863277)
      ·
        refine ⟨70678469419028860432073729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 188475918450743627818863277 70678469419028860432073729)
        ·
          refine ⟨53008852064271645324055297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70678469419028860432073729 53008852064271645324055297)
          ·
            refine ⟨39756639048203733993041473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53008852064271645324055297 39756639048203733993041473)
            ·
              refine ⟨29817479286152800494781105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39756639048203733993041473 29817479286152800494781105)
              ·
                refine ⟨22363109464614600371085829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29817479286152800494781105 22363109464614600371085829)
                ·
                  refine ⟨4193083024615237569578593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22363109464614600371085829 4193083024615237569578593)
                  ·
                    refine ⟨3144812268461428177183945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4193083024615237569578593 3144812268461428177183945)
                    ·
                      refine ⟨2358609201346071132887959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3144812268461428177183945 2358609201346071132887959)
                      ·
                        rfl

theorem cell23_4593375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 4, 2, 2].length) (baseStart_4593375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4593375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4593375 prefixEnd_4593375 := by exact prefixLift 4593375
  have htrace : WordTrace (prefixWord ++ tailWord_4593375) baseStart_4593375 baseEnd_4593375 := by
    simpa [prefixWord, tailWord_4593375, baseEnd_4593375] using wordTrace_append hprefix tailTrace_4593375
  have hstable : (prefixWord ++ tailWord_4593375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4593375).length < 2 ^ (prefixWord ++ tailWord_4593375).sum := by decide
  have hdescent : baseEnd_4593375 < baseStart_4593375 := by decide
  rcases family_descends (prefixWord ++ tailWord_4593375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4593381 : List Nat := [1, 3, 1, 4, 1, 1, 1, 2, 9]
def baseStart_4593381 : Nat := 118140960795 + 4593381 * 2 ^ 59
def prefixEnd_4593381 : Nat := 4983230072969 + 3 ^ 40 * 4593381 * 2
def baseEnd_4593381 : Nat := 262068031358888678823659

theorem tailTrace_4593381 : CollatzResearch.WordTrace tailWord_4593381 prefixEnd_4593381 262068031358888678823659 := by
  unfold tailWord_4593381
  simp only [CollatzResearch.WordTrace]
  refine ⟨167534368571972598863707997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111689579047981732575805331 167534368571972598863707997)
  ·
    refine ⟨62825388214489724573890499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167534368571972598863707997 62825388214489724573890499)
    ·
      refine ⟨94238082321734586860835749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62825388214489724573890499 94238082321734586860835749)
      ·
        refine ⟨17669640435325235036406703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94238082321734586860835749 17669640435325235036406703)
        ·
          refine ⟨26504460652987852554610055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17669640435325235036406703 26504460652987852554610055)
          ·
            refine ⟨39756690979481778831915083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26504460652987852554610055 39756690979481778831915083)
            ·
              refine ⟨59635036469222668247872625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39756690979481778831915083 59635036469222668247872625)
              ·
                refine ⟨44726277351917001185904469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59635036469222668247872625 44726277351917001185904469)
                ·
                  refine ⟨262068031358888678823659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 44726277351917001185904469 262068031358888678823659)
                  ·
                    rfl

theorem cell23_4593381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 9].length) (baseStart_4593381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4593381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4593381 prefixEnd_4593381 := by exact prefixLift 4593381
  have htrace : WordTrace (prefixWord ++ tailWord_4593381) baseStart_4593381 baseEnd_4593381 := by
    simpa [prefixWord, tailWord_4593381, baseEnd_4593381] using wordTrace_append hprefix tailTrace_4593381
  have hstable : (prefixWord ++ tailWord_4593381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4593381).length < 2 ^ (prefixWord ++ tailWord_4593381).sum := by decide
  have hdescent : baseEnd_4593381 < baseStart_4593381 := by decide
  rcases family_descends (prefixWord ++ tailWord_4593381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4593398 : List Nat := [5, 1, 1, 1, 1, 3, 1, 3, 7]
def baseStart_4593398 : Nat := 118140960795 + 4593398 * 2 ^ 59
def prefixEnd_4593398 : Nat := 4983230072969 + 3 ^ 40 * 4593398 * 2
def baseEnd_4593398 : Nat := 262069001266791615877817

theorem tailTrace_4593398 : CollatzResearch.WordTrace tailWord_4593398 prefixEnd_4593398 262069001266791615877817 := by
  unfold tailWord_4593398
  simp only [CollatzResearch.WordTrace]
  refine ⟨10470936788306938172942303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 111689992408607340511384565 10470936788306938172942303)
  ·
    refine ⟨15706405182460407259413455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10470936788306938172942303 15706405182460407259413455)
    ·
      refine ⟨23559607773690610889120183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15706405182460407259413455 23559607773690610889120183)
      ·
        refine ⟨35339411660535916333680275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23559607773690610889120183 35339411660535916333680275)
        ·
          refine ⟨53009117490803874500520413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35339411660535916333680275 53009117490803874500520413)
          ·
            refine ⟨19878419059051452937695155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53009117490803874500520413 19878419059051452937695155)
            ·
              refine ⟨29817628588577179406542733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19878419059051452937695155 29817628588577179406542733)
              ·
                refine ⟨11181610720716442277453525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29817628588577179406542733 11181610720716442277453525)
                ·
                  refine ⟨262069001266791615877817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11181610720716442277453525 262069001266791615877817)
                  ·
                    rfl

theorem cell23_4593398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 3, 7].length) (baseStart_4593398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4593398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4593398 prefixEnd_4593398 := by exact prefixLift 4593398
  have htrace : WordTrace (prefixWord ++ tailWord_4593398) baseStart_4593398 baseEnd_4593398 := by
    simpa [prefixWord, tailWord_4593398, baseEnd_4593398] using wordTrace_append hprefix tailTrace_4593398
  have hstable : (prefixWord ++ tailWord_4593398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4593398).length < 2 ^ (prefixWord ++ tailWord_4593398).sum := by decide
  have hdescent : baseEnd_4593398 < baseStart_4593398 := by decide
  rcases family_descends (prefixWord ++ tailWord_4593398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4593411 : List Nat := [1, 1, 1, 3, 2, 2, 3, 2, 1, 7]
def baseStart_4593411 : Nat := 118140960795 + 4593411 * 2 ^ 59
def prefixEnd_4593411 : Nat := 4983230072969 + 3 ^ 40 * 4593411 * 2
def baseEnd_4593411 : Nat := 786209228883210997345931

theorem tailTrace_4593411 : CollatzResearch.WordTrace tailWord_4593411 prefixEnd_4593411 786209228883210997345931 := by
  unfold tailWord_4593411
  simp only [CollatzResearch.WordTrace]
  refine ⟨167535462761863913987300087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111690308507909275991533391 167535462761863913987300087)
  ·
    refine ⟨251303194142795870980950131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167535462761863913987300087 251303194142795870980950131)
    ·
      refine ⟨376954791214193806471425197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251303194142795870980950131 376954791214193806471425197)
      ·
        refine ⟨141358046705322677426784449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 376954791214193806471425197 141358046705322677426784449)
        ·
          refine ⟨106018535028992008070088337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141358046705322677426784449 106018535028992008070088337)
          ·
            refine ⟨79513901271744006052566253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106018535028992008070088337 79513901271744006052566253)
            ·
              refine ⟨29817712976904002269712345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79513901271744006052566253 29817712976904002269712345)
              ·
                refine ⟨22363284732678001702284259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29817712976904002269712345 22363284732678001702284259)
                ·
                  refine ⟨33544927099017002553426389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22363284732678001702284259 33544927099017002553426389)
                  ·
                    refine ⟨786209228883210997345931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33544927099017002553426389 786209228883210997345931)
                    ·
                      rfl

theorem cell23_4593411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 7].length) (baseStart_4593411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4593411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4593411 prefixEnd_4593411 := by exact prefixLift 4593411
  have htrace : WordTrace (prefixWord ++ tailWord_4593411) baseStart_4593411 baseEnd_4593411 := by
    simpa [prefixWord, tailWord_4593411, baseEnd_4593411] using wordTrace_append hprefix tailTrace_4593411
  have hstable : (prefixWord ++ tailWord_4593411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4593411).length < 2 ^ (prefixWord ++ tailWord_4593411).sum := by decide
  have hdescent : baseEnd_4593411 < baseStart_4593411 := by decide
  rcases family_descends (prefixWord ++ tailWord_4593411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4593468 : List Nat := [2, 2, 2, 2, 1, 1, 2, 1, 3, 4, 3]
def baseStart_4593468 : Nat := 118140960795 + 4593468 * 2 ^ 59
def prefixEnd_4593468 : Nat := 4983230072969 + 3 ^ 40 * 4593468 * 2
def baseEnd_4593468 : Nat := 2358656955046939269025031

theorem tailTrace_4593468 : CollatzResearch.WordTrace tailWord_4593468 prefixEnd_4593468 2358656955046939269025031 := by
  unfold tailWord_4593468
  simp only [CollatzResearch.WordTrace]
  refine ⟨83768770861328706361062529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111691694481771608481416705 83768770861328706361062529)
  ·
    refine ⟨62826578145996529770796897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83768770861328706361062529 62826578145996529770796897)
    ·
      refine ⟨47119933609497397328097673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62826578145996529770796897 47119933609497397328097673)
      ·
        refine ⟨35339950207123047996073255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47119933609497397328097673 35339950207123047996073255)
        ·
          refine ⟨53009925310684571994109883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35339950207123047996073255 53009925310684571994109883)
          ·
            refine ⟨79514887966026857991164825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53009925310684571994109883 79514887966026857991164825)
            ·
              refine ⟨59636165974520143493373619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79514887966026857991164825 59636165974520143493373619)
              ·
                refine ⟨89454248961780215240060429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59636165974520143493373619 89454248961780215240060429)
                ·
                  refine ⟨33545343360667580715022661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 89454248961780215240060429 33545343360667580715022661)
                  ·
                    refine ⟨6289751880125171384066749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33545343360667580715022661 6289751880125171384066749)
                    ·
                      refine ⟨2358656955046939269025031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6289751880125171384066749 2358656955046939269025031)
                      ·
                        rfl

theorem cell23_4593468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 3, 4, 3].length) (baseStart_4593468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4593468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4593468 prefixEnd_4593468 := by exact prefixLift 4593468
  have htrace : WordTrace (prefixWord ++ tailWord_4593468) baseStart_4593468 baseEnd_4593468 := by
    simpa [prefixWord, tailWord_4593468, baseEnd_4593468] using wordTrace_append hprefix tailTrace_4593468
  have hstable : (prefixWord ++ tailWord_4593468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4593468).length < 2 ^ (prefixWord ++ tailWord_4593468).sum := by decide
  have hdescent : baseEnd_4593468 < baseStart_4593468 := by decide
  rcases family_descends (prefixWord ++ tailWord_4593468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4593491 : List Nat := [1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 8]
def baseStart_4593491 : Nat := 118140960795 + 4593491 * 2 ^ 59
def prefixEnd_4593491 : Nat := 4983230072969 + 3 ^ 40 * 4593491 * 2
def baseEnd_4593491 : Nat := 2358668765101992679037425

theorem tailTrace_4593491 : CollatzResearch.WordTrace tailWord_4593491 prefixEnd_4593491 2358668765101992679037425 := by
  unfold tailWord_4593491
  simp only [CollatzResearch.WordTrace]
  refine ⟨167538380601574087650212327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111692253734382725100141551 167538380601574087650212327)
  ·
    refine ⟨251307570902361131475318491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167538380601574087650212327 251307570902361131475318491)
    ·
      refine ⟨376961356353541697212977737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251307570902361131475318491 376961356353541697212977737)
      ·
        refine ⟨282721017265156272909733303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 376961356353541697212977737 282721017265156272909733303)
        ·
          refine ⟨424081525897734409364599955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 282721017265156272909733303 424081525897734409364599955)
          ·
            refine ⟨636122288846601614046899933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 424081525897734409364599955 636122288846601614046899933)
            ·
              refine ⟨238545858317475605267587475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 636122288846601614046899933 238545858317475605267587475)
              ·
                refine ⟨357818787476213407901381213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 238545858317475605267587475 357818787476213407901381213)
                ·
                  refine ⟨134182045303580027963017955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 357818787476213407901381213 134182045303580027963017955)
                  ·
                    refine ⟨201273067955370041944526933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 134182045303580027963017955 201273067955370041944526933)
                    ·
                      refine ⟨2358668765101992679037425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 201273067955370041944526933 2358668765101992679037425)
                      ·
                        rfl

theorem cell23_4593491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 8].length) (baseStart_4593491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4593491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4593491 prefixEnd_4593491 := by exact prefixLift 4593491
  have htrace : WordTrace (prefixWord ++ tailWord_4593491) baseStart_4593491 baseEnd_4593491 := by
    simpa [prefixWord, tailWord_4593491, baseEnd_4593491] using wordTrace_append hprefix tailTrace_4593491
  have hstable : (prefixWord ++ tailWord_4593491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4593491).length < 2 ^ (prefixWord ++ tailWord_4593491).sum := by decide
  have hdescent : baseEnd_4593491 < baseStart_4593491 := by decide
  rcases family_descends (prefixWord ++ tailWord_4593491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4593515 : List Nat := [1, 1, 1, 1, 2, 2, 3, 5, 3, 1, 3]
def baseStart_4593515 : Nat := 118140960795 + 4593515 * 2 ^ 59
def prefixEnd_4593515 : Nat := 4983230072969 + 3 ^ 40 * 4593515 * 2
def baseEnd_4593515 : Nat := 2358681088637700585137315

theorem tailTrace_4593515 : CollatzResearch.WordTrace tailWord_4593515 prefixEnd_4593515 2358681088637700585137315 := by
  unfold tailWord_4593515
  simp only [CollatzResearch.WordTrace]
  refine ⟨167539255953487139749085999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111692837302324759832723999 167539255953487139749085999)
  ·
    refine ⟨251308883930230709623628999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167539255953487139749085999 251308883930230709623628999)
    ·
      refine ⟨376963325895346064435443499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251308883930230709623628999 376963325895346064435443499)
      ·
        refine ⟨565444988843019096653165249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 376963325895346064435443499 565444988843019096653165249)
        ·
          refine ⟨424083741632264322489873937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 565444988843019096653165249 424083741632264322489873937)
          ·
            refine ⟨318062806224198241867405453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 424083741632264322489873937 318062806224198241867405453)
            ·
              refine ⟨119273552334074340700277045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 318062806224198241867405453 119273552334074340700277045)
              ·
                refine ⟨11181895531319469440650973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 119273552334074340700277045 11181895531319469440650973)
                ·
                  refine ⟨4193210824244801040244115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11181895531319469440650973 4193210824244801040244115)
                  ·
                    refine ⟨6289816236367201560366173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4193210824244801040244115 6289816236367201560366173)
                    ·
                      refine ⟨2358681088637700585137315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6289816236367201560366173 2358681088637700585137315)
                      ·
                        rfl

theorem cell23_4593515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5, 3, 1, 3].length) (baseStart_4593515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4593515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4593515 prefixEnd_4593515 := by exact prefixLift 4593515
  have htrace : WordTrace (prefixWord ++ tailWord_4593515) baseStart_4593515 baseEnd_4593515 := by
    simpa [prefixWord, tailWord_4593515, baseEnd_4593515] using wordTrace_append hprefix tailTrace_4593515
  have hstable : (prefixWord ++ tailWord_4593515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4593515).length < 2 ^ (prefixWord ++ tailWord_4593515).sum := by decide
  have hdescent : baseEnd_4593515 < baseStart_4593515 := by decide
  rcases family_descends (prefixWord ++ tailWord_4593515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4593568 : List Nat := [2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 6]
def baseStart_4593568 : Nat := 118140960795 + 4593568 * 2 ^ 59
def prefixEnd_4593568 : Nat := 4983230072969 + 3 ^ 40 * 4593568 * 2
def baseEnd_4593568 : Nat := 2358708303112388877774571

theorem tailTrace_4593568 : CollatzResearch.WordTrace tailWord_4593568 prefixEnd_4593568 2358708303112388877774571 := by
  unfold tailWord_4593568
  simp only [CollatzResearch.WordTrace]
  refine ⟨83770594511147564900382679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111694126014863419867176905 83770594511147564900382679)
  ·
    refine ⟨125655891766721347350574019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83770594511147564900382679 125655891766721347350574019)
    ·
      refine ⟨188483837650082021025861029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125655891766721347350574019 188483837650082021025861029)
      ·
        refine ⟨35340719559390378942348943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 188483837650082021025861029 35340719559390378942348943)
        ·
          refine ⟨53011079339085568413523415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35340719559390378942348943 53011079339085568413523415)
          ·
            refine ⟨79516619008628352620285123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53011079339085568413523415 79516619008628352620285123)
            ·
              refine ⟨119274928512942528930427685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79516619008628352620285123 119274928512942528930427685)
              ·
                refine ⟨22364049096176724174455191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 119274928512942528930427685 22364049096176724174455191)
                ·
                  refine ⟨33546073644265086261682787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22364049096176724174455191 33546073644265086261682787)
                  ·
                    refine ⟨50319110466397629392524181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33546073644265086261682787 50319110466397629392524181)
                    ·
                      refine ⟨2358708303112388877774571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50319110466397629392524181 2358708303112388877774571)
                      ·
                        rfl

theorem cell23_4593568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_4593568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4593568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4593568 prefixEnd_4593568 := by exact prefixLift 4593568
  have htrace : WordTrace (prefixWord ++ tailWord_4593568) baseStart_4593568 baseEnd_4593568 := by
    simpa [prefixWord, tailWord_4593568, baseEnd_4593568] using wordTrace_append hprefix tailTrace_4593568
  have hstable : (prefixWord ++ tailWord_4593568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4593568).length < 2 ^ (prefixWord ++ tailWord_4593568).sum := by decide
  have hdescent : baseEnd_4593568 < baseStart_4593568 := by decide
  rcases family_descends (prefixWord ++ tailWord_4593568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4593575 : List Nat := [1, 1, 6, 1, 2, 1, 1, 1, 3, 1, 5]
def baseStart_4593575 : Nat := 118140960795 + 4593575 * 2 ^ 59
def prefixEnd_4593575 : Nat := 4983230072969 + 3 ^ 40 * 4593575 * 2
def baseEnd_4593575 : Nat := 2358711897476970350387039

theorem tailTrace_4593575 : CollatzResearch.WordTrace tailWord_4593575 prefixEnd_4593575 2358711897476970350387039 := by
  unfold tailWord_4593575
  simp only [CollatzResearch.WordTrace]
  refine ⟨167541444333269769996270179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111694296222179846664180119 167541444333269769996270179)
  ·
    refine ⟨251312166499904654994405269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167541444333269769996270179 251312166499904654994405269)
    ·
      refine ⟨11780257804683030702862747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 251312166499904654994405269 11780257804683030702862747)
      ·
        refine ⟨17670386707024546054294121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11780257804683030702862747 17670386707024546054294121)
        ·
          refine ⟨13252790030268409540720591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17670386707024546054294121 13252790030268409540720591)
          ·
            refine ⟨19879185045402614311080887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13252790030268409540720591 19879185045402614311080887)
            ·
              refine ⟨29818777568103921466621331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19879185045402614311080887 29818777568103921466621331)
              ·
                refine ⟨44728166352155882199931997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29818777568103921466621331 44728166352155882199931997)
                ·
                  refine ⟨16773062382058455824974499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44728166352155882199931997 16773062382058455824974499)
                  ·
                    refine ⟨25159593573087683737461749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16773062382058455824974499 25159593573087683737461749)
                    ·
                      refine ⟨2358711897476970350387039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25159593573087683737461749 2358711897476970350387039)
                      ·
                        rfl

theorem cell23_4593575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_4593575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4593575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4593575 prefixEnd_4593575 := by exact prefixLift 4593575
  have htrace : WordTrace (prefixWord ++ tailWord_4593575) baseStart_4593575 baseEnd_4593575 := by
    simpa [prefixWord, tailWord_4593575, baseEnd_4593575] using wordTrace_append hprefix tailTrace_4593575
  have hstable : (prefixWord ++ tailWord_4593575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4593575).length < 2 ^ (prefixWord ++ tailWord_4593575).sum := by decide
  have hdescent : baseEnd_4593575 < baseStart_4593575 := by decide
  rcases family_descends (prefixWord ++ tailWord_4593575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4593585 : List Nat := [1, 2, 2, 4, 2, 2, 1, 1, 1, 1, 6]
def baseStart_4593585 : Nat := 118140960795 + 4593585 * 2 ^ 59
def prefixEnd_4593585 : Nat := 4983230072969 + 3 ^ 40 * 4593585 * 2
def baseEnd_4593585 : Nat := 2358717032283515311261993

theorem tailTrace_4593585 : CollatzResearch.WordTrace tailWord_4593585 prefixEnd_4593585 2358717032283515311261993 := by
  unfold tailWord_4593585
  simp only [CollatzResearch.WordTrace]
  refine ⟨167541809063233541704134209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111694539375489027802756139 167541809063233541704134209)
  ·
    refine ⟨125656356797425156278100657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167541809063233541704134209 125656356797425156278100657)
    ·
      refine ⟨94242267598068867208575493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125656356797425156278100657 94242267598068867208575493)
      ·
        refine ⟨17670425174637912601607905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94242267598068867208575493 17670425174637912601607905)
        ·
          refine ⟨13252818880978434451205929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17670425174637912601607905 13252818880978434451205929)
          ·
            refine ⟨9939614160733825838404447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13252818880978434451205929 9939614160733825838404447)
            ·
              refine ⟨14909421241100738757606671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9939614160733825838404447 14909421241100738757606671)
              ·
                refine ⟨22364131861651108136410007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14909421241100738757606671 22364131861651108136410007)
                ·
                  refine ⟨33546197792476662204615011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22364131861651108136410007 33546197792476662204615011)
                  ·
                    refine ⟨50319296688714993306922517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33546197792476662204615011 50319296688714993306922517)
                    ·
                      refine ⟨2358717032283515311261993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50319296688714993306922517 2358717032283515311261993)
                      ·
                        rfl

theorem cell23_4593585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_4593585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4593585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4593585 prefixEnd_4593585 := by exact prefixLift 4593585
  have htrace : WordTrace (prefixWord ++ tailWord_4593585) baseStart_4593585 baseEnd_4593585 := by
    simpa [prefixWord, tailWord_4593585, baseEnd_4593585] using wordTrace_append hprefix tailTrace_4593585
  have hstable : (prefixWord ++ tailWord_4593585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4593585).length < 2 ^ (prefixWord ++ tailWord_4593585).sum := by decide
  have hdescent : baseEnd_4593585 < baseStart_4593585 := by decide
  rcases family_descends (prefixWord ++ tailWord_4593585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4593589 : List Nat := [1, 3, 3, 2, 1, 2, 2, 2, 3, 2, 2]
def baseStart_4593589 : Nat := 118140960795 + 4593589 * 2 ^ 59
def prefixEnd_4593589 : Nat := 4983230072969 + 3 ^ 40 * 4593589 * 2
def baseEnd_4593589 : Nat := 2358719086206133295611975

theorem tailTrace_4593589 : CollatzResearch.WordTrace tailWord_4593589 prefixEnd_4593589 2358719086206133295611975 := by
  unfold tailWord_4593589
  simp only [CollatzResearch.WordTrace]
  refine ⟨167541954955219050387279821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111694636636812700258186547 167541954955219050387279821)
  ·
    refine ⟨62828233108207143895229933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167541954955219050387279821 62828233108207143895229933)
    ·
      refine ⟨23560587415577678960711225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62828233108207143895229933 23560587415577678960711225)
      ·
        refine ⟨17670440561683259220533419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23560587415577678960711225 17670440561683259220533419)
        ·
          refine ⟨26505660842524888830800129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17670440561683259220533419 26505660842524888830800129)
          ·
            refine ⟨19879245631893666623100097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26505660842524888830800129 19879245631893666623100097)
            ·
              refine ⟨14909434223920249967325073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19879245631893666623100097 14909434223920249967325073)
              ·
                refine ⟨11182075667940187475493805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14909434223920249967325073 11182075667940187475493805)
                ·
                  refine ⟨4193278375477570303310177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11182075667940187475493805 4193278375477570303310177)
                  ·
                    refine ⟨3144958781608177727482633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4193278375477570303310177 3144958781608177727482633)
                    ·
                      refine ⟨2358719086206133295611975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3144958781608177727482633 2358719086206133295611975)
                      ·
                        rfl

theorem cell23_4593589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 2, 3, 2, 2].length) (baseStart_4593589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4593589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4593589 prefixEnd_4593589 := by exact prefixLift 4593589
  have htrace : WordTrace (prefixWord ++ tailWord_4593589) baseStart_4593589 baseEnd_4593589 := by
    simpa [prefixWord, tailWord_4593589, baseEnd_4593589] using wordTrace_append hprefix tailTrace_4593589
  have hstable : (prefixWord ++ tailWord_4593589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4593589).length < 2 ^ (prefixWord ++ tailWord_4593589).sum := by decide
  have hdescent : baseEnd_4593589 < baseStart_4593589 := by decide
  rcases family_descends (prefixWord ++ tailWord_4593589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4593592 : List Nat := [2, 1, 2, 1, 2, 3, 4, 2, 1, 2, 3]
def baseStart_4593592 : Nat := 118140960795 + 4593592 * 2 ^ 59
def prefixEnd_4593592 : Nat := 4983230072969 + 3 ^ 40 * 4593592 * 2
def baseEnd_4593592 : Nat := 2358720626648096783874461

theorem tailTrace_4593592 : CollatzResearch.WordTrace tailWord_4593592 prefixEnd_4593592 2358720626648096783874461 := by
  unfold tailWord_4593592
  simp only [CollatzResearch.WordTrace]
  refine ⟨83771032187104090949819515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111694709582805454599759353 83771032187104090949819515)
  ·
    refine ⟨125656548280656136424729273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83771032187104090949819515 125656548280656136424729273)
    ·
      refine ⟨94242411210492102318546955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125656548280656136424729273 94242411210492102318546955)
      ·
        refine ⟨141363616815738153477820433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94242411210492102318546955 141363616815738153477820433)
        ·
          refine ⟨106022712611803615108365325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141363616815738153477820433 106022712611803615108365325)
          ·
            refine ⟨39758517229426355665636997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106022712611803615108365325 39758517229426355665636997)
            ·
              refine ⟨7454721980517441687306937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39758517229426355665636997 7454721980517441687306937)
              ·
                refine ⟨5591041485388081265480203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7454721980517441687306937 5591041485388081265480203)
                ·
                  refine ⟨8386562228082121898220305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5591041485388081265480203 8386562228082121898220305)
                  ·
                    refine ⟨6289921671061591423665229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8386562228082121898220305 6289921671061591423665229)
                    ·
                      refine ⟨2358720626648096783874461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6289921671061591423665229 2358720626648096783874461)
                      ·
                        rfl

theorem cell23_4593592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 2, 1, 2, 3].length) (baseStart_4593592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4593592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4593592 prefixEnd_4593592 := by exact prefixLift 4593592
  have htrace : WordTrace (prefixWord ++ tailWord_4593592) baseStart_4593592 baseEnd_4593592 := by
    simpa [prefixWord, tailWord_4593592, baseEnd_4593592] using wordTrace_append hprefix tailTrace_4593592
  have hstable : (prefixWord ++ tailWord_4593592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4593592).length < 2 ^ (prefixWord ++ tailWord_4593592).sum := by decide
  have hdescent : baseEnd_4593592 < baseStart_4593592 := by decide
  rcases family_descends (prefixWord ++ tailWord_4593592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4593649 : List Nat := [1, 2, 2, 2, 5, 1, 1, 1, 3, 3, 2]
def baseStart_4593649 : Nat := 118140960795 + 4593649 * 2 ^ 59
def prefixEnd_4593649 : Nat := 4983230072969 + 3 ^ 40 * 4593649 * 2
def baseEnd_4593649 : Nat := 2358749895045403060861699

theorem tailTrace_4593649 : CollatzResearch.WordTrace tailWord_4593649 prefixEnd_4593649 2358749895045403060861699 := by
  unfold tailWord_4593649
  simp only [CollatzResearch.WordTrace]
  refine ⟨167544143335001680634464001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111696095556667787089642667 167544143335001680634464001)
  ·
    refine ⟨125658107501251260475848001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167544143335001680634464001 125658107501251260475848001)
    ·
      refine ⟨94243580625938445356886001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125658107501251260475848001 94243580625938445356886001)
      ·
        refine ⟨70682685469453834017664501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94243580625938445356886001 70682685469453834017664501)
        ·
          refine ⟨6626501762761296939156047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 70682685469453834017664501 6626501762761296939156047)
          ·
            refine ⟨9939752644141945408734071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6626501762761296939156047 9939752644141945408734071)
            ·
              refine ⟨14909628966212918113101107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9939752644141945408734071 14909628966212918113101107)
              ·
                refine ⟨22364443449319377169651661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14909628966212918113101107 22364443449319377169651661)
                ·
                  refine ⟨8386666293494766438619373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22364443449319377169651661 8386666293494766438619373)
                  ·
                    refine ⟨3144999860060537414482265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8386666293494766438619373 3144999860060537414482265)
                    ·
                      refine ⟨2358749895045403060861699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3144999860060537414482265 2358749895045403060861699)
                      ·
                        rfl

theorem cell23_4593649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 3, 3, 2].length) (baseStart_4593649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4593649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4593649 prefixEnd_4593649 := by exact prefixLift 4593649
  have htrace : WordTrace (prefixWord ++ tailWord_4593649) baseStart_4593649 baseEnd_4593649 := by
    simpa [prefixWord, tailWord_4593649, baseEnd_4593649] using wordTrace_append hprefix tailTrace_4593649
  have hstable : (prefixWord ++ tailWord_4593649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4593649).length < 2 ^ (prefixWord ++ tailWord_4593649).sum := by decide
  have hdescent : baseEnd_4593649 < baseStart_4593649 := by decide
  rcases family_descends (prefixWord ++ tailWord_4593649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4593665 : List Nat := [1, 2, 4, 1, 2, 1, 1, 3, 2, 1, 5]
def baseStart_4593665 : Nat := 118140960795 + 4593665 * 2 ^ 59
def prefixEnd_4593665 : Nat := 4983230072969 + 3 ^ 40 * 4593665 * 2
def baseEnd_4593665 : Nat := 2358758110735874998261625

theorem tailTrace_4593665 : CollatzResearch.WordTrace tailWord_4593665 prefixEnd_4593665 2358758110735874998261625 := by
  unfold tailWord_4593665
  simp only [CollatzResearch.WordTrace]
  refine ⟨167544726902943715367046449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111696484601962476911364299 167544726902943715367046449)
  ·
    refine ⟨125658545177207786525284837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167544726902943715367046449 125658545177207786525284837)
    ·
      refine ⟨23560977220726459973490907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 125658545177207786525284837 23560977220726459973490907)
      ·
        refine ⟨35341465831089689960236361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23560977220726459973490907 35341465831089689960236361)
        ·
          refine ⟨26506099373317267470177271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35341465831089689960236361 26506099373317267470177271)
          ·
            refine ⟨39759149059975901205265907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26506099373317267470177271 39759149059975901205265907)
            ·
              refine ⟨59638723589963851807898861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39759149059975901205265907 59638723589963851807898861)
              ·
                refine ⟨22364521346236444427962073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59638723589963851807898861 22364521346236444427962073)
                ·
                  refine ⟨16773391009677333320971555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22364521346236444427962073 16773391009677333320971555)
                  ·
                    refine ⟨25160086514515999981457333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16773391009677333320971555 25160086514515999981457333)
                    ·
                      refine ⟨2358758110735874998261625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25160086514515999981457333 2358758110735874998261625)
                      ·
                        rfl

theorem cell23_4593665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_4593665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4593665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4593665 prefixEnd_4593665 := by exact prefixLift 4593665
  have htrace : WordTrace (prefixWord ++ tailWord_4593665) baseStart_4593665 baseEnd_4593665 := by
    simpa [prefixWord, tailWord_4593665, baseEnd_4593665] using wordTrace_append hprefix tailTrace_4593665
  have hstable : (prefixWord ++ tailWord_4593665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4593665).length < 2 ^ (prefixWord ++ tailWord_4593665).sum := by decide
  have hdescent : baseEnd_4593665 < baseStart_4593665 := by decide
  rcases family_descends (prefixWord ++ tailWord_4593665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4593675 : List Nat := [1, 1, 1, 1, 6, 1, 2, 2, 2, 2, 4]
def baseStart_4593675 : Nat := 118140960795 + 4593675 * 2 ^ 59
def prefixEnd_4593675 : Nat := 4983230072969 + 3 ^ 40 * 4593675 * 2
def baseEnd_4593675 : Nat := 2358763245542419959136579

theorem tailTrace_4593675 : CollatzResearch.WordTrace tailWord_4593675 prefixEnd_4593675 2358763245542419959136579 := by
  unfold tailWord_4593675
  simp only [CollatzResearch.WordTrace]
  refine ⟨167545091632907487074910479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111696727755271658049940319 167545091632907487074910479)
  ·
    refine ⟨251317637449361230612365719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167545091632907487074910479 251317637449361230612365719)
    ·
      refine ⟨376976456174041845918548579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251317637449361230612365719 376976456174041845918548579)
      ·
        refine ⟨565464684261062768877822869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 376976456174041845918548579 565464684261062768877822869)
        ·
          refine ⟨26506157074737317291147947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 565464684261062768877822869 26506157074737317291147947)
          ·
            refine ⟨39759235612105975936721921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26506157074737317291147947 39759235612105975936721921)
            ·
              refine ⟨29819426709079481952541441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39759235612105975936721921 29819426709079481952541441)
              ·
                refine ⟨22364570031809611464406081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29819426709079481952541441 22364570031809611464406081)
                ·
                  refine ⟨16773427523857208598304561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22364570031809611464406081 16773427523857208598304561)
                  ·
                    refine ⟨12580070642892906448728421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16773427523857208598304561 12580070642892906448728421)
                    ·
                      refine ⟨2358763245542419959136579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12580070642892906448728421 2358763245542419959136579)
                      ·
                        rfl

theorem cell23_4593675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 2, 2, 4].length) (baseStart_4593675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4593675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4593675 prefixEnd_4593675 := by exact prefixLift 4593675
  have htrace : WordTrace (prefixWord ++ tailWord_4593675) baseStart_4593675 baseEnd_4593675 := by
    simpa [prefixWord, tailWord_4593675, baseEnd_4593675] using wordTrace_append hprefix tailTrace_4593675
  have hstable : (prefixWord ++ tailWord_4593675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4593675).length < 2 ^ (prefixWord ++ tailWord_4593675).sum := by decide
  have hdescent : baseEnd_4593675 < baseStart_4593675 := by decide
  rcases family_descends (prefixWord ++ tailWord_4593675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4593692 : List Nat := [2, 2, 3, 1, 3, 2, 1, 1, 2, 2, 4]
def baseStart_4593692 : Nat := 118140960795 + 4593692 * 2 ^ 59
def prefixEnd_4593692 : Nat := 4983230072969 + 3 ^ 40 * 4593692 * 2
def baseEnd_4593692 : Nat := 2358771974713546392624001

theorem tailTrace_4593692 : CollatzResearch.WordTrace tailWord_4593692 prefixEnd_4593692 2358771974713546392624001 := by
  unfold tailWord_4593692
  simp only [CollatzResearch.WordTrace]
  refine ⟨83772855836922949489139665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111697141115897265985519553 83772855836922949489139665)
  ·
    refine ⟨62829641877692212116854749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83772855836922949489139665 62829641877692212116854749)
    ·
      refine ⟨23561115704134579543820531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62829641877692212116854749 23561115704134579543820531)
      ·
        refine ⟨35341673556201869315730797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23561115704134579543820531 35341673556201869315730797)
        ·
          refine ⟨13253127583575700993399049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35341673556201869315730797 13253127583575700993399049)
          ·
            refine ⟨9939845687681775745049287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13253127583575700993399049 9939845687681775745049287)
            ·
              refine ⟨14909768531522663617573931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9939845687681775745049287 14909768531522663617573931)
              ·
                refine ⟨22364652797283995426360897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14909768531522663617573931 22364652797283995426360897)
                ·
                  refine ⟨16773489597962996569770673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22364652797283995426360897 16773489597962996569770673)
                  ·
                    refine ⟨12580117198472247427328005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16773489597962996569770673 12580117198472247427328005)
                    ·
                      refine ⟨2358771974713546392624001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12580117198472247427328005 2358771974713546392624001)
                      ·
                        rfl

theorem cell23_4593692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_4593692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4593692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4593692 prefixEnd_4593692 := by exact prefixLift 4593692
  have htrace : WordTrace (prefixWord ++ tailWord_4593692) baseStart_4593692 baseEnd_4593692 := by
    simpa [prefixWord, tailWord_4593692, baseEnd_4593692] using wordTrace_append hprefix tailTrace_4593692
  have hstable : (prefixWord ++ tailWord_4593692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4593692).length < 2 ^ (prefixWord ++ tailWord_4593692).sum := by decide
  have hdescent : baseEnd_4593692 < baseStart_4593692 := by decide
  rcases family_descends (prefixWord ++ tailWord_4593692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4593772 : List Nat := [2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 3]
def baseStart_4593772 : Nat := 118140960795 + 4593772 * 2 ^ 59
def prefixEnd_4593772 : Nat := 4983230072969 + 3 ^ 40 * 4593772 * 2
def baseEnd_4593772 : Nat := 2358813053165906079623633

theorem tailTrace_4593772 : CollatzResearch.WordTrace tailWord_4593772 prefixEnd_4593772 2358813053165906079623633 := by
  unfold tailWord_4593772
  simp only [CollatzResearch.WordTrace]
  refine ⟨83774314756778036320595785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111699086342370715094127713 83774314756778036320595785)
  ·
    refine ⟨62830736067583527240446839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83774314756778036320595785 62830736067583527240446839)
    ·
      refine ⟨94246104101375290860670259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62830736067583527240446839 94246104101375290860670259)
      ·
        refine ⟨141369156152062936291005389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94246104101375290860670259 141369156152062936291005389)
        ·
          refine ⟨53013433557023601109127021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 141369156152062936291005389 53013433557023601109127021)
          ·
            refine ⟨19880037583883850415922633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53013433557023601109127021 19880037583883850415922633)
            ·
              refine ⟨14910028187912887811941975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19880037583883850415922633 14910028187912887811941975)
              ·
                refine ⟨22365042281869331717912963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14910028187912887811941975 22365042281869331717912963)
                ·
                  refine ⟨33547563422803997576869445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22365042281869331717912963 33547563422803997576869445)
                  ·
                    refine ⟨6290168141775749545663021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33547563422803997576869445 6290168141775749545663021)
                    ·
                      refine ⟨2358813053165906079623633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6290168141775749545663021 2358813053165906079623633)
                      ·
                        rfl

theorem cell23_4593772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 3].length) (baseStart_4593772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4593772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4593772 prefixEnd_4593772 := by exact prefixLift 4593772
  have htrace : WordTrace (prefixWord ++ tailWord_4593772) baseStart_4593772 baseEnd_4593772 := by
    simpa [prefixWord, tailWord_4593772, baseEnd_4593772] using wordTrace_append hprefix tailTrace_4593772
  have hstable : (prefixWord ++ tailWord_4593772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4593772).length < 2 ^ (prefixWord ++ tailWord_4593772).sum := by decide
  have hdescent : baseEnd_4593772 < baseStart_4593772 := by decide
  rcases family_descends (prefixWord ++ tailWord_4593772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4593775 : List Nat := [1, 1, 2, 1, 3, 4, 1, 2, 8]
def baseStart_4593775 : Nat := 118140960795 + 4593775 * 2 ^ 59
def prefixEnd_4593775 : Nat := 4983230072969 + 3 ^ 40 * 4593775 * 2
def baseEnd_4593775 : Nat := 262090510400874396431791

theorem tailTrace_4593775 : CollatzResearch.WordTrace tailWord_4593775 prefixEnd_4593775 262090510400874396431791 := by
  unfold tailWord_4593775
  simp only [CollatzResearch.WordTrace]
  refine ⟨167548738932545204153550779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111699159288363469435700519 167548738932545204153550779)
  ·
    refine ⟨251323108398817806230326169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167548738932545204153550779 251323108398817806230326169)
    ·
      refine ⟨188492331299113354672744627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 251323108398817806230326169 188492331299113354672744627)
      ·
        refine ⟨282738496948670032009116941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188492331299113354672744627 282738496948670032009116941)
        ·
          refine ⟨106026936355751262003418853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 282738496948670032009116941 106026936355751262003418853)
          ·
            refine ⟨19880050566703361625641035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 106026936355751262003418853 19880050566703361625641035)
            ·
              refine ⟨29820075850055042438461553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19880050566703361625641035 29820075850055042438461553)
              ·
                refine ⟨22365056887541281828846165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29820075850055042438461553 22365056887541281828846165)
                ·
                  refine ⟨262090510400874396431791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22365056887541281828846165 262090510400874396431791)
                  ·
                    rfl

theorem cell23_4593775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 8].length) (baseStart_4593775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4593775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4593775 prefixEnd_4593775 := by exact prefixLift 4593775
  have htrace : WordTrace (prefixWord ++ tailWord_4593775) baseStart_4593775 baseEnd_4593775 := by
    simpa [prefixWord, tailWord_4593775, baseEnd_4593775] using wordTrace_append hprefix tailTrace_4593775
  have hstable : (prefixWord ++ tailWord_4593775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4593775).length < 2 ^ (prefixWord ++ tailWord_4593775).sum := by decide
  have hdescent : baseEnd_4593775 < baseStart_4593775 := by decide
  rcases family_descends (prefixWord ++ tailWord_4593775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4593789 : List Nat := [1, 4, 1, 1, 3, 3, 1, 2, 2, 2, 3]
def baseStart_4593789 : Nat := 118140960795 + 4593789 * 2 ^ 59
def prefixEnd_4593789 : Nat := 4983230072969 + 3 ^ 40 * 4593789 * 2
def baseEnd_4593789 : Nat := 2358821782337032513111055

theorem tailTrace_4593789 : CollatzResearch.WordTrace tailWord_4593789 prefixEnd_4593789 2358821782337032513111055 := by
  unfold tailWord_4593789
  simp only [CollatzResearch.WordTrace]
  refine ⟨167549249554494484544560421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111699499702996323029706947 167549249554494484544560421)
  ·
    refine ⟨31415484291467715852105079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 167549249554494484544560421 31415484291467715852105079)
    ·
      refine ⟨47123226437201573778157619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31415484291467715852105079 47123226437201573778157619)
      ·
        refine ⟨70684839655802360667236429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47123226437201573778157619 70684839655802360667236429)
        ·
          refine ⟨26506814870925885250213661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70684839655802360667236429 26506814870925885250213661)
          ·
            refine ⟨9940055576597206968830123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26506814870925885250213661 9940055576597206968830123)
            ·
              refine ⟨14910083364895810453245185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9940055576597206968830123 14910083364895810453245185)
              ·
                refine ⟨11182562523671857839933889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14910083364895810453245185 11182562523671857839933889)
                ·
                  refine ⟨8386921892753893379950417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11182562523671857839933889 8386921892753893379950417)
                  ·
                    refine ⟨6290191419565420034962813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8386921892753893379950417 6290191419565420034962813)
                    ·
                      refine ⟨2358821782337032513111055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6290191419565420034962813 2358821782337032513111055)
                      ·
                        rfl

theorem cell23_4593789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 2, 2, 2, 3].length) (baseStart_4593789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4593789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4593789 prefixEnd_4593789 := by exact prefixLift 4593789
  have htrace : WordTrace (prefixWord ++ tailWord_4593789) baseStart_4593789 baseEnd_4593789 := by
    simpa [prefixWord, tailWord_4593789, baseEnd_4593789] using wordTrace_append hprefix tailTrace_4593789
  have hstable : (prefixWord ++ tailWord_4593789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4593789).length < 2 ^ (prefixWord ++ tailWord_4593789).sum := by decide
  have hdescent : baseEnd_4593789 < baseStart_4593789 := by decide
  rcases family_descends (prefixWord ++ tailWord_4593789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4593865 : List Nat := [1, 2, 1, 1, 2, 1, 1, 14]
def baseStart_4593865 : Nat := 118140960795 + 4593865 * 2 ^ 59
def prefixEnd_4593865 : Nat := 4983230072969 + 3 ^ 40 * 4593865 * 2
def baseEnd_4593865 : Nat := 87365215069139785768915

theorem tailTrace_4593865 : CollatzResearch.WordTrace tailWord_4593865 prefixEnd_4593865 87365215069139785768915 := by
  unfold tailWord_4593865
  simp only [CollatzResearch.WordTrace]
  refine ⟨167552021502219149524327049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111701347668146099682884699 167552021502219149524327049)
  ·
    refine ⟨125664016126664362143245287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167552021502219149524327049 125664016126664362143245287)
    ·
      refine ⟨188496024189996543214867931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125664016126664362143245287 188496024189996543214867931)
      ·
        refine ⟨282744036284994814822301897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188496024189996543214867931 282744036284994814822301897)
        ·
          refine ⟨212058027213746111116726423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 282744036284994814822301897 212058027213746111116726423)
          ·
            refine ⟨318087040820619166675089635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212058027213746111116726423 318087040820619166675089635)
            ·
              refine ⟨477130561230928750012634453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 318087040820619166675089635 477130561230928750012634453)
              ·
                refine ⟨87365215069139785768915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 14 477130561230928750012634453 87365215069139785768915)
                ·
                  rfl

theorem cell23_4593865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 14].length) (baseStart_4593865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4593865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4593865 prefixEnd_4593865 := by exact prefixLift 4593865
  have htrace : WordTrace (prefixWord ++ tailWord_4593865) baseStart_4593865 baseEnd_4593865 := by
    simpa [prefixWord, tailWord_4593865, baseEnd_4593865] using wordTrace_append hprefix tailTrace_4593865
  have hstable : (prefixWord ++ tailWord_4593865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4593865).length < 2 ^ (prefixWord ++ tailWord_4593865).sum := by decide
  have hdescent : baseEnd_4593865 < baseStart_4593865 := by decide
  rcases family_descends (prefixWord ++ tailWord_4593865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4593879 : List Nat := [1, 1, 3, 2, 1, 2, 1, 6, 1, 2, 3]
def baseStart_4593879 : Nat := 118140960795 + 4593879 * 2 ^ 59
def prefixEnd_4593879 : Nat := 4983230072969 + 3 ^ 40 * 4593879 * 2
def baseEnd_4593879 : Nat := 2358867995595937160985641

theorem tailTrace_4593879 : CollatzResearch.WordTrace tailWord_4593879 prefixEnd_4593879 2358867995595937160985641 := by
  unfold tailWord_4593879
  simp only [CollatzResearch.WordTrace]
  refine ⟨167552532124168429915336691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111701688082778953276891127 167552532124168429915336691)
  ·
    refine ⟨251328798186252644873005037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167552532124168429915336691 251328798186252644873005037)
    ·
      refine ⟨94248299319844741827376889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 251328798186252644873005037 94248299319844741827376889)
      ·
        refine ⟨70686224489883556370532667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94248299319844741827376889 70686224489883556370532667)
        ·
          refine ⟨106029336734825334555799001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70686224489883556370532667 106029336734825334555799001)
          ·
            refine ⟨79522002551119000916849251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106029336734825334555799001 79522002551119000916849251)
            ·
              refine ⟨119283003826678501375273877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79522002551119000916849251 119283003826678501375273877)
              ·
                refine ⟨5591390804375554751965963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 119283003826678501375273877 5591390804375554751965963)
                ·
                  refine ⟨8387086206563332127948945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5591390804375554751965963 8387086206563332127948945)
                  ·
                    refine ⟨6290314654922499095961709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8387086206563332127948945 6290314654922499095961709)
                    ·
                      refine ⟨2358867995595937160985641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6290314654922499095961709 2358867995595937160985641)
                      ·
                        rfl

theorem cell23_4593879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 6, 1, 2, 3].length) (baseStart_4593879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4593879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4593879 prefixEnd_4593879 := by exact prefixLift 4593879
  have htrace : WordTrace (prefixWord ++ tailWord_4593879) baseStart_4593879 baseEnd_4593879 := by
    simpa [prefixWord, tailWord_4593879, baseEnd_4593879] using wordTrace_append hprefix tailTrace_4593879
  have hstable : (prefixWord ++ tailWord_4593879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4593879).length < 2 ^ (prefixWord ++ tailWord_4593879).sum := by decide
  have hdescent : baseEnd_4593879 < baseStart_4593879 := by decide
  rcases family_descends (prefixWord ++ tailWord_4593879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4593890 : List Nat := [3, 3, 4, 1, 1, 1, 1, 3, 1, 5]
def baseStart_4593890 : Nat := 118140960795 + 4593890 * 2 ^ 59
def prefixEnd_4593890 : Nat := 4983230072969 + 3 ^ 40 * 4593890 * 2
def baseEnd_4593890 : Nat := 786291214627712205982697

theorem tailTrace_4593890 : CollatzResearch.WordTrace tailWord_4593890 prefixEnd_4593890 786291214627712205982697 := by
  unfold tailWord_4593890
  simp only [CollatzResearch.WordTrace]
  refine ⟨41888233331782144698496781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111701955551419052529324749 41888233331782144698496781)
  ·
    refine ⟨15708087499418304261936293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41888233331782144698496781 15708087499418304261936293)
    ·
      refine ⟨2945266406140932049113055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15708087499418304261936293 2945266406140932049113055)
      ·
        refine ⟨4417899609211398073669583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2945266406140932049113055 4417899609211398073669583)
        ·
          refine ⟨6626849413817097110504375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4417899609211398073669583 6626849413817097110504375)
          ·
            refine ⟨9940274120725645665756563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6626849413817097110504375 9940274120725645665756563)
            ·
              refine ⟨14910411181088468498634845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9940274120725645665756563 14910411181088468498634845)
              ·
                refine ⟨5591404192908175686988067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14910411181088468498634845 5591404192908175686988067)
                ·
                  refine ⟨8387106289362263530482101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5591404192908175686988067 8387106289362263530482101)
                  ·
                    refine ⟨786291214627712205982697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8387106289362263530482101 786291214627712205982697)
                    ·
                      rfl

theorem cell23_4593890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_4593890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4593890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4593890 prefixEnd_4593890 := by exact prefixLift 4593890
  have htrace : WordTrace (prefixWord ++ tailWord_4593890) baseStart_4593890 baseEnd_4593890 := by
    simpa [prefixWord, tailWord_4593890, baseEnd_4593890] using wordTrace_append hprefix tailTrace_4593890
  have hstable : (prefixWord ++ tailWord_4593890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4593890).length < 2 ^ (prefixWord ++ tailWord_4593890).sum := by decide
  have hdescent : baseEnd_4593890 < baseStart_4593890 := by decide
  rcases family_descends (prefixWord ++ tailWord_4593890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4593893 : List Nat := [1, 3, 1, 4, 2, 3, 2, 1, 1, 1, 4]
def baseStart_4593893 : Nat := 118140960795 + 4593893 * 2 ^ 59
def prefixEnd_4593893 : Nat := 4983230072969 + 3 ^ 40 * 4593893 * 2
def baseEnd_4593893 : Nat := 2358875184325100106210577

theorem tailTrace_4593893 : CollatzResearch.WordTrace tailWord_4593893 prefixEnd_4593893 2358875184325100106210577 := by
  unfold tailWord_4593893
  simp only [CollatzResearch.WordTrace]
  refine ⟨167553042746117710306346333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111702028497411806870897555 167553042746117710306346333)
  ·
    refine ⟨62832391029794141364879875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167553042746117710306346333 62832391029794141364879875)
    ·
      refine ⟨94248586544691212047319813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62832391029794141364879875 94248586544691212047319813)
      ·
        refine ⟨17671609977129602258872465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94248586544691212047319813 17671609977129602258872465)
        ·
          refine ⟨13253707482847201694154349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17671609977129602258872465 13253707482847201694154349)
          ·
            refine ⟨4970140306067700635307881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13253707482847201694154349 4970140306067700635307881)
            ·
              refine ⟨3727605229550775476480911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4970140306067700635307881 3727605229550775476480911)
              ·
                refine ⟨5591407844326163214721367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3727605229550775476480911 5591407844326163214721367)
                ·
                  refine ⟨8387111766489244822082051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5591407844326163214721367 8387111766489244822082051)
                  ·
                    refine ⟨12580667649733867233123077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8387111766489244822082051 12580667649733867233123077)
                    ·
                      refine ⟨2358875184325100106210577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12580667649733867233123077 2358875184325100106210577)
                      ·
                        rfl

theorem cell23_4593893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 2, 1, 1, 1, 4].length) (baseStart_4593893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4593893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4593893 prefixEnd_4593893 := by exact prefixLift 4593893
  have htrace : WordTrace (prefixWord ++ tailWord_4593893) baseStart_4593893 baseEnd_4593893 := by
    simpa [prefixWord, tailWord_4593893, baseEnd_4593893] using wordTrace_append hprefix tailTrace_4593893
  have hstable : (prefixWord ++ tailWord_4593893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4593893).length < 2 ^ (prefixWord ++ tailWord_4593893).sum := by decide
  have hdescent : baseEnd_4593893 < baseStart_4593893 := by decide
  rcases family_descends (prefixWord ++ tailWord_4593893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4593896 : List Nat := [2, 1, 4, 1, 2, 3, 1, 3, 1, 2, 3]
def baseStart_4593896 : Nat := 118140960795 + 4593896 * 2 ^ 59
def prefixEnd_4593896 : Nat := 4983230072969 + 3 ^ 40 * 4593896 * 2
def baseEnd_4593896 : Nat := 2358876724767063594473063

theorem tailTrace_4593896 : CollatzResearch.WordTrace tailWord_4593896 prefixEnd_4593896 2358876724767063594473063 := by
  unfold tailWord_4593896
  simp only [CollatzResearch.WordTrace]
  refine ⟨83776576082553420909352771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111702101443404561212470361 83776576082553420909352771)
  ·
    refine ⟨125664864123830131364029157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83776576082553420909352771 125664864123830131364029157)
    ·
      refine ⟨23562162023218149630755467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 125664864123830131364029157 23562162023218149630755467)
      ·
        refine ⟨35343243034827224446133201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23562162023218149630755467 35343243034827224446133201)
        ·
          refine ⟨26507432276120418334599901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35343243034827224446133201 26507432276120418334599901)
          ·
            refine ⟨9940287103545156875474963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26507432276120418334599901 9940287103545156875474963)
            ·
              refine ⟨14910430655317735313212445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9940287103545156875474963 14910430655317735313212445)
              ·
                refine ⟨5591411495744150742454667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14910430655317735313212445 5591411495744150742454667)
                ·
                  refine ⟨8387117243616226113682001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5591411495744150742454667 8387117243616226113682001)
                  ·
                    refine ⟨6290337932712169585261501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8387117243616226113682001 6290337932712169585261501)
                    ·
                      refine ⟨2358876724767063594473063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6290337932712169585261501 2358876724767063594473063)
                      ·
                        rfl

theorem cell23_4593896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 3, 1, 2, 3].length) (baseStart_4593896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4593896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4593896 prefixEnd_4593896 := by exact prefixLift 4593896
  have htrace : WordTrace (prefixWord ++ tailWord_4593896) baseStart_4593896 baseEnd_4593896 := by
    simpa [prefixWord, tailWord_4593896, baseEnd_4593896] using wordTrace_append hprefix tailTrace_4593896
  have hstable : (prefixWord ++ tailWord_4593896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4593896).length < 2 ^ (prefixWord ++ tailWord_4593896).sum := by decide
  have hdescent : baseEnd_4593896 < baseStart_4593896 := by decide
  rcases family_descends (prefixWord ++ tailWord_4593896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4593902 : List Nat := [4, 1, 2, 1, 1, 1, 1, 2, 2, 2, 6]
def baseStart_4593902 : Nat := 118140960795 + 4593902 * 2 ^ 59
def prefixEnd_4593902 : Nat := 4983230072969 + 3 ^ 40 * 4593902 * 2
def baseEnd_4593902 : Nat := 2358879805650990570998035

theorem tailTrace_4593902 : CollatzResearch.WordTrace tailWord_4593902 prefixEnd_4593902 2358879805650990570998035 := by
  unfold tailWord_4593902
  simp only [CollatzResearch.WordTrace]
  refine ⟨20944171375385638105427995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111702247335390069895615973 20944171375385638105427995)
  ·
    refine ⟨31416257063078457158141993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20944171375385638105427995 31416257063078457158141993)
    ·
      refine ⟨23562192797308842868606495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31416257063078457158141993 23562192797308842868606495)
      ·
        refine ⟨35343289195963264302909743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23562192797308842868606495 35343289195963264302909743)
        ·
          refine ⟨53014933793944896454364615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35343289195963264302909743 53014933793944896454364615)
          ·
            refine ⟨79522400690917344681546923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53014933793944896454364615 79522400690917344681546923)
            ·
              refine ⟨119283601036376017022320385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79522400690917344681546923 119283601036376017022320385)
              ·
                refine ⟨89462700777282012766740289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 119283601036376017022320385 89462700777282012766740289)
                ·
                  refine ⟨67097025582961509575055217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 89462700777282012766740289 67097025582961509575055217)
                  ·
                    refine ⟨50322769187221132181291413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 67097025582961509575055217 50322769187221132181291413)
                    ·
                      refine ⟨2358879805650990570998035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50322769187221132181291413 2358879805650990570998035)
                      ·
                        rfl

theorem cell23_4593902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_4593902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4593902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4593902 prefixEnd_4593902 := by exact prefixLift 4593902
  have htrace : WordTrace (prefixWord ++ tailWord_4593902) baseStart_4593902 baseEnd_4593902 := by
    simpa [prefixWord, tailWord_4593902, baseEnd_4593902] using wordTrace_append hprefix tailTrace_4593902
  have hstable : (prefixWord ++ tailWord_4593902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4593902).length < 2 ^ (prefixWord ++ tailWord_4593902).sum := by decide
  have hdescent : baseEnd_4593902 < baseStart_4593902 := by decide
  rcases family_descends (prefixWord ++ tailWord_4593902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4593910 : List Nat := [5, 1, 1, 1, 1, 1, 4, 4, 1, 2, 2]
def baseStart_4593910 : Nat := 118140960795 + 4593910 * 2 ^ 59
def prefixEnd_4593910 : Nat := 4983230072969 + 3 ^ 40 * 4593910 * 2
def baseEnd_4593910 : Nat := 2358883913496226539697999

theorem tailTrace_4593910 : CollatzResearch.WordTrace tailWord_4593910 prefixEnd_4593910 2358883913496226539697999 := by
  unfold tailWord_4593910
  simp only [CollatzResearch.WordTrace]
  refine ⟨10472103924191007638107199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 111702441858037414806476789 10472103924191007638107199)
  ·
    refine ⟨15708155886286511457160799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10472103924191007638107199 15708155886286511457160799)
    ·
      refine ⟨23562233829429767185741199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15708155886286511457160799 23562233829429767185741199)
      ·
        refine ⟨35343350744144650778611799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23562233829429767185741199 35343350744144650778611799)
        ·
          refine ⟨53015026116216976167917699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35343350744144650778611799 53015026116216976167917699)
          ·
            refine ⟨79522539174325464251876549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53015026116216976167917699 79522539174325464251876549)
            ·
              refine ⟨14910476095186024547226853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79522539174325464251876549 14910476095186024547226853)
              ·
                refine ⟨2795714267847379602605035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14910476095186024547226853 2795714267847379602605035)
                ·
                  refine ⟨4193571401771069403907553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2795714267847379602605035 4193571401771069403907553)
                  ·
                    refine ⟨3145178551328302052930665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4193571401771069403907553 3145178551328302052930665)
                    ·
                      refine ⟨2358883913496226539697999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3145178551328302052930665 2358883913496226539697999)
                      ·
                        rfl

theorem cell23_4593910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 4, 1, 2, 2].length) (baseStart_4593910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4593910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4593910 prefixEnd_4593910 := by exact prefixLift 4593910
  have htrace : WordTrace (prefixWord ++ tailWord_4593910) baseStart_4593910 baseEnd_4593910 := by
    simpa [prefixWord, tailWord_4593910, baseEnd_4593910] using wordTrace_append hprefix tailTrace_4593910
  have hstable : (prefixWord ++ tailWord_4593910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4593910).length < 2 ^ (prefixWord ++ tailWord_4593910).sum := by decide
  have hdescent : baseEnd_4593910 < baseStart_4593910 := by decide
  rcases family_descends (prefixWord ++ tailWord_4593910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4593983 : List Nat := [1, 1, 2, 2, 4, 1, 3, 3, 2, 2, 2]
def baseStart_4593983 : Nat := 118140960795 + 4593983 * 2 ^ 59
def prefixEnd_4593983 : Nat := 4983230072969 + 3 ^ 40 * 4593983 * 2
def baseEnd_4593983 : Nat := 2358921397584004754085163

theorem tailTrace_4593983 : CollatzResearch.WordTrace tailWord_4593983 prefixEnd_4593983 2358921397584004754085163 := by
  unfold tailWord_4593983
  simp only [CollatzResearch.WordTrace]
  refine ⟨167556325315791655677122603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111704216877194437118081735 167556325315791655677122603)
  ·
    refine ⟨251334487973687483515683905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167556325315791655677122603 251334487973687483515683905)
    ·
      refine ⟨188500865980265612636762929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 251334487973687483515683905 188500865980265612636762929)
      ·
        refine ⟨141375649485199209477572197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188500865980265612636762929 141375649485199209477572197)
        ·
          refine ⟨26507934278474851777044787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 141375649485199209477572197 26507934278474851777044787)
          ·
            refine ⟨39761901417712277665567181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26507934278474851777044787 39761901417712277665567181)
            ·
              refine ⟨14910713031642104124587693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39761901417712277665567181 14910713031642104124587693)
              ·
                refine ⟨5591517386865789046720385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14910713031642104124587693 5591517386865789046720385)
                ·
                  refine ⟨4193638040149341785040289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5591517386865789046720385 4193638040149341785040289)
                  ·
                    refine ⟨3145228530112006338780217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4193638040149341785040289 3145228530112006338780217)
                    ·
                      refine ⟨2358921397584004754085163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3145228530112006338780217 2358921397584004754085163)
                      ·
                        rfl

theorem cell23_4593983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 3, 2, 2, 2].length) (baseStart_4593983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4593983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4593983 prefixEnd_4593983 := by exact prefixLift 4593983
  have htrace : WordTrace (prefixWord ++ tailWord_4593983) baseStart_4593983 baseEnd_4593983 := by
    simpa [prefixWord, tailWord_4593983, baseEnd_4593983] using wordTrace_append hprefix tailTrace_4593983
  have hstable : (prefixWord ++ tailWord_4593983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4593983).length < 2 ^ (prefixWord ++ tailWord_4593983).sum := by decide
  have hdescent : baseEnd_4593983 < baseStart_4593983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4593983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4594019 : List Nat := [1, 1, 1, 5, 2, 1, 1, 4, 2, 5]
def baseStart_4594019 : Nat := 118140960795 + 4594019 * 2 ^ 59
def prefixEnd_4594019 : Nat := 4983230072969 + 3 ^ 40 * 4594019 * 2
def baseEnd_4594019 : Nat := 786313294295855537744999

theorem tailTrace_4594019 : CollatzResearch.WordTrace tailWord_4594019 prefixEnd_4594019 786313294295855537744999 := by
  unfold tailWord_4594019
  simp only [CollatzResearch.WordTrace]
  refine ⟨167557638343661233825433111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111705092229107489216955407 167557638343661233825433111)
  ·
    refine ⟨251336457515491850738149667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167557638343661233825433111 251336457515491850738149667)
    ·
      refine ⟨377004686273237776107224501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251336457515491850738149667 377004686273237776107224501)
      ·
        refine ⟨35344189338116041510052297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 377004686273237776107224501 35344189338116041510052297)
        ·
          refine ⟨26508142003587031132539223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35344189338116041510052297 26508142003587031132539223)
          ·
            refine ⟨39762213005380546698808835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26508142003587031132539223 39762213005380546698808835)
            ·
              refine ⟨59643319508070820048213253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39762213005380546698808835 59643319508070820048213253)
              ·
                refine ⟨11183122407763278759039985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59643319508070820048213253 11183122407763278759039985)
                ·
                  refine ⟨8387341805822459069279989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11183122407763278759039985 8387341805822459069279989)
                  ·
                    refine ⟨786313294295855537744999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8387341805822459069279989 786313294295855537744999)
                    ·
                      rfl

theorem cell23_4594019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 4, 2, 5].length) (baseStart_4594019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4594019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4594019 prefixEnd_4594019 := by exact prefixLift 4594019
  have htrace : WordTrace (prefixWord ++ tailWord_4594019) baseStart_4594019 baseEnd_4594019 := by
    simpa [prefixWord, tailWord_4594019, baseEnd_4594019] using wordTrace_append hprefix tailTrace_4594019
  have hstable : (prefixWord ++ tailWord_4594019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4594019).length < 2 ^ (prefixWord ++ tailWord_4594019).sum := by decide
  have hdescent : baseEnd_4594019 < baseStart_4594019 := by decide
  rcases family_descends (prefixWord ++ tailWord_4594019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4594023 : List Nat := [1, 1, 5, 1, 3, 1, 4, 2, 5]
def baseStart_4594023 : Nat := 118140960795 + 4594023 * 2 ^ 59
def prefixEnd_4594023 : Nat := 4983230072969 + 3 ^ 40 * 4594023 * 2
def baseEnd_4594023 : Nat := 262104659645576066398331

theorem tailTrace_4594023 : CollatzResearch.WordTrace tailWord_4594023 prefixEnd_4594023 262104659645576066398331 := by
  unfold tailWord_4594023
  simp only [CollatzResearch.WordTrace]
  refine ⟨167557784235646742508578723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111705189490431161672385815 167557784235646742508578723)
  ·
    refine ⟨251336676353470113762868085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167557784235646742508578723 251336676353470113762868085)
    ·
      refine ⟨23562813408137823165268883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 251336676353470113762868085 23562813408137823165268883)
      ·
        refine ⟨35344220112206734747903325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23562813408137823165268883 35344220112206734747903325)
        ·
          refine ⟨13254082542077525530463747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35344220112206734747903325 13254082542077525530463747)
          ·
            refine ⟨19881123813116288295695621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13254082542077525530463747 19881123813116288295695621)
            ·
              refine ⟨3727710714959304055442929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19881123813116288295695621 3727710714959304055442929)
              ·
                refine ⟨2795783036219478041582197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3727710714959304055442929 2795783036219478041582197)
                ·
                  refine ⟨262104659645576066398331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2795783036219478041582197 262104659645576066398331)
                  ·
                    rfl

theorem cell23_4594023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 4, 2, 5].length) (baseStart_4594023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4594023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4594023 prefixEnd_4594023 := by exact prefixLift 4594023
  have htrace : WordTrace (prefixWord ++ tailWord_4594023) baseStart_4594023 baseEnd_4594023 := by
    simpa [prefixWord, tailWord_4594023, baseEnd_4594023] using wordTrace_append hprefix tailTrace_4594023
  have hstable : (prefixWord ++ tailWord_4594023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4594023).length < 2 ^ (prefixWord ++ tailWord_4594023).sum := by decide
  have hdescent : baseEnd_4594023 < baseStart_4594023 := by decide
  rcases family_descends (prefixWord ++ tailWord_4594023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4594029 : List Nat := [1, 5, 1, 1, 1, 2, 1, 3, 1, 2, 5]
def baseStart_4594029 : Nat := 118140960795 + 4594029 * 2 ^ 59
def prefixEnd_4594029 : Nat := 4983230072969 + 3 ^ 40 * 4594029 * 2
def baseEnd_4594029 : Nat := 2358945017694111574109951

theorem tailTrace_4594029 : CollatzResearch.WordTrace tailWord_4594029 prefixEnd_4594029 2358945017694111574109951 := by
  unfold tailWord_4594029
  simp only [CollatzResearch.WordTrace]
  refine ⟨167558003073625005533297141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111705335382416670355531427 167558003073625005533297141)
  ·
    refine ⟨15708562788152344268746607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 167558003073625005533297141 15708562788152344268746607)
    ·
      refine ⟨23562844182228516403119911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15708562788152344268746607 23562844182228516403119911)
      ·
        refine ⟨35344266273342774604679867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23562844182228516403119911 35344266273342774604679867)
        ·
          refine ⟨53016399410014161907019801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35344266273342774604679867 53016399410014161907019801)
          ·
            refine ⟨39762299557510621430264851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53016399410014161907019801 39762299557510621430264851)
            ·
              refine ⟨59643449336265932145397277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39762299557510621430264851 59643449336265932145397277)
              ·
                refine ⟨22366293501099724554523979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59643449336265932145397277 22366293501099724554523979)
                ·
                  refine ⟨33549440251649586831785969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22366293501099724554523979 33549440251649586831785969)
                  ·
                    refine ⟨25162080188737190123839477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33549440251649586831785969 25162080188737190123839477)
                    ·
                      refine ⟨2358945017694111574109951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25162080188737190123839477 2358945017694111574109951)
                      ·
                        rfl

theorem cell23_4594029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_4594029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4594029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4594029 prefixEnd_4594029 := by exact prefixLift 4594029
  have htrace : WordTrace (prefixWord ++ tailWord_4594029) baseStart_4594029 baseEnd_4594029 := by
    simpa [prefixWord, tailWord_4594029, baseEnd_4594029] using wordTrace_append hprefix tailTrace_4594029
  have hstable : (prefixWord ++ tailWord_4594029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4594029).length < 2 ^ (prefixWord ++ tailWord_4594029).sum := by decide
  have hdescent : baseEnd_4594029 < baseStart_4594029 := by decide
  rcases family_descends (prefixWord ++ tailWord_4594029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4594056 : List Nat := [2, 1, 3, 3, 1, 1, 1, 2, 1, 6, 2]
def baseStart_4594056 : Nat := 118140960795 + 4594056 * 2 ^ 59
def prefixEnd_4594056 : Nat := 4983230072969 + 3 ^ 40 * 4594056 * 2
def baseEnd_4594056 : Nat := 2358958881671782968472327

theorem tailTrace_4594056 : CollatzResearch.WordTrace tailWord_4594056 prefixEnd_4594056 2358958881671782968472327 := by
  unfold tailWord_4594056
  simp only [CollatzResearch.WordTrace]
  refine ⟨83779493922263594572265011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111705991896351459429686681 83779493922263594572265011)
  ·
    refine ⟨125669240883395391858397517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83779493922263594572265011 125669240883395391858397517)
    ·
      refine ⟨47125965331273271946899069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125669240883395391858397517 47125965331273271946899069)
      ·
        refine ⟨17672236999227476980087151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47125965331273271946899069 17672236999227476980087151)
        ·
          refine ⟨26508355498841215470130727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17672236999227476980087151 26508355498841215470130727)
          ·
            refine ⟨39762533248261823205196091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26508355498841215470130727 39762533248261823205196091)
            ·
              refine ⟨59643799872392734807794137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39762533248261823205196091 59643799872392734807794137)
              ·
                refine ⟨44732849904294551105845603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59643799872392734807794137 44732849904294551105845603)
                ·
                  refine ⟨67099274856441826658768405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44732849904294551105845603 67099274856441826658768405)
                  ·
                    refine ⟨3145278508895710624629769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 67099274856441826658768405 3145278508895710624629769)
                    ·
                      refine ⟨2358958881671782968472327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3145278508895710624629769 2358958881671782968472327)
                      ·
                        rfl

theorem cell23_4594056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 1, 6, 2].length) (baseStart_4594056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4594056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4594056 prefixEnd_4594056 := by exact prefixLift 4594056
  have htrace : WordTrace (prefixWord ++ tailWord_4594056) baseStart_4594056 baseEnd_4594056 := by
    simpa [prefixWord, tailWord_4594056, baseEnd_4594056] using wordTrace_append hprefix tailTrace_4594056
  have hstable : (prefixWord ++ tailWord_4594056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4594056).length < 2 ^ (prefixWord ++ tailWord_4594056).sum := by decide
  have hdescent : baseEnd_4594056 < baseStart_4594056 := by decide
  rcases family_descends (prefixWord ++ tailWord_4594056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4594079 : List Nat := [1, 1, 2, 5, 1, 1, 3, 1, 8]
def baseStart_4594079 : Nat := 118140960795 + 4594079 * 2 ^ 59
def prefixEnd_4594079 : Nat := 4983230072969 + 3 ^ 40 * 4594079 * 2
def baseEnd_4594079 : Nat := 262107854636315153164969

theorem tailTrace_4594079 : CollatzResearch.WordTrace tailWord_4594079 prefixEnd_4594079 262107854636315153164969 := by
  unfold tailWord_4594079
  simp only [CollatzResearch.WordTrace]
  refine ⟨167559826723443864072617291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111706551148962576048411527 167559826723443864072617291)
  ·
    refine ⟨251339740085165796108925937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167559826723443864072617291 251339740085165796108925937)
    ·
      refine ⟨188504805063874347081694453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 251339740085165796108925937 188504805063874347081694453)
      ·
        refine ⟨17672325474738220038908855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 188504805063874347081694453 17672325474738220038908855)
        ·
          refine ⟨26508488212107330058363283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17672325474738220038908855 26508488212107330058363283)
          ·
            refine ⟨39762732318160995087544925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26508488212107330058363283 39762732318160995087544925)
            ·
              refine ⟨14911024619310373157829347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39762732318160995087544925 14911024619310373157829347)
              ·
                refine ⟨22366536928965559736744021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14911024619310373157829347 22366536928965559736744021)
                ·
                  refine ⟨262107854636315153164969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22366536928965559736744021 262107854636315153164969)
                  ·
                    rfl

theorem cell23_4594079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 8].length) (baseStart_4594079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4594079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4594079 prefixEnd_4594079 := by exact prefixLift 4594079
  have htrace : WordTrace (prefixWord ++ tailWord_4594079) baseStart_4594079 baseEnd_4594079 := by
    simpa [prefixWord, tailWord_4594079, baseEnd_4594079] using wordTrace_append hprefix tailTrace_4594079
  have hstable : (prefixWord ++ tailWord_4594079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4594079).length < 2 ^ (prefixWord ++ tailWord_4594079).sum := by decide
  have hdescent : baseEnd_4594079 < baseStart_4594079 := by decide
  rcases family_descends (prefixWord ++ tailWord_4594079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4594083 : List Nat := [1, 1, 1, 4, 1, 4, 2, 4, 1, 4]
def baseStart_4594083 : Nat := 118140960795 + 4594083 * 2 ^ 59
def prefixEnd_4594083 : Nat := 4983230072969 + 3 ^ 40 * 4594083 * 2
def baseEnd_4594083 : Nat := 786324248549818120944901

theorem tailTrace_4594083 : CollatzResearch.WordTrace tailWord_4594083 prefixEnd_4594083 786324248549818120944901 := by
  unfold tailWord_4594083
  simp only [CollatzResearch.WordTrace]
  refine ⟨167559972615429372755762903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111706648410286248503841935 167559972615429372755762903)
  ·
    refine ⟨251339958923144059133644355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167559972615429372755762903 251339958923144059133644355)
    ·
      refine ⟨377009938384716088700466533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251339958923144059133644355 377009938384716088700466533)
      ·
        refine ⟨70689363447134266631337475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 377009938384716088700466533 70689363447134266631337475)
        ·
          refine ⟨106034045170701399947006213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70689363447134266631337475 106034045170701399947006213)
          ·
            refine ⟨19881383469506512490063665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 106034045170701399947006213 19881383469506512490063665)
            ·
              refine ⟨14911037602129884367547749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19881383469506512490063665 14911037602129884367547749)
              ·
                refine ⟨2795819550399353318915203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14911037602129884367547749 2795819550399353318915203)
                ·
                  refine ⟨4193729325599029978372805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2795819550399353318915203 4193729325599029978372805)
                  ·
                    refine ⟨786324248549818120944901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4193729325599029978372805 786324248549818120944901)
                    ·
                      rfl

theorem cell23_4594083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 4, 1, 4].length) (baseStart_4594083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4594083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4594083 prefixEnd_4594083 := by exact prefixLift 4594083
  have htrace : WordTrace (prefixWord ++ tailWord_4594083) baseStart_4594083 baseEnd_4594083 := by
    simpa [prefixWord, tailWord_4594083, baseEnd_4594083] using wordTrace_append hprefix tailTrace_4594083
  have hstable : (prefixWord ++ tailWord_4594083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4594083).length < 2 ^ (prefixWord ++ tailWord_4594083).sum := by decide
  have hdescent : baseEnd_4594083 < baseStart_4594083 := by decide
  rcases family_descends (prefixWord ++ tailWord_4594083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4594133 : List Nat := [1, 3, 2, 3, 1, 2, 1, 1, 4, 3, 2]
def baseStart_4594133 : Nat := 118140960795 + 4594133 * 2 ^ 59
def prefixEnd_4594133 : Nat := 4983230072969 + 3 ^ 40 * 4594133 * 2
def baseEnd_4594133 : Nat := 2358998419682179167209473

theorem tailTrace_4594133 : CollatzResearch.WordTrace tailWord_4594133 prefixEnd_4594133 2358998419682179167209473 := by
  unfold tailWord_4594133
  simp only [CollatzResearch.WordTrace]
  refine ⟨167561796265248231295083053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111707864176832154196722035 167561796265248231295083053)
  ·
    refine ⟨62835673599468086735656145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167561796265248231295083053 62835673599468086735656145)
    ·
      refine ⟨47126755199601065051742109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62835673599468086735656145 47126755199601065051742109)
      ·
        refine ⟨17672533199850399394403291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47126755199601065051742109 17672533199850399394403291)
        ·
          refine ⟨26508799799775599091604937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17672533199850399394403291 26508799799775599091604937)
          ·
            refine ⟨19881599849831699318703703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26508799799775599091604937 19881599849831699318703703)
            ·
              refine ⟨29822399774747548978055555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19881599849831699318703703 29822399774747548978055555)
              ·
                refine ⟨44733599662121323467083333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29822399774747548978055555 44733599662121323467083333)
                ·
                  refine ⟨8387549936647748150078125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44733599662121323467083333 8387549936647748150078125)
                  ·
                    refine ⟨3145331226242905556279297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8387549936647748150078125 3145331226242905556279297)
                    ·
                      refine ⟨2358998419682179167209473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3145331226242905556279297 2358998419682179167209473)
                      ·
                        rfl

theorem cell23_4594133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 4, 3, 2].length) (baseStart_4594133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4594133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4594133 prefixEnd_4594133 := by exact prefixLift 4594133
  have htrace : WordTrace (prefixWord ++ tailWord_4594133) baseStart_4594133 baseEnd_4594133 := by
    simpa [prefixWord, tailWord_4594133, baseEnd_4594133] using wordTrace_append hprefix tailTrace_4594133
  have hstable : (prefixWord ++ tailWord_4594133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4594133).length < 2 ^ (prefixWord ++ tailWord_4594133).sum := by decide
  have hdescent : baseEnd_4594133 < baseStart_4594133 := by decide
  rcases family_descends (prefixWord ++ tailWord_4594133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4594163 : List Nat := [1, 1, 1, 2, 2, 2, 4, 1, 5, 2, 2]
def baseStart_4594163 : Nat := 118140960795 + 4594163 * 2 ^ 59
def prefixEnd_4594163 : Nat := 4983230072969 + 3 ^ 40 * 4594163 * 2
def baseEnd_4594163 : Nat := 2359013824101814049834335

theorem tailTrace_4594163 : CollatzResearch.WordTrace tailWord_4594163 prefixEnd_4594163 2359013824101814049834335 := by
  unfold tailWord_4594163
  simp only [CollatzResearch.WordTrace]
  refine ⟨167562890455139546418675143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111708593636759697612450095 167562890455139546418675143)
  ·
    refine ⟨251344335682709319628012715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167562890455139546418675143 251344335682709319628012715)
    ·
      refine ⟨377016503524063979442019073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251344335682709319628012715 377016503524063979442019073)
      ·
        refine ⟨282762377643047984581514305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 377016503524063979442019073 282762377643047984581514305)
        ·
          refine ⟨212071783232285988436135729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 282762377643047984581514305 212071783232285988436135729)
          ·
            refine ⟨159053837424214491327101797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 212071783232285988436135729 159053837424214491327101797)
            ·
              refine ⟨29822594517040217123831587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 159053837424214491327101797 29822594517040217123831587)
              ·
                refine ⟨44733891775560325685747381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29822594517040217123831587 44733891775560325685747381)
                ·
                  refine ⟨4193802353958780533038817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44733891775560325685747381 4193802353958780533038817)
                  ·
                    refine ⟨3145351765469085399779113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4193802353958780533038817 3145351765469085399779113)
                    ·
                      refine ⟨2359013824101814049834335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3145351765469085399779113 2359013824101814049834335)
                      ·
                        rfl

theorem cell23_4594163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 5, 2, 2].length) (baseStart_4594163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4594163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4594163 prefixEnd_4594163 := by exact prefixLift 4594163
  have htrace : WordTrace (prefixWord ++ tailWord_4594163) baseStart_4594163 baseEnd_4594163 := by
    simpa [prefixWord, tailWord_4594163, baseEnd_4594163] using wordTrace_append hprefix tailTrace_4594163
  have hstable : (prefixWord ++ tailWord_4594163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4594163).length < 2 ^ (prefixWord ++ tailWord_4594163).sum := by decide
  have hdescent : baseEnd_4594163 < baseStart_4594163 := by decide
  rcases family_descends (prefixWord ++ tailWord_4594163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4594169 : List Nat := [1, 2, 1, 3, 1, 2, 4, 9]
def baseStart_4594169 : Nat := 118140960795 + 4594169 * 2 ^ 59
def prefixEnd_4594169 : Nat := 4983230072969 + 3 ^ 40 * 4594169 * 2
def baseEnd_4594169 : Nat := 87370996480953371346641

theorem tailTrace_4594169 : CollatzResearch.WordTrace tailWord_4594169 prefixEnd_4594169 87370996480953371346641 := by
  unfold tailWord_4594169
  simp only [CollatzResearch.WordTrace]
  refine ⟨167563109293117809443393561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111708739528745206295595707 167563109293117809443393561)
  ·
    refine ⟨125672331969838357082545171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167563109293117809443393561 125672331969838357082545171)
    ·
      refine ⟨188508497954757535623817757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125672331969838357082545171 188508497954757535623817757)
      ·
        refine ⟨70690686733034075858931659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 188508497954757535623817757 70690686733034075858931659)
        ·
          refine ⟨106036030099551113788397489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70690686733034075858931659 106036030099551113788397489)
          ·
            refine ⟨79527022574663335341298117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106036030099551113788397489 79527022574663335341298117)
            ·
              refine ⟨14911316732749375376493397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79527022574663335341298117 14911316732749375376493397)
              ·
                refine ⟨87370996480953371346641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14911316732749375376493397 87370996480953371346641)
                ·
                  rfl

theorem cell23_4594169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 9].length) (baseStart_4594169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4594169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4594169 prefixEnd_4594169 := by exact prefixLift 4594169
  have htrace : WordTrace (prefixWord ++ tailWord_4594169) baseStart_4594169 baseEnd_4594169 := by
    simpa [prefixWord, tailWord_4594169, baseEnd_4594169] using wordTrace_append hprefix tailTrace_4594169
  have hstable : (prefixWord ++ tailWord_4594169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4594169).length < 2 ^ (prefixWord ++ tailWord_4594169).sum := by decide
  have hdescent : baseEnd_4594169 < baseStart_4594169 := by decide
  rcases family_descends (prefixWord ++ tailWord_4594169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4594190 : List Nat := [4, 1, 1, 2, 3, 2, 2, 2, 2, 4]
def baseStart_4594190 : Nat := 118140960795 + 4594190 * 2 ^ 59
def prefixEnd_4594190 : Nat := 4983230072969 + 3 ^ 40 * 4594190 * 2
def baseEnd_4594190 : Nat := 786342562693161814732237

theorem tailTrace_4594190 : CollatzResearch.WordTrace tailWord_4594190 prefixEnd_4594190 786342562693161814732237 := by
  unfold tailWord_4594190
  simp only [CollatzResearch.WordTrace]
  refine ⟨20945484403255216253738503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111709250150694486686605349 20945484403255216253738503)
  ·
    refine ⟨31418226604882824380607755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20945484403255216253738503 31418226604882824380607755)
    ·
      refine ⟨47127339907324236570911633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31418226604882824380607755 47127339907324236570911633)
      ·
        refine ⟨35345504930493177428183725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47127339907324236570911633 35345504930493177428183725)
        ·
          refine ⟨13254564348934941535568897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35345504930493177428183725 13254564348934941535568897)
          ·
            refine ⟨9940923261701206151676673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13254564348934941535568897 9940923261701206151676673)
            ·
              refine ⟨7455692446275904613757505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9940923261701206151676673 7455692446275904613757505)
              ·
                refine ⟨5591769334706928460318129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7455692446275904613757505 5591769334706928460318129)
                ·
                  refine ⟨4193827001030196345238597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5591769334706928460318129 4193827001030196345238597)
                  ·
                    refine ⟨786342562693161814732237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4193827001030196345238597 786342562693161814732237)
                    ·
                      rfl

theorem cell23_4594190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 2, 2, 4].length) (baseStart_4594190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4594190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4594190 prefixEnd_4594190 := by exact prefixLift 4594190
  have htrace : WordTrace (prefixWord ++ tailWord_4594190) baseStart_4594190 baseEnd_4594190 := by
    simpa [prefixWord, tailWord_4594190, baseEnd_4594190] using wordTrace_append hprefix tailTrace_4594190
  have hstable : (prefixWord ++ tailWord_4594190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4594190).length < 2 ^ (prefixWord ++ tailWord_4594190).sum := by decide
  have hdescent : baseEnd_4594190 < baseStart_4594190 := by decide
  rcases family_descends (prefixWord ++ tailWord_4594190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4594197 : List Nat := [1, 3, 2, 1, 3, 1, 3, 4, 1, 2, 2]
def baseStart_4594197 : Nat := 118140960795 + 4594197 * 2 ^ 59
def prefixEnd_4594197 : Nat := 4983230072969 + 3 ^ 40 * 4594197 * 2
def baseEnd_4594197 : Nat := 2359031282444066916809179

theorem tailTrace_4594197 : CollatzResearch.WordTrace tailWord_4594197 prefixEnd_4594197 2359031282444066916809179 := by
  unfold tailWord_4594197
  simp only [CollatzResearch.WordTrace]
  refine ⟨167564130537016370225412845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111709420358010913483608563 167564130537016370225412845)
  ·
    refine ⟨62836548951381138834529817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167564130537016370225412845 62836548951381138834529817)
    ·
      refine ⟨47127411713535854125897363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62836548951381138834529817 47127411713535854125897363)
      ·
        refine ⟨70691117570303781188846045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47127411713535854125897363 70691117570303781188846045)
        ·
          refine ⟨26509169088863917945817267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70691117570303781188846045 26509169088863917945817267)
          ·
            refine ⟨39763753633295876918725901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26509169088863917945817267 39763753633295876918725901)
            ·
              refine ⟨14911407612485953844522213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39763753633295876918725901 14911407612485953844522213)
              ·
                refine ⟨2795888927341116345847915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14911407612485953844522213 2795888927341116345847915)
                ·
                  refine ⟨4193833391011674518771873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2795888927341116345847915 4193833391011674518771873)
                  ·
                    refine ⟨3145375043258755889078905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4193833391011674518771873 3145375043258755889078905)
                    ·
                      refine ⟨2359031282444066916809179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3145375043258755889078905 2359031282444066916809179)
                      ·
                        rfl

theorem cell23_4594197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 4, 1, 2, 2].length) (baseStart_4594197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4594197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4594197 prefixEnd_4594197 := by exact prefixLift 4594197
  have htrace : WordTrace (prefixWord ++ tailWord_4594197) baseStart_4594197 baseEnd_4594197 := by
    simpa [prefixWord, tailWord_4594197, baseEnd_4594197] using wordTrace_append hprefix tailTrace_4594197
  have hstable : (prefixWord ++ tailWord_4594197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4594197).length < 2 ^ (prefixWord ++ tailWord_4594197).sum := by decide
  have hdescent : baseEnd_4594197 < baseStart_4594197 := by decide
  rcases family_descends (prefixWord ++ tailWord_4594197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4594230 : List Nat := [5, 1, 2, 1, 2, 1, 2, 2, 1, 3, 3]
def baseStart_4594230 : Nat := 118140960795 + 4594230 * 2 ^ 59
def prefixEnd_4594230 : Nat := 4983230072969 + 3 ^ 40 * 4594230 * 2
def baseEnd_4594230 : Nat := 2359048227305665287696527

theorem tailTrace_4594230 : CollatzResearch.WordTrace tailWord_4594230 prefixEnd_4594230 2359048227305665287696527 := by
  unfold tailWord_4594230
  simp only [CollatzResearch.WordTrace]
  refine ⟨10472833384118551053835259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 111710222763931211240909429 10472833384118551053835259)
  ·
    refine ⟨15709250076177826580752889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10472833384118551053835259 15709250076177826580752889)
    ·
      refine ⟨11781937557133369935564667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15709250076177826580752889 11781937557133369935564667)
      ·
        refine ⟨17672906335700054903347001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11781937557133369935564667 17672906335700054903347001)
        ·
          refine ⟨13254679751775041177510251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17672906335700054903347001 13254679751775041177510251)
          ·
            refine ⟨19882019627662561766265377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13254679751775041177510251 19882019627662561766265377)
            ·
              refine ⟨14911514720746921324699033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19882019627662561766265377 14911514720746921324699033)
              ·
                refine ⟨11183636040560190993524275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14911514720746921324699033 11183636040560190993524275)
                ·
                  refine ⟨16775454060840286490286413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11183636040560190993524275 16775454060840286490286413)
                  ·
                    refine ⟨6290795272815107433857405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16775454060840286490286413 6290795272815107433857405)
                    ·
                      refine ⟨2359048227305665287696527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6290795272815107433857405 2359048227305665287696527)
                      ·
                        rfl

theorem cell23_4594230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_4594230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4594230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4594230 prefixEnd_4594230 := by exact prefixLift 4594230
  have htrace : WordTrace (prefixWord ++ tailWord_4594230) baseStart_4594230 baseEnd_4594230 := by
    simpa [prefixWord, tailWord_4594230, baseEnd_4594230] using wordTrace_append hprefix tailTrace_4594230
  have hstable : (prefixWord ++ tailWord_4594230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4594230).length < 2 ^ (prefixWord ++ tailWord_4594230).sum := by decide
  have hdescent : baseEnd_4594230 < baseStart_4594230 := by decide
  rcases family_descends (prefixWord ++ tailWord_4594230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4594247 : List Nat := [1, 1, 4, 1, 4, 3, 1, 2, 2, 1, 3]
def baseStart_4594247 : Nat := 118140960795 + 4594247 * 2 ^ 59
def prefixEnd_4594247 : Nat := 4983230072969 + 3 ^ 40 * 4594247 * 2
def baseEnd_4594247 : Nat := 2359056956476791721183949

theorem tailTrace_4594247 : CollatzResearch.WordTrace tailWord_4594247 prefixEnd_4594247 2359056956476791721183949 := by
  unfold tailWord_4594247
  simp only [CollatzResearch.WordTrace]
  refine ⟨167565954186835228764732995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111710636124556819176488663 167565954186835228764732995)
  ·
    refine ⟨251348931280252843147099493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167565954186835228764732995 251348931280252843147099493)
    ·
      refine ⟨47127924615047408090081155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 251348931280252843147099493 47127924615047408090081155)
      ·
        refine ⟨70691886922571112135121733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47127924615047408090081155 70691886922571112135121733)
        ·
          refine ⟨13254728797982083525335325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70691886922571112135121733 13254728797982083525335325)
          ·
            refine ⟨4970523299243281322000747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13254728797982083525335325 4970523299243281322000747)
            ·
              refine ⟨7455784948864921983001121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4970523299243281322000747 7455784948864921983001121)
              ·
                refine ⟨5591838711648691487250841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7455784948864921983001121 5591838711648691487250841)
                ·
                  refine ⟨4193879033736518615438131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5591838711648691487250841 4193879033736518615438131)
                  ·
                    refine ⟨6290818550604777923157197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4193879033736518615438131 6290818550604777923157197)
                    ·
                      refine ⟨2359056956476791721183949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6290818550604777923157197 2359056956476791721183949)
                      ·
                        rfl

theorem cell23_4594247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 2, 2, 1, 3].length) (baseStart_4594247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4594247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4594247 prefixEnd_4594247 := by exact prefixLift 4594247
  have htrace : WordTrace (prefixWord ++ tailWord_4594247) baseStart_4594247 baseEnd_4594247 := by
    simpa [prefixWord, tailWord_4594247, baseEnd_4594247] using wordTrace_append hprefix tailTrace_4594247
  have hstable : (prefixWord ++ tailWord_4594247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4594247).length < 2 ^ (prefixWord ++ tailWord_4594247).sum := by decide
  have hdescent : baseEnd_4594247 < baseStart_4594247 := by decide
  rcases family_descends (prefixWord ++ tailWord_4594247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4594256 : List Nat := [2, 1, 1, 1, 1, 3, 2, 3, 2, 4, 3]
def baseStart_4594256 : Nat := 118140960795 + 4594256 * 2 ^ 59
def prefixEnd_4594256 : Nat := 4983230072969 + 3 ^ 40 * 4594256 * 2
def baseEnd_4594256 : Nat := 2359061577802682185971407

theorem tailTrace_4594256 : CollatzResearch.WordTrace tailWord_4594256 prefixEnd_4594256 2359061577802682185971407 := by
  unfold tailWord_4594256
  simp only [CollatzResearch.WordTrace]
  refine ⟨83783141221901311650905311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111710854962535082201207081 83783141221901311650905311)
  ·
    refine ⟨125674711832851967476357967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83783141221901311650905311 125674711832851967476357967)
    ·
      refine ⟨188512067749277951214536951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125674711832851967476357967 188512067749277951214536951)
      ·
        refine ⟨282768101623916926821805427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188512067749277951214536951 282768101623916926821805427)
        ·
          refine ⟨424152152435875390232708141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 282768101623916926821805427 424152152435875390232708141)
          ·
            refine ⟨159057057163453271337265553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 424152152435875390232708141 159057057163453271337265553)
            ·
              refine ⟨119292792872589953502949165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 159057057163453271337265553 119292792872589953502949165)
              ·
                refine ⟨44734797327221232563605937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 119292792872589953502949165 44734797327221232563605937)
                ·
                  refine ⟨33551097995415924422704453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44734797327221232563605937 33551097995415924422704453)
                  ·
                    refine ⟨6290830874140485829257085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33551097995415924422704453 6290830874140485829257085)
                    ·
                      refine ⟨2359061577802682185971407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6290830874140485829257085 2359061577802682185971407)
                      ·
                        rfl

theorem cell23_4594256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 2, 4, 3].length) (baseStart_4594256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4594256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4594256 prefixEnd_4594256 := by exact prefixLift 4594256
  have htrace : WordTrace (prefixWord ++ tailWord_4594256) baseStart_4594256 baseEnd_4594256 := by
    simpa [prefixWord, tailWord_4594256, baseEnd_4594256] using wordTrace_append hprefix tailTrace_4594256
  have hstable : (prefixWord ++ tailWord_4594256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4594256).length < 2 ^ (prefixWord ++ tailWord_4594256).sum := by decide
  have hdescent : baseEnd_4594256 < baseStart_4594256 := by decide
  rcases family_descends (prefixWord ++ tailWord_4594256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4594276 : List Nat := [2, 3, 1, 1, 2, 2, 1, 4, 7]
def baseStart_4594276 : Nat := 118140960795 + 4594276 * 2 ^ 59
def prefixEnd_4594276 : Nat := 4983230072969 + 3 ^ 40 * 4594276 * 2
def baseEnd_4594276 : Nat := 262119094157308011969035

theorem tailTrace_4594276 : CollatzResearch.WordTrace tailWord_4594276 prefixEnd_4594276 262119094157308011969035 := by
  unfold tailWord_4594276
  simp only [CollatzResearch.WordTrace]
  refine ⟨83783505951865083358769341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111711341269153444478359121 83783505951865083358769341)
  ·
    refine ⟨31418814731949406259538503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83783505951865083358769341 31418814731949406259538503)
    ·
      refine ⟨47128222097924109389307755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31418814731949406259538503 47128222097924109389307755)
      ·
        refine ⟨70692333146886164083961633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47128222097924109389307755 70692333146886164083961633)
        ·
          refine ⟨53019249860164623062971225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70692333146886164083961633 53019249860164623062971225)
          ·
            refine ⟨39764437395123467297228419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53019249860164623062971225 39764437395123467297228419)
            ·
              refine ⟨59646656092685200945842629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39764437395123467297228419 59646656092685200945842629)
              ·
                refine ⟨11183748017378475177345493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59646656092685200945842629 11183748017378475177345493)
                ·
                  refine ⟨262119094157308011969035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11183748017378475177345493 262119094157308011969035)
                  ·
                    rfl

theorem cell23_4594276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 4, 7].length) (baseStart_4594276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4594276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4594276 prefixEnd_4594276 := by exact prefixLift 4594276
  have htrace : WordTrace (prefixWord ++ tailWord_4594276) baseStart_4594276 baseEnd_4594276 := by
    simpa [prefixWord, tailWord_4594276, baseEnd_4594276] using wordTrace_append hprefix tailTrace_4594276
  have hstable : (prefixWord ++ tailWord_4594276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4594276).length < 2 ^ (prefixWord ++ tailWord_4594276).sum := by decide
  have hdescent : baseEnd_4594276 < baseStart_4594276 := by decide
  rcases family_descends (prefixWord ++ tailWord_4594276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4594313 : List Nat := [1, 2, 1, 1, 4, 1, 1, 3, 2, 5, 2]
def baseStart_4594313 : Nat := 118140960795 + 4594313 * 2 ^ 59
def prefixEnd_4594313 : Nat := 4983230072969 + 3 ^ 40 * 4594313 * 2
def baseEnd_4594313 : Nat := 2359090846199988462958645

theorem tailTrace_4594313 : CollatzResearch.WordTrace tailWord_4594313 prefixEnd_4594313 2359090846199988462958645 := by
  unfold tailWord_4594313
  simp only [CollatzResearch.WordTrace]
  refine ⟨167568361404596122036635593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111712240936397414691090395 167568361404596122036635593)
  ·
    refine ⟨125676271053447091527476695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167568361404596122036635593 125676271053447091527476695)
    ·
      refine ⟨188514406580170637291215043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125676271053447091527476695 188514406580170637291215043)
      ·
        refine ⟨282771609870255955936822565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188514406580170637291215043 282771609870255955936822565)
        ·
          refine ⟨53019676850672991738154231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 282771609870255955936822565 53019676850672991738154231)
          ·
            refine ⟨79529515276009487607231347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53019676850672991738154231 79529515276009487607231347)
            ·
              refine ⟨119294272914014231410847021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79529515276009487607231347 119294272914014231410847021)
              ·
                refine ⟨44735352342755336779067633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 119294272914014231410847021 44735352342755336779067633)
                ·
                  refine ⟨33551514257066502584300725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44735352342755336779067633 33551514257066502584300725)
                  ·
                    refine ⟨3145454461599984617278193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33551514257066502584300725 3145454461599984617278193)
                    ·
                      refine ⟨2359090846199988462958645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3145454461599984617278193 2359090846199988462958645)
                      ·
                        rfl

theorem cell23_4594313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 5, 2].length) (baseStart_4594313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4594313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4594313 prefixEnd_4594313 := by exact prefixLift 4594313
  have htrace : WordTrace (prefixWord ++ tailWord_4594313) baseStart_4594313 baseEnd_4594313 := by
    simpa [prefixWord, tailWord_4594313, baseEnd_4594313] using wordTrace_append hprefix tailTrace_4594313
  have hstable : (prefixWord ++ tailWord_4594313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4594313).length < 2 ^ (prefixWord ++ tailWord_4594313).sum := by decide
  have hdescent : baseEnd_4594313 < baseStart_4594313 := by decide
  rcases family_descends (prefixWord ++ tailWord_4594313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4594350 : List Nat := [4, 1, 4, 1, 1, 1, 1, 2, 1, 2, 5]
def baseStart_4594350 : Nat := 118140960795 + 4594350 * 2 ^ 59
def prefixEnd_4594350 : Nat := 4983230072969 + 3 ^ 40 * 4594350 * 2
def baseEnd_4594350 : Nat := 2359109844984204818195975

theorem tailTrace_4594350 : CollatzResearch.WordTrace tailWord_4594350 prefixEnd_4594350 2359109844984204818195975 := by
  unfold tailWord_4594350
  simp only [CollatzResearch.WordTrace]
  refine ⟨20946213863182759669466563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111713140603641384903821669 20946213863182759669466563)
  ·
    refine ⟨31419320794774139504199845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20946213863182759669466563 31419320794774139504199845)
    ·
      refine ⟨5891122649020151157037471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31419320794774139504199845 5891122649020151157037471)
      ·
        refine ⟨8836683973530226735556207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5891122649020151157037471 8836683973530226735556207)
        ·
          refine ⟨13255025960295340103334311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8836683973530226735556207 13255025960295340103334311)
          ·
            refine ⟨19882538940443010155001467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13255025960295340103334311 19882538940443010155001467)
            ·
              refine ⟨29823808410664515232502201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19882538940443010155001467 29823808410664515232502201)
              ·
                refine ⟨22367856307998386424376651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29823808410664515232502201 22367856307998386424376651)
                ·
                  refine ⟨33551784461997579636564977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22367856307998386424376651 33551784461997579636564977)
                  ·
                    refine ⟨25163838346498184727423733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33551784461997579636564977 25163838346498184727423733)
                    ·
                      refine ⟨2359109844984204818195975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25163838346498184727423733 2359109844984204818195975)
                      ·
                        rfl

theorem cell23_4594350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_4594350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4594350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4594350 prefixEnd_4594350 := by exact prefixLift 4594350
  have htrace : WordTrace (prefixWord ++ tailWord_4594350) baseStart_4594350 baseEnd_4594350 := by
    simpa [prefixWord, tailWord_4594350, baseEnd_4594350] using wordTrace_append hprefix tailTrace_4594350
  have hstable : (prefixWord ++ tailWord_4594350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4594350).length < 2 ^ (prefixWord ++ tailWord_4594350).sum := by decide
  have hdescent : baseEnd_4594350 < baseStart_4594350 := by decide
  rcases family_descends (prefixWord ++ tailWord_4594350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4594410 : List Nat := [3, 1, 3, 1, 1, 1, 1, 1, 7, 1, 3]
def baseStart_4594410 : Nat := 118140960795 + 4594410 * 2 ^ 59
def prefixEnd_4594410 : Nat := 4983230072969 + 3 ^ 40 * 4594410 * 2
def baseEnd_4594410 : Nat := 2359140653823474583445699

theorem tailTrace_4594410 : CollatzResearch.WordTrace tailWord_4594410 prefixEnd_4594410 2359140653823474583445699 := by
  unfold tailWord_4594410
  simp only [CollatzResearch.WordTrace]
  refine ⟨41892974821311176900729171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111714599523496471735277789 41892974821311176900729171)
  ·
    refine ⟨62839462231966765351093757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41892974821311176900729171 62839462231966765351093757)
    ·
      refine ⟨23564798336987537006660159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62839462231966765351093757 23564798336987537006660159)
      ·
        refine ⟨35347197505481305509990239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23564798336987537006660159 35347197505481305509990239)
        ·
          refine ⟨53020796258221958264985359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35347197505481305509990239 53020796258221958264985359)
          ·
            refine ⟨79531194387332937397478039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53020796258221958264985359 79531194387332937397478039)
            ·
              refine ⟨119296791580999406096217059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79531194387332937397478039 119296791580999406096217059)
              ·
                refine ⟨178945187371499109144325589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119296791580999406096217059 178945187371499109144325589)
                ·
                  refine ⟨4194027829019510370570131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 178945187371499109144325589 4194027829019510370570131)
                  ·
                    refine ⟨6291041743529265555855197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4194027829019510370570131 6291041743529265555855197)
                    ·
                      refine ⟨2359140653823474583445699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6291041743529265555855197 2359140653823474583445699)
                      ·
                        rfl

theorem cell23_4594410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 7, 1, 3].length) (baseStart_4594410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4594410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4594410 prefixEnd_4594410 := by exact prefixLift 4594410
  have htrace : WordTrace (prefixWord ++ tailWord_4594410) baseStart_4594410 baseEnd_4594410 := by
    simpa [prefixWord, tailWord_4594410, baseEnd_4594410] using wordTrace_append hprefix tailTrace_4594410
  have hstable : (prefixWord ++ tailWord_4594410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4594410).length < 2 ^ (prefixWord ++ tailWord_4594410).sum := by decide
  have hdescent : baseEnd_4594410 < baseStart_4594410 := by decide
  rcases family_descends (prefixWord ++ tailWord_4594410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4594421 : List Nat := [1, 3, 6, 1, 1, 1, 2, 1, 3, 4]
def baseStart_4594421 : Nat := 118140960795 + 4594421 * 2 ^ 59
def prefixEnd_4594421 : Nat := 4983230072969 + 3 ^ 40 * 4594421 * 2
def baseEnd_4594421 : Nat := 786382100703558013469383

theorem tailTrace_4594421 : CollatzResearch.WordTrace tailWord_4594421 prefixEnd_4594421 786382100703558013469383 := by
  unfold tailWord_4594421
  simp only [CollatzResearch.WordTrace]
  refine ⟨167572300488204856481567117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111714866992136570987711411 167572300488204856481567117)
  ·
    refine ⟨62839612683076821180587669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167572300488204856481567117 62839612683076821180587669)
    ·
      refine ⟨2945606844519225992840047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 62839612683076821180587669 2945606844519225992840047)
      ·
        refine ⟨4418410266778838989260071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2945606844519225992840047 4418410266778838989260071)
        ·
          refine ⟨6627615400168258483890107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4418410266778838989260071 6627615400168258483890107)
          ·
            refine ⟨9941423100252387725835161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6627615400168258483890107 9941423100252387725835161)
            ·
              refine ⟨7456067325189290794376371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9941423100252387725835161 7456067325189290794376371)
              ·
                refine ⟨11184100987783936191564557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7456067325189290794376371 11184100987783936191564557)
                ·
                  refine ⟨4194037870418976071836709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11184100987783936191564557 4194037870418976071836709)
                  ·
                    refine ⟨786382100703558013469383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4194037870418976071836709 786382100703558013469383)
                    ·
                      rfl

theorem cell23_4594421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_4594421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4594421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4594421 prefixEnd_4594421 := by exact prefixLift 4594421
  have htrace : WordTrace (prefixWord ++ tailWord_4594421) baseStart_4594421 baseEnd_4594421 := by
    simpa [prefixWord, tailWord_4594421, baseEnd_4594421] using wordTrace_append hprefix tailTrace_4594421
  have hstable : (prefixWord ++ tailWord_4594421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4594421).length < 2 ^ (prefixWord ++ tailWord_4594421).sum := by decide
  have hdescent : baseEnd_4594421 < baseStart_4594421 := by decide
  rcases family_descends (prefixWord ++ tailWord_4594421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4594453 : List Nat := [1, 3, 2, 1, 2, 2, 1, 2, 3, 1, 5]
def baseStart_4594453 : Nat := 118140960795 + 4594453 * 2 ^ 59
def prefixEnd_4594453 : Nat := 4983230072969 + 3 ^ 40 * 4594453 * 2
def baseEnd_4594453 : Nat := 2359162733491617915208001

theorem tailTrace_4594453 : CollatzResearch.WordTrace tailWord_4594453 prefixEnd_4594453 2359162733491617915208001 := by
  unfold tailWord_4594453
  simp only [CollatzResearch.WordTrace]
  refine ⟨167573467624088925946732013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111715645082725950631154675 167573467624088925946732013)
  ·
    refine ⟨62840050359033347230024505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167573467624088925946732013 62840050359033347230024505)
    ·
      refine ⟨47130037769275010422518379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62840050359033347230024505 47130037769275010422518379)
      ·
        refine ⟨70695056653912515633777569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47130037769275010422518379 70695056653912515633777569)
        ·
          refine ⟨53021292490434386725333177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70695056653912515633777569 53021292490434386725333177)
          ·
            refine ⟨39765969367825790043999883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53021292490434386725333177 39765969367825790043999883)
            ·
              refine ⟨59648954051738685065999825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39765969367825790043999883 59648954051738685065999825)
              ·
                refine ⟨44736715538804013799499869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59648954051738685065999825 44736715538804013799499869)
                ·
                  refine ⟨16776268327051505174812451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44736715538804013799499869 16776268327051505174812451)
                  ·
                    refine ⟨25164402490577257762218677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16776268327051505174812451 25164402490577257762218677)
                    ·
                      refine ⟨2359162733491617915208001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25164402490577257762218677 2359162733491617915208001)
                      ·
                        rfl

theorem cell23_4594453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 3, 1, 5].length) (baseStart_4594453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4594453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4594453 prefixEnd_4594453 := by exact prefixLift 4594453
  have htrace : WordTrace (prefixWord ++ tailWord_4594453) baseStart_4594453 baseEnd_4594453 := by
    simpa [prefixWord, tailWord_4594453, baseEnd_4594453] using wordTrace_append hprefix tailTrace_4594453
  have hstable : (prefixWord ++ tailWord_4594453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4594453).length < 2 ^ (prefixWord ++ tailWord_4594453).sum := by decide
  have hdescent : baseEnd_4594453 < baseStart_4594453 := by decide
  rcases family_descends (prefixWord ++ tailWord_4594453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4594460 : List Nat := [2, 2, 3, 1, 1, 3, 1, 2, 4, 4]
def baseStart_4594460 : Nat := 118140960795 + 4594460 * 2 ^ 59
def prefixEnd_4594460 : Nat := 4983230072969 + 3 ^ 40 * 4594460 * 2
def baseEnd_4594460 : Nat := 786388775952066462606823

theorem tailTrace_4594460 : CollatzResearch.WordTrace tailWord_4594460 prefixEnd_4594460 786388775952066462606823 := by
  unfold tailWord_4594460
  simp only [CollatzResearch.WordTrace]
  refine ⟨83786861467531783071118417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111715815290042377428157889 83786861467531783071118417)
  ·
    refine ⟨62840146100648837303338813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83786861467531783071118417 62840146100648837303338813)
    ·
      refine ⟨23565054787743313988752055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62840146100648837303338813 23565054787743313988752055)
      ·
        refine ⟨35347582181614970983128083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23565054787743313988752055 35347582181614970983128083)
        ·
          refine ⟨53021373272422456474692125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35347582181614970983128083 53021373272422456474692125)
          ·
            refine ⟨19883014977158421178009547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53021373272422456474692125 19883014977158421178009547)
            ·
              refine ⟨29824522465737631767014321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19883014977158421178009547 29824522465737631767014321)
              ·
                refine ⟨22368391849303223825260741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29824522465737631767014321 22368391849303223825260741)
                ·
                  refine ⟨4194073471744354467236389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22368391849303223825260741 4194073471744354467236389)
                  ·
                    refine ⟨786388775952066462606823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4194073471744354467236389 786388775952066462606823)
                    ·
                      rfl

theorem cell23_4594460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 4, 4].length) (baseStart_4594460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4594460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4594460 prefixEnd_4594460 := by exact prefixLift 4594460
  have htrace : WordTrace (prefixWord ++ tailWord_4594460) baseStart_4594460 baseEnd_4594460 := by
    simpa [prefixWord, tailWord_4594460, baseEnd_4594460] using wordTrace_append hprefix tailTrace_4594460
  have hstable : (prefixWord ++ tailWord_4594460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4594460).length < 2 ^ (prefixWord ++ tailWord_4594460).sum := by decide
  have hdescent : baseEnd_4594460 < baseStart_4594460 := by decide
  rcases family_descends (prefixWord ++ tailWord_4594460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4594478 : List Nat := [4, 1, 3, 2, 1, 2, 3, 2, 1, 1, 3]
def baseStart_4594478 : Nat := 118140960795 + 4594478 * 2 ^ 59
def prefixEnd_4594478 : Nat := 4983230072969 + 3 ^ 40 * 4594478 * 2
def baseEnd_4594478 : Nat := 2359175570507980317395387

theorem tailTrace_4594478 : CollatzResearch.WordTrace tailWord_4594478 prefixEnd_4594478 2359175570507980317395387 := by
  unfold tailWord_4594478
  simp only [CollatzResearch.WordTrace]
  refine ⟨20946797431124794402049011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111716252965998903477594725 20946797431124794402049011)
  ·
    refine ⟨31420196146687191603073517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20946797431124794402049011 31420196146687191603073517)
    ·
      refine ⟨11782573555007696851152569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31420196146687191603073517 11782573555007696851152569)
      ·
        refine ⟨8836930166255772638364427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11782573555007696851152569 8836930166255772638364427)
        ·
          refine ⟨13255395249383658957546641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8836930166255772638364427 13255395249383658957546641)
          ·
            refine ⟨9941546437037744218159981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13255395249383658957546641 9941546437037744218159981)
            ·
              refine ⟨3728079913889154081809993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9941546437037744218159981 3728079913889154081809993)
              ·
                refine ⟨2796059935416865561357495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3728079913889154081809993 2796059935416865561357495)
                ·
                  refine ⟨4194089903125298342036243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2796059935416865561357495 4194089903125298342036243)
                  ·
                    refine ⟨6291134854687947513054365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4194089903125298342036243 6291134854687947513054365)
                    ·
                      refine ⟨2359175570507980317395387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6291134854687947513054365 2359175570507980317395387)
                      ·
                        rfl

theorem cell23_4594478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_4594478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4594478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4594478 prefixEnd_4594478 := by exact prefixLift 4594478
  have htrace : WordTrace (prefixWord ++ tailWord_4594478) baseStart_4594478 baseEnd_4594478 := by
    simpa [prefixWord, tailWord_4594478, baseEnd_4594478] using wordTrace_append hprefix tailTrace_4594478
  have hstable : (prefixWord ++ tailWord_4594478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4594478).length < 2 ^ (prefixWord ++ tailWord_4594478).sum := by decide
  have hdescent : baseEnd_4594478 < baseStart_4594478 := by decide
  rcases family_descends (prefixWord ++ tailWord_4594478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4594490 : List Nat := [3, 1, 1, 1, 6, 1, 2, 8]
def baseStart_4594490 : Nat := 118140960795 + 4594490 * 2 ^ 59
def prefixEnd_4594490 : Nat := 4983230072969 + 3 ^ 40 * 4594490 * 2
def baseEnd_4594490 : Nat := 87377101195401269275753

theorem tailTrace_4594490 : CollatzResearch.WordTrace tailWord_4594490 prefixEnd_4594490 87377101195401269275753 := by
  unfold tailWord_4594490
  simp only [CollatzResearch.WordTrace]
  refine ⟨41893704281238720316457231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111716544749969920843885949 41893704281238720316457231)
  ·
    refine ⟨62840556421858080474685847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41893704281238720316457231 62840556421858080474685847)
    ·
      refine ⟨94260834632787120712028771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62840556421858080474685847 94260834632787120712028771)
      ·
        refine ⟨141391251949180681068043157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94260834632787120712028771 141391251949180681068043157)
        ·
          refine ⟨6627714935117844425064523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 141391251949180681068043157 6627714935117844425064523)
          ·
            refine ⟨9941572402676766637596785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6627714935117844425064523 9941572402676766637596785)
            ·
              refine ⟨7456179302007574978197589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9941572402676766637596785 7456179302007574978197589)
              ·
                refine ⟨87377101195401269275753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7456179302007574978197589 87377101195401269275753)
                ·
                  rfl

theorem cell23_4594490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 8].length) (baseStart_4594490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4594490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4594490 prefixEnd_4594490 := by exact prefixLift 4594490
  have htrace : WordTrace (prefixWord ++ tailWord_4594490) baseStart_4594490 baseEnd_4594490 := by
    simpa [prefixWord, tailWord_4594490, baseEnd_4594490] using wordTrace_append hprefix tailTrace_4594490
  have hstable : (prefixWord ++ tailWord_4594490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4594490).length < 2 ^ (prefixWord ++ tailWord_4594490).sum := by decide
  have hdescent : baseEnd_4594490 < baseStart_4594490 := by decide
  rcases family_descends (prefixWord ++ tailWord_4594490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4594494 : List Nat := [4, 2, 1, 2, 3, 1, 1, 3, 2, 4]
def baseStart_4594494 : Nat := 118140960795 + 4594494 * 2 ^ 59
def prefixEnd_4594494 : Nat := 4983230072969 + 3 ^ 40 * 4594494 * 2
def baseEnd_4594494 : Nat := 786394595399484084931771

theorem tailTrace_4594494 : CollatzResearch.WordTrace tailWord_4594494 prefixEnd_4594494 786394595399484084931771 := by
  unfold tailWord_4594494
  simp only [CollatzResearch.WordTrace]
  refine ⟨20946870377117548743621817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111716642011293593299316357 20946870377117548743621817)
  ·
    refine ⟨15710152782838161557716363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20946870377117548743621817 15710152782838161557716363)
    ·
      refine ⟨23565229174257242336574545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15710152782838161557716363 23565229174257242336574545)
      ·
        refine ⟨17673921880692931752430909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23565229174257242336574545 17673921880692931752430909)
        ·
          refine ⟨6627720705259849407161591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17673921880692931752430909 6627720705259849407161591)
          ·
            refine ⟨9941581057889774110742387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6627720705259849407161591 9941581057889774110742387)
            ·
              refine ⟨14912371586834661166113581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9941581057889774110742387 14912371586834661166113581)
              ·
                refine ⟨5592139345062997937292593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14912371586834661166113581 5592139345062997937292593)
                ·
                  refine ⟨4194104508797248452969445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5592139345062997937292593 4194104508797248452969445)
                  ·
                    refine ⟨786394595399484084931771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4194104508797248452969445 786394595399484084931771)
                    ·
                      rfl

theorem cell23_4594494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 3, 2, 4].length) (baseStart_4594494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4594494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4594494 prefixEnd_4594494 := by exact prefixLift 4594494
  have htrace : WordTrace (prefixWord ++ tailWord_4594494) baseStart_4594494 baseEnd_4594494 := by
    simpa [prefixWord, tailWord_4594494, baseEnd_4594494] using wordTrace_append hprefix tailTrace_4594494
  have hstable : (prefixWord ++ tailWord_4594494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4594494).length < 2 ^ (prefixWord ++ tailWord_4594494).sum := by decide
  have hdescent : baseEnd_4594494 < baseStart_4594494 := by decide
  rcases family_descends (prefixWord ++ tailWord_4594494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4594543 : List Nat := [1, 1, 2, 1, 3, 1, 1, 4, 1, 3, 5]
def baseStart_4594543 : Nat := 118140960795 + 4594543 * 2 ^ 59
def prefixEnd_4594543 : Nat := 4983230072969 + 3 ^ 40 * 4594543 * 2
def baseEnd_4594543 : Nat := 2359208946750522563082587

theorem tailTrace_4594543 : CollatzResearch.WordTrace tailWord_4594543 prefixEnd_4594543 2359208946750522563082587 := by
  unfold tailWord_4594543
  simp only [CollatzResearch.WordTrace]
  refine ⟨167576750193762871317508283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111717833462508580878338855 167576750193762871317508283)
  ·
    refine ⟨251365125290644306976262425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167576750193762871317508283 251365125290644306976262425)
    ·
      refine ⟨188523843967983230232196819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 251365125290644306976262425 188523843967983230232196819)
      ·
        refine ⟨282785765951974845348295229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188523843967983230232196819 282785765951974845348295229)
        ·
          refine ⟨106044662231990567005610711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 282785765951974845348295229 106044662231990567005610711)
          ·
            refine ⟨159066993347985850508416067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106044662231990567005610711 159066993347985850508416067)
            ·
              refine ⟨238600490021978775762624101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159066993347985850508416067 238600490021978775762624101)
              ·
                refine ⟨44737591879121020455492019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 238600490021978775762624101 44737591879121020455492019)
                ·
                  refine ⟨67106387818681530683238029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44737591879121020455492019 67106387818681530683238029)
                  ·
                    refine ⟨25164895432005574006214261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 67106387818681530683238029 25164895432005574006214261)
                    ·
                      refine ⟨2359208946750522563082587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25164895432005574006214261 2359208946750522563082587)
                      ·
                        rfl

theorem cell23_4594543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 3, 5].length) (baseStart_4594543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4594543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4594543 prefixEnd_4594543 := by exact prefixLift 4594543
  have htrace : WordTrace (prefixWord ++ tailWord_4594543) baseStart_4594543 baseEnd_4594543 := by
    simpa [prefixWord, tailWord_4594543, baseEnd_4594543] using wordTrace_append hprefix tailTrace_4594543
  have hstable : (prefixWord ++ tailWord_4594543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4594543).length < 2 ^ (prefixWord ++ tailWord_4594543).sum := by decide
  have hdescent : baseEnd_4594543 < baseStart_4594543 := by decide
  rcases family_descends (prefixWord ++ tailWord_4594543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4594557 : List Nat := [1, 4, 1, 1, 2, 1, 3, 3, 1, 4, 2]
def baseStart_4594557 : Nat := 118140960795 + 4594557 * 2 ^ 59
def prefixEnd_4594557 : Nat := 4983230072969 + 3 ^ 40 * 4594557 * 2
def baseEnd_4594557 : Nat := 2359216135479685508307523

theorem tailTrace_4594557 : CollatzResearch.WordTrace tailWord_4594557 prefixEnd_4594557 2359216135479685508307523 := by
  unfold tailWord_4594557
  simp only [CollatzResearch.WordTrace]
  refine ⟨167577260815712151708517925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111718173877141434472345283 167577260815712151708517925)
  ·
    refine ⟨31420736402946028445347111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 167577260815712151708517925 31420736402946028445347111)
    ·
      refine ⟨47131104604419042668020667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31420736402946028445347111 47131104604419042668020667)
      ·
        refine ⟨70696656906628564002031001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47131104604419042668020667 70696656906628564002031001)
        ·
          refine ⟨53022492679971423001523251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70696656906628564002031001 53022492679971423001523251)
          ·
            refine ⟨79533739019957134502284877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53022492679971423001523251 79533739019957134502284877)
            ·
              refine ⟨29825152132483925438356829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79533739019957134502284877 29825152132483925438356829)
              ·
                refine ⟨11184432049681472039383811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29825152132483925438356829 11184432049681472039383811)
                ·
                  refine ⟨16776648074522208059075717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11184432049681472039383811 16776648074522208059075717)
                  ·
                    refine ⟨3145621513972914011076697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16776648074522208059075717 3145621513972914011076697)
                    ·
                      refine ⟨2359216135479685508307523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3145621513972914011076697 2359216135479685508307523)
                      ·
                        rfl

theorem cell23_4594557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 3, 1, 4, 2].length) (baseStart_4594557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4594557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4594557 prefixEnd_4594557 := by exact prefixLift 4594557
  have htrace : WordTrace (prefixWord ++ tailWord_4594557) baseStart_4594557 baseEnd_4594557 := by
    simpa [prefixWord, tailWord_4594557, baseEnd_4594557] using wordTrace_append hprefix tailTrace_4594557
  have hstable : (prefixWord ++ tailWord_4594557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4594557).length < 2 ^ (prefixWord ++ tailWord_4594557).sum := by decide
  have hdescent : baseEnd_4594557 < baseStart_4594557 := by decide
  rcases family_descends (prefixWord ++ tailWord_4594557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4594580 : List Nat := [2, 4, 2, 1, 1, 1, 1, 2, 9]
def baseStart_4594580 : Nat := 118140960795 + 4594580 * 2 ^ 59
def prefixEnd_4594580 : Nat := 4983230072969 + 3 ^ 40 * 4594580 * 2
def baseEnd_4594580 : Nat := 262136438392748768702213

theorem tailTrace_4594580 : CollatzResearch.WordTrace tailWord_4594580 prefixEnd_4594580 262136438392748768702213 := by
  unfold tailWord_4594580
  simp only [CollatzResearch.WordTrace]
  refine ⟨83789049847314413318302597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111718733129752551091070129 83789049847314413318302597)
  ·
    refine ⟨15710446846371452497181737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83789049847314413318302597 15710446846371452497181737)
    ·
      refine ⟨11782835134778589372886303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15710446846371452497181737 11782835134778589372886303)
      ·
        refine ⟨17674252702167884059329455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11782835134778589372886303 17674252702167884059329455)
        ·
          refine ⟨26511379053251826088994183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17674252702167884059329455 26511379053251826088994183)
          ·
            refine ⟨39767068579877739133491275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26511379053251826088994183 39767068579877739133491275)
            ·
              refine ⟨59650602869816608700236913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39767068579877739133491275 59650602869816608700236913)
              ·
                refine ⟨44737952152362456525177685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59650602869816608700236913 44737952152362456525177685)
                ·
                  refine ⟨262136438392748768702213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 44737952152362456525177685 262136438392748768702213)
                  ·
                    rfl

theorem cell23_4594580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 9].length) (baseStart_4594580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4594580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4594580 prefixEnd_4594580 := by exact prefixLift 4594580
  have htrace : WordTrace (prefixWord ++ tailWord_4594580) baseStart_4594580 baseEnd_4594580 := by
    simpa [prefixWord, tailWord_4594580, baseEnd_4594580] using wordTrace_append hprefix tailTrace_4594580
  have hstable : (prefixWord ++ tailWord_4594580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4594580).length < 2 ^ (prefixWord ++ tailWord_4594580).sum := by decide
  have hdescent : baseEnd_4594580 < baseStart_4594580 := by decide
  rcases family_descends (prefixWord ++ tailWord_4594580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4594591 : List Nat := [1, 1, 2, 5, 2, 1, 3, 2, 2, 2, 2]
def baseStart_4594591 : Nat := 118140960795 + 4594591 * 2 ^ 59
def prefixEnd_4594591 : Nat := 4983230072969 + 3 ^ 40 * 4594591 * 2
def baseEnd_4594591 : Nat := 2359233593821938375282367

theorem tailTrace_4594591 : CollatzResearch.WordTrace tailWord_4594591 prefixEnd_4594591 2359233593821938375282367 := by
  unfold tailWord_4594591
  simp only [CollatzResearch.WordTrace]
  refine ⟨167578500897588975515255627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111719000598392650343503751 167578500897588975515255627)
  ·
    refine ⟨251367751346383463272883441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167578500897588975515255627 251367751346383463272883441)
    ·
      refine ⟨188525813509787597454662581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 251367751346383463272883441 188525813509787597454662581)
      ·
        refine ⟨17674295016542587261374617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 188525813509787597454662581 17674295016542587261374617)
        ·
          refine ⟨13255721262406940446030963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17674295016542587261374617 13255721262406940446030963)
          ·
            refine ⟨19883581893610410669046445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13255721262406940446030963 19883581893610410669046445)
            ·
              refine ⟨7456343210103904000892417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19883581893610410669046445 7456343210103904000892417)
              ·
                refine ⟨5592257407577928000669313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7456343210103904000892417 5592257407577928000669313)
                ·
                  refine ⟨4194193055683446000501985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5592257407577928000669313 4194193055683446000501985)
                  ·
                    refine ⟨3145644791762584500376489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4194193055683446000501985 3145644791762584500376489)
                    ·
                      refine ⟨2359233593821938375282367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3145644791762584500376489 2359233593821938375282367)
                      ·
                        rfl

theorem cell23_4594591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 2, 2, 2, 2].length) (baseStart_4594591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4594591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4594591 prefixEnd_4594591 := by exact prefixLift 4594591
  have htrace : WordTrace (prefixWord ++ tailWord_4594591) baseStart_4594591 baseEnd_4594591 := by
    simpa [prefixWord, tailWord_4594591, baseEnd_4594591] using wordTrace_append hprefix tailTrace_4594591
  have hstable : (prefixWord ++ tailWord_4594591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4594591).length < 2 ^ (prefixWord ++ tailWord_4594591).sum := by decide
  have hdescent : baseEnd_4594591 < baseStart_4594591 := by decide
  rcases family_descends (prefixWord ++ tailWord_4594591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4594647 : List Nat := [1, 1, 3, 2, 1, 1, 2, 4, 2, 4, 2]
def baseStart_4594647 : Nat := 118140960795 + 4594647 * 2 ^ 59
def prefixEnd_4594647 : Nat := 4983230072969 + 3 ^ 40 * 4594647 * 2
def baseEnd_4594647 : Nat := 2359262348738590156182109

theorem tailTrace_4594647 : CollatzResearch.WordTrace tailWord_4594647 prefixEnd_4594647 2359262348738590156182109 := by
  unfold tailWord_4594647
  simp only [CollatzResearch.WordTrace]
  refine ⟨167580543385386097079294195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111720362256924064719529463 167580543385386097079294195)
  ·
    refine ⟨251370815078079145618941293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167580543385386097079294195 251370815078079145618941293)
    ·
      refine ⟨94264055654279679607102985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 251370815078079145618941293 94264055654279679607102985)
      ·
        refine ⟨70698041740709759705327239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94264055654279679607102985 70698041740709759705327239)
        ·
          refine ⟨106047062611064639557990859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70698041740709759705327239 106047062611064639557990859)
          ·
            refine ⟨159070593916596959336986289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106047062611064639557990859 159070593916596959336986289)
            ·
              refine ⟨119302945437447719502739717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 159070593916596959336986289 119302945437447719502739717)
              ·
                refine ⟨22369302269521447406763697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 119302945437447719502739717 22369302269521447406763697)
                ·
                  refine ⟨16776976702141085555072773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22369302269521447406763697 16776976702141085555072773)
                  ·
                    refine ⟨3145683131651453541576145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16776976702141085555072773 3145683131651453541576145)
                    ·
                      refine ⟨2359262348738590156182109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3145683131651453541576145 2359262348738590156182109)
                      ·
                        rfl

theorem cell23_4594647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 2, 4, 2].length) (baseStart_4594647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4594647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4594647 prefixEnd_4594647 := by exact prefixLift 4594647
  have htrace : WordTrace (prefixWord ++ tailWord_4594647) baseStart_4594647 baseEnd_4594647 := by
    simpa [prefixWord, tailWord_4594647, baseEnd_4594647] using wordTrace_append hprefix tailTrace_4594647
  have hstable : (prefixWord ++ tailWord_4594647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4594647).length < 2 ^ (prefixWord ++ tailWord_4594647).sum := by decide
  have hdescent : baseEnd_4594647 < baseStart_4594647 := by decide
  rcases family_descends (prefixWord ++ tailWord_4594647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4594660 : List Nat := [2, 3, 1, 1, 1, 1, 2, 2, 2, 4, 4]
def baseStart_4594660 : Nat := 118140960795 + 4594660 * 2 ^ 59
def prefixEnd_4594660 : Nat := 4983230072969 + 3 ^ 40 * 4594660 * 2
def baseEnd_4594660 : Nat := 2359269023987098605319549

theorem tailTrace_4594660 : CollatzResearch.WordTrace tailWord_4594660 prefixEnd_4594660 2359269023987098605319549 := by
  unfold tailWord_4594660
  simp only [CollatzResearch.WordTrace]
  refine ⟨83790508767169500149758717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111720678356226000199678289 83790508767169500149758717)
  ·
    refine ⟨31421440787688562556159519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83790508767169500149758717 31421440787688562556159519)
    ·
      refine ⟨47132161181532843834239279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31421440787688562556159519 47132161181532843834239279)
      ·
        refine ⟨70698241772299265751358919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47132161181532843834239279 70698241772299265751358919)
        ·
          refine ⟨106047362658448898627038379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70698241772299265751358919 106047362658448898627038379)
          ·
            refine ⟨159071043987673347940557569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106047362658448898627038379 159071043987673347940557569)
            ·
              refine ⟨119303282990755010955418177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 159071043987673347940557569 119303282990755010955418177)
              ·
                refine ⟨89477462243066258216563633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 119303282990755010955418177 89477462243066258216563633)
                ·
                  refine ⟨67108096682299693662422725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 89477462243066258216563633 67108096682299693662422725)
                  ·
                    refine ⟨12582768127931192561704261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 67108096682299693662422725 12582768127931192561704261)
                    ·
                      refine ⟨2359269023987098605319549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12582768127931192561704261 2359269023987098605319549)
                      ·
                        rfl

theorem cell23_4594660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 2, 4, 4].length) (baseStart_4594660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4594660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4594660 prefixEnd_4594660 := by exact prefixLift 4594660
  have htrace : WordTrace (prefixWord ++ tailWord_4594660) baseStart_4594660 baseEnd_4594660 := by
    simpa [prefixWord, tailWord_4594660, baseEnd_4594660] using wordTrace_append hprefix tailTrace_4594660
  have hstable : (prefixWord ++ tailWord_4594660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4594660).length < 2 ^ (prefixWord ++ tailWord_4594660).sum := by decide
  have hdescent : baseEnd_4594660 < baseStart_4594660 := by decide
  rcases family_descends (prefixWord ++ tailWord_4594660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4594684 : List Nat := [2, 2, 2, 1, 2, 4, 2, 1, 2, 2, 3]
def baseStart_4594684 : Nat := 118140960795 + 4594684 * 2 ^ 59
def prefixEnd_4594684 : Nat := 4983230072969 + 3 ^ 40 * 4594684 * 2
def baseEnd_4594684 : Nat := 2359281347522806511419439

theorem tailTrace_4594684 : CollatzResearch.WordTrace tailWord_4594684 prefixEnd_4594684 2359281347522806511419439 := by
  unfold tailWord_4594684
  simp only [CollatzResearch.WordTrace]
  refine ⟨83790946443126026199195553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111721261924168034932260737 83790946443126026199195553)
  ·
    refine ⟨62843209832344519649396665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83790946443126026199195553 62843209832344519649396665)
    ·
      refine ⟨47132407374258389737047499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62843209832344519649396665 47132407374258389737047499)
      ·
        refine ⟨70698611061387584605571249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47132407374258389737047499 70698611061387584605571249)
        ·
          refine ⟨53023958296040688454178437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70698611061387584605571249 53023958296040688454178437)
          ·
            refine ⟨9941992180507629085158457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53023958296040688454178437 9941992180507629085158457)
            ·
              refine ⟨7456494135380721813868843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9941992180507629085158457 7456494135380721813868843)
              ·
                refine ⟨11184741203071082720803265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7456494135380721813868843 11184741203071082720803265)
                ·
                  refine ⟨8388555902303312040602449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11184741203071082720803265 8388555902303312040602449)
                  ·
                    refine ⟨6291416926727484030451837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8388555902303312040602449 6291416926727484030451837)
                    ·
                      refine ⟨2359281347522806511419439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6291416926727484030451837 2359281347522806511419439)
                      ·
                        rfl

theorem cell23_4594684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 1, 2, 2, 3].length) (baseStart_4594684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4594684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4594684 prefixEnd_4594684 := by exact prefixLift 4594684
  have htrace : WordTrace (prefixWord ++ tailWord_4594684) baseStart_4594684 baseEnd_4594684 := by
    simpa [prefixWord, tailWord_4594684, baseEnd_4594684] using wordTrace_append hprefix tailTrace_4594684
  have hstable : (prefixWord ++ tailWord_4594684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4594684).length < 2 ^ (prefixWord ++ tailWord_4594684).sum := by decide
  have hdescent : baseEnd_4594684 < baseStart_4594684 := by decide
  rcases family_descends (prefixWord ++ tailWord_4594684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4594707 : List Nat := [1, 1, 1, 2, 1, 4, 1, 2, 3, 5, 2]
def baseStart_4594707 : Nat := 118140960795 + 4594707 * 2 ^ 59
def prefixEnd_4594707 : Nat := 4983230072969 + 3 ^ 40 * 4594707 * 2
def baseEnd_4594707 : Nat := 2359293157577859921431833

theorem tailTrace_4594707 : CollatzResearch.WordTrace tailWord_4594707 prefixEnd_4594707 2359293157577859921431833 := by
  unfold tailWord_4594707
  simp only [CollatzResearch.WordTrace]
  refine ⟨167582731765168727326478375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111721821176779151550985583 167582731765168727326478375)
  ·
    refine ⟨251374097647753090989717563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167582731765168727326478375 251374097647753090989717563)
    ·
      refine ⟨377061146471629636484576345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251374097647753090989717563 377061146471629636484576345)
      ·
        refine ⟨282795859853722227363432259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 377061146471629636484576345 282795859853722227363432259)
        ·
          refine ⟨424193789780583341045148389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 282795859853722227363432259 424193789780583341045148389)
          ·
            refine ⟨79536335583859376445965323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 424193789780583341045148389 79536335583859376445965323)
            ·
              refine ⟨119304503375789064668947985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79536335583859376445965323 119304503375789064668947985)
              ·
                refine ⟨89478377531841798501710989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 119304503375789064668947985 89478377531841798501710989)
                ·
                  refine ⟨33554391574440674438141621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 89478377531841798501710989 33554391574440674438141621)
                  ·
                    refine ⟨3145724210103813228575777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33554391574440674438141621 3145724210103813228575777)
                    ·
                      refine ⟨2359293157577859921431833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3145724210103813228575777 2359293157577859921431833)
                      ·
                        rfl

theorem cell23_4594707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 5, 2].length) (baseStart_4594707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4594707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4594707 prefixEnd_4594707 := by exact prefixLift 4594707
  have htrace : WordTrace (prefixWord ++ tailWord_4594707) baseStart_4594707 baseEnd_4594707 := by
    simpa [prefixWord, tailWord_4594707, baseEnd_4594707] using wordTrace_append hprefix tailTrace_4594707
  have hstable : (prefixWord ++ tailWord_4594707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4594707).length < 2 ^ (prefixWord ++ tailWord_4594707).sum := by decide
  have hdescent : baseEnd_4594707 < baseStart_4594707 := by decide
  rcases family_descends (prefixWord ++ tailWord_4594707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4594714 : List Nat := [3, 1, 1, 3, 1, 2, 2, 3, 3, 1, 3]
def baseStart_4594714 : Nat := 118140960795 + 4594714 * 2 ^ 59
def prefixEnd_4594714 : Nat := 4983230072969 + 3 ^ 40 * 4594714 * 2
def baseEnd_4594714 : Nat := 2359296751942441394044301

theorem tailTrace_4594714 : CollatzResearch.WordTrace tailWord_4594714 prefixEnd_4594714 2359296751942441394044301 := by
  unfold tailWord_4594714
  simp only [CollatzResearch.WordTrace]
  refine ⟨41895746769035841880495799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111721991384095578347988797 41895746769035841880495799)
  ·
    refine ⟨62843620153553762820743699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41895746769035841880495799 62843620153553762820743699)
    ·
      refine ⟨94265430230330644231115549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62843620153553762820743699 94265430230330644231115549)
      ·
        refine ⟨35349536336373991586668331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94265430230330644231115549 35349536336373991586668331)
        ·
          refine ⟨53024304504560987380002497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35349536336373991586668331 53024304504560987380002497)
          ·
            refine ⟨39768228378420740535001873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53024304504560987380002497 39768228378420740535001873)
            ·
              refine ⟨29826171283815555401251405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39768228378420740535001873 29826171283815555401251405)
              ·
                refine ⟨11184814231430833275469277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29826171283815555401251405 11184814231430833275469277)
                ·
                  refine ⟨4194305336786562478300979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11184814231430833275469277 4194305336786562478300979)
                  ·
                    refine ⟨6291458005179843717451469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4194305336786562478300979 6291458005179843717451469)
                    ·
                      refine ⟨2359296751942441394044301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6291458005179843717451469 2359296751942441394044301)
                      ·
                        rfl

theorem cell23_4594714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 3, 3, 1, 3].length) (baseStart_4594714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4594714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4594714 prefixEnd_4594714 := by exact prefixLift 4594714
  have htrace : WordTrace (prefixWord ++ tailWord_4594714) baseStart_4594714 baseEnd_4594714 := by
    simpa [prefixWord, tailWord_4594714, baseEnd_4594714] using wordTrace_append hprefix tailTrace_4594714
  have hstable : (prefixWord ++ tailWord_4594714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4594714).length < 2 ^ (prefixWord ++ tailWord_4594714).sum := by decide
  have hdescent : baseEnd_4594714 < baseStart_4594714 := by decide
  rcases family_descends (prefixWord ++ tailWord_4594714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4594734 : List Nat := [4, 1, 3, 1, 1, 1, 2, 4, 1, 5]
def baseStart_4594734 : Nat := 118140960795 + 4594734 * 2 ^ 59
def prefixEnd_4594734 : Nat := 4983230072969 + 3 ^ 40 * 4594734 * 2
def baseEnd_4594734 : Nat := 786435673851843771931403

theorem tailTrace_4594734 : CollatzResearch.WordTrace tailWord_4594734 prefixEnd_4594734 786435673851843771931403 := by
  unfold tailWord_4594734
  simp only [CollatzResearch.WordTrace]
  refine ⟨20947964567008863867213907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111722477690713940625140837 20947964567008863867213907)
  ·
    refine ⟨31421946850513295800820861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20947964567008863867213907 31421946850513295800820861)
    ·
      refine ⟨11783230068942485925307823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31421946850513295800820861 11783230068942485925307823)
      ·
        refine ⟨17674845103413728887961735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11783230068942485925307823 17674845103413728887961735)
        ·
          refine ⟨26512267655120593331942603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17674845103413728887961735 26512267655120593331942603)
          ·
            refine ⟨39768401482680889997913905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26512267655120593331942603 39768401482680889997913905)
            ·
              refine ⟨29826301112010667498435429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39768401482680889997913905 29826301112010667498435429)
              ·
                refine ⟨5592431458502000155956643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29826301112010667498435429 5592431458502000155956643)
                ·
                  refine ⟨8388647187753000233934965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5592431458502000155956643 8388647187753000233934965)
                  ·
                    refine ⟨786435673851843771931403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8388647187753000233934965 786435673851843771931403)
                    ·
                      rfl

theorem cell23_4594734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_4594734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4594734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4594734 prefixEnd_4594734 := by exact prefixLift 4594734
  have htrace : WordTrace (prefixWord ++ tailWord_4594734) baseStart_4594734 baseEnd_4594734 := by
    simpa [prefixWord, tailWord_4594734, baseEnd_4594734] using wordTrace_append hprefix tailTrace_4594734
  have hstable : (prefixWord ++ tailWord_4594734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4594734).length < 2 ^ (prefixWord ++ tailWord_4594734).sum := by decide
  have hdescent : baseEnd_4594734 < baseStart_4594734 := by decide
  rcases family_descends (prefixWord ++ tailWord_4594734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4594737 : List Nat := [1, 2, 2, 3, 1, 2, 1, 3, 3, 1, 4]
def baseStart_4594737 : Nat := 118140960795 + 4594737 * 2 ^ 59
def prefixEnd_4594737 : Nat := 4983230072969 + 3 ^ 40 * 4594737 * 2
def baseEnd_4594737 : Nat := 2359308561997494804056695

theorem tailTrace_4594737 : CollatzResearch.WordTrace tailWord_4594737 prefixEnd_4594737 2359308561997494804056695 := by
  unfold tailWord_4594737
  simp only [CollatzResearch.WordTrace]
  refine ⟨167583825955060042450070465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111722550636706694966713643 167583825955060042450070465)
  ·
    refine ⟨125687869466295031837552849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167583825955060042450070465 125687869466295031837552849)
    ·
      refine ⟨94265902099721273878164637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125687869466295031837552849 94265902099721273878164637)
      ·
        refine ⟨35349713287395477704311739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94265902099721273878164637 35349713287395477704311739)
        ·
          refine ⟨53024569931093216556467609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35349713287395477704311739 53024569931093216556467609)
          ·
            refine ⟨39768427448319912417350707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53024569931093216556467609 39768427448319912417350707)
            ·
              refine ⟨59652641172479868626026061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39768427448319912417350707 59652641172479868626026061)
              ·
                refine ⟨22369740439679950734759773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59652641172479868626026061 22369740439679950734759773)
                ·
                  refine ⟨8388652664879981525534915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22369740439679950734759773 8388652664879981525534915)
                  ·
                    refine ⟨12582978997319972288302373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8388652664879981525534915 12582978997319972288302373)
                    ·
                      refine ⟨2359308561997494804056695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12582978997319972288302373 2359308561997494804056695)
                      ·
                        rfl

theorem cell23_4594737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_4594737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4594737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4594737 prefixEnd_4594737 := by exact prefixLift 4594737
  have htrace : WordTrace (prefixWord ++ tailWord_4594737) baseStart_4594737 baseEnd_4594737 := by
    simpa [prefixWord, tailWord_4594737, baseEnd_4594737] using wordTrace_append hprefix tailTrace_4594737
  have hstable : (prefixWord ++ tailWord_4594737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4594737).length < 2 ^ (prefixWord ++ tailWord_4594737).sum := by decide
  have hdescent : baseEnd_4594737 < baseStart_4594737 := by decide
  rcases family_descends (prefixWord ++ tailWord_4594737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4594748 : List Nat := [2, 2, 2, 2, 2, 3, 2, 3, 1, 1, 3]
def baseStart_4594748 : Nat := 118140960795 + 4594748 * 2 ^ 59
def prefixEnd_4594748 : Nat := 4983230072969 + 3 ^ 40 * 4594748 * 2
def baseEnd_4594748 : Nat := 2359314210284694261019145

theorem tailTrace_4594748 : CollatzResearch.WordTrace tailWord_4594748 prefixEnd_4594748 2359314210284694261019145 := by
  unfold tailWord_4594748
  simp only [CollatzResearch.WordTrace]
  refine ⟨83792113579010095664360449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111722818105346794219147265 83792113579010095664360449)
  ·
    refine ⟨62844085184257571748270337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83792113579010095664360449 62844085184257571748270337)
    ·
      refine ⟨47133063888193178811202753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62844085184257571748270337 47133063888193178811202753)
      ·
        refine ⟨35349797916144884108402065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47133063888193178811202753 35349797916144884108402065)
        ·
          refine ⟨26512348437108663081301549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35349797916144884108402065 26512348437108663081301549)
          ·
            refine ⟨9942130663915748655488081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26512348437108663081301549 9942130663915748655488081)
            ·
              refine ⟨7456597997936811491616061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9942130663915748655488081 7456597997936811491616061)
              ·
                refine ⟨2796224249226304309356023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7456597997936811491616061 2796224249226304309356023)
                ·
                  refine ⟨4194336373839456464034035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2796224249226304309356023 4194336373839456464034035)
                  ·
                    refine ⟨6291504560759184696051053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4194336373839456464034035 6291504560759184696051053)
                    ·
                      refine ⟨2359314210284694261019145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6291504560759184696051053 2359314210284694261019145)
                      ·
                        rfl

theorem cell23_4594748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 3, 1, 1, 3].length) (baseStart_4594748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4594748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4594748 prefixEnd_4594748 := by exact prefixLift 4594748
  have htrace : WordTrace (prefixWord ++ tailWord_4594748) baseStart_4594748 baseEnd_4594748 := by
    simpa [prefixWord, tailWord_4594748, baseEnd_4594748] using wordTrace_append hprefix tailTrace_4594748
  have hstable : (prefixWord ++ tailWord_4594748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4594748).length < 2 ^ (prefixWord ++ tailWord_4594748).sum := by decide
  have hdescent : baseEnd_4594748 < baseStart_4594748 := by decide
  rcases family_descends (prefixWord ++ tailWord_4594748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4594760 : List Nat := [2, 1, 3, 1, 1, 1, 14]
def baseStart_4594760 : Nat := 118140960795 + 4594760 * 2 ^ 59
def prefixEnd_4594760 : Nat := 4983230072969 + 3 ^ 40 * 4594760 * 2
def baseEnd_4594760 : Nat := 29127412000648743383569

theorem tailTrace_4594760 : CollatzResearch.WordTrace tailWord_4594760 prefixEnd_4594760 29127412000648743383569 := by
  unfold tailWord_4594760
  simp only [CollatzResearch.WordTrace]
  refine ⟨83792332416988358689078867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111723109889317811585438489 83792332416988358689078867)
  ·
    refine ⟨125688498625482538033618301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83792332416988358689078867 125688498625482538033618301)
    ·
      refine ⟨47133186984555951762606863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125688498625482538033618301 47133186984555951762606863)
      ·
        refine ⟨70699780476833927643910295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47133186984555951762606863 70699780476833927643910295)
        ·
          refine ⟨106049670715250891465865443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70699780476833927643910295 106049670715250891465865443)
          ·
            refine ⟨159074506072876337198798165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106049670715250891465865443 159074506072876337198798165)
            ·
              refine ⟨29127412000648743383569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 159074506072876337198798165 29127412000648743383569)
              ·
                rfl

theorem cell23_4594760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 14].length) (baseStart_4594760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4594760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4594760 prefixEnd_4594760 := by exact prefixLift 4594760
  have htrace : WordTrace (prefixWord ++ tailWord_4594760) baseStart_4594760 baseEnd_4594760 := by
    simpa [prefixWord, tailWord_4594760, baseEnd_4594760] using wordTrace_append hprefix tailTrace_4594760
  have hstable : (prefixWord ++ tailWord_4594760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4594760).length < 2 ^ (prefixWord ++ tailWord_4594760).sum := by decide
  have hdescent : baseEnd_4594760 < baseStart_4594760 := by decide
  rcases family_descends (prefixWord ++ tailWord_4594760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4594791 : List Nat := [1, 1, 5, 1, 1, 4, 2, 2, 1, 2, 3]
def baseStart_4594791 : Nat := 118140960795 + 4594791 * 2 ^ 59
def prefixEnd_4594791 : Nat := 4983230072969 + 3 ^ 40 * 4594791 * 2
def baseEnd_4594791 : Nat := 2359336289952837592781447

theorem tailTrace_4594791 : CollatzResearch.WordTrace tailWord_4594791 prefixEnd_4594791 2359336289952837592781447 := by
  unfold tailWord_4594791
  simp only [CollatzResearch.WordTrace]
  refine ⟨167585795496864409672536227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111723863664576273115024151 167585795496864409672536227)
  ·
    refine ⟨251378693245296614508804341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167585795496864409672536227 251378693245296614508804341)
    ·
      refine ⟨23566752491746557610200407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 251378693245296614508804341 23566752491746557610200407)
      ·
        refine ⟨35350128737619836415300611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23566752491746557610200407 35350128737619836415300611)
        ·
          refine ⟨53025193106429754622950917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35350128737619836415300611 53025193106429754622950917)
          ·
            refine ⟨9942223707455578991803297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53025193106429754622950917 9942223707455578991803297)
            ·
              refine ⟨7456667780591684243852473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9942223707455578991803297 7456667780591684243852473)
              ·
                refine ⟨5592500835443763182889355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7456667780591684243852473 5592500835443763182889355)
                ·
                  refine ⟨8388751253165644774334033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5592500835443763182889355 8388751253165644774334033)
                  ·
                    refine ⟨6291563439874233580750525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8388751253165644774334033 6291563439874233580750525)
                    ·
                      refine ⟨2359336289952837592781447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6291563439874233580750525 2359336289952837592781447)
                      ·
                        rfl

theorem cell23_4594791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 2, 1, 2, 3].length) (baseStart_4594791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4594791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4594791 prefixEnd_4594791 := by exact prefixLift 4594791
  have htrace : WordTrace (prefixWord ++ tailWord_4594791) baseStart_4594791 baseEnd_4594791 := by
    simpa [prefixWord, tailWord_4594791, baseEnd_4594791] using wordTrace_append hprefix tailTrace_4594791
  have hstable : (prefixWord ++ tailWord_4594791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4594791).length < 2 ^ (prefixWord ++ tailWord_4594791).sum := by decide
  have hdescent : baseEnd_4594791 < baseStart_4594791 := by decide
  rcases family_descends (prefixWord ++ tailWord_4594791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4594794 : List Nat := [3, 1, 3, 2, 2, 1, 4, 7]
def baseStart_4594794 : Nat := 118140960795 + 4594794 * 2 ^ 59
def prefixEnd_4594794 : Nat := 4983230072969 + 3 ^ 40 * 4594794 * 2
def baseEnd_4594794 : Nat := 87382882607214854853479

theorem tailTrace_4594794 : CollatzResearch.WordTrace tailWord_4594794 prefixEnd_4594794 87382882607214854853479 := by
  unfold tailWord_4594794
  simp only [CollatzResearch.WordTrace]
  refine ⟨41896476228963385296223859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111723936610569027456596957 41896476228963385296223859)
  ·
    refine ⟨62844714343445077944335789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41896476228963385296223859 62844714343445077944335789)
    ·
      refine ⟨23566767878791904229125921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62844714343445077944335789 23566767878791904229125921)
      ·
        refine ⟨17675075909093928171844441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23566767878791904229125921 17675075909093928171844441)
        ·
          refine ⟨13256306931820446128883331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17675075909093928171844441 13256306931820446128883331)
          ·
            refine ⟨19884460397730669193324997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13256306931820446128883331 19884460397730669193324997)
            ·
              refine ⟨3728336324574500473748437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19884460397730669193324997 3728336324574500473748437)
              ·
                refine ⟨87382882607214854853479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3728336324574500473748437 87382882607214854853479)
                ·
                  rfl

theorem cell23_4594794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 4, 7].length) (baseStart_4594794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4594794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4594794 prefixEnd_4594794 := by exact prefixLift 4594794
  have htrace : WordTrace (prefixWord ++ tailWord_4594794) baseStart_4594794 baseEnd_4594794 := by
    simpa [prefixWord, tailWord_4594794, baseEnd_4594794] using wordTrace_append hprefix tailTrace_4594794
  have hstable : (prefixWord ++ tailWord_4594794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4594794).length < 2 ^ (prefixWord ++ tailWord_4594794).sum := by decide
  have hdescent : baseEnd_4594794 < baseStart_4594794 := by decide
  rcases family_descends (prefixWord ++ tailWord_4594794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4594865 : List Nat := [1, 2, 2, 5, 1, 2, 3, 1, 1, 3, 2]
def baseStart_4594865 : Nat := 118140960795 + 4594865 * 2 ^ 59
def prefixEnd_4594865 : Nat := 4983230072969 + 3 ^ 40 * 4594865 * 2
def baseEnd_4594865 : Nat := 2359374287521270303256107

theorem tailTrace_4594865 : CollatzResearch.WordTrace tailWord_4594865 prefixEnd_4594865 2359374287521270303256107 := by
  unfold tailWord_4594865
  simp only [CollatzResearch.WordTrace]
  refine ⟨167588494498596320310730049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111725662999064213540486699 167588494498596320310730049)
  ·
    refine ⟨125691370873947240233047537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167588494498596320310730049 125691370873947240233047537)
    ·
      refine ⟨94268528155460430174785653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125691370873947240233047537 94268528155460430174785653)
      ·
        refine ⟨8837674514574415328886155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 94268528155460430174785653 8837674514574415328886155)
        ·
          refine ⟨13256511771861622993329233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8837674514574415328886155 13256511771861622993329233)
          ·
            refine ⟨9942383828896217244996925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13256511771861622993329233 9942383828896217244996925)
            ·
              refine ⟨3728393935836081466873847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9942383828896217244996925 3728393935836081466873847)
              ·
                refine ⟨5592590903754122200310771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3728393935836081466873847 5592590903754122200310771)
                ·
                  refine ⟨8388886355631183300466157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5592590903754122200310771 8388886355631183300466157)
                  ·
                    refine ⟨3145832383361693737674809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8388886355631183300466157 3145832383361693737674809)
                    ·
                      refine ⟨2359374287521270303256107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3145832383361693737674809 2359374287521270303256107)
                      ·
                        rfl

theorem cell23_4594865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_4594865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4594865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4594865 prefixEnd_4594865 := by exact prefixLift 4594865
  have htrace : WordTrace (prefixWord ++ tailWord_4594865) baseStart_4594865 baseEnd_4594865 := by
    simpa [prefixWord, tailWord_4594865, baseEnd_4594865] using wordTrace_append hprefix tailTrace_4594865
  have hstable : (prefixWord ++ tailWord_4594865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4594865).length < 2 ^ (prefixWord ++ tailWord_4594865).sum := by decide
  have hdescent : baseEnd_4594865 < baseStart_4594865 := by decide
  rcases family_descends (prefixWord ++ tailWord_4594865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4594877 : List Nat := [1, 4, 1, 2, 1, 1, 2, 1, 1, 2, 7]
def baseStart_4594877 : Nat := 118140960795 + 4594877 * 2 ^ 59
def prefixEnd_4594877 : Nat := 4983230072969 + 3 ^ 40 * 4594877 * 2
def baseEnd_4594877 : Nat := 2359380449289124256306051

theorem tailTrace_4594877 : CollatzResearch.WordTrace tailWord_4594877 prefixEnd_4594877 2359380449289124256306051 := by
  unfold tailWord_4594877
  simp only [CollatzResearch.WordTrace]
  refine ⟨167588932174552846360166885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111725954783035230906777923 167588932174552846360166885)
  ·
    refine ⟨31422924782728658692531291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 167588932174552846360166885 31422924782728658692531291)
    ·
      refine ⟨47134387174092988038796937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31422924782728658692531291 47134387174092988038796937)
      ·
        refine ⟨35350790380569741029097703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47134387174092988038796937 35350790380569741029097703)
        ·
          refine ⟨53026185570854611543646555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35350790380569741029097703 53026185570854611543646555)
          ·
            refine ⟨79539278356281917315469833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53026185570854611543646555 79539278356281917315469833)
            ·
              refine ⟨59654458767211437986602375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79539278356281917315469833 59654458767211437986602375)
              ·
                refine ⟨89481688150817156979903563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59654458767211437986602375 89481688150817156979903563)
                ·
                  refine ⟨134222532226225735469855345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89481688150817156979903563 134222532226225735469855345)
                  ·
                    refine ⟨100666899169669301602391509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 134222532226225735469855345 100666899169669301602391509)
                    ·
                      refine ⟨2359380449289124256306051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 100666899169669301602391509 2359380449289124256306051)
                      ·
                        rfl

theorem cell23_4594877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_4594877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4594877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4594877 prefixEnd_4594877 := by exact prefixLift 4594877
  have htrace : WordTrace (prefixWord ++ tailWord_4594877) baseStart_4594877 baseEnd_4594877 := by
    simpa [prefixWord, tailWord_4594877, baseEnd_4594877] using wordTrace_append hprefix tailTrace_4594877
  have hstable : (prefixWord ++ tailWord_4594877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4594877).length < 2 ^ (prefixWord ++ tailWord_4594877).sum := by decide
  have hdescent : baseEnd_4594877 < baseStart_4594877 := by decide
  rcases family_descends (prefixWord ++ tailWord_4594877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4594881 : List Nat := [1, 2, 6, 1, 1, 1, 1, 1, 2, 4, 3]
def baseStart_4594881 : Nat := 118140960795 + 4594881 * 2 ^ 59
def prefixEnd_4594881 : Nat := 4983230072969 + 3 ^ 40 * 4594881 * 2
def baseEnd_4594881 : Nat := 2359382503211742240656033

theorem tailTrace_4594881 : CollatzResearch.WordTrace tailWord_4594881 prefixEnd_4594881 2359382503211742240656033 := by
  unfold tailWord_4594881
  simp only [CollatzResearch.WordTrace]
  refine ⟨167589078066538355043312497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111726052044358903362208331 167589078066538355043312497)
  ·
    refine ⟨125691808549903766282484373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167589078066538355043312497 125691808549903766282484373)
    ·
      refine ⟨5891803525776739044491455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 125691808549903766282484373 5891803525776739044491455)
      ·
        refine ⟨8837705288665108566737183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5891803525776739044491455 8837705288665108566737183)
        ·
          refine ⟨13256557932997662850105775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8837705288665108566737183 13256557932997662850105775)
          ·
            refine ⟨19884836899496494275158663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13256557932997662850105775 19884836899496494275158663)
            ·
              refine ⟨29827255349244741412737995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19884836899496494275158663 29827255349244741412737995)
              ·
                refine ⟨44740883023867112119106993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29827255349244741412737995 44740883023867112119106993)
                ·
                  refine ⟨33555662267900334089330245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44740883023867112119106993 33555662267900334089330245)
                  ·
                    refine ⟨6291686675231312641749421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33555662267900334089330245 6291686675231312641749421)
                    ·
                      refine ⟨2359382503211742240656033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6291686675231312641749421 2359382503211742240656033)
                      ·
                        rfl

theorem cell23_4594881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_4594881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4594881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4594881 prefixEnd_4594881 := by exact prefixLift 4594881
  have htrace : WordTrace (prefixWord ++ tailWord_4594881) baseStart_4594881 baseEnd_4594881 := by
    simpa [prefixWord, tailWord_4594881, baseEnd_4594881] using wordTrace_append hprefix tailTrace_4594881
  have hstable : (prefixWord ++ tailWord_4594881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4594881).length < 2 ^ (prefixWord ++ tailWord_4594881).sum := by decide
  have hdescent : baseEnd_4594881 < baseStart_4594881 := by decide
  rcases family_descends (prefixWord ++ tailWord_4594881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4594897 : List Nat := [1, 2, 2, 1, 2, 2, 1, 4, 1, 7]
def baseStart_4594897 : Nat := 118140960795 + 4594897 * 2 ^ 59
def prefixEnd_4594897 : Nat := 4983230072969 + 3 ^ 40 * 4594897 * 2
def baseEnd_4594897 : Nat := 786463572967404726018653

theorem tailTrace_4594897 : CollatzResearch.WordTrace tailWord_4594897 prefixEnd_4594897 786463572967404726018653 := by
  unfold tailWord_4594897
  simp only [CollatzResearch.WordTrace]
  refine ⟨167589661634480389775894945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111726441089653593183929963 167589661634480389775894945)
  ·
    refine ⟨125692246225860292331921209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167589661634480389775894945 125692246225860292331921209)
    ·
      refine ⟨94269184669395219248940907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125692246225860292331921209 94269184669395219248940907)
      ·
        refine ⟨141403777004092828873411361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94269184669395219248940907 141403777004092828873411361)
        ·
          refine ⟨106052832753069621655058521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141403777004092828873411361 106052832753069621655058521)
          ·
            refine ⟨79539624564802216241293891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106052832753069621655058521 79539624564802216241293891)
            ·
              refine ⟨119309436847203324361940837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79539624564802216241293891 119309436847203324361940837)
              ·
                refine ⟨22370519408850623317863907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 119309436847203324361940837 22370519408850623317863907)
                ·
                  refine ⟨33555779113275934976795861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22370519408850623317863907 33555779113275934976795861)
                  ·
                    refine ⟨786463572967404726018653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33555779113275934976795861 786463572967404726018653)
                    ·
                      rfl

theorem cell23_4594897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 7].length) (baseStart_4594897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4594897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4594897 prefixEnd_4594897 := by exact prefixLift 4594897
  have htrace : WordTrace (prefixWord ++ tailWord_4594897) baseStart_4594897 baseEnd_4594897 := by
    simpa [prefixWord, tailWord_4594897, baseEnd_4594897] using wordTrace_append hprefix tailTrace_4594897
  have hstable : (prefixWord ++ tailWord_4594897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4594897).length < 2 ^ (prefixWord ++ tailWord_4594897).sum := by decide
  have hdescent : baseEnd_4594897 < baseStart_4594897 := by decide
  rcases family_descends (prefixWord ++ tailWord_4594897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4594995 : List Nat := [1, 1, 1, 2, 5, 3, 3, 2, 1, 4]
def baseStart_4594995 : Nat := 118140960795 + 4594995 * 2 ^ 59
def prefixEnd_4594995 : Nat := 4983230072969 + 3 ^ 40 * 4594995 * 2
def baseEnd_4594995 : Nat := 786480346668784931543503

theorem tailTrace_4594995 : CollatzResearch.WordTrace tailWord_4594995 prefixEnd_4594995 786480346668784931543503 := by
  unfold tailWord_4594995
  simp only [CollatzResearch.WordTrace]
  refine ⟨167593235988125352512962439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111728823992083568341974959 167593235988125352512962439)
  ·
    refine ⟨251389853982188028769443659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167593235988125352512962439 251389853982188028769443659)
    ·
      refine ⟨377084780973282043154165489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251389853982188028769443659 377084780973282043154165489)
      ·
        refine ⟨282813585729961532365624117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 377084780973282043154165489 282813585729961532365624117)
        ·
          refine ⟨26513773662183893659277261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 282813585729961532365624117 26513773662183893659277261)
          ·
            refine ⟨9942665123318960122228973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26513773662183893659277261 9942665123318960122228973)
            ·
              refine ⟨3728499421244610045835865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9942665123318960122228973 3728499421244610045835865)
              ·
                refine ⟨2796374565933457534376899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3728499421244610045835865 2796374565933457534376899)
                ·
                  refine ⟨4194561848900186301565349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2796374565933457534376899 4194561848900186301565349)
                  ·
                    refine ⟨786480346668784931543503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4194561848900186301565349 786480346668784931543503)
                    ·
                      rfl

theorem cell23_4594995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 3, 2, 1, 4].length) (baseStart_4594995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4594995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4594995 prefixEnd_4594995 := by exact prefixLift 4594995
  have htrace : WordTrace (prefixWord ++ tailWord_4594995) baseStart_4594995 baseEnd_4594995 := by
    simpa [prefixWord, tailWord_4594995, baseEnd_4594995] using wordTrace_append hprefix tailTrace_4594995
  have hstable : (prefixWord ++ tailWord_4594995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4594995).length < 2 ^ (prefixWord ++ tailWord_4594995).sum := by decide
  have hdescent : baseEnd_4594995 < baseStart_4594995 := by decide
  rcases family_descends (prefixWord ++ tailWord_4594995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4595011 : List Nat := [1, 1, 1, 3, 1, 3, 1, 1, 6, 3, 2]
def baseStart_4595011 : Nat := 118140960795 + 4595011 * 2 ^ 59
def prefixEnd_4595011 : Nat := 4983230072969 + 3 ^ 40 * 4595011 * 2
def baseEnd_4595011 : Nat := 2359449255696826732030435

theorem tailTrace_4595011 : CollatzResearch.WordTrace tailWord_4595011 prefixEnd_4595011 2359449255696826732030435 := by
  unfold tailWord_4595011
  simp only [CollatzResearch.WordTrace]
  refine ⟨167593819556067387245544887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111729213037378258163696591 167593819556067387245544887)
  ·
    refine ⟨251390729334101080868317331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167593819556067387245544887 251390729334101080868317331)
    ·
      refine ⟨377086094001151621302475997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251390729334101080868317331 377086094001151621302475997)
      ·
        refine ⟨141407285250431857988428499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 377086094001151621302475997 141407285250431857988428499)
        ·
          refine ⟨212110927875647786982642749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141407285250431857988428499 212110927875647786982642749)
          ·
            refine ⟨79541597953367920118491031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 212110927875647786982642749 79541597953367920118491031)
            ·
              refine ⟨119312396930051880177736547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79541597953367920118491031 119312396930051880177736547)
              ·
                refine ⟨178968595395077820266604821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119312396930051880177736547 178968595395077820266604821)
                ·
                  refine ⟨8389152909144272824997101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 178968595395077820266604821 8389152909144272824997101)
                  ·
                    refine ⟨3145932340929102309373913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8389152909144272824997101 3145932340929102309373913)
                    ·
                      refine ⟨2359449255696826732030435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3145932340929102309373913 2359449255696826732030435)
                      ·
                        rfl

theorem cell23_4595011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 6, 3, 2].length) (baseStart_4595011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4595011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4595011 prefixEnd_4595011 := by exact prefixLift 4595011
  have htrace : WordTrace (prefixWord ++ tailWord_4595011) baseStart_4595011 baseEnd_4595011 := by
    simpa [prefixWord, tailWord_4595011, baseEnd_4595011] using wordTrace_append hprefix tailTrace_4595011
  have hstable : (prefixWord ++ tailWord_4595011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4595011).length < 2 ^ (prefixWord ++ tailWord_4595011).sum := by decide
  have hdescent : baseEnd_4595011 < baseStart_4595011 := by decide
  rcases family_descends (prefixWord ++ tailWord_4595011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4595034 : List Nat := [3, 1, 1, 2, 1, 2, 3, 1, 3, 6]
def baseStart_4595034 : Nat := 118140960795 + 4595034 * 2 ^ 59
def prefixEnd_4595034 : Nat := 4983230072969 + 3 ^ 40 * 4595034 * 2
def baseEnd_4595034 : Nat := 786487021917293380680943

theorem tailTrace_4595034 : CollatzResearch.WordTrace tailWord_4595034 prefixEnd_4595034 786487021917293380680943 := by
  unfold tailWord_4595034
  simp only [CollatzResearch.WordTrace]
  refine ⟨41898664608746015543408039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111729772289989374782421437 41898664608746015543408039)
  ·
    refine ⟨62847996913119023315112059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41898664608746015543408039 62847996913119023315112059)
    ·
      refine ⟨94271995369678534972668089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62847996913119023315112059 94271995369678534972668089)
      ·
        refine ⟨70703996527258901229501067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94271995369678534972668089 70703996527258901229501067)
        ·
          refine ⟨106055994790888351844251601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70703996527258901229501067 106055994790888351844251601)
          ·
            refine ⟨79541996093166263883188701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106055994790888351844251601 79541996093166263883188701)
            ·
              refine ⟨29828248534937348956195763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79541996093166263883188701 29828248534937348956195763)
              ·
                refine ⟨44742372802406023434293645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29828248534937348956195763 44742372802406023434293645)
                ·
                  refine ⟨16778389800902258787860117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44742372802406023434293645 16778389800902258787860117)
                  ·
                    refine ⟨786487021917293380680943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16778389800902258787860117 786487021917293380680943)
                    ·
                      rfl

theorem cell23_4595034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 3, 6].length) (baseStart_4595034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4595034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4595034 prefixEnd_4595034 := by exact prefixLift 4595034
  have htrace : WordTrace (prefixWord ++ tailWord_4595034) baseStart_4595034 baseEnd_4595034 := by
    simpa [prefixWord, tailWord_4595034, baseEnd_4595034] using wordTrace_append hprefix tailTrace_4595034
  have hstable : (prefixWord ++ tailWord_4595034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4595034).length < 2 ^ (prefixWord ++ tailWord_4595034).sum := by decide
  have hdescent : baseEnd_4595034 < baseStart_4595034 := by decide
  rcases family_descends (prefixWord ++ tailWord_4595034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4595041 : List Nat := [1, 2, 3, 1, 1, 1, 1, 7, 1, 1, 4]
def baseStart_4595041 : Nat := 118140960795 + 4595041 * 2 ^ 59
def prefixEnd_4595041 : Nat := 4983230072969 + 3 ^ 40 * 4595041 * 2
def baseEnd_4595041 : Nat := 2359464660116461614655297

theorem tailTrace_4595041 : CollatzResearch.WordTrace tailWord_4595041 prefixEnd_4595041 2359464660116461614655297 := by
  unfold tailWord_4595041
  simp only [CollatzResearch.WordTrace]
  refine ⟨167594913745958702369136977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111729942497305801579424651 167594913745958702369136977)
  ·
    refine ⟨125696185309469026776852733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167594913745958702369136977 125696185309469026776852733)
    ·
      refine ⟨47136069491050885041319775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125696185309469026776852733 47136069491050885041319775)
      ·
        refine ⟨70704104236576327561979663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47136069491050885041319775 70704104236576327561979663)
        ·
          refine ⟨106056156354864491342969495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70704104236576327561979663 106056156354864491342969495)
          ·
            refine ⟨159084234532296737014454243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106056156354864491342969495 159084234532296737014454243)
            ·
              refine ⟨238626351798445105521681365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159084234532296737014454243 238626351798445105521681365)
              ·
                refine ⟨5592805120276057160664407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 238626351798445105521681365 5592805120276057160664407)
                ·
                  refine ⟨8389207680414085740996611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5592805120276057160664407 8389207680414085740996611)
                  ·
                    refine ⟨12583811520621128611494917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8389207680414085740996611 12583811520621128611494917)
                    ·
                      refine ⟨2359464660116461614655297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12583811520621128611494917 2359464660116461614655297)
                      ·
                        rfl

theorem cell23_4595041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 7, 1, 1, 4].length) (baseStart_4595041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4595041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4595041 prefixEnd_4595041 := by exact prefixLift 4595041
  have htrace : WordTrace (prefixWord ++ tailWord_4595041) baseStart_4595041 baseEnd_4595041 := by
    simpa [prefixWord, tailWord_4595041, baseEnd_4595041] using wordTrace_append hprefix tailTrace_4595041
  have hstable : (prefixWord ++ tailWord_4595041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4595041).length < 2 ^ (prefixWord ++ tailWord_4595041).sum := by decide
  have hdescent : baseEnd_4595041 < baseStart_4595041 := by decide
  rcases family_descends (prefixWord ++ tailWord_4595041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4595052 : List Nat := [2, 2, 1, 1, 5, 1, 4, 2, 1, 1, 3]
def baseStart_4595052 : Nat := 118140960795 + 4595052 * 2 ^ 59
def prefixEnd_4595052 : Nat := 4983230072969 + 3 ^ 40 * 4595052 * 2
def baseEnd_4595052 : Nat := 2359470308403661071617747

theorem tailTrace_4595052 : CollatzResearch.WordTrace tailWord_4595052 prefixEnd_4595052 2359470308403661071617747 := by
  unfold tailWord_4595052
  simp only [CollatzResearch.WordTrace]
  refine ⟨83797657474459425623893705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111730209965945900831858273 83797657474459425623893705)
  ·
    refine ⟨62848243105844569217920279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83797657474459425623893705 62848243105844569217920279)
    ·
      refine ⟨94272364658766853826880419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62848243105844569217920279 94272364658766853826880419)
      ·
        refine ⟨141408546988150280740320629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94272364658766853826880419 141408546988150280740320629)
        ·
          refine ⟨13257051280139088819405059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 141408546988150280740320629 13257051280139088819405059)
          ·
            refine ⟨19885576920208633229107589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13257051280139088819405059 19885576920208633229107589)
            ·
              refine ⟨3728545672539118730457673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19885576920208633229107589 3728545672539118730457673)
              ·
                refine ⟨2796409254404339047843255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3728545672539118730457673 2796409254404339047843255)
                ·
                  refine ⟨4194613881606508571764883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2796409254404339047843255 4194613881606508571764883)
                  ·
                    refine ⟨6291920822409762857647325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4194613881606508571764883 6291920822409762857647325)
                    ·
                      refine ⟨2359470308403661071617747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6291920822409762857647325 2359470308403661071617747)
                      ·
                        rfl

theorem cell23_4595052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 4, 2, 1, 1, 3].length) (baseStart_4595052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4595052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4595052 prefixEnd_4595052 := by exact prefixLift 4595052
  have htrace : WordTrace (prefixWord ++ tailWord_4595052) baseStart_4595052 baseEnd_4595052 := by
    simpa [prefixWord, tailWord_4595052, baseEnd_4595052] using wordTrace_append hprefix tailTrace_4595052
  have hstable : (prefixWord ++ tailWord_4595052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4595052).length < 2 ^ (prefixWord ++ tailWord_4595052).sum := by decide
  have hdescent : baseEnd_4595052 < baseStart_4595052 := by decide
  rcases family_descends (prefixWord ++ tailWord_4595052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4595075 : List Nat := [1, 1, 1, 3, 5, 2, 1, 2, 3, 2, 2]
def baseStart_4595075 : Nat := 118140960795 + 4595075 * 2 ^ 59
def prefixEnd_4595075 : Nat := 4983230072969 + 3 ^ 40 * 4595075 * 2
def baseEnd_4595075 : Nat := 2359482118458714481630141

theorem tailTrace_4595075 : CollatzResearch.WordTrace tailWord_4595075 prefixEnd_4595075 2359482118458714481630141 := by
  unfold tailWord_4595075
  simp only [CollatzResearch.WordTrace]
  refine ⟨167596153827835526175874679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111730769218557017450583119 167596153827835526175874679)
  ·
    refine ⟨251394230741753289263812019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167596153827835526175874679 251394230741753289263812019)
    ·
      refine ⟨377091346112629933895718029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251394230741753289263812019 377091346112629933895718029)
      ·
        refine ⟨141409254792236225210894261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 377091346112629933895718029 141409254792236225210894261)
        ·
          refine ⟨13257117636772146113521337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 141409254792236225210894261 13257117636772146113521337)
          ·
            refine ⟨9942838227579109585141003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13257117636772146113521337 9942838227579109585141003)
            ·
              refine ⟨14914257341368664377711505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9942838227579109585141003 14914257341368664377711505)
              ·
                refine ⟨11185693006026498283283629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14914257341368664377711505 11185693006026498283283629)
                ·
                  refine ⟨4194634877259936856231361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11185693006026498283283629 4194634877259936856231361)
                  ·
                    refine ⟨3145976157944952642173521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4194634877259936856231361 3145976157944952642173521)
                    ·
                      refine ⟨2359482118458714481630141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3145976157944952642173521 2359482118458714481630141)
                      ·
                        rfl

theorem cell23_4595075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 2, 3, 2, 2].length) (baseStart_4595075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4595075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4595075 prefixEnd_4595075 := by exact prefixLift 4595075
  have htrace : WordTrace (prefixWord ++ tailWord_4595075) baseStart_4595075 baseEnd_4595075 := by
    simpa [prefixWord, tailWord_4595075, baseEnd_4595075] using wordTrace_append hprefix tailTrace_4595075
  have hstable : (prefixWord ++ tailWord_4595075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4595075).length < 2 ^ (prefixWord ++ tailWord_4595075).sum := by decide
  have hdescent : baseEnd_4595075 < baseStart_4595075 := by decide
  rcases family_descends (prefixWord ++ tailWord_4595075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4595092 : List Nat := [2, 4, 2, 1, 2, 3, 2, 1, 1, 1, 4]
def baseStart_4595092 : Nat := 118140960795 + 4595092 * 2 ^ 59
def prefixEnd_4595092 : Nat := 4983230072969 + 3 ^ 40 * 4595092 * 2
def baseEnd_4595092 : Nat := 2359490847629840915117563

theorem tailTrace_4595092 : CollatzResearch.WordTrace tailWord_4595092 prefixEnd_4595092 2359490847629840915117563 := by
  unfold tailWord_4595092
  simp only [CollatzResearch.WordTrace]
  refine ⟨83798386934386969039621765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111731182579182625386162353 83798386934386969039621765)
  ·
    refine ⟨15712197550197556694929081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83798386934386969039621765 15712197550197556694929081)
    ·
      refine ⟨11784148162648167521196811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15712197550197556694929081 11784148162648167521196811)
      ·
        refine ⟨17676222243972251281795217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11784148162648167521196811 17676222243972251281795217)
        ·
          refine ⟨13257166682979188461346413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17676222243972251281795217 13257166682979188461346413)
          ·
            refine ⟨4971437506117195673004905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13257166682979188461346413 4971437506117195673004905)
            ·
              refine ⟨3728578129587896754753679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4971437506117195673004905 3728578129587896754753679)
              ·
                refine ⟨5592867194381845132130519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3728578129587896754753679 5592867194381845132130519)
                ·
                  refine ⟨8389300791572767698195779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5592867194381845132130519 8389300791572767698195779)
                  ·
                    refine ⟨12583951187359151547293669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8389300791572767698195779 12583951187359151547293669)
                    ·
                      refine ⟨2359490847629840915117563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12583951187359151547293669 2359490847629840915117563)
                      ·
                        rfl

theorem cell23_4595092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 2, 1, 1, 1, 4].length) (baseStart_4595092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4595092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4595092 prefixEnd_4595092 := by exact prefixLift 4595092
  have htrace : WordTrace (prefixWord ++ tailWord_4595092) baseStart_4595092 baseEnd_4595092 := by
    simpa [prefixWord, tailWord_4595092, baseEnd_4595092] using wordTrace_append hprefix tailTrace_4595092
  have hstable : (prefixWord ++ tailWord_4595092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4595092).length < 2 ^ (prefixWord ++ tailWord_4595092).sum := by decide
  have hdescent : baseEnd_4595092 < baseStart_4595092 := by decide
  rcases family_descends (prefixWord ++ tailWord_4595092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4595125 : List Nat := [1, 3, 3, 2, 2, 3, 1, 1, 1, 3, 3]
def baseStart_4595125 : Nat := 118140960795 + 4595125 * 2 ^ 59
def prefixEnd_4595125 : Nat := 4983230072969 + 3 ^ 40 * 4595125 * 2
def baseEnd_4595125 : Nat := 2359507792491439286004911

theorem tailTrace_4595125 : CollatzResearch.WordTrace tailWord_4595125 prefixEnd_4595125 2359507792491439286004911 := by
  unfold tailWord_4595125
  simp only [CollatzResearch.WordTrace]
  refine ⟨167597977477654384715194829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111731984985102923143463219 167597977477654384715194829)
  ·
    refine ⟨62849241554120394268198061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167597977477654384715194829 62849241554120394268198061)
    ·
      refine ⟨23568465582795147850574273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62849241554120394268198061 23568465582795147850574273)
      ·
        refine ⟨17676349187096360887930705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23568465582795147850574273 17676349187096360887930705)
        ·
          refine ⟨13257261890322270665948029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17676349187096360887930705 13257261890322270665948029)
          ·
            refine ⟨4971473208870851499730511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13257261890322270665948029 4971473208870851499730511)
            ·
              refine ⟨7457209813306277249595767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4971473208870851499730511 7457209813306277249595767)
              ·
                refine ⟨11185814719959415874393651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7457209813306277249595767 11185814719959415874393651)
                ·
                  refine ⟨16778722079939123811590477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11185814719959415874393651 16778722079939123811590477)
                  ·
                    refine ⟨6292020779977171429346429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16778722079939123811590477 6292020779977171429346429)
                    ·
                      refine ⟨2359507792491439286004911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6292020779977171429346429 2359507792491439286004911)
                      ·
                        rfl

theorem cell23_4595125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_4595125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4595125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4595125 prefixEnd_4595125 := by exact prefixLift 4595125
  have htrace : WordTrace (prefixWord ++ tailWord_4595125) baseStart_4595125 baseEnd_4595125 := by
    simpa [prefixWord, tailWord_4595125, baseEnd_4595125] using wordTrace_append hprefix tailTrace_4595125
  have hstable : (prefixWord ++ tailWord_4595125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4595125).length < 2 ^ (prefixWord ++ tailWord_4595125).sum := by decide
  have hdescent : baseEnd_4595125 < baseStart_4595125 := by decide
  rcases family_descends (prefixWord ++ tailWord_4595125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4595182 : List Nat := [4, 1, 2, 1, 2, 1, 3, 3, 2, 2, 2]
def baseStart_4595182 : Nat := 118140960795 + 4595182 * 2 ^ 59
def prefixEnd_4595182 : Nat := 4983230072969 + 3 ^ 40 * 4595182 * 2
def baseEnd_4595182 : Nat := 2359537060888745562992149

theorem tailTrace_4595182 : CollatzResearch.WordTrace tailWord_4595182 prefixEnd_4595182 2359537060888745562992149 := by
  unfold tailWord_4595182
  simp only [CollatzResearch.WordTrace]
  refine ⟨20950007054805985431252475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111733370958965255633346533 20950007054805985431252475)
  ·
    refine ⟨31425010582208978146878713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20950007054805985431252475 31425010582208978146878713)
    ·
      refine ⟨23568757936656733610159035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31425010582208978146878713 23568757936656733610159035)
      ·
        refine ⟨35353136904985100415238553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23568757936656733610159035 35353136904985100415238553)
        ·
          refine ⟨26514852678738825311428915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35353136904985100415238553 26514852678738825311428915)
          ·
            refine ⟨39772279018108237967143373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26514852678738825311428915 39772279018108237967143373)
            ·
              refine ⟨14914604631790589237678765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39772279018108237967143373 14914604631790589237678765)
              ·
                refine ⟨5592976736921470964129537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14914604631790589237678765 5592976736921470964129537)
                ·
                  refine ⟨4194732552691103223097153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5592976736921470964129537 4194732552691103223097153)
                  ·
                    refine ⟨3146049414518327417322865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4194732552691103223097153 3146049414518327417322865)
                    ·
                      refine ⟨2359537060888745562992149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3146049414518327417322865 2359537060888745562992149)
                      ·
                        rfl

theorem cell23_4595182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 3, 2, 2, 2].length) (baseStart_4595182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4595182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4595182 prefixEnd_4595182 := by exact prefixLift 4595182
  have htrace : WordTrace (prefixWord ++ tailWord_4595182) baseStart_4595182 baseEnd_4595182 := by
    simpa [prefixWord, tailWord_4595182, baseEnd_4595182] using wordTrace_append hprefix tailTrace_4595182
  have hstable : (prefixWord ++ tailWord_4595182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4595182).length < 2 ^ (prefixWord ++ tailWord_4595182).sum := by decide
  have hdescent : baseEnd_4595182 < baseStart_4595182 := by decide
  rcases family_descends (prefixWord ++ tailWord_4595182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4595255 : List Nat := [1, 1, 3, 1, 2, 6, 1, 1, 2, 1, 4]
def baseStart_4595255 : Nat := 118140960795 + 4595255 * 2 ^ 59
def prefixEnd_4595255 : Nat := 4983230072969 + 3 ^ 40 * 4595255 * 2
def baseEnd_4595255 : Nat := 2359574544976523777379313

theorem tailTrace_4595255 : CollatzResearch.WordTrace tailWord_4595255 prefixEnd_4595255 2359574544976523777379313 := by
  unfold tailWord_4595255
  simp only [CollatzResearch.WordTrace]
  refine ⟨167602718967183416917427219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111735145978122277944951479 167602718967183416917427219)
  ·
    refine ⟨251404078450775125376140829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167602718967183416917427219 251404078450775125376140829)
    ·
      refine ⟨94276529419040672016052811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 251404078450775125376140829 94276529419040672016052811)
      ·
        refine ⟨141414794128561008024079217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94276529419040672016052811 141414794128561008024079217)
        ·
          refine ⟨106061095596420756018059413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141414794128561008024079217 106061095596420756018059413)
          ·
            refine ⟨4971613856082222938346535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 106061095596420756018059413 4971613856082222938346535)
            ·
              refine ⟨7457420784123334407519803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4971613856082222938346535 7457420784123334407519803)
              ·
                refine ⟨11186131176185001611279705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7457420784123334407519803 11186131176185001611279705)
                ·
                  refine ⟨8389598382138751208459779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11186131176185001611279705 8389598382138751208459779)
                  ·
                    refine ⟨12584397573208126812689669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8389598382138751208459779 12584397573208126812689669)
                    ·
                      refine ⟨2359574544976523777379313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12584397573208126812689669 2359574544976523777379313)
                      ·
                        rfl

theorem cell23_4595255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 1, 2, 1, 4].length) (baseStart_4595255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4595255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4595255 prefixEnd_4595255 := by exact prefixLift 4595255
  have htrace : WordTrace (prefixWord ++ tailWord_4595255) baseStart_4595255 baseEnd_4595255 := by
    simpa [prefixWord, tailWord_4595255, baseEnd_4595255] using wordTrace_append hprefix tailTrace_4595255
  have hstable : (prefixWord ++ tailWord_4595255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4595255).length < 2 ^ (prefixWord ++ tailWord_4595255).sum := by decide
  have hdescent : baseEnd_4595255 < baseStart_4595255 := by decide
  rcases family_descends (prefixWord ++ tailWord_4595255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4595258 : List Nat := [3, 1, 1, 1, 3, 2, 3, 1, 1, 4, 3]
def baseStart_4595258 : Nat := 118140960795 + 4595258 * 2 ^ 59
def prefixEnd_4595258 : Nat := 4983230072969 + 3 ^ 40 * 4595258 * 2
def baseEnd_4595258 : Nat := 2359576085418487265641799

theorem tailTrace_4595258 : CollatzResearch.WordTrace tailWord_4595258 prefixEnd_4595258 2359576085418487265641799 := by
  unfold tailWord_4595258
  simp only [CollatzResearch.WordTrace]
  refine ⟨41900707096543137107446607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111735218924115032286524285 41900707096543137107446607)
  ·
    refine ⟨62851060644814705661169911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41900707096543137107446607 62851060644814705661169911)
    ·
      refine ⟨94276590967222058491754867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62851060644814705661169911 94276590967222058491754867)
      ·
        refine ⟨141414886450833087737632301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94276590967222058491754867 141414886450833087737632301)
        ·
          refine ⟨53030582419062407901612113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 141414886450833087737632301 53030582419062407901612113)
          ·
            refine ⟨39772936814296805926209085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53030582419062407901612113 39772936814296805926209085)
            ·
              refine ⟨14914851305361302222328407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39772936814296805926209085 14914851305361302222328407)
              ·
                refine ⟨22372276958041953333492611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14914851305361302222328407 22372276958041953333492611)
                ·
                  refine ⟨33558415437062930000238917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22372276958041953333492611 33558415437062930000238917)
                  ·
                    refine ⟨6292202894449299375044797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33558415437062930000238917 6292202894449299375044797)
                    ·
                      refine ⟨2359576085418487265641799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6292202894449299375044797 2359576085418487265641799)
                      ·
                        rfl

theorem cell23_4595258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 1, 4, 3].length) (baseStart_4595258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4595258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4595258 prefixEnd_4595258 := by exact prefixLift 4595258
  have htrace : WordTrace (prefixWord ++ tailWord_4595258) baseStart_4595258 baseEnd_4595258 := by
    simpa [prefixWord, tailWord_4595258, baseEnd_4595258] using wordTrace_append hprefix tailTrace_4595258
  have hstable : (prefixWord ++ tailWord_4595258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4595258).length < 2 ^ (prefixWord ++ tailWord_4595258).sum := by decide
  have hdescent : baseEnd_4595258 < baseStart_4595258 := by decide
  rcases family_descends (prefixWord ++ tailWord_4595258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4595281 : List Nat := [1, 2, 2, 1, 3, 2, 1, 1, 1, 1, 8]
def baseStart_4595281 : Nat := 118140960795 + 4595281 * 2 ^ 59
def prefixEnd_4595281 : Nat := 4983230072969 + 3 ^ 40 * 4595281 * 2
def baseEnd_4595281 : Nat := 2359587895473540675654193

theorem tailTrace_4595281 : CollatzResearch.WordTrace tailWord_4595281 prefixEnd_4595281 2359587895473540675654193 := by
  unfold tailWord_4595281
  simp only [CollatzResearch.WordTrace]
  refine ⟨167603667265089223357873697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111735778176726148905249131 167603667265089223357873697)
  ·
    refine ⟨125702750448816917518405273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167603667265089223357873697 125702750448816917518405273)
    ·
      refine ⟨94277062836612688138803955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125702750448816917518405273 94277062836612688138803955)
      ·
        refine ⟨141415594254919032208205933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94277062836612688138803955 141415594254919032208205933)
        ·
          refine ⟨53030847845594637078077225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 141415594254919032208205933 53030847845594637078077225)
          ·
            refine ⟨39773135884195977808557919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53030847845594637078077225 39773135884195977808557919)
            ·
              refine ⟨59659703826293966712836879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39773135884195977808557919 59659703826293966712836879)
              ·
                refine ⟨89489555739440950069255319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59659703826293966712836879 89489555739440950069255319)
                ·
                  refine ⟨134234333609161425103882979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89489555739440950069255319 134234333609161425103882979)
                  ·
                    refine ⟨201351500413742137655824469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 134234333609161425103882979 201351500413742137655824469)
                    ·
                      refine ⟨2359587895473540675654193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 201351500413742137655824469 2359587895473540675654193)
                      ·
                        rfl

theorem cell23_4595281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 1, 8].length) (baseStart_4595281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4595281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4595281 prefixEnd_4595281 := by exact prefixLift 4595281
  have htrace : WordTrace (prefixWord ++ tailWord_4595281) baseStart_4595281 baseEnd_4595281 := by
    simpa [prefixWord, tailWord_4595281, baseEnd_4595281] using wordTrace_append hprefix tailTrace_4595281
  have hstable : (prefixWord ++ tailWord_4595281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4595281).length < 2 ^ (prefixWord ++ tailWord_4595281).sum := by decide
  have hdescent : baseEnd_4595281 < baseStart_4595281 := by decide
  rcases family_descends (prefixWord ++ tailWord_4595281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4595282 : List Nat := [3, 2, 2, 1, 2, 2, 2, 4, 1, 4]
def baseStart_4595282 : Nat := 118140960795 + 4595282 * 2 ^ 59
def prefixEnd_4595282 : Nat := 4983230072969 + 3 ^ 40 * 4595282 * 2
def baseEnd_4595282 : Nat := 786529469651398390580563

theorem tailTrace_4595282 : CollatzResearch.WordTrace tailWord_4595282 prefixEnd_4595282 786529469651398390580563 := by
  unfold tailWord_4595282
  simp only [CollatzResearch.WordTrace]
  refine ⟨41900925934521400132165025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111735802492057067019106733 41900925934521400132165025)
  ·
    refine ⟨31425694450891050099123769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41900925934521400132165025 31425694450891050099123769)
    ·
      refine ⟨23569270838168287574342827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31425694450891050099123769 23569270838168287574342827)
      ·
        refine ⟨35353906257252431361514241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23569270838168287574342827 35353906257252431361514241)
        ·
          refine ⟨26515429692939323521135681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35353906257252431361514241 26515429692939323521135681)
          ·
            refine ⟨19886572269704492640851761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26515429692939323521135681 19886572269704492640851761)
            ·
              refine ⟨14914929202278369480638821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19886572269704492640851761 14914929202278369480638821)
              ·
                refine ⟨2796549225427194277619779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14914929202278369480638821 2796549225427194277619779)
                ·
                  refine ⟨4194823838140791416429669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2796549225427194277619779 4194823838140791416429669)
                  ·
                    refine ⟨786529469651398390580563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4194823838140791416429669 786529469651398390580563)
                    ·
                      rfl

theorem cell23_4595282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 4, 1, 4].length) (baseStart_4595282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4595282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4595282 prefixEnd_4595282 := by exact prefixLift 4595282
  have htrace : WordTrace (prefixWord ++ tailWord_4595282) baseStart_4595282 baseEnd_4595282 := by
    simpa [prefixWord, tailWord_4595282, baseEnd_4595282] using wordTrace_append hprefix tailTrace_4595282
  have hstable : (prefixWord ++ tailWord_4595282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4595282).length < 2 ^ (prefixWord ++ tailWord_4595282).sum := by decide
  have hdescent : baseEnd_4595282 < baseStart_4595282 := by decide
  rcases family_descends (prefixWord ++ tailWord_4595282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4595305 : List Nat := [1, 2, 1, 1, 1, 4, 4, 2, 3, 1, 3]
def baseStart_4595305 : Nat := 118140960795 + 4595305 * 2 ^ 59
def prefixEnd_4595305 : Nat := 4983230072969 + 3 ^ 40 * 4595305 * 2
def baseEnd_4595305 : Nat := 2359600219009248581754083

theorem tailTrace_4595305 : CollatzResearch.WordTrace tailWord_4595305 prefixEnd_4595305 2359600219009248581754083 := by
  unfold tailWord_4595305
  simp only [CollatzResearch.WordTrace]
  refine ⟨167604542617002275456747369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111736361744668183637831579 167604542617002275456747369)
  ·
    refine ⟨125703406962751706592560527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167604542617002275456747369 125703406962751706592560527)
    ·
      refine ⟨188555110444127559888840791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125703406962751706592560527 188555110444127559888840791)
      ·
        refine ⟨282832665666191339833261187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188555110444127559888840791 282832665666191339833261187)
        ·
          refine ⟨424248998499287009749891781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 282832665666191339833261187 424248998499287009749891781)
          ·
            refine ⟨79546687218616314328104709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 424248998499287009749891781 79546687218616314328104709)
            ·
              refine ⟨14915003853490558936519633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79546687218616314328104709 14915003853490558936519633)
              ·
                refine ⟨11186252890117919202389725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14915003853490558936519633 11186252890117919202389725)
                ·
                  refine ⟨4194844833794219700896147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11186252890117919202389725 4194844833794219700896147)
                  ·
                    refine ⟨6292267250691329551344221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4194844833794219700896147 6292267250691329551344221)
                    ·
                      refine ⟨2359600219009248581754083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6292267250691329551344221 2359600219009248581754083)
                      ·
                        rfl

theorem cell23_4595305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 2, 3, 1, 3].length) (baseStart_4595305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4595305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4595305 prefixEnd_4595305 := by exact prefixLift 4595305
  have htrace : WordTrace (prefixWord ++ tailWord_4595305) baseStart_4595305 baseEnd_4595305 := by
    simpa [prefixWord, tailWord_4595305, baseEnd_4595305] using wordTrace_append hprefix tailTrace_4595305
  have hstable : (prefixWord ++ tailWord_4595305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4595305).length < 2 ^ (prefixWord ++ tailWord_4595305).sum := by decide
  have hdescent : baseEnd_4595305 < baseStart_4595305 := by decide
  rcases family_descends (prefixWord ++ tailWord_4595305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4595322 : List Nat := [3, 1, 1, 1, 1, 1, 1, 9, 1, 1, 3]
def baseStart_4595322 : Nat := 118140960795 + 4595322 * 2 ^ 59
def prefixEnd_4595322 : Nat := 4983230072969 + 3 ^ 40 * 4595322 * 2
def baseEnd_4595322 : Nat := 2359608948180375015241505

theorem tailTrace_4595322 : CollatzResearch.WordTrace tailWord_4595322 prefixEnd_4595322 2359608948180375015241505 := by
  unfold tailWord_4595322
  simp only [CollatzResearch.WordTrace]
  refine ⟨41901290664485171840029055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111736775105293791573410813 41901290664485171840029055)
  ·
    refine ⟨62851935996727757760043583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41901290664485171840029055 62851935996727757760043583)
    ·
      refine ⟨94277903995091636640065375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62851935996727757760043583 94277903995091636640065375)
      ·
        refine ⟨141416855992637454960098063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94277903995091636640065375 141416855992637454960098063)
        ·
          refine ⟨212125283988956182440147095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141416855992637454960098063 212125283988956182440147095)
          ·
            refine ⟨318187925983434273660220643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212125283988956182440147095 318187925983434273660220643)
            ·
              refine ⟨477281888975151410490330965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 318187925983434273660220643 477281888975151410490330965)
              ·
                refine ⟨2796573568213777795841783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 477281888975151410490330965 2796573568213777795841783)
                ·
                  refine ⟨4194860352320666693762675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2796573568213777795841783 4194860352320666693762675)
                  ·
                    refine ⟨6292290528481000040644013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4194860352320666693762675 6292290528481000040644013)
                    ·
                      refine ⟨2359608948180375015241505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6292290528481000040644013 2359608948180375015241505)
                      ·
                        rfl

theorem cell23_4595322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 9, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 9, 1, 1, 3].length) (baseStart_4595322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4595322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4595322 prefixEnd_4595322 := by exact prefixLift 4595322
  have htrace : WordTrace (prefixWord ++ tailWord_4595322) baseStart_4595322 baseEnd_4595322 := by
    simpa [prefixWord, tailWord_4595322, baseEnd_4595322] using wordTrace_append hprefix tailTrace_4595322
  have hstable : (prefixWord ++ tailWord_4595322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4595322).length < 2 ^ (prefixWord ++ tailWord_4595322).sum := by decide
  have hdescent : baseEnd_4595322 < baseStart_4595322 := by decide
  rcases family_descends (prefixWord ++ tailWord_4595322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4595325 : List Nat := [1, 4, 1, 1, 4, 1, 2, 3, 1, 5]
def baseStart_4595325 : Nat := 118140960795 + 4595325 * 2 ^ 59
def prefixEnd_4595325 : Nat := 4983230072969 + 3 ^ 40 * 4595325 * 2
def baseEnd_4595325 : Nat := 786536829540779501167997

theorem tailTrace_4595325 : CollatzResearch.WordTrace tailWord_4595325 prefixEnd_4595325 786536829540779501167997 := by
  unfold tailWord_4595325
  simp only [CollatzResearch.WordTrace]
  refine ⟨167605272076929818872475429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111736848051286545914983619 167605272076929818872475429)
  ·
    refine ⟨31425988514424341038589143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 167605272076929818872475429 31425988514424341038589143)
    ·
      refine ⟨47138982771636511557883715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31425988514424341038589143 47138982771636511557883715)
      ·
        refine ⟨70708474157454767336825573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47138982771636511557883715 70708474157454767336825573)
        ·
          refine ⟨13257838904522768875654795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70708474157454767336825573 13257838904522768875654795)
          ·
            refine ⟨19886758356784153313482193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13257838904522768875654795 19886758356784153313482193)
            ·
              refine ⟨14915068767588114985111645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19886758356784153313482193 14915068767588114985111645)
              ·
                refine ⟨5593150787845543119416867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14915068767588114985111645 5593150787845543119416867)
                ·
                  refine ⟨8389726181768314679125301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5593150787845543119416867 8389726181768314679125301)
                  ·
                    refine ⟨786536829540779501167997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8389726181768314679125301 786536829540779501167997)
                    ·
                      rfl

theorem cell23_4595325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 3, 1, 5].length) (baseStart_4595325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4595325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4595325 prefixEnd_4595325 := by exact prefixLift 4595325
  have htrace : WordTrace (prefixWord ++ tailWord_4595325) baseStart_4595325 baseEnd_4595325 := by
    simpa [prefixWord, tailWord_4595325, baseEnd_4595325] using wordTrace_append hprefix tailTrace_4595325
  have hstable : (prefixWord ++ tailWord_4595325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4595325).length < 2 ^ (prefixWord ++ tailWord_4595325).sum := by decide
  have hdescent : baseEnd_4595325 < baseStart_4595325 := by decide
  rcases family_descends (prefixWord ++ tailWord_4595325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4595339 : List Nat := [1, 1, 1, 1, 4, 1, 7, 2, 1, 1, 3]
def baseStart_4595339 : Nat := 118140960795 + 4595339 * 2 ^ 59
def prefixEnd_4595339 : Nat := 4983230072969 + 3 ^ 40 * 4595339 * 2
def baseEnd_4595339 : Nat := 2359617677351501448728927

theorem tailTrace_4595339 : CollatzResearch.WordTrace tailWord_4595339 prefixEnd_4595339 2359617677351501448728927 := by
  unfold tailWord_4595339
  simp only [CollatzResearch.WordTrace]
  refine ⟨167605782698879099263485071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111737188465919399508990047 167605782698879099263485071)
  ·
    refine ⟨251408674048318648895227607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167605782698879099263485071 251408674048318648895227607)
    ·
      refine ⟨377113011072477973342841411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251408674048318648895227607 377113011072477973342841411)
      ·
        refine ⟨565669516608716960014262117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 377113011072477973342841411 565669516608716960014262117)
        ·
          refine ⟨106063034364134430002674147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 565669516608716960014262117 106063034364134430002674147)
          ·
            refine ⟨159094551546201645004011221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106063034364134430002674147 159094551546201645004011221)
            ·
              refine ⟨3728778551864101054781513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 159094551546201645004011221 3728778551864101054781513)
              ·
                refine ⟨2796583913898075791086135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3728778551864101054781513 2796583913898075791086135)
                ·
                  refine ⟨4194875870847113686629203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2796583913898075791086135 4194875870847113686629203)
                  ·
                    refine ⟨6292313806270670529943805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4194875870847113686629203 6292313806270670529943805)
                    ·
                      refine ⟨2359617677351501448728927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6292313806270670529943805 2359617677351501448728927)
                      ·
                        rfl

theorem cell23_4595339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 7, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 7, 2, 1, 1, 3].length) (baseStart_4595339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4595339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4595339 prefixEnd_4595339 := by exact prefixLift 4595339
  have htrace : WordTrace (prefixWord ++ tailWord_4595339) baseStart_4595339 baseEnd_4595339 := by
    simpa [prefixWord, tailWord_4595339, baseEnd_4595339] using wordTrace_append hprefix tailTrace_4595339
  have hstable : (prefixWord ++ tailWord_4595339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4595339).length < 2 ^ (prefixWord ++ tailWord_4595339).sum := by decide
  have hdescent : baseEnd_4595339 < baseStart_4595339 := by decide
  rcases family_descends (prefixWord ++ tailWord_4595339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4595359 : List Nat := [1, 1, 2, 7, 1, 2, 1, 2, 1, 5]
def baseStart_4595359 : Nat := 118140960795 + 4595359 * 2 ^ 59
def prefixEnd_4595359 : Nat := 4983230072969 + 3 ^ 40 * 4595359 * 2
def baseEnd_4595359 : Nat := 786542648988197123492945

theorem tailTrace_4595359 : CollatzResearch.WordTrace tailWord_4595359 prefixEnd_4595359 786542648988197123492945 := by
  unfold tailWord_4595359
  simp only [CollatzResearch.WordTrace]
  refine ⟨167606512158806642679213131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111737674772537761786142087 167606512158806642679213131)
  ·
    refine ⟨251409768238209964018819697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167606512158806642679213131 251409768238209964018819697)
    ·
      refine ⟨188557326178657473014114773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 251409768238209964018819697 188557326178657473014114773)
      ·
        refine ⟨4419312332312284523768315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 188557326178657473014114773 4419312332312284523768315)
        ·
          refine ⟨6628968498468426785652473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4419312332312284523768315 6628968498468426785652473)
          ·
            refine ⟨4971726373851320089239355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6628968498468426785652473 4971726373851320089239355)
            ·
              refine ⟨7457589560776980133859033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4971726373851320089239355 7457589560776980133859033)
              ·
                refine ⟨5593192170582735100394275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7457589560776980133859033 5593192170582735100394275)
                ·
                  refine ⟨8389788255874102650591413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5593192170582735100394275 8389788255874102650591413)
                  ·
                    refine ⟨786542648988197123492945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8389788255874102650591413 786542648988197123492945)
                    ·
                      rfl

theorem cell23_4595359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 2, 1, 5].length) (baseStart_4595359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4595359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4595359 prefixEnd_4595359 := by exact prefixLift 4595359
  have htrace : WordTrace (prefixWord ++ tailWord_4595359) baseStart_4595359 baseEnd_4595359 := by
    simpa [prefixWord, tailWord_4595359, baseEnd_4595359] using wordTrace_append hprefix tailTrace_4595359
  have hstable : (prefixWord ++ tailWord_4595359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4595359).length < 2 ^ (prefixWord ++ tailWord_4595359).sum := by decide
  have hdescent : baseEnd_4595359 < baseStart_4595359 := by decide
  rcases family_descends (prefixWord ++ tailWord_4595359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4595379 : List Nat := [1, 1, 1, 2, 3, 3, 2, 5, 1, 2, 2]
def baseStart_4595379 : Nat := 118140960795 + 4595379 * 2 ^ 59
def prefixEnd_4595379 : Nat := 4983230072969 + 3 ^ 40 * 4595379 * 2
def baseEnd_4595379 : Nat := 2359638216577681292228743

theorem tailTrace_4595379 : CollatzResearch.WordTrace tailWord_4595379 prefixEnd_4595379 2359638216577681292228743 := by
  unfold tailWord_4595379
  simp only [CollatzResearch.WordTrace]
  refine ⟨167607241618734186094941191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111738161079156124063294127 167607241618734186094941191)
  ·
    refine ⟨251410862428101279142411787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167607241618734186094941191 251410862428101279142411787)
    ·
      refine ⟨377116293642151918713617681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251410862428101279142411787 377116293642151918713617681)
      ·
        refine ⟨282837220231613939035213261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 377116293642151918713617681 282837220231613939035213261)
        ·
          refine ⟨106063957586855227138204973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 282837220231613939035213261 106063957586855227138204973)
          ·
            refine ⟨39773984095070710176826865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106063957586855227138204973 39773984095070710176826865)
            ·
              refine ⟨29830488071303032632620149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39773984095070710176826865 29830488071303032632620149)
              ·
                refine ⟨2796608256684659309308139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29830488071303032632620149 2796608256684659309308139)
                ·
                  refine ⟨4194912385026988963962209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2796608256684659309308139 4194912385026988963962209)
                  ·
                    refine ⟨3146184288770241722971657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4194912385026988963962209 3146184288770241722971657)
                    ·
                      refine ⟨2359638216577681292228743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3146184288770241722971657 2359638216577681292228743)
                      ·
                        rfl

theorem cell23_4595379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 5, 1, 2, 2].length) (baseStart_4595379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4595379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4595379 prefixEnd_4595379 := by exact prefixLift 4595379
  have htrace : WordTrace (prefixWord ++ tailWord_4595379) baseStart_4595379 baseEnd_4595379 := by
    simpa [prefixWord, tailWord_4595379, baseEnd_4595379] using wordTrace_append hprefix tailTrace_4595379
  have hstable : (prefixWord ++ tailWord_4595379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4595379).length < 2 ^ (prefixWord ++ tailWord_4595379).sum := by decide
  have hdescent : baseEnd_4595379 < baseStart_4595379 := by decide
  rcases family_descends (prefixWord ++ tailWord_4595379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4595396 : List Nat := [2, 3, 3, 1, 1, 1, 3, 4, 1, 2, 2]
def baseStart_4595396 : Nat := 118140960795 + 4595396 * 2 ^ 59
def prefixEnd_4595396 : Nat := 4983230072969 + 3 ^ 40 * 4595396 * 2
def baseEnd_4595396 : Nat := 2359646945748807725716165

theorem tailTrace_4595396 : CollatzResearch.WordTrace tailWord_4595396 prefixEnd_4595396 2359646945748807725716165 := by
  unfold tailWord_4595396
  simp only [CollatzResearch.WordTrace]
  refine ⟨83803930829836298999155021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111738574439781731998873361 83803930829836298999155021)
  ·
    refine ⟨31426474061188612124683133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83803930829836298999155021 31426474061188612124683133)
    ·
      refine ⟨11784927772945729546756175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31426474061188612124683133 11784927772945729546756175)
      ·
        refine ⟨17677391659418594320134263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11784927772945729546756175 17677391659418594320134263)
        ·
          refine ⟨26516087489127891480201395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17677391659418594320134263 26516087489127891480201395)
          ·
            refine ⟨39774131233691837220302093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26516087489127891480201395 39774131233691837220302093)
            ·
              refine ⟨14915299212634438957613285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39774131233691837220302093 14915299212634438957613285)
              ·
                refine ⟨2796618602368957304552491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14915299212634438957613285 2796618602368957304552491)
                ·
                  refine ⟨4194927903553435956828737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2796618602368957304552491 4194927903553435956828737)
                  ·
                    refine ⟨3146195927665076967621553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4194927903553435956828737 3146195927665076967621553)
                    ·
                      refine ⟨2359646945748807725716165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3146195927665076967621553 2359646945748807725716165)
                      ·
                        rfl

theorem cell23_4595396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 4, 1, 2, 2].length) (baseStart_4595396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4595396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4595396 prefixEnd_4595396 := by exact prefixLift 4595396
  have htrace : WordTrace (prefixWord ++ tailWord_4595396) baseStart_4595396 baseEnd_4595396 := by
    simpa [prefixWord, tailWord_4595396, baseEnd_4595396] using wordTrace_append hprefix tailTrace_4595396
  have hstable : (prefixWord ++ tailWord_4595396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4595396).length < 2 ^ (prefixWord ++ tailWord_4595396).sum := by decide
  have hdescent : baseEnd_4595396 < baseStart_4595396 := by decide
  rcases family_descends (prefixWord ++ tailWord_4595396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4595402 : List Nat := [3, 1, 2, 1, 6, 1, 1, 8]
def baseStart_4595402 : Nat := 118140960795 + 4595402 * 2 ^ 59
def prefixEnd_4595402 : Nat := 4983230072969 + 3 ^ 40 * 4595402 * 2
def baseEnd_4595402 : Nat := 87394445430842026008931

theorem tailTrace_4595402 : CollatzResearch.WordTrace tailWord_4595402 prefixEnd_4595402 87394445430842026008931 := by
  unfold tailWord_4595402
  simp only [CollatzResearch.WordTrace]
  refine ⟨41902020124412715255757115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111738720331767240682018973 41902020124412715255757115)
  ·
    refine ⟨62853030186619072883635673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41902020124412715255757115 62853030186619072883635673)
    ·
      refine ⟨47139772639964304662726755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62853030186619072883635673 47139772639964304662726755)
      ·
        refine ⟨70709658959946456994090133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47139772639964304662726755 70709658959946456994090133)
        ·
          refine ⟨3314515263747490171597975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 70709658959946456994090133 3314515263747490171597975)
          ·
            refine ⟨4971772895621235257396963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3314515263747490171597975 4971772895621235257396963)
            ·
              refine ⟨7457659343431852886095445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4971772895621235257396963 7457659343431852886095445)
              ·
                refine ⟨87394445430842026008931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7457659343431852886095445 87394445430842026008931)
                ·
                  rfl

theorem cell23_4595402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 8].length) (baseStart_4595402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4595402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4595402 prefixEnd_4595402 := by exact prefixLift 4595402
  have htrace : WordTrace (prefixWord ++ tailWord_4595402) baseStart_4595402 baseEnd_4595402 := by
    simpa [prefixWord, tailWord_4595402, baseEnd_4595402] using wordTrace_append hprefix tailTrace_4595402
  have hstable : (prefixWord ++ tailWord_4595402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4595402).length < 2 ^ (prefixWord ++ tailWord_4595402).sum := by decide
  have hdescent : baseEnd_4595402 < baseStart_4595402 := by decide
  rcases family_descends (prefixWord ++ tailWord_4595402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4595412 : List Nat := [2, 4, 1, 3, 1, 1, 1, 3, 1, 3, 3]
def baseStart_4595412 : Nat := 118140960795 + 4595412 * 2 ^ 59
def prefixEnd_4595412 : Nat := 4983230072969 + 3 ^ 40 * 4595412 * 2
def baseEnd_4595412 : Nat := 2359655161439279663116091

theorem tailTrace_4595412 : CollatzResearch.WordTrace tailWord_4595412 prefixEnd_4595412 2359655161439279663116091 := by
  unfold tailWord_4595412
  simp only [CollatzResearch.WordTrace]
  refine ⟨83804222613807316365446245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111738963485076421820594993 83804222613807316365446245)
  ·
    refine ⟨15713291740088871818521171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83804222613807316365446245 15713291740088871818521171)
    ·
      refine ⟨23569937610133307727781757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15713291740088871818521171 23569937610133307727781757)
      ·
        refine ⟨8838726603799990397918159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23569937610133307727781757 8838726603799990397918159)
        ·
          refine ⟨13258089905699985596877239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8838726603799990397918159 13258089905699985596877239)
          ·
            refine ⟨19887134858549978395315859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13258089905699985596877239 19887134858549978395315859)
            ·
              refine ⟨29830702287824967592973789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19887134858549978395315859 29830702287824967592973789)
              ·
                refine ⟨11186513357934362847365171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29830702287824967592973789 11186513357934362847365171)
                ·
                  refine ⟨16779770036901544271047757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11186513357934362847365171 16779770036901544271047757)
                  ·
                    refine ⟨6292413763838079101642909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16779770036901544271047757 6292413763838079101642909)
                    ·
                      refine ⟨2359655161439279663116091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6292413763838079101642909 2359655161439279663116091)
                      ·
                        rfl

theorem cell23_4595412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_4595412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4595412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4595412 prefixEnd_4595412 := by exact prefixLift 4595412
  have htrace : WordTrace (prefixWord ++ tailWord_4595412) baseStart_4595412 baseEnd_4595412 := by
    simpa [prefixWord, tailWord_4595412, baseEnd_4595412] using wordTrace_append hprefix tailTrace_4595412
  have hstable : (prefixWord ++ tailWord_4595412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4595412).length < 2 ^ (prefixWord ++ tailWord_4595412).sum := by decide
  have hdescent : baseEnd_4595412 < baseStart_4595412 := by decide
  rcases family_descends (prefixWord ++ tailWord_4595412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4595428 : List Nat := [2, 3, 1, 1, 1, 3, 1, 2, 1, 8]
def baseStart_4595428 : Nat := 118140960795 + 4595428 * 2 ^ 59
def prefixEnd_4595428 : Nat := 4983230072969 + 3 ^ 40 * 4595428 * 2
def baseEnd_4595428 : Nat := 786554459043250533505339

theorem tailTrace_4595428 : CollatzResearch.WordTrace tailWord_4595428 prefixEnd_4595428 786554459043250533505339 := by
  unfold tailWord_4595428
  simp only [CollatzResearch.WordTrace]
  refine ⟨83804514397778333731737469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111739352530371111642316625 83804514397778333731737469)
  ·
    refine ⟨31426692899166875149401551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83804514397778333731737469 31426692899166875149401551)
    ·
      refine ⟨47140039348750312724102327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31426692899166875149401551 47140039348750312724102327)
      ·
        refine ⟨70710059023125469086153491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47140039348750312724102327 70710059023125469086153491)
        ·
          refine ⟨106065088534688203629230237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70710059023125469086153491 106065088534688203629230237)
          ·
            refine ⟨39774408200508076360961339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106065088534688203629230237 39774408200508076360961339)
            ·
              refine ⟨59661612300762114541442009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39774408200508076360961339 59661612300762114541442009)
              ·
                refine ⟨44746209225571585906081507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59661612300762114541442009 44746209225571585906081507)
                ·
                  refine ⟨67119313838357378859122261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44746209225571585906081507 67119313838357378859122261)
                  ·
                    refine ⟨786554459043250533505339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 67119313838357378859122261 786554459043250533505339)
                    ·
                      rfl

theorem cell23_4595428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 1, 8].length) (baseStart_4595428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4595428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4595428 prefixEnd_4595428 := by exact prefixLift 4595428
  have htrace : WordTrace (prefixWord ++ tailWord_4595428) baseStart_4595428 baseEnd_4595428 := by
    simpa [prefixWord, tailWord_4595428, baseEnd_4595428] using wordTrace_append hprefix tailTrace_4595428
  have hstable : (prefixWord ++ tailWord_4595428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4595428).length < 2 ^ (prefixWord ++ tailWord_4595428).sum := by decide
  have hdescent : baseEnd_4595428 < baseStart_4595428 := by decide
  rcases family_descends (prefixWord ++ tailWord_4595428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4595446 : List Nat := [5, 1, 1, 1, 1, 5, 1, 2, 2, 1, 3]
def baseStart_4595446 : Nat := 118140960795 + 4595446 * 2 ^ 59
def prefixEnd_4595446 : Nat := 4983230072969 + 3 ^ 40 * 4595446 * 2
def baseEnd_4595446 : Nat := 2359672619781532530090935

theorem tailTrace_4595446 : CollatzResearch.WordTrace tailWord_4595446 prefixEnd_4595446 2359672619781532530090935 := by
  unfold tailWord_4595446
  simp only [CollatzResearch.WordTrace]
  refine ⟨10475605331843216033601887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 111739790206327637691753461 10475605331843216033601887)
  ·
    refine ⟨15713407997764824050402831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10475605331843216033601887 15713407997764824050402831)
    ·
      refine ⟨23570111996647236075604247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15713407997764824050402831 23570111996647236075604247)
      ·
        refine ⟨35355167994970854113406371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23570111996647236075604247 35355167994970854113406371)
        ·
          refine ⟨53032751992456281170109557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35355167994970854113406371 53032751992456281170109557)
          ·
            refine ⟨4971820499292776359697771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53032751992456281170109557 4971820499292776359697771)
            ·
              refine ⟨7457730748939164539546657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4971820499292776359697771 7457730748939164539546657)
              ·
                refine ⟨5593298061704373404659993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7457730748939164539546657 5593298061704373404659993)
                ·
                  refine ⟨4194973546278280053494995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5593298061704373404659993 4194973546278280053494995)
                  ·
                    refine ⟨6292460319417420080242493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4194973546278280053494995 6292460319417420080242493)
                    ·
                      refine ⟨2359672619781532530090935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6292460319417420080242493 2359672619781532530090935)
                      ·
                        rfl

theorem cell23_4595446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 2, 2, 1, 3].length) (baseStart_4595446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4595446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4595446 prefixEnd_4595446 := by exact prefixLift 4595446
  have htrace : WordTrace (prefixWord ++ tailWord_4595446) baseStart_4595446 baseEnd_4595446 := by
    simpa [prefixWord, tailWord_4595446, baseEnd_4595446] using wordTrace_append hprefix tailTrace_4595446
  have hstable : (prefixWord ++ tailWord_4595446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4595446).length < 2 ^ (prefixWord ++ tailWord_4595446).sum := by decide
  have hdescent : baseEnd_4595446 < baseStart_4595446 := by decide
  rcases family_descends (prefixWord ++ tailWord_4595446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4595505 : List Nat := [1, 2, 2, 3, 2, 2, 1, 1, 4, 5]
def baseStart_4595505 : Nat := 118140960795 + 4595505 * 2 ^ 59
def prefixEnd_4595505 : Nat := 4983230072969 + 3 ^ 40 * 4595505 * 2
def baseEnd_4595505 : Nat := 786567638380049266417721

theorem tailTrace_4595505 : CollatzResearch.WordTrace tailWord_4595505 prefixEnd_4595505 786567638380049266417721 := by
  unfold tailWord_4595505
  simp only [CollatzResearch.WordTrace]
  refine ⟨167611837216277709614027969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111741224810851806409351979 167611837216277709614027969)
  ·
    refine ⟨125708877912208282210520977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167611837216277709614027969 125708877912208282210520977)
    ·
      refine ⟨94281658434156211657890733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125708877912208282210520977 94281658434156211657890733)
      ·
        refine ⟨35355621912808579371709025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94281658434156211657890733 35355621912808579371709025)
        ·
          refine ⟨26516716434606434528781769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35355621912808579371709025 26516716434606434528781769)
          ·
            refine ⟨19887537325954825896586327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26516716434606434528781769 19887537325954825896586327)
            ·
              refine ⟨29831305988932238844879491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19887537325954825896586327 29831305988932238844879491)
              ·
                refine ⟨44746958983398358267319237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29831305988932238844879491 44746958983398358267319237)
                ·
                  refine ⟨8390054809387192175122357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44746958983398358267319237 8390054809387192175122357)
                  ·
                    refine ⟨786567638380049266417721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8390054809387192175122357 786567638380049266417721)
                    ·
                      rfl

theorem cell23_4595505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 4, 5].length) (baseStart_4595505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4595505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4595505 prefixEnd_4595505 := by exact prefixLift 4595505
  have htrace : WordTrace (prefixWord ++ tailWord_4595505) baseStart_4595505 baseEnd_4595505 := by
    simpa [prefixWord, tailWord_4595505, baseEnd_4595505] using wordTrace_append hprefix tailTrace_4595505
  have hstable : (prefixWord ++ tailWord_4595505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4595505).length < 2 ^ (prefixWord ++ tailWord_4595505).sum := by decide
  have hdescent : baseEnd_4595505 < baseStart_4595505 := by decide
  rcases family_descends (prefixWord ++ tailWord_4595505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4595509 : List Nat := [1, 3, 3, 1, 5, 1, 1, 1, 7]
def baseStart_4595509 : Nat := 118140960795 + 4595509 * 2 ^ 59
def prefixEnd_4595509 : Nat := 4983230072969 + 3 ^ 40 * 4595509 * 2
def baseEnd_4595509 : Nat := 262189441006973975955905

theorem tailTrace_4595509 : CollatzResearch.WordTrace tailWord_4595509 prefixEnd_4595509 262189441006973975955905 := by
  unfold tailWord_4595509
  simp only [CollatzResearch.WordTrace]
  refine ⟨167611983108263218297173581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111741322072175478864782387 167611983108263218297173581)
  ·
    refine ⟨62854493665598706861440093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167611983108263218297173581 62854493665598706861440093)
    ·
      refine ⟨23570435124599515073040035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62854493665598706861440093 23570435124599515073040035)
      ·
        refine ⟨35355652686899272609560053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23570435124599515073040035 35355652686899272609560053)
        ·
          refine ⟨3314592439396806807146255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35355652686899272609560053 3314592439396806807146255)
          ·
            refine ⟨4971888659095210210719383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3314592439396806807146255 4971888659095210210719383)
            ·
              refine ⟨7457832988642815316079075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4971888659095210210719383 7457832988642815316079075)
              ·
                refine ⟨11186749482964222974118613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7457832988642815316079075 11186749482964222974118613)
                ·
                  refine ⟨262189441006973975955905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11186749482964222974118613 262189441006973975955905)
                  ·
                    rfl

theorem cell23_4595509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 1, 7].length) (baseStart_4595509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4595509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4595509 prefixEnd_4595509 := by exact prefixLift 4595509
  have htrace : WordTrace (prefixWord ++ tailWord_4595509) baseStart_4595509 baseEnd_4595509 := by
    simpa [prefixWord, tailWord_4595509, baseEnd_4595509] using wordTrace_append hprefix tailTrace_4595509
  have hstable : (prefixWord ++ tailWord_4595509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4595509).length < 2 ^ (prefixWord ++ tailWord_4595509).sum := by decide
  have hdescent : baseEnd_4595509 < baseStart_4595509 := by decide
  rcases family_descends (prefixWord ++ tailWord_4595509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4595525 : List Nat := [1, 3, 1, 1, 1, 2, 3, 2, 4, 1, 4]
def baseStart_4595525 : Nat := 118140960795 + 4595525 * 2 ^ 59
def prefixEnd_4595525 : Nat := 4983230072969 + 3 ^ 40 * 4595525 * 2
def baseEnd_4595525 : Nat := 2359713184753237721003071

theorem tailTrace_4595525 : CollatzResearch.WordTrace tailWord_4595525 prefixEnd_4595525 2359713184753237721003071 := by
  unfold tailWord_4595525
  simp only [CollatzResearch.WordTrace]
  refine ⟨167612566676205253029756029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111741711117470168686504019 167612566676205253029756029)
  ·
    refine ⟨62854712503576969886158511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167612566676205253029756029 62854712503576969886158511)
    ·
      refine ⟨94282068755365454829237767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62854712503576969886158511 94282068755365454829237767)
      ·
        refine ⟨141423103133048182243856651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94282068755365454829237767 141423103133048182243856651)
        ·
          refine ⟨212134654699572273365784977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141423103133048182243856651 212134654699572273365784977)
          ·
            refine ⟨159100991024679205024338733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 212134654699572273365784977 159100991024679205024338733)
            ·
              refine ⟨59662871634254701884127025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 159100991024679205024338733 59662871634254701884127025)
              ·
                refine ⟨44747153725691026413095269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59662871634254701884127025 44747153725691026413095269)
                ·
                  refine ⟨8390091323567067452455363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44747153725691026413095269 8390091323567067452455363)
                  ·
                    refine ⟨12585136985350601178683045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8390091323567067452455363 12585136985350601178683045)
                    ·
                      refine ⟨2359713184753237721003071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12585136985350601178683045 2359713184753237721003071)
                      ·
                        rfl

theorem cell23_4595525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 4, 1, 4].length) (baseStart_4595525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4595525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4595525 prefixEnd_4595525 := by exact prefixLift 4595525
  have htrace : WordTrace (prefixWord ++ tailWord_4595525) baseStart_4595525 baseEnd_4595525 := by
    simpa [prefixWord, tailWord_4595525, baseEnd_4595525] using wordTrace_append hprefix tailTrace_4595525
  have hstable : (prefixWord ++ tailWord_4595525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4595525).length < 2 ^ (prefixWord ++ tailWord_4595525).sum := by decide
  have hdescent : baseEnd_4595525 < baseStart_4595525 := by decide
  rcases family_descends (prefixWord ++ tailWord_4595525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4595565 : List Nat := [1, 5, 1, 1, 1, 1, 2, 3, 8]
def baseStart_4595565 : Nat := 118140960795 + 4595565 * 2 ^ 59
def prefixEnd_4595565 : Nat := 4983230072969 + 3 ^ 40 * 4595565 * 2
def baseEnd_4595565 : Nat := 262192635997713062722543

theorem tailTrace_4595565 : CollatzResearch.WordTrace tailWord_4595565 prefixEnd_4595565 262192635997713062722543 := by
  unfold tailWord_4595565
  simp only [CollatzResearch.WordTrace]
  refine ⟨167614025596060339861212149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111742683730706893240808099 167614025596060339861212149)
  ·
    refine ⟨15713814899630656861988639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 167614025596060339861212149 15713814899630656861988639)
    ·
      refine ⟨23570722349445985292982959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15713814899630656861988639 23570722349445985292982959)
      ·
        refine ⟨35356083524168977939474439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23570722349445985292982959 35356083524168977939474439)
        ·
          refine ⟨53034125286253466909211659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35356083524168977939474439 53034125286253466909211659)
          ·
            refine ⟨79551187929380200363817489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53034125286253466909211659 79551187929380200363817489)
            ·
              refine ⟨59663390947035150272863117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79551187929380200363817489 59663390947035150272863117)
              ·
                refine ⟨22373771605138181352323669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59663390947035150272863117 22373771605138181352323669)
                ·
                  refine ⟨262192635997713062722543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22373771605138181352323669 262192635997713062722543)
                  ·
                    rfl

theorem cell23_4595565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 8].length) (baseStart_4595565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4595565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4595565 prefixEnd_4595565 := by exact prefixLift 4595565
  have htrace : WordTrace (prefixWord ++ tailWord_4595565) baseStart_4595565 baseEnd_4595565 := by
    simpa [prefixWord, tailWord_4595565, baseEnd_4595565] using wordTrace_append hprefix tailTrace_4595565
  have hstable : (prefixWord ++ tailWord_4595565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4595565).length < 2 ^ (prefixWord ++ tailWord_4595565).sum := by decide
  have hdescent : baseEnd_4595565 < baseStart_4595565 := by decide
  rcases family_descends (prefixWord ++ tailWord_4595565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4595569 : List Nat := [1, 2, 2, 2, 1, 3, 3, 4, 1, 4]
def baseStart_4595569 : Nat := 118140960795 + 4595569 * 2 ^ 59
def prefixEnd_4595569 : Nat := 4983230072969 + 3 ^ 40 * 4595569 * 2
def baseEnd_4595569 : Nat := 786578592634011849617623

theorem tailTrace_4595569 : CollatzResearch.WordTrace tailWord_4595569 prefixEnd_4595569 786578592634011849617623 := by
  unfold tailWord_4595569
  simp only [CollatzResearch.WordTrace]
  refine ⟨167614171488045848544357761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111742780992030565696238507 167614171488045848544357761)
  ·
    refine ⟨125710628616034386408268321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167614171488045848544357761 125710628616034386408268321)
    ·
      refine ⟨94282971462025789806201241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125710628616034386408268321 94282971462025789806201241)
      ·
        refine ⟨70712228596519342354650931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94282971462025789806201241 70712228596519342354650931)
        ·
          refine ⟨106068342894779013531976397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70712228596519342354650931 106068342894779013531976397)
          ·
            refine ⟨39775628585542130074491149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106068342894779013531976397 39775628585542130074491149)
            ·
              refine ⟨14915860719578298777934181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39775628585542130074491149 14915860719578298777934181)
              ·
                refine ⟨2796723884920931020862659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14915860719578298777934181 2796723884920931020862659)
                ·
                  refine ⟨4195085827381396531293989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2796723884920931020862659 4195085827381396531293989)
                  ·
                    refine ⟨786578592634011849617623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4195085827381396531293989 786578592634011849617623)
                    ·
                      rfl

theorem cell23_4595569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 4, 1, 4].length) (baseStart_4595569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4595569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4595569 prefixEnd_4595569 := by exact prefixLift 4595569
  have htrace : WordTrace (prefixWord ++ tailWord_4595569) baseStart_4595569 baseEnd_4595569 := by
    simpa [prefixWord, tailWord_4595569, baseEnd_4595569] using wordTrace_append hprefix tailTrace_4595569
  have hstable : (prefixWord ++ tailWord_4595569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4595569).length < 2 ^ (prefixWord ++ tailWord_4595569).sum := by decide
  have hdescent : baseEnd_4595569 < baseStart_4595569 := by decide
  rcases family_descends (prefixWord ++ tailWord_4595569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4595575 : List Nat := [1, 1, 3, 1, 1, 2, 1, 1, 4, 5, 3]
def baseStart_4595575 : Nat := 118140960795 + 4595575 * 2 ^ 59
def prefixEnd_4595575 : Nat := 4983230072969 + 3 ^ 40 * 4595575 * 2
def baseEnd_4595575 : Nat := 2359738858785962525377841

theorem tailTrace_4595575 : CollatzResearch.WordTrace tailWord_4595575 prefixEnd_4595575 2359738858785962525377841 := by
  unfold tailWord_4595575
  simp only [CollatzResearch.WordTrace]
  refine ⟨167614390326024111569076179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111742926884016074379384119 167614390326024111569076179)
  ·
    refine ⟨251421585489036167353614269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167614390326024111569076179 251421585489036167353614269)
    ·
      refine ⟨94283094558388562757605351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 251421585489036167353614269 94283094558388562757605351)
      ·
        refine ⟨141424641837582844136408027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94283094558388562757605351 141424641837582844136408027)
        ·
          refine ⟨212136962756374266204612041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141424641837582844136408027 212136962756374266204612041)
          ·
            refine ⟨159102722067280699653459031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 212136962756374266204612041 159102722067280699653459031)
            ·
              refine ⟨238654083100921049480188547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159102722067280699653459031 238654083100921049480188547)
              ·
                refine ⟨357981124651381574220282821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 238654083100921049480188547 357981124651381574220282821)
                ·
                  refine ⟨67121460872134045166303029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 357981124651381574220282821 67121460872134045166303029)
                  ·
                    refine ⟨6292636956762566734340909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 67121460872134045166303029 6292636956762566734340909)
                    ·
                      refine ⟨2359738858785962525377841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6292636956762566734340909 2359738858785962525377841)
                      ·
                        rfl

theorem cell23_4595575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 5, 3].length) (baseStart_4595575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4595575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4595575 prefixEnd_4595575 := by exact prefixLift 4595575
  have htrace : WordTrace (prefixWord ++ tailWord_4595575) baseStart_4595575 baseEnd_4595575 := by
    simpa [prefixWord, tailWord_4595575, baseEnd_4595575] using wordTrace_append hprefix tailTrace_4595575
  have hstable : (prefixWord ++ tailWord_4595575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4595575).length < 2 ^ (prefixWord ++ tailWord_4595575).sum := by decide
  have hdescent : baseEnd_4595575 < baseStart_4595575 := by decide
  rcases family_descends (prefixWord ++ tailWord_4595575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4595662 : List Nat := [4, 1, 1, 1, 2, 2, 2, 1, 3, 2, 4]
def baseStart_4595662 : Nat := 118140960795 + 4595662 * 2 ^ 59
def prefixEnd_4595662 : Nat := 4983230072969 + 3 ^ 40 * 4595662 * 2
def baseEnd_4595662 : Nat := 2359783531602903684989941

theorem tailTrace_4595662 : CollatzResearch.WordTrace tailWord_4595662 prefixEnd_4595662 2359783531602903684989941 := by
  unfold tailWord_4595662
  simp only [CollatzResearch.WordTrace]
  refine ⟨20952195434588615678436655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111745042317805950284995493 20952195434588615678436655)
  ·
    refine ⟨31428293151882923517654983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20952195434588615678436655 31428293151882923517654983)
    ·
      refine ⟨47142439727824385276482475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31428293151882923517654983 47142439727824385276482475)
      ·
        refine ⟨70713659591736577914723713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47142439727824385276482475 70713659591736577914723713)
        ·
          refine ⟨53035244693802433436042785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70713659591736577914723713 53035244693802433436042785)
          ·
            refine ⟨39776433520351825077032089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53035244693802433436042785 39776433520351825077032089)
            ·
              refine ⟨29832325140263868807774067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39776433520351825077032089 29832325140263868807774067)
              ·
                refine ⟨44748487710395803211661101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29832325140263868807774067 44748487710395803211661101)
                ·
                  refine ⟨16780682891398426204372913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44748487710395803211661101 16780682891398426204372913)
                  ·
                    refine ⟨12585512168548819653279685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16780682891398426204372913 12585512168548819653279685)
                    ·
                      refine ⟨2359783531602903684989941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12585512168548819653279685 2359783531602903684989941)
                      ·
                        rfl

theorem cell23_4595662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 3, 2, 4].length) (baseStart_4595662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4595662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4595662 prefixEnd_4595662 := by exact prefixLift 4595662
  have htrace : WordTrace (prefixWord ++ tailWord_4595662) baseStart_4595662 baseEnd_4595662 := by
    simpa [prefixWord, tailWord_4595662, baseEnd_4595662] using wordTrace_append hprefix tailTrace_4595662
  have hstable : (prefixWord ++ tailWord_4595662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4595662).length < 2 ^ (prefixWord ++ tailWord_4595662).sum := by decide
  have hdescent : baseEnd_4595662 < baseStart_4595662 := by decide
  rcases family_descends (prefixWord ++ tailWord_4595662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4595669 : List Nat := [1, 3, 2, 3, 2, 2, 2, 1, 1, 1, 5]
def baseStart_4595669 : Nat := 118140960795 + 4595669 * 2 ^ 59
def prefixEnd_4595669 : Nat := 4983230072969 + 3 ^ 40 * 4595669 * 2
def baseEnd_4595669 : Nat := 2359787125967485157602409

theorem tailTrace_4595669 : CollatzResearch.WordTrace tailWord_4595669 prefixEnd_4595669 2359787125967485157602409 := by
  unfold tailWord_4595669
  simp only [CollatzResearch.WordTrace]
  refine ⟨167617818787683565622998061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111745212525122377081998707 167617818787683565622998061)
  ·
    refine ⟨62856682045381337108624273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167617818787683565622998061 62856682045381337108624273)
    ·
      refine ⟨47142511534036002831468205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62856682045381337108624273 47142511534036002831468205)
      ·
        refine ⟨17678441825263501061800577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47142511534036002831468205 17678441825263501061800577)
        ·
          refine ⟨13258831368947625796350433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17678441825263501061800577 13258831368947625796350433)
          ·
            refine ⟨9944123526710719347262825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13258831368947625796350433 9944123526710719347262825)
            ·
              refine ⟨7458092645033039510447119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9944123526710719347262825 7458092645033039510447119)
              ·
                refine ⟨11187138967549559265670679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7458092645033039510447119 11187138967549559265670679)
                ·
                  refine ⟨16780708451324338898506019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11187138967549559265670679 16780708451324338898506019)
                  ·
                    refine ⟨25171062676986508347759029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16780708451324338898506019 25171062676986508347759029)
                    ·
                      refine ⟨2359787125967485157602409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25171062676986508347759029 2359787125967485157602409)
                      ·
                        rfl

theorem cell23_4595669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_4595669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4595669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4595669 prefixEnd_4595669 := by exact prefixLift 4595669
  have htrace : WordTrace (prefixWord ++ tailWord_4595669) baseStart_4595669 baseEnd_4595669 := by
    simpa [prefixWord, tailWord_4595669, baseEnd_4595669] using wordTrace_append hprefix tailTrace_4595669
  have hstable : (prefixWord ++ tailWord_4595669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4595669).length < 2 ^ (prefixWord ++ tailWord_4595669).sum := by decide
  have hdescent : baseEnd_4595669 < baseStart_4595669 := by decide
  rcases family_descends (prefixWord ++ tailWord_4595669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4595683 : List Nat := [1, 1, 1, 6, 1, 4, 1, 1, 3, 2, 2]
def baseStart_4595683 : Nat := 118140960795 + 4595683 * 2 ^ 59
def prefixEnd_4595683 : Nat := 4983230072969 + 3 ^ 40 * 4595683 * 2
def baseEnd_4595683 : Nat := 2359794314696648102827345

theorem tailTrace_4595683 : CollatzResearch.WordTrace tailWord_4595683 prefixEnd_4595683 2359794314696648102827345 := by
  unfold tailWord_4595683
  simp only [CollatzResearch.WordTrace]
  refine ⟨167618329409632846014007703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111745552939755230676005135 167618329409632846014007703)
  ·
    refine ⟨251427494114449269021011555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167618329409632846014007703 251427494114449269021011555)
    ·
      refine ⟨377141241171673903531517333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251427494114449269021011555 377141241171673903531517333)
      ·
        refine ⟨17678495679922214228039875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 377141241171673903531517333 17678495679922214228039875)
        ·
          refine ⟨26517743519883321342059813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17678495679922214228039875 26517743519883321342059813)
          ·
            refine ⟨4972076909978122751636215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26517743519883321342059813 4972076909978122751636215)
            ·
              refine ⟨7458115364967184127454323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4972076909978122751636215 7458115364967184127454323)
              ·
                refine ⟨11187173047450776191181485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7458115364967184127454323 11187173047450776191181485)
                ·
                  refine ⟨4195189892794041071693057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11187173047450776191181485 4195189892794041071693057)
                  ·
                    refine ⟨3146392419595530803769793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4195189892794041071693057 3146392419595530803769793)
                    ·
                      refine ⟨2359794314696648102827345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3146392419595530803769793 2359794314696648102827345)
                      ·
                        rfl

theorem cell23_4595683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 1, 3, 2, 2].length) (baseStart_4595683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4595683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4595683 prefixEnd_4595683 := by exact prefixLift 4595683
  have htrace : WordTrace (prefixWord ++ tailWord_4595683) baseStart_4595683 baseEnd_4595683 := by
    simpa [prefixWord, tailWord_4595683, baseEnd_4595683] using wordTrace_append hprefix tailTrace_4595683
  have hstable : (prefixWord ++ tailWord_4595683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4595683).length < 2 ^ (prefixWord ++ tailWord_4595683).sum := by decide
  have hdescent : baseEnd_4595683 < baseStart_4595683 := by decide
  rcases family_descends (prefixWord ++ tailWord_4595683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
